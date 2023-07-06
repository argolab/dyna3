(ns dyna.rexpr-aggregators-optimized
  (:require [dyna.utils :refer :all])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.rexpr :refer :all])
  (:require [dyna.system :as system])
  (:require [dyna.rexpr-aggregators :refer [aggregators]])
  (:require [dyna.rexpr-constructors :refer [is-disjunct-op? make-disjunct-op]])
  (:require [dyna.context :as context])
  (:require [dyna.prefix-trie :as trie])
  (:require [dyna.iterators :refer [make-skip-variables-iterator run-iterator]])
  (:require [dyna.rexpr-pretty-printer :refer [rexpr-printer optional-line-break indent-increase indent-decrease]])
  (:require [clojure.set :refer [difference union intersection subset?]])
  (:require [clojure.string :refer [join]])
  (:import [dyna.rexpr proj-rexpr disjunct-rexpr aggregator-rexpr])
  (:import [dyna.rexpr_disjunction disjunct-op-rexpr])
  (:import [dyna.prefix_trie PrefixTrie])
  (:import [dyna UnificationFailure ClojureUnorderedVector ClojureHashMap]))


(def-base-rexpr aggregator-op-outer [:unchecked operator
                                     :var result
                                     :rexpr bodies]
  (is-constraint? [this] true)
  (all-conjunctive-rexprs [this] (all-conjunctive-rexprs bodies)))

(def-base-rexpr aggregator-op-inner [:hidden-var incoming
                                     :var-list projected ;; all of these variables are hidden
                                     :rexpr body]
  (exposed-variables [this]
                     (cache-field cached-exposed-variables
                                  (difference (exposed-variables body)
                                              (into #{incoming} projected))))
  (remap-variables [this variable-map]
                   ;; this is going to have to perform remapping of the body
                   ;(dyna-assert (not (some (into #{incoming} projected) (keys variable-map))))
                   (let [variable-map (apply dissoc variable-map incoming projected)]
                     (if (empty? variable-map)
                       this
                       (make-aggregator-op-inner incoming projected
                                                 (remap-variables body
                                                                  (apply dissoc variable-map incoming projected))))))

  (remap-variables-handle-hidden [this variable-map]
                                 (let [new-hidden-names (into {} (for [v (if (is-variable? incoming)
                                                                           (cons incoming projected)
                                                                           projected)]
                                                                   [v (make-variable (gensym 'agg-op-hidden))]))
                                       new-map (merge variable-map new-hidden-names)]
                                   (make-aggregator-op-inner (get new-map incoming incoming)
                                                             (vec (map new-map projected))
                                                             (remap-variables-handle-hidden body new-map))))
  (all-conjunctive-rexprs [this]
                          (cons [#{} this]
                                (let [vs (conj (ensure-set projected) incoming)]
                                  (for [[proj-out rexpr] (all-conjunctive-rexprs body)]
                                    [(union proj-out (intersection vs (exposed-variables rexpr))) rexpr])))))

(def ^{:dynamic true :private true} *aggregator-print-input-depth* 0)
(defmethod rexpr-printer aggregator-op-outer-rexpr [r]
  (binding [*aggregator-print-input-depth* (+ 1 *aggregator-print-input-depth*)]
    (str "(" (rexpr-printer (:result r)) "=`" (:name (:operator r)) "`("
         (indent-increase) "AGGIN_" *aggregator-print-input-depth* ", " (optional-line-break)
         (rexpr-printer (:bodies r)) (indent-decrease) "))")))
(defmethod rexpr-printer aggregator-op-inner-rexpr [r]
  (let [bod (str (indent-increase)
                 (join (map #(str "proj(" (rexpr-printer %) ",") (:projected r)))
                 (optional-line-break)
                 (rexpr-printer (:body r))
                 (optional-line-break)
                 (join (repeat (count (:projected r)) ")"))
                 (indent-decrease))]
    (if (is-variable? (:incoming r))
      (str "proj(" (indent-increase) (rexpr-printer (:incoming r)) ", (AGGIN_" *aggregator-print-input-depth* "=" (rexpr-printer (:incoming r)) ")*" (optional-line-break)
           bod
           (indent-decrease)
           ")")
      (str "(AGGIN_" *aggregator-print-input-depth* "=" (rexpr-printer (:incoming r)) ")*" bod))))

;; this might be something that the memoization is going to want to override,
;; which would allow for it to get the result of aggregation directly
(def ^{:dynamic true} *aggregator-op-contribute-value*
  (fn r
    ([value mult]
     ;; return a dummy expression in the case that there is nothing that is able
     ;; to take the value, this can hold the value until there is something else
     (make-aggregator-op-inner (make-constant value) [] (make-multiplicity mult)))))
    ;([value] (r value 1))


(def ^{:dynamic true} *aggregator-op-additional-constraints*
  ;; additional constraints that can be added to the R-expr in the case that it
  ;; would not be resolved, this can take into account the current value known
  ;; to the aggregator
  (fn [incoming-variable]
    (make-multiplicity 1)))

(def ^{:dynamic true} *aggregator-op-saturated*
  ;; if the current bindings to variables are sautrated, meaning that the
  ;; contributed values are done, then we can avoid continuing to process other stuff
  (fn [] false))

(def ^{:dynamic true} *aggregator-op-get-variable-value*
  ;; aggregator uses get-value by default to get the value of a variable from
  ;; the context we might need to override that in some cases---such as
  ;; memoization where the variables have been renamed, but we might not be
  ;; using the new names, or in the jit generated code

  get-value)

(def ^{:dynamic true} *aggregator-op-should-eager-run-iterators*
  ;; if we want to eagerly run iterators.  This is something that we want to do
  ;; in the case of memoization, as that corresponds with doing work ahead of
  ;; time (before it will get put into the memo table)
  false)


(def-rewrite
  :match {:rexpr (aggregator (:unchecked operator) (:any result-variable) (:any incoming-variable)
                             (#(= % true) body-is-conjunctive) (:rexpr R))
          :check system/*use-optimized-rexprs*}
  :run-at [:construction :inference]
  (let [inner (make-aggregator-op-inner incoming-variable
                                                        []
                                                        R)]
    (make-aggregator-op-outer (get @aggregators operator) result-variable inner)))

;; if there is a project nested inside of the aggregator inner expression, then we are going pull the projection out and add it to the aggregator
(def-rewrite
  :match {:rexpr (aggregator-op-inner (:any incoming) (:variable-list projected-vars) (proj (:variable hid-var) (:rexpr R)))
          :check (and system/*use-optimized-rexprs* ;; this check should not be necessary here....
                      (not (some #{hid-var} projected-vars)))}
  :run-at :construction
  (make-aggregator-op-inner incoming (conj projected-vars hid-var) R))

(def-rewrite
  :match {:rexpr (aggregator-op-inner (:any incoming) (:variable-list projected-vars) (conjunct (:rexpr-list Rs)))}
  :run-at :construction
  (let [exposed (exposed-variables rexpr)
        pvs (into #{incoming} projected-vars)
        pr (first (filter #(and (is-proj? %) (not (pvs (:var %))) (not (exposed (:var %)))) Rs))]
    (if pr
      (make-aggregator-op-inner incoming
                                (conj projected-vars (:var pr))
                                (make-conjunct (vec (for [r Rs]
                                                      (if (identical? r pr)
                                                        (:body r)
                                                        r)))))
      nil)))

;; we want to lift the disjunction out of the aggregation, as we can handle the disjunctions before there are
(def-rewrite
  :match {:rexpr (aggregator-op-inner (:any incoming) (:any-list projected-vars) (disjunct (:rexpr-list Rs)))
          :check system/*use-optimized-rexprs*}
  :run-at :construction
  (make-disjunct (vec (map #(make-aggregator-op-inner incoming projected-vars %) Rs))))

;; lift the optimized disjunct out of the aggregation inner
(def-rewrite
  :match {:rexpr (aggregator-op-inner (:any incoming) (:any-list projected-vars) (disjunct-op (:any-list disjunction-variables) (:unchecked trie-Rs)))
          :check system/*use-optimized-rexprs*}
  :run-at :construction
  (let [incoming-idx (indexof disjunction-variables #{incoming})
        pjv (into (if (is-variable? incoming) #{incoming} #{}) projected-vars)
        new-trie-vars (for [[idx var] (zipseq (range) disjunction-variables)
                            :when (not (pjv var))]
                        [idx var])
        save-proj-vars (for [[idx var] (zipseq (range) disjunction-variables)
                             :when (pjv var)]
                         [idx var])
        resulting-trie (volatile! (trie/make-PrefixTrie (count new-trie-vars) 0 nil))
        ;num-children (volatile! 0)
        ]
    (doseq [[var-binding children] (trie/trie-get-values-collection trie-Rs nil)]
      (let [income-val (if (nil? incoming-idx)
                         (get-value incoming)
                         (nth var-binding incoming-idx))
            income-var (if (nil? income-val) incoming (make-constant income-val))
            trie-binding (vec (map #(nth var-binding (first %)) new-trie-vars))
            pvb (vec (for [[idx var] save-proj-vars
                           :let [bnd (nth var-binding idx)]
                           :when (and (not (nil? bnd)) (not= incoming var))]
                       (make-no-simp-unify var (make-constant bnd))))
            new-children (vec (for [c children]
                                (make-aggregator-op-inner income-var projected-vars (make-conjunct (conj pvb c)))))]
        ;(vswap! num-children + (count new-children))
        (vswap! resulting-trie trie/trie-update-collection trie-binding
                (fn [col]
                  (concat col new-children)))))
    (let [ret (make-disjunct-op (vec (map second new-trie-vars)) @resulting-trie)]
      #_(when (<= @num-children 1)
        (debug-repl "optimized aggregator disjunction trie"))
      ret)))

(def-rewrite
  :match (aggregator-op-inner (:any incoming) (:any-list projected-vars) (is-empty-rexpr? _))
  :run-at :construction
  (make-multiplicity 0))

(def-rewrite
  :match {:rexpr (aggregator-op-inner (:any incoming) (:any-list projected-vars) (:rexpr R))
          :check (not (or (is-constant? incoming) (some #{incoming} (exposed-variables R))))}
  :is-debug-check-rewrite true
  :run-at :construction
  (do
    (debug-repl "bad agg op inner")
    (???)))

(defn- convert-to-trie-mul1 [cnt trie lower-value]
  (if (= cnt 0)
    (try (let [key (lower-value trie)]
           [(trie/trie-hash-map key (ClojureUnorderedVector/create [(make-multiplicity 1)])) (if (nil? key) 1 0)])
         (catch UnificationFailure err [{} 0])) ;; if there is a unification failure by lower, then this is just empty
    (let [contains-wildcard (volatile! 0)
          n (into ClojureHashMap/EMPTY
                  (for [[k v] trie
                        :let [[n2 wildcard] (convert-to-trie-mul1 (- cnt 1) v lower-value)]]
                    (do (vswap! contains-wildcard bit-or wildcard)
                        [k n2])))]
      [n (bit-or (bit-shift-left @contains-wildcard 1) (if (contains? n nil) 1 0))])))

(defn- convert-to-trie-agg [cnt trie]
  (if (= cnt 0)
    [(ClojureUnorderedVector/create [(make-aggregator-op-inner (make-constant trie) [] (make-multiplicity 1))]) 0]
    (let [contains-wildcard (volatile! 0)
          n (into ClojureHashMap/EMPTY
                  (for [[k v] trie
                        :let [[n2 wildcard] (convert-to-trie-agg (- cnt 1) v)]]
                    (do (vswap! contains-wildcard bit-or wildcard)
                        [k n2])))]
      [n (bit-or (bit-shift-left @contains-wildcard 1) (if (contains? n nil) 1 0))])))

(defn- convert-to-trie-rexprs [cnt trie]
  (if (= cnt 0)
    [(ClojureUnorderedVector/create trie) 0]
    (let [contains-wildcard (volatile! 0)
          n (into ClojureHashMap/EMPTY
                  (for [[k v] trie
                        :let [[r wildcard] (convert-to-trie-rexprs (- cnt 1) v)]
                        :when (not (empty? r))]
                    (do (vswap! contains-wildcard bit-or wildcard)
                        [k r])))]
      [n (bit-or (bit-shift-left @contains-wildcard 1) (if (contains? n nil) 1 0))])))

(def-rewrite
  :match (aggregator-op-outer (:unchecked operator) (:any result-variable) (:rexpr Rbody))
  :run-at [:standard :inference]
  (let [accumulator (volatile! nil)
        exposed-vars (vec (exposed-variables Rbody))
        ctx (context/make-nested-context-aggregator-op-outer Rbody)
        contrib-func (fn [value mult]
                       (assert (>= mult 1))
                       (dyna-assert (not (nil? value)))
                       (let [kvals (vec (map *aggregator-op-get-variable-value* exposed-vars))]
                         ;(debug-in-block "contrib")
                         (vswap! accumulator update-in kvals (fn [old]
                                                               (if (nil? old)
                                                                 ((:many-items operator) value mult)
                                                                 ((:combine-mult operator) old value mult)))))
                       ;; this will return mult 0, as we are saving the values directly rather than having this come back through the R-expr
                       (make-multiplicity 0))
        additional-constraint-func
        (if (and (= simplify simplify-inference) (:add-to-in-rexpr operator))
          (let [ati (:add-to-in-rexpr operator)]
            (fn [incoming-variable]
              (let [kvals (vec (map *aggregator-op-get-variable-value* exposed-vars))
                    cur-val (if (empty? exposed-vars)
                              (get @accumulator nil)
                              (get-in @accumulator kvals))]
                (if-not (nil? cur-val)
                  (simplify-inference (ati cur-val incoming-variable))
                  (make-multiplicity 1)))))
          (fn [incoming-variable] ;; there is no additional constriants which can be added, so return mult 1
            (make-multiplicity 1)))
        check-saturated-func
        (if (:saturate operator)
          (let [sf (:saturate operator)]
            (fn []
              (let [kvals (vec (map *aggregator-op-get-variable-value* exposed-vars))
                   cur-val (if (empty? exposed-vars)
                              (get @accumulator nil)
                              (get-in @accumulator kvals))]
                ;; it is not just the current value, but if there is a "more general" version of the bindings (something with nil)
                ;; that also would cause saturate to be true, then this can be done
                (when-not (nil? cur-val)
                  (sf cur-val)))))
          (fn [] false))]
    (binding [*aggregator-op-contribute-value* contrib-func
              *aggregator-op-additional-constraints* additional-constraint-func
              *aggregator-op-saturated* check-saturated-func
              *aggregator-op-should-eager-run-iterators* false]
      (let [ret (context/bind-context ctx (try (simplify Rbody)
                                               (catch UnificationFailure e (make-multiplicity 0))))]
        (if (is-empty-rexpr? ret)
          (if (nil? @accumulator)
            (do ;(debug-repl )
                ;(make-multiplicity 0)
                ;; just pass along the empty result, as this might have tracing information attached
                ret)
            (do
              ;; this needs to identify any values contained in the accumulator trie and turn those into some disjunct or return the single value
              ;; there should be no aggregator remaining in this case, as it will have that all of the values will have already gotten resolved
              (if (empty? exposed-vars)
                (make-unify result-variable (make-constant ((:lower-value operator identity) (get @accumulator nil)))) ;; if there are no keys, it will be stored like {nil value} by update-in
                (make-conjunct
                 (loop [ret []
                        ev exposed-vars
                        trie @accumulator]
                   (if (empty? ev) ;; then we got to the end of the list
                     (conj ret (make-unify result-variable (make-constant ((:lower-value operator identity) trie))))
                     (if (and (= (count trie) 1) (not (nil? (first (keys trie)))))
                       (recur (conj ret (make-unify (first ev) (make-constant (first (keys trie)))))
                              (rest ev)
                              (first (vals trie)))
                       (conj ret (make-disjunct-op
                                  (conj (vec ev) result-variable)
                                  (let [[trie-root trie-wildcard] (convert-to-trie-mul1 (count ev) trie (:lower-value operator identity))]
                                    (trie/make-PrefixTrie (+ 1 (count ev))
                                                          trie-wildcard
                                                          trie-root)))))))))))
          (if (nil? @accumulator)
            (make-aggregator-op-outer operator result-variable ret)
            (let [accum-vals (if (empty? exposed-vars)
                               (make-aggregator-op-inner (make-constant (get @accumulator nil)) [] (make-multiplicity 1))
                               (make-disjunct-op exposed-vars
                                                 (let [[trie-root trie-wildcard] (convert-to-trie-agg (count exposed-vars) @accumulator)]
                                                   (trie/make-PrefixTrie (count exposed-vars) trie-wildcard trie-root))))
                  ;; this will merge the tries due to rewrites on the disjunction construction
                  rr (make-aggregator-op-outer operator result-variable (make-disjunct [accum-vals
                                                                                        ret]))
                  rr2 (if (and (= simplify simplify-inference) (:add-to-out-rexpr operator) (empty? exposed-vars) (not (nil? (get @accumulator nil))))
                        (make-conjunct [rr ((:add-to-out-rexpr operator) (get @accumulator nil) result-variable)])
                        rr)]
              rr2)))))))

;; in the case that the disjunct is lifted out, it would be possible that
;; something which does not contain the proejcted vars and does not contain the
;; incoming-variables is also going to be lifted out.  Which means that this is
;; not able to just perform "sideways" passing of the information
(def-rewrite
  :match (aggregator-op-inner (:any incoming-variable) (:any-list projected-vars) (:rexpr Rbody))
  :run-at [:standard :inference]
  (let [ctx (context/make-nested-context-aggregator-op-inner Rbody projected-vars incoming-variable)]
    (context/bind-context-raw
     ctx
     (let [exposed (vec (exposed-variables rexpr)) ;; if all of the exposed are ground, then we should just go ahead and compute the value
           parent-is-bound (vec (map is-bound? exposed))
           nR (try (simplify Rbody)
                   (catch UnificationFailure e (make-multiplicity 0)))
           eager-run-iterators *aggregator-op-should-eager-run-iterators*]
       (cond
         (is-empty-rexpr? nR) nR ;(make-multiplicity 0)

         (and (is-multiplicity? nR) (is-bound-in-context? incoming-variable ctx))
         (let [ret (*aggregator-op-contribute-value* (get-value-in-context incoming-variable ctx) (:mult nR))]
           ret)

         (or (every? is-bound? exposed)
             (and eager-run-iterators
                  (not *simplify-looking-for-fast-fail-only*)))
         (let [iterators (find-iterators nR)
               accumulator (volatile! nil)
               result-rexprs (volatile! nil)]
           ;; will loop over assignments to all of the variables
           (try
             (run-iterator
              :iterators iterators
              :bind-all true
              :rexpr-in nR
              :rexpr-result inner-r
              :simplify #(binding [*simplify-looking-for-fast-fail-only* true] (simplify %))

                                        ;:required [incoming-variable] ;; we still want to loop even if we can't directly assign this value
              (let [inner-r (simplify inner-r)]
                ;; if this is not a multiplicity, then this expression has something that can not be handled
                ;; in which case this will need to report an error, or return the R-expr while having that it can not be solved...
                (when (is-empty-rexpr? inner-r)
                  (debug-repl "empty r"))
                (if (is-multiplicity? inner-r)
                  (let [val (get-value incoming-variable)
                        mult (:mult inner-r)]
                    (when-not (= mult 0)
                      (dyna-assert (not (nil? val)))
                      (let [rc (*aggregator-op-contribute-value* val mult)]
                        (when-not (is-empty-rexpr? rc)
                          ;; then we have to save the result of this R-expr, as it could not get processed for some reason
                          (if eager-run-iterators
                            (vswap! accumulator update-in (map get-value exposed) conj rc)
                            (vswap! result-rexprs conj rc))))))
                  (when-not (*aggregator-op-saturated*)
                                        ;(debug-repl "all bound but not done")
                    (let [new-incoming (if (is-bound? incoming-variable)
                                         (make-constant (get-value incoming-variable))
                                         incoming-variable)
                          remapping-map (into {} (for [v (cons incoming-variable projected-vars)
                                                       :when (and (not (is-constant? v)) (is-bound? v))]
                                                   [v (make-constant (get-value v))]))
                          new-projected (vec (filter #(not (is-bound? %)) projected-vars))
                                        ;zzz (dyna-assert (subset? (keys remapping-map) (exposed-variables inner-r)))
                          new-body
                          (debug-binding [*current-simplify-stack* (conj *current-simplify-stack* inner-r)]
                                         (remap-variables inner-r remapping-map))
                          other-constraints (*aggregator-op-additional-constraints* new-incoming)
                          ;; zzz (when (and *aggregator-op-should-eager-run-iterators* (not= parent-is-bound (map is-bound? exposed)))
                          ;;       (debug-repl "agg egg run"))
                          rc (make-aggregator-op-inner new-incoming new-projected
                                                       (if (not= (make-multiplicity 1) other-constraints)
                                                         (make-conjunct [new-body other-constraints])
                                                         new-body))]
                      (when (is-empty-rexpr? rc)
                        (debug-repl "add empty"))
                      (if eager-run-iterators
                        (vswap! accumulator update-in (map get-value exposed) conj rc)
                        (vswap! result-rexprs conj rc)))))))
             (catch Exception err
               (debug-repl "err")))

           (if eager-run-iterators
             (if (empty? @accumulator)
               (make-multiplicity 0)
               (let [[root wildcard] (convert-to-trie-rexprs (count exposed) @accumulator)
                     ret (make-disjunct-op exposed
                                           (trie/make-PrefixTrie (count exposed) wildcard root))]
                                        ;(debug-repl "inner accum")
                 (when (not= (ensure-set (union (filter is-bound? (exposed-variables rexpr)) (exposed-variables ret)))
                             (ensure-set (exposed-variables rexpr)))
                   (debug-repl "diff exposed"))
                 (when (is-empty-rexpr? ret)
                   (debug-repl "empty ret"))
                 ret))
             (if (empty? @result-rexprs)
               (make-multiplicity 0)
               (let [ret (make-disjunct (vec @result-rexprs))]
                 (when (is-empty-rexpr? ret)
                   (debug-repl "empty ret"))
                 ret))))

         :else
         (let [new-incoming (if (is-bound-in-context? incoming-variable ctx)
                              (make-constant (get-value-in-context incoming-variable ctx))
                              incoming-variable)
               remapping-map (into {} (for [v (cons incoming-variable projected-vars)
                                            :when (and (not (is-constant? v)) (is-bound-in-context? v ctx))]
                                        [v (make-constant (get-value-in-context v ctx))]))
               new-projected (vec (filter #(not (is-bound-in-context? % ctx)) projected-vars))
               new-body (remap-variables nR remapping-map)
               ret (make-aggregator-op-inner new-incoming new-projected new-body)]
           #_(when (not= (map is-bound? exposed) parent-is-bound)
               (debug-repl "bound in body"))
           (when-not (subset? (remove is-bound? (exposed-variables rexpr)) (exposed-variables ret))
             (debug-repl "diff exposed"))
           ret))))))

;; these are only conjunctive, so if the body is zero, then the expression will also be zero
(def-rewrite
  :match (aggregator-op-outer (:unchecked operator) (:any result) (is-empty-rexpr? _))
  :run-at [:standard :construction]
  (make-multiplicity 0))


(def-iterator
  :match (aggregator-op-inner (:any incoming-variable) (:any-list projected-vars) (:rexpr Rbody))
  (let [iters (find-iterators Rbody)
        pv (ensure-set (conj projected-vars incoming-variable))]
    (remove nil? (for [i iters
                       :let [b (iter-what-variables-bound i)]]
                   (if-not (some pv b)
                     i ;; this does not interact with the restricted variables, so this can just to through
                     (if (some #(not (pv %)) b) ;; then there is at least one variable that is not something that we are projecting out
                       (make-skip-variables-iterator i pv)))))))

(def-iterator
  :match (aggregator-op-outer (:unchecked operator) (:any result-variable) (:rexpr R))
  ;; the outer expression does not do any projection, so it should be able to just pass the finding iterators to the inner R-expr
  (find-iterators R))
