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
  (:require [clojure.set :refer [difference]])
  (:import [dyna.rexpr proj-rexpr disjunct-rexpr aggregator-rexpr])
  (:import [dyna.rexpr_disjunction disjunct-op-rexpr])
  (:import [dyna.prefix_trie PrefixTrie]))


(def-base-rexpr aggregator-op-outer [:unchecked operator
                                     :var result
                                     :rexpr bodies])

(def-base-rexpr aggregator-op-inner [:hidden-var incoming
                                     :var-list projected ;; all of these variables are hidden
                                     :rexpr body]
  (exposed-variables [this]
                     (cache-field cached-exposed-variables
                                  (difference (exposed-variables body)
                                              (into #{incoming} projected))))
  (remap-variables [this variable-map]
                   ;; this is going to have to perform remapping of the body
                   (dyna-assert (not (some (into #{incoming} projected) (keys variable-map))))
                   (if (empty? variable-map)
                     this
                     (make-aggregator-op-inner incoming projected
                                               (remap-variables body
                                                                (apply dissoc variable-map incoming projected)))))

  (remap-variables-handle-hidden [this variable-map]
                                 (let [new-hidden-names (into {} (for [v (cons incoming projected)]
                                                                   [v (make-variable (gensym 'agg-op-hidden))]))
                                       new-map (merge variable-map new-hidden-names)]
                                   (make-aggregator-op-inner (get new-map incoming incoming)
                                                             (vec (map new-map projected))
                                                             (remap-variables-handle-hidden body new-map)))))

(def ^{:private true :dynamic true} *aggregator-op-contribute-value*
  (fn r
    ([value mult]
     ;; return a dummy expression in the case that there is nothing that is able
     ;; to take the value, this can hold the value until there is something else
     (make-aggregator-op-inner (make-constant value) [] (make-multiplicity mult)))
    ;([value] (r value 1))
    ))


(def-rewrite
  :match {:rexpr (aggregator (:unchecked operator) (:any result-variable) (:any incoming-variable)
                             (#(= % true) body-is-conjunctive) (:rexpr R))
          :check system/*use-optimized-rexprs*}
  :run-at :construction
  (make-aggregator-op-outer (get @aggregators operator) result-variable
                            (make-aggregator-op-inner incoming-variable
                                                      []
                                                      R)))

;; if there is a project nested inside of the aggregator inner expression, then we are going pull the projection out and add it to the aggregator
(def-rewrite
  :match {:rexpr (aggregator-op-inner (:any incoming) (:variable-list projected-vars) (proj (:variable hid-var) (:rexpr R)))
          :check (and system/*use-optimized-rexprs*
                      (not (some #{hid-var} projected-vars)))}
  :run-at :construction
  (make-aggregator-op-inner incoming (conj projected-vars hid-var) R))

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
        other-vars (drop-nth disjunction-variables incoming-idx)
        resulting-trie (volatile! (PrefixTrie. (- (count disjunction-variables) 1) 0 nil))]
    (doseq [[var-binding children] (trie/trie-get-values-collection trie-Rs nil)]
      (let [income-val (nth var-binding incoming-idx)
            income-var (if (nil? income-val) incoming (make-constant income-val))
            other-binding (vec (drop-nth var-binding incoming-idx))
            new-children (vec (for [c children]
                                (make-aggregator-op-inner income-var projected-vars c)))]
        (vswap! resulting-trie trie/trie-update-collection other-binding
                (fn [col]
                  (concat col new-children)))))
    (let [ret (make-disjunct-op other-vars @resulting-trie)]
      ;(debug-repl "optimized aggregator disjunction trie")
      ret)))

(def-rewrite
  :match (aggregator-op-inner (:any incoming) (:any-list projected-vars) (is-empty-rexpr? _))
  :run-at :construction
  (make-multiplicity 0))

(def-rewrite
  :match (aggregator-op-outer (:unchecked operator) (:any result-variable) (:rexpr Rbody))
  :run-at [:standard :inference]
  (let [exp-vars (exposed-variables Rbody)
        accumulator (volatile! nil)
        ctx (context/make-nested-context-aggregator-op-outer Rbody)]
    (context/bind-context ctx
     (binding [*aggregator-op-contribute-value* (fn [value mult]
                                                  (assert (= mult 1))
                                                  (if (nil? @accumulator)
                                                    (vreset! accumulator value) ;; we should be able to just store this value, though we are going to need to check what the binding are to the variables in this case... if there is some result, then it should have that
                                                    (vswap! accumulator (:combine operator) value))
                                                  (make-multiplicity 0))]
       (let [ret (simplify Rbody)]
         (if (is-empty-rexpr? ret)
           (if (nil? @accumulator)
             (make-multiplicity 0) ;; did not find any contributions
             (make-unify result-variable (make-constant ((:lower-value operator identity) @accumulator))))
           (if (nil? @accumulator)
             (make-aggregator-op-outer operator result-variable ret)
             (make-aggregator-op-outer operator result-variable (make-disjunct [(make-aggregator-op-inner (make-constant @accumulator) [] (make-multiplicity 1)) ;; store the value so far
                                                                                ret])))))))))

;; in the case that the disjunct is lifted out, it would be possible that
;; something which does not contain the proejcted vars and does not contain the
;; incoming-variables is also going to be lifted out.  Which means that this is
;; not able to just perform "sideways" passing of the information
(def-rewrite
  :match (aggregator-op-inner (:any incoming-variable) (:any-list projected-vars) (:rexpr Rbody))
  :run-at [:standard :inference]
  (let [exposed (exposed-variables rexpr) ;; if all of the exposed are ground, then we should just go ahead and compute the value
        ctx (context/make-nested-context-aggregator-op-inner Rbody projected-vars incoming-variable)
        nR (context/bind-context ctx (simplify Rbody))]

    ;(debug-repl "oo")

    (cond
      (is-empty-rexpr? nR) (make-multiplicity 0)
      (and (is-multiplicity? nR) (is-bound-in-context? incoming-variable ctx)) (let [ret (*aggregator-op-contribute-value* (get-value-in-context incoming-variable ctx) (:mult nR))]
                                                                                 ;; this needs to just return the value from the expression
                                                                                 (debug-repl "result is found")
                                                                                 ret)
      (every? is-ground? exposed)
      (context/bind-context-raw
       ctx
       (let [iterators (find-iterators nR)
             result-rexprs (volatile! nil)]
         ;; will loop over assignments to all of the variables
         (run-iterator
          :iterators iterators
          :bind-all true
          :rexpr-in nR
          :rexpr-result inner-r
          :simplify simplify
                                        ;:required [incoming-variable] ;; we still want to loop even if we can't directly assign this value
          (do
            ;; if this is not a multiplicity, then this expression has something that can not be handled
            ;; in which case this will need to report an error, or return the R-expr while having that it can not be solved...
            (if (is-multiplicity? inner-r)
              (let [val (get-value incoming-variable)
                    mult (:mult inner-r)]
                (when-not (= mult 0)
                  (let [rc (*aggregator-op-contribute-value* val mult)]
                    (when-not (is-empty-rexpr? rc)
                      ;; then we have to save the result of this R-expr, as it could not get processed for some reason
                      (vswap! result-rexprs conj rc)))))
              (let [new-incoming (if (is-bound? incoming-variable)
                                   (make-constant (get-value incoming-variable))
                                   incoming-variable)
                    remapping-map (into {} (for [v (cons incoming-variable projected-vars)
                                                 :when (is-bound? v)]
                                             [v (make-constant (get-value v))]))
                    new-projected (vec (filter #(not (is-bound? %)) projected-vars))
                    new-body (remap-variables inner-r remapping-map)
                    rc (make-aggregator-op-inner new-incoming new-projected new-body)]
                ;(debug-repl "pp") ;; this needs to save the result, and remove any projections that are now fully resolved
                (vswap! result-rexprs conj rc)
               ))))

         (if (empty? @result-rexprs)
           ;; then everything has been processed, so there is no need for this to remain
           (make-multiplicity 0)
           ;; there exists some branches which could not be fully resolved, so this is going to remain
           (make-disjunct (vec @result-rexprs)))))

      :else (let [new-incoming (if (is-bound-in-context? incoming-variable ctx)
                                 (make-constant (get-value-in-context incoming-variable ctx))
                                 incoming-variable)
                  remapping-map (into {} (for [v (cons incoming-variable projected-vars)
                                               :when (is-bound-in-context? v ctx)]
                                           [v (make-constant (get-value-in-context v ctx))]))
                  new-projected (vec (filter #(not (is-bound-in-context? % ctx)) projected-vars))
                  new-body (remap-variables nR remapping-map)
                  ret (make-aggregator-op-inner new-incoming new-projected new-body)]
              ;(debug-repl "aoi ret3")
              ret))))

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
