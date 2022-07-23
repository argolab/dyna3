(ns dyna.rexpr-disjunction  ;; should change this to disjunct optimized or something, as there are now multiple kinds of disjuncts that we can have
  (:require [dyna.utils :refer :all])
  (:require [dyna.rexpr :refer :all])
  (:require [dyna.system :as system])
  (:require [dyna.context :as context])
  (:require [dyna.prefix-trie :refer :all])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.iterators :refer [run-iterator]])
  (:require [clojure.set :refer [subset? union]])
  (:import [dyna.rexpr disjunct-rexpr])
  (:import [dyna.prefix_trie PrefixTrie])
  (:import [dyna UnificationFailure DIterable DIterator DIteratorInstance]))

(def ^:dynamic *disjunct-op-remove-if-single* true)

;(def ^:dynamic *disjunct-constructed-add-function* nil)

(def ^:dynamic *disjunct-run-inner-iterators* true)

(declare ^:private remap-variables-disjunct-op)

;(def ^{:dynamic true :private true} *make-optimized-disjuncts* true)


(def-base-rexpr disjunct-op [:var-list disjunction-variables
                             :prefix-trie rexprs]
  (get-children [this] (map second (trie-get-values rexprs nil)))

  (remap-variables [this variable-renaming-map]
                   (remap-variables-disjunct-op this variable-renaming-map remap-variables))
  (remap-variables-handle-hidden [this variable-renaming-map]
                                 (remap-variables-disjunct-op this variable-renaming-map remap-variables-handle-hidden))
  ;; the exposed variables will just be the disjunction-variables.  The
  ;; prefix-trie will be a subset of those variables, so it does not need to get scanned

  ;; if we can determine that the disjunct does not overlap from the trie, and
  ;; that all of the branches are also only containing constraints
  (is-constraint? [this]
                (and (= 0 (.contains-wildcard ^PrefixTrie rexprs))
                     (every? #(and (= (count (second %)) 1)
                                   (is-constraint? (cdar %)))
                             (trie-get-values-collection rexprs nil))))
  (is-non-empty-rexpr? [this]
                       (let [vmap (if (context/has-context)
                                    (vec (map get-value disjunction-variables))
                                    (repeat (count disjunction-variables) nil))
                             ;iter (trie-get-values-collection rexprs vmap)
                             ]
                         (first (remove nil? (for [[key r] (trie-get-values-collection-no-wildcard rexprs vmap)]
                                               (when (some is-non-empty-rexpr? r) true))))))
  (rewrite-rexpr-children [this remap-function]
                          (make-disjunct-op disjunction-variables
                                            (trie-map-values rexprs nil (fn [trie-path r]
                                                                          (remap-function r)))))
  )

(defn- remap-variables-disjunct-op [this variable-renaming-map remap-fn]
  (if (empty? variable-renaming-map)
    this
    (let [new-vars (vec (map #(get variable-renaming-map % %) (:disjunction-variables this)))]
      (if (= new-vars (:disjunction-variables this))
        this ;; return this unchanged, as the variable names are the same
        (let [new-vars-values (vec (map #(when (is-constant? %) (get-value %)) new-vars))]
          ;; this is going to have to remap the variables
          (if (= new-vars (:disjunction-variables this))
            this  ;; then nothing has changed so don't create a new structure
            (let [new-trie (trie-map-values-subset (:rexprs this)
                                                   new-vars-values
                                                   (fn [key rr]
                                                     (let [ret (remap-fn rr variable-renaming-map)]
                                                       (dyna-debug (when-not (subset?  (exposed-variables ret) (into #{} new-vars))
                                                                     (debug-repl "exposed fail")))
                                                       (when-not (is-empty-rexpr? ret)
                                                         ret))))]
                                        ;(debug-repl "trie remap")
              (make-disjunct-op new-vars new-trie))))))))


(def ^:private not-seen-in-trie (Object.))

(defn- merge-rexpr-disjunct-list [lst radd]
  (if (is-empty-rexpr? radd)
    [false lst] ;; [(if it added something to the list) (the list)]
    (if (is-multiplicity? radd)
      (let [cnt (volatile! 0)
            others (doall (filter (fn [x] (if (is-multiplicity? x)
                                            (do (vswap! cnt + (:mult x))
                                                nil)
                                            x))
                                  lst))]
        [(= @cnt 0) (conj others (make-multiplicity (+ @cnt (:mult radd))))])
      [true (conj lst radd)])))

;; want to go through the conjuncts, and find any unify with a constant
;; expressions, so that we can efficiently store results into the trie when it is constructed
(defn- conjunct-iterator [x]
  (if (is-conjunct? x)
    (sequence cat (map conjunct-iterator (:args x)))
    [x]))


;; if there already exists tries in the disjunct, then it will construct the more optimized disjunct
(def-rewrite
  :match {:rexpr (disjunct (:rexpr-list children))
          :check system/*use-optimized-rexprs*}
  :run-at :construction
  (let [dj-vars (vec (exposed-variables rexpr))
        existing-tries (filter is-disjunct-op? children)
        non-tries (vec (filter #(not (is-disjunct-op? %)) children))
        non-tries-map (loop [n (count dj-vars)
                             s non-tries]
                    (if (= n 0)
                      s
                      (recur (- n 1) {nil s})))
        base-trie (PrefixTrie. (count dj-vars)
                               (if-not (empty? non-tries)
                                 (- (bit-shift-left 1 (count dj-vars)) 1)
                                 0)
                               non-tries-map)
        combined-trie (loop [trie base-trie
                             nt (first existing-tries)
                             rt (next existing-tries)]
                        (if (nil? nt) trie
                            (let [vorder (:disjunction-variables nt)
                                  t (:rexprs nt)
                                  vorder-idx (zipmap vorder (range))
                                  new-order (vec (map vorder-idx dj-vars))  ;; if the var is not present, it will be nil
                                  t-reordered (trie-reorder-keys t new-order)]
                              (recur (trie-merge trie t-reordered)
                                     (first rt)
                                     (next rt)))))
        ret (make-disjunct-op dj-vars
                              combined-trie)
        ]
    ret))


(def-rewrite
  :match (disjunct-op (:any-list dj-vars) (:unchecked rexprs))
  :run-at [:standard :inference]
  (let [outer-context (context/get-context)
        ret-children (volatile! (PrefixTrie. (count dj-vars) 0 nil))
        num-children (volatile! 0)
        var-map (map get-value dj-vars)
        child-var-values (transient (vec (repeat (count dj-vars) not-seen-in-trie)))
        save-result-in-trie (fn save-result-in-trie [new-child-rexpr child-context]
                              (when-not (is-empty-rexpr? new-child-rexpr)
                                (let [dj-key (map #(get-value-in-context % child-context) dj-vars)]
                                  ;; identify the different values seen for variables when running
                                  (doseq [i (range (count dj-vars))]
                                    (let [vv (get-value-in-context (nth dj-vars i) child-context)
                                          cv (nth child-var-values i)]
                                      (if (not= cv vv)
                                        (assoc! child-var-values i (if (= cv not-seen-in-trie) vv nil)))))
                                  ;; save the resulting R-expr in the resulting trie
                                  (if (is-disjunct-op? new-child-rexpr)
                                    (let []
                                      ;; this might never happen if it has disjunct-run-inner-iterator set to true, it would have already expanded
                                      ;; the trie using that
                                      (debug-repl "should combine tries into the current trie")
                                      (???))
                                    (let [added-new (volatile! false)]
                                      #_(when-not (empty? (filter is-unify? (conjunct-iterator new-child-rexpr)))
                                        (debug-repl "contains unify2"))
                                      (vswap! ret-children trie-update-collection dj-key
                                              (fn [col]
                                                (let [[made-new ret] (merge-rexpr-disjunct-list col new-child-rexpr)]
                                                  (vreset! added-new made-new)
                                                  ret)))
                                        ;(debug-repl "ddj")
                                      (if @added-new
                                        (vswap! num-children inc)))))))
        ]
    (doseq [[var-binding child] (trie-get-values rexprs var-map)]
      ;; this should loop through the children
      (let [child-context (context/make-nested-context-disjunct child)]
        (doseq [i (range (count dj-vars))]
          ;; this should create bindings for the variables in the context when they are already known
          (let [djv (nth var-binding i)
                dv (nth dj-vars i)]
            (when (and (not (nil? djv)) (is-variable? dv))
              (ctx-set-value! child-context dv djv))))
        (context/bind-context-raw child-context
                                  (let [new-child-rexpr (try (simplify child)
                                                             (catch UnificationFailure e (make-multiplicity 0)))]
                                    ;; if this is a disjunct, then it should just take the values into this
                                    (assert (and (not (is-disjunct? new-child-rexpr))
                                                 (not (is-disjunct-op? new-child-rexpr))))
                                        ;(when-not (is-empty-rexpr? new-child-rexpr))
                                    (if (and *disjunct-run-inner-iterators* (not (is-multiplicity? new-child-rexpr)))
                                      (let [iters (find-iterators new-child-rexpr)]
                                        (run-iterator
                                         :iterators iters
                                         :bind-all true
                                         :rexpr-in new-child-rexpr
                                         :rexpr-result child-rexpr-itered
                                         :simplify simplify
                                         (save-result-in-trie (try (simplify child-rexpr-itered)
                                                                   (catch UnificationFailure e (make-multiplicity 0)))
                                                              (context/get-context) ;; we have to use get-context here as the iterator might have rebound the context
                                                              )))
                                      (save-result-in-trie new-child-rexpr child-context))))))
    ;; set the values of variables which are the same across all branches
    (doseq [i (range (count dj-vars))]
      (let [dv (nth child-var-values i)]
        (when (and (not= dv not-seen-in-trie) (not (nil? dv)) (is-variable? (nth dj-vars i)))
          (ctx-set-value! outer-context (nth dj-vars i) dv))))
    (if (= @num-children 0)
      (make-multiplicity 0) ;; there is nothing in the disjunct
      (if (= @num-children 1)
        ;; then there is only a single child, so we can return that
        (let [[[child-bindings child]] (trie-get-values @ret-children nil)]
          child)
        ;; then there are multiple children, so we have to return the entire trie
        (let [ret (make-disjunct-op dj-vars @ret-children)]
                                        ;(debug-repl "qqq")
          ret)))))



(declare run-trie-iterator-from-node
         run-trie-iterator-from-node-unconsolidated)

(defn- trie-diterator-instance [remains node variable-order]
  (reify DIterator
    (iter-run-cb [this cb-fn]
      (doseq [v (iter-run-iterable this)]
        (cb-fn v)))
    (iter-run-iterable [this]
      (run-trie-iterator-from-node remains node variable-order))
    (iter-run-iterable-unconsolidated [this]
      (run-trie-iterator-from-node-unconsolidated remains node variable-order))
    (iter-bind-value [this value]
      (let [v (get node value)]
        (when-not (nil? v)
          (trie-diterator-instance (- remains 1) v (next variable-order)))))
    (iter-debug-which-variable-bound [this] (first variable-order))
    (iter-estimate-cardinality [this]
      (count node))))

;; return a lazy sequence over bindings
(defn- run-trie-iterator-from-node [remains trie-node variable-order]
  (dyna-assert (not (contains? trie-node nil))) ;; if this happens, this means that it is trying to iterate over something which would
  (for [[key next-node] trie-node]
    (reify DIteratorInstance
      (iter-variable-value [this] key)
      (iter-continuation [this]
        (if (= 0 remains)
          nil  ;; there are going to be more disjuncts here
          (trie-diterator-instance (- remains 1) next-node (next variable-order)))
        ))))

(defn- run-trie-iterator-from-node-unconsolidated [remains trie-node variable-order]
  (for [[key next-node] trie-node]
    (reify DIteratorInstance
      (iter-variable-value [this] key)
      (iter-continuation [this]
        (if (= 0 remains)
          nil
          (trie-diterator-instance (- remains 1) next-node (next variable-order)))))))

(def-iterator
  :match (disjunct-op (:any-list dj-vars) (:unchecked rexprs))
  (let [contains-wildcard (.contains-wildcard ^PrefixTrie rexprs)
        trie-root (.root ^PrefixTrie rexprs)]
    ;(debug-repl "dit")
    (when (not= contains-wildcard (- (bit-shift-left 1 (count dj-vars)) 1))
      ;; then there exists at least one variable which does not contain a whild card, so it could be iterated
      #{(reify DIterable
          (iter-what-variables-bound [this]
            (into #{} (for [idx (range (count dj-vars))
                            :when (and (= 0 (bit-and contains-wildcard (bit-shift-left 1 idx)))
                                       (is-variable? (nth dj-vars idx)))]
                        (nth dj-vars idx))))
          (iter-variable-binding-order [this] [dj-vars])
          (iter-create-iterator [this which-binding]
            (assert (.contains (iter-variable-binding-order this) which-binding))
            (let [ret (trie-diterator-instance (count dj-vars) trie-root dj-vars)
                                        ;(run-trie-iterator-from-node (count dj-vars) trie-root)
                  ]
              ;(debug-repl "creating iterator from trie")
              ret)))})))





(def-deep-equals disjunct-op [a b]
  (when (instance? disjunct-rexpr b)
    ;; in the case of the origional disjunct, this is going to have that
    ;; unification between variables is represented as unify expressions instead
    ;; of as a trie.  I suppose that we could attempt to construct a representation and then compare between them

    ;; if there is a single value in the expression, I suppose that this could also result in creating which of the values would get represented
    ;; though that would potentially result in a lot of expensive compare options, in the case that it would be constantly looking through the trie
    (debug-repl "disjunct and disjunct-op deep equals")
    (???)
    ))

(def-deep-equals disjunct-op [a b]
  (when (instance? disjunct-op-rexpr b)
    ;; the tries could be in different orderes, in which case, we are going to have to reorder one of the tries
    ;; from there we are going to have to zip the tries, and compare if there is some kind of representation which is the same between them
    (let [va (:disjunction-variables a)
          vb (:disjunction-variables b)]
      (if (or (not= (count va) (count vb))
              (not= (into #{} va) (into #{} vb)))
        false ;; the variables exposed are different, so this is going to
        (let [^PrefixTrie ta (:rexprs a)
              ^PrefixTrie tb (:rexprs b)
              ai (zipmap va (range)) ;; what if a variable appears more than once, then this is not going to work correctly?
              ^PrefixTrie tbr (trie-reorder-keys tb (map ai vb))]
          ;; this needs to compare the triesss, need to implement this
          ;(debug-repl "disjunct op deep equals")
          ((fn rec [d x y]
             (if (= d 0)
               ;; we are at the leaf, so we have check that the elements contained are the same
               (deep-equals-list-compare x y)
               ;; this is somewhere in the middle of the trie, so we should just check that the
               (if (or (not= (count x) (count y))
                       (not= (into #{} (keys x)) (into #{} (keys y))))
                 false
                 (every? true? (for [[k xv] x
                                     :let [yv (get y k)]]
                                 (rec (- d 1) xv yv))))))
           (count va) (.root ta) (.root tbr)))
        ))))


(def-rewrite
  :match (disjunct-op (:any-list var-list) rexprs)
  :run-at :construction
  :is-check-rewrite true
  (let [var-set (into #{} var-list)]
    (when-not (every? (fn [[var-bindings x]] (if (and (rexpr? x)
                                                      ;; the variables which are exposed should be a subset of what is not ground
                                                      ;; or are we going to have to represent which of the values are represented with
                                                      (subset? (exposed-variables x) var-set))
                                               true
                                               (do
                                                 (debug-repl "gg1")
                                                 false)))
                      (trie-get-values rexprs nil))
      (let [rx (into [] (map second (trie-get-values rexprs nil)))]
        (debug-repl "R-expr in trie has extra exposed variables"))
      (???))))

#_(def-rewrite
  :match (disjunct-op (:any-list var-list) ^PrefixTrie rexprs)
  :run-at :construction
  :is-check-rewrite true
  (let [var-set (ensure-set var-list)
        res (for [[bindings rexpr] (trie-get-values rexprs nil)
                  r (conjunct-iterator rexpr)
                  :when (is-unify? r)]
              [bindings r])]
    (when-not (empty? res)
      (let [sw (java.io.StringWriter.)]
        (.printStackTrace (Throwable.) (java.io.PrintWriter. sw))
        (when-not (or (.contains (.toString sw) "rexpr_disjunction.clj:132")  ;; this is the place where it is first constructed
                      (.contains (.toString sw) "rexpr_disjunction.clj:57") ;; the remap disjunction variables op
                      (.contains (.toString sw) "user_defined_terms.clj:227") ;; rewrite user defined terms when they are introduced
                      (.contains (.toString sw) "memoization.clj:171")  ;; when the rexpr is getting returned by a memoized expression
                      )
          (debug-repl "contains unify"))))))
