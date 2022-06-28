(ns dyna.rexpr-disjunction  ;; should change this to disjunct optimized or something, as there are now multiple kinds of disjuncts that we can have
  (:require [dyna.utils :refer :all])
  (:require [dyna.rexpr :refer :all])
  (:require [dyna.system :as system])
  (:require [dyna.context :as context])
  (:require [dyna.prefix-trie :refer :all])
  (:require [dyna.base-protocols :refer :all])
  ;(:require [dyna.iterators :refer iterators])
  (:require [clojure.set :refer [subset? union]])
  (:import [dyna.rexpr disjunct-rexpr])
  (:import [dyna.prefix_trie PrefixTrie])
  (:import [dyna UnificationFailure DIterable DIterator DIteratorInstance]))

(def ^:dynamic *disjunct-op-remove-if-single* true)

(def ^:dynamic *disjunct-constructed-add-function* nil)

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
                             (trie-get-values-collection rexprs nil)))))

(defn- remap-variables-disjunct-op [this variable-renaming-map remap-fn]
  (if (empty? variable-renaming-map)
    this
    (let [new-vars (vec (map #(get variable-renaming-map % %) (:disjunction-variables this)))
          new-vars-values (vec (map #(and (is-constant? %) (get-value %)) new-vars))]
      ;; this is going to have to remap the variables
      (if (= new-vars (:disjunction-variables this))
        this  ;; then nothing has changed so don't create a new structure
        (let [new-trie (trie-map-values (:rexprs this)
                                           new-vars-values
                                           (fn [key rr]
                                             (let [ret (remap-fn rr variable-renaming-map)]
                                               (when-not (subset?  (exposed-variables ret) (into #{} new-vars))
                                                 (debug-repl "exposed fail"))
                                               (when-not (is-empty-rexpr? ret)
                                                 ret))))]
          (make-disjunct-op new-vars new-trie))))))

;; if there already exists tries in the disjunct, then it will construct the more optimized disjunct
(def-rewrite
  :match {:rexpr (disjunct (:rexpr-list children))
          :check system/*use-optimized-rexprs*}
  :run-at :construction
  (let [dj-vars (vec (exposed-variables rexpr))
        rexpr-map (loop [n (count dj-vars)
                         s children]
                    (if (= n 0)
                      s
                      (recur (- n 1) {nil s})))
        ret (make-disjunct-op dj-vars
                              (PrefixTrie. (count dj-vars)
                                           (reduce bit-or (map #(bit-shift-left 1 %) (range (count dj-vars))))  ;; all of the disjuncts are unknown variables
                                           rexpr-map))]
    (when (some is-disjunct-op? children)
      (debug-repl "need to combine tries"))
    (when (.contains (str ret) "range")
      (debug-repl "made dd"))
    ret))


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

(def-rewrite
  :match (disjunct-op (:any-list dj-vars) (:unchecked rexprs))
  :run-at [:standard :inference]
  (let [outer-context (context/get-context)
        ret-children (volatile! (PrefixTrie. (count dj-vars) 0 nil))
        num-children (volatile! 0)
        var-map (map get-value dj-vars)
        child-var-values (transient (vec (repeat (count dj-vars) not-seen-in-trie)))]
    (doseq [[var-binding child] (trie-get-values rexprs var-map)]
      ;; this should loop through the children
      (let [child-context (context/make-nested-context-disjunct child)]
        (doseq [i (range (count dj-vars))]
          ;; this should create bindings for the variables in the context when they are already known
          (let [djv (nth var-binding i)
                dv (nth dj-vars i)]
            (when (and (not (nil? djv)) (is-variable? dv))
              (ctx-set-value! child-context dv djv))))
        (let [new-child-rexpr (context/bind-context-raw child-context
                                                        (try (simplify child)
                                                             (catch UnificationFailure e (make-multiplicity 0))))]
          ;; if this is a disjunct, then it should just take the values into this
          (assert (and (not (is-disjunct? new-child-rexpr))
                       (not (is-disjunct-op? new-child-rexpr))))
          (when-not (is-empty-rexpr? new-child-rexpr)
            (let [dj-key (map #(get-value-in-context % child-context) dj-vars)]
              ;; identify the different values seen for variables when running
              (doseq [i (range (count dj-vars))]
                (let [vv (get-value-in-context (nth dj-vars i) child-context)
                      cv (nth child-var-values i)]
                  (if (not= cv vv)
                    (assoc! child-var-values i (if (= cv not-seen-in-trie) vv nil)))))
              ;; save the resulting R-expr in the resulting trie
              (when (is-disjunct-op? new-child-rexpr)
                (debug-repl "should combine tries into the current trie"))
              (let [added-new (volatile! false)]
                (vswap! ret-children trie-update-collection dj-key
                        (fn [col]
                          (let [[made-new ret] (merge-rexpr-disjunct-list col new-child-rexpr)]
                            (vreset! added-new made-new)
                            ret)))
                ;(debug-repl "ddj")
                (if @added-new
                  (vswap! num-children inc))))))))
    ;; set the values of variables which are the same across all branches
    (doseq [i (range (count dj-vars))]
      (let [dv (nth child-var-values i)]
        (when (and (not= dv not-seen-in-trie) (not (nil? dv)) (is-variable? (nth dj-vars i)))
          (ctx-set-value! outer-context (nth dj-vars i) dv))))
    (if (= @num-children 1)
      ;; then there is only a single child, so we can return that
      (let [[[child-bindings child]] (trie-get-values @ret-children nil)]
        child)
      ;; then there are multiple children, so we have to return the entire trie
      (let [ret (make-disjunct-op dj-vars @ret-children)]
                                        ;(debug-repl "qqq")
        ret))))


#_(defn- make-disjunct-op-iterator [dj-vars idx binding-var rexprs]
  (reify DIterable
    (iter-what-variables-bound [this] #{binding-var}) ;; this can bind more than just this variable...
    (iter-variable-binding-order [this] [[binding-var]])
    (iter-create-iterator [this which-binding]
                                        ;(debug-repl)
      (when-not (or (nil? which-binding) (= which-binding [binding-var]))
        (debug-repl "g2")
        (???))
                                        ;(debug-repl "ci")
      (reify DIterator
        (iter-run-cb [this cb-fun]
          (doseq [v (iter-run-iterable this)]
            (cb-fun v)))
        #_(iter-run-cb [this cb-fun]
          (let [values-seen (transient #{})
                current-bindings (map get-value dj-vars)]
            (doseq [vals (trie-get-values-collection rexprs current-bindings)]
              (let [val (nth (first vals) idx)]
                (when-not (contains? values-seen val)
                  (conj! values-seen val)
                  (cb-fun {binding-var val}))))))
        (iter-run-iterable [this]
          ;; create a lazy sequence for this
          (let [values-seen (transient #{})
                current-bindings (map get-value dj-vars)]
            (for [vals (trie-get-values-collection rexprs current-bindings)
                  :let [val (nth (first vals) idx)]
                  :when (not (contains? values-seen val))]
              (do (conj! values-seen val)
                  (reify DIteratorInstance
                    (iter-variable-value [this] val)
                    (iter-continuation [this] nil) ;; this is not a multi iterator yet, but this should support
                    )))
              )
          )
        ))))

#_(defn- make-disjunct-op-iterator2 [dj-vars idxs binding-vars rexprs]
    (reify DIterable
      (iter-what-variables-bound [this] (into #{} binding-vars))
      (iter-variable-binding-order [this] (let [bound (iter-what-variables-bound this)]
                                            [(vec (filter #(contains? bound %) dj-vars))]))
      (iter-create-iterator [this which-binding]
        (when-not (or (nil? which-binding) (= (first (iter-variable-binding-order this)) which-binding))
          (debug-repl "g3")
          (???))
        (reify DIterator
          (iter-run-cb [this cb-fun]
            ;; this is going to have to go through the trie, and then will perform the

            ))
        )
      )
    )


#_(comment
  (def-iterator
    :match (disjunct-op (:any-list dj-vars) (:unchecked rexprs))
    ;; if any of the variables are fully ground, then it
    (let [contains-wildcard (.contains-wildcard ^PrefixTrie rexprs)
          ret (reduce union (for [idx (range (count dj-vars))]
                              (when (and (not (is-bound? (nth dj-vars idx)))
                                         (= 0 (bit-and contains-wildcard (bit-shift-left 1 idx))))
                                (let [binding-var (nth dj-vars idx)]
                                  #{(make-disjunct-op-iterator dj-vars idx binding-var rexprs)}))))]
                                        ;(when-not (empty? ret)
                                        ;  (debug-repl "diter"))
      ret)))

(declare run-trie-iterator-from-node
         run-trie-iterator-from-node-unconsolidated)

(defn- trie-diterator-instance [remains node]
  (reify DIterator
    (iter-run-cb [this cb-fn]
      (doseq [v (iter-run-iterable this)]
        (cb-fn v)))
    (iter-run-iterable [this]
      (run-trie-iterator-from-node remains node))
    (iter-run-iterable-unconsolidated [this]
      (run-trie-iterator-from-node-unconsolidated remains node))
    (iter-bind-value [this value]
      (let [v (get node value)]
        (when-not (nil? v)
          (trie-diterator-instance (- remains 1) v))))
    (iter-debug-which-variable-bound [this] (???))
    (iter-estimate-cardinality [this]
      (count node))))

;; return a lazy sequence over bindings
(defn- run-trie-iterator-from-node [remains trie-node]
  (assert (not (contains? trie-node nil))) ;; if this happens, this means that it is trying to iterate over something which would
  (for [[key next-node] trie-node]
    (reify DIteratorInstance
      (iter-variable-value [this] key)
      (iter-continuation [this]
        (if (= 0 remains)
          nil  ;; there are going to be more disjuncts here
          (trie-diterator-instance (- remains 1) next-node))
        ))
    ))

(defn- run-trie-iterator-from-node-unconsolidated [remains trie-node]
  (for [[key next-node] trie-node]
    (reify DIteratorInstance
      (iter-variable-value [this] (???)) ;; the value should not be used in this case, as it could be replicated etc
      (iter-continuation [this]
        (if (= 0 remains)
          nil
          (trie-diterator-instance (- remains 1) next-node))))))

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
            (let [ret (trie-diterator-instance (count dj-vars) trie-root)
                                        ;(run-trie-iterator-from-node (count dj-vars) trie-root)
                  ]
              ;(debug-repl "creating iterator from trie")
              ret)))})))


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
