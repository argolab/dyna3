(ns dyna.rexpr-disjunction  ;; should change this to disjunct optimized or something, as there are now multiple kinds of disjuncts that we can have
  (:require [dyna.utils :refer :all])
  (:require [dyna.rexpr :refer :all])
  (:require [dyna.system :as system])
  (:require [dyna.context :as context])
  (:require [dyna.prefix-trie :refer :all])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.iterators :refer [run-iterator iterator-disjunct-diterator]])
  (:require [clojure.set :refer [subset? union]])
  (:import [dyna.rexpr disjunct-rexpr])
  (:import [dyna.prefix_trie PrefixTrie])
  (:import [dyna UnificationFailure DIterable DIterator DIteratorInstance ClojureUnorderedVector IteratorBadBindingOrder]))

(def ^:dynamic *disjunct-op-remove-if-single* true)

(def ^:dynamic *disjunct-run-inner-iterators* true)

(declare ^:private remap-variables-disjunct-op)

;; TODO: wonder if there should be some kind index which is cached, it could
;; allow for more efficient queries in some cases, but the cached index would
;; have to be keep up to date.  I suppose that a cached index could go in the
;; memo table instead where it would just keep the values in a different order.
;;
;; The different orders would have to be keep up to date as it updates with
;; different values.  Though I suppose that it could keep the different orders
;; as some kind of an upper bound instead of a tight bound for the value?  In
;; which case it could allow for iterators to run faster in some cases

;; the metadata should track useful information for the disjunct
;; I suppose that this could be things like the types of R-exprs contained in the trie
;; as well as which variables still have constraints on them

(def-base-rexpr disjunct-op [:var-list disjunction-variables
                             :prefix-trie rexprs
                             :unchecked metadata]
  (primitive-rexpr [this]
                   ;; this might want to remap back into a disjunct which is
                   ;; simple, in which case it would want to find all of the
                   ;; different branches with the unify expressions?

                   ;; I suppose that would mean that the expression would ned to get some mapping
                   (debug-repl "make primitive rexpr out of trie")
                   (???))
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
                                                                          (remap-function r)))
                                            metadata))
  (remap-variables-func [this remap-function]
                        (???) ;; TODO
                        )

  (rexpr-jit-info [this] {:jittable false} ;; this will get converted into a primitive disjunct which we can compile
                  )
  (rexpr-jittype-hash [this] 0))

(defn- remap-variables-disjunct-op [this variable-renaming-map remap-fn]
  (if (empty? variable-renaming-map)
    this
    (debug-tbinding
     [current-simplify-stack (conj (tlocal *current-simplify-stack*) this)]
     (let [this-dv (:disjunction-variables this)
           new-vars (vec (map #(get variable-renaming-map % %) this-dv))]
       (if (= new-vars this-dv)
         this ;; return this unchanged, as the variable names are the same
         (let [new-vars-values (vec (map #(when (is-constant? %) (get-value %)) new-vars))]
           ;; this is going to have to remap the variables
           (if (= new-vars this-dv)
             this  ;; then nothing has changed so don't create a new structure
             (context/bind-no-context
              (let [new-trie (trie-map-values-subset (:rexprs this)
                                                     new-vars-values
                                                     (fn [key rr]
                                                       (let [ret (remap-fn rr variable-renaming-map)]
                                                         (dyna-debug (subset?  (exposed-variables ret) (into #{} new-vars)))
                                                         (when-not (is-empty-rexpr? ret)
                                                           ret))))
                    metadata (:metadata this)
                    new-metadata (when-not (nil? metadata)
                                   (assoc metadata :rexprs-exposed-vars (set (map #(get variable-renaming-map % %) (:rexprs-exposed-vars metadata)))))]
                (make-disjunct-op new-vars new-trie new-metadata))))))))))


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
          :check (and system/use-optimized-rexprs (tlocal use-optimized-disjunct))}
  :run-at :construction
  :run-in-jit false
  (let [dj-vars (vec (exposed-variables rexpr))]
    (when-not (empty? dj-vars)
      (let [existing-tries (filter is-disjunct-op? children)
            non-tries (ClojureUnorderedVector/create (filter #(not (is-disjunct-op? %)) children))
            base-trie (if (empty? non-tries)
                        (make-PrefixTrie (count dj-vars) 0 nil)
                        (make-PrefixTrie (count dj-vars)
                                         (- (bit-shift-left 1 (count dj-vars)) 1)
                                         (loop [n (count dj-vars)
                                                s non-tries]
                                           (if (= n 0)
                                             s
                                             (recur (- n 1) (trie-hash-map nil s))))))
            combined-trie (loop [trie base-trie
                                 nt (first existing-tries)
                                 rt (next existing-tries)]
                            (if (nil? nt) trie
                                (let [vorder (:disjunction-variables nt)
                                      t (:rexprs nt)
                                      vorder-idx (zipmap vorder (range))
                                      new-order (vec (map vorder-idx dj-vars)) ;; if the var is not present, it will be nil
                                      ;; t2 (if (not= (count new-order) (count vorder))
                                      ;;      (do
                                      ;;        (debug-repl "subselect trie")
                                      ;;        (???))
                                      ;;      t)
                                      existing-values (vec (map (fn [v]
                                                                  (if (some #{v} dj-vars)
                                                                    nil
                                                                    (get-value v)))
                                                                vorder))
                                      ;; zzzz (when (not= (count vorder) (count new-order))
                                      ;;        (debug-repl "trie d" false))
                                      t-reordered (trie-reorder-keys-subselect t new-order existing-values)]
                                  (recur (trie-merge trie t-reordered)
                                         (first rt)
                                         (next rt)))))
            ret (make-disjunct-op dj-vars
                                  combined-trie
                                  nil)]
        ret))))


(defn- disjunct-op-rewrite-internals [dj-vars ^PrefixTrie rexprs simplify]
  (let [outer-context (context/get-context)
        ret-children (volatile! (make-PrefixTrie (count dj-vars) 0 nil))
        num-children (volatile! 0)
        new-metadata (volatile! {:contained-rexprs #{}
                                 :rexprs-exposed-vars #{}
                                        ;:all-constraints  if everything contained in the trie is a constraint, then we could remove the aggregator, even in the case that we still have a disjunct.  Though not 100% sure if that would be all that helpful, it would essentially just be rewriting the R-expr such that the result passes through the aggregator and then we can remove the outer and inner aggregators in that case
                                 ;; all-constraints would also require that there are no wildcards and the max number of branches are 1.
                                 ;; this might be redudant, as if it has rexprs-exposed-vars is an empty set, then it should be able to run the aggregators on all branches as long as there are no wildcards.  It would just have to combine all of the values that it sees along a given branch

                                 :current-var-vals (vec (map get-value dj-vars))
                                 })
        dj-var-values (map get-value dj-vars)
        ;; track the different values which have been seen when added to the trie to identify things which are constant
        child-var-values (transient (vec (repeat (count dj-vars) not-seen-in-trie)))
        save-result-in-trie (fn save-result-in-trie [new-child-rexpr child-context]
                              (when-not (is-empty-rexpr? new-child-rexpr)
                                (vswap! new-metadata (fn [m]
                                                       ;; track information about the R-exprs which are contained in the trie.  This information should
                                                       ;; be useful to figure out which operations we need to perform
                                                       (assoc m
                                                              :contained-rexprs (conj (:contained-rexprs m) (rexpr-name new-child-rexpr))
                                                              :rexprs-exposed-vars (union (:rexprs-exposed-vars m) (exposed-variables new-child-rexpr)))))
                                (let [dj-key (map #(get-value-in-context % child-context) dj-vars)]
                                  ;; track what values we have seen
                                  (doseq [[i v] (zipseq (range) dj-key)
                                          :let [x (nth child-var-values i)]
                                          :when (and (not= x nil) (not= x v))]
                                    (assoc! child-var-values i (if (= not-seen-in-trie x)
                                                                 v
                                                                 nil)))
                                  (if (is-disjunct-op? new-child-rexpr)
                                    (let [child-trie ^PrefixTrie (:rexprs new-child-rexpr)
                                          child-vars (:disjunction-variables new-child-rexpr)
                                          known-values (vec (map #(get-value-in-context % child-context) child-vars))
                                          new-order (vec (map (zipmap child-vars (range)) dj-vars))
                                          t-reordered (trie-reorder-keys-subselect child-trie new-order known-values)]
                                      (vswap! ret-children trie-merge t-reordered)
                                      (vswap! num-children #(+ 2 %)) ;; there should be at least 2 children getting added, so we will still return a trie in the end
                                      )
                                    (let [added-new (volatile! false)]
                                      (vswap! ret-children trie-update-collection dj-key
                                              (fn [col]
                                                (let [[made-new ret] (merge-rexpr-disjunct-list col new-child-rexpr)]
                                                  (vreset! added-new made-new)
                                                  ret)))
                                      (if @added-new
                                        (vswap! num-children inc)))))))]
    (doseq [[var-binding child] (trie-get-values rexprs dj-var-values)]
      ;; loop through all of the children which at least match on the values
      (try
        (let [child-context (context/make-nested-context-disjunct child)]
          (doseq [[dv djv] (zipseq dj-vars var-binding)
                  :when (not (nil? djv))]
            (if (is-constant? dv)
              (when (not= (get-value dv) djv)
                (throw (UnificationFailure. "not equal to const")))
              (ctx-set-value! child-context dv djv)))
          (context/bind-context-raw
           child-context
           (let [new-child-rexpr (simplify child)]
             ;; deal with the resulting child expression and save it into the trie
             (save-result-in-trie new-child-rexpr child-context)
             #_(when-not (is-empty-rexpr? new-child-rexpr)
               (debug-repl "todo")
               (???)))))
        (catch UnificationFailure err nil)))
    ;; set the value of variables which are the same along all branches
    (doseq [[v x] (zipseq dj-vars (persistent! child-var-values))
            :when (not (contains? #{not-seen-in-trie nil} x))]
      (set-value! v x))
    (case (long @num-children)
      0 (make-multiplicity 0)
      1 (let [[[child-bindings child]] (trie-get-values @ret-children nil)]
          (doseq [[dv djv] (zipseq dj-vars child-bindings)
                  :when (not (nil? djv))]
            (set-value! dv djv))
          child)
      (let [;; new-vars (vec (map (fn [v]
            ;;                      (if (is-bound? v)
            ;;                        (make-constant (get-value v))
            ;;                        v))
            ;;                    dj-vars))
            ret (make-disjunct-op dj-vars @ret-children @new-metadata)]
        ;(println @new-metadata)
                                        ;(debug-repl)
        ret))))

(def-rewrite
  :match {:rexpr (disjunct-op (:any-list dj-vars) (:unchecked ^PrefixTrie rexprs) metadata)
          :check (not (tlocal *simplify-looking-for-fast-fail-only*))}
  :run-at :standard
  :run-in-jit false
  (disjunct-op-rewrite-internals dj-vars rexprs simplify)

  ;; this does work to save rewrites, as there might be operations internally
  ;; which still need to get processed.  I suppose that if all of the internals
  ;; were mult values, then we could skip the rewriting work, but because we do
  ;; not guarantee that we have completed rewriting, there might still be other
  ;; rewrites which are still pending
  #_(if (not= (:current-var-vals metadata) (map get-value dj-vars))

    (do
      (println "save disjunct rewrite" metadata)
      nil)))

(def-rewrite
  :match {:rexpr (disjunct-op (:any-list dj-vars) (:unchecked ^PrefixTrie rexprs) metadata)
          :check (not (tlocal *simplify-looking-for-fast-fail-only*))}
  :run-at :inference
  :run-in-jit false
  ;; this will always attempt to do rewrites on the internal structure, as there might be something that we can infer as a result
  ;; if we tracked the different types of R-exprs which are contained, then
  (disjunct-op-rewrite-internals dj-vars rexprs simplify))

#_(def-rewrite
  :match {:rexpr (disjunct-op (:any-list dj-vars) (:unchecked ^PrefixTrie rexprs) metadata)
          :check (not *simplify-looking-for-fast-fail-only*)}
  :run-at [:standard :inference]
  :run-in-jit false
  (let [outer-context (context/get-context)
        dj-vars-vals-init (doall (map get-value dj-vars))
        ret-children (volatile! (make-PrefixTrie (count dj-vars) 0 nil))
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
                                    (let [child-trie ^PrefixTrie (:rexprs new-child-rexpr)
                                          child-vars (:disjunction-variables new-child-rexpr)
                                          new-order (vec (map (zipmap child-vars (range)) dj-vars))
                                          t-reordered (trie-reorder-keys child-trie new-order)]
                                      (vswap! ret-children trie-merge t-reordered)
                                      (vswap! num-children #(+ 2 %)) ;; there are at least 2 children getting added, which should ensure that we maintain the trie structure
                                      )
                                    (let [added-new (volatile! false)]
                                      (vswap! ret-children trie-update-collection dj-key
                                              (fn [col]
                                                (let [[made-new ret] (merge-rexpr-disjunct-list col new-child-rexpr)]
                                                  (vreset! added-new made-new)
                                                  ret)))
                                      (if @added-new
                                        (vswap! num-children inc)))))))
        ]
    (doseq [[var-binding child] (trie-get-values rexprs var-map)]
      ;; this should loop through the children
      (try
        (let [child-context (context/make-nested-context-disjunct child)]
          (doseq [i (range (count dj-vars))]
            ;; this should create bindings for the variables in the context when they are already known
            (let [djv (nth var-binding i)
                  dv (nth dj-vars i)]
              (when (and (not (nil? djv)) (is-variable? dv))
                                        ;(dyna-assert (not (is-bound-in-context? dv child-context)))
                (ctx-set-value! child-context dv djv))))
          (context/bind-context-raw
           child-context
           (let [new-child-rexpr (simplify child)]
             ;; if the new-child-rexpr is a disjunct, then we are just going to combine that into the thing that we are processing
             (cond (is-disjunct? new-child-rexpr)
                   (let [args (:args new-child-rexpr)
                         ctx (context/get-context)]
                     (doseq [a args]
                       (save-result-in-trie a ctx)))

                   (is-disjunct-op? new-child-rexpr)
                   (let [child-var-order (:disjunction-variables new-child-rexpr)
                         child-prefix-trie (:rexprs new-child-rexpr)]
                     (doseq [[key djc-rexpr] (trie-get-values child-prefix-trie nil)]
                       (let [val-map (zipmap child-var-order key)
                             new-keys (map #(get val-map %) dj-vars)
                             added-new (volatile! false)]
                         (vswap! ret-children trie-update-collection new-keys
                                 (fn [col]
                                   (let [[made-new ret] (merge-rexpr-disjunct-list col djc-rexpr)]
                                     (vreset! added-new made-new)
                                     ret)))
                         (if @added-new (vswap! num-children inc)))))

                   ;; if this is a more complex expression, then we will try to run iterators on the inner expression to allow it to become simpler and split into smaller expressions in the trie
                   (and *disjunct-run-inner-iterators*
                        (not *simplify-looking-for-fast-fail-only*)
                        (not (is-multiplicity? new-child-rexpr)))
                   (let [iters (find-iterators new-child-rexpr)]
                     (run-iterator
                      :iterators iters
                      :bind-all true
                      :rexpr-in new-child-rexpr
                      :rexpr-result child-rexpr-itered
                      :simplify #(binding [*simplify-looking-for-fast-fail-only* false] (simplify-fast %))
                      (let []
                        (save-result-in-trie (simplify child-rexpr-itered)
                                             (context/get-context) ;; we have to use get-context here as the iterator might have rebound the context
                                             ))))
                   :else
                   (save-result-in-trie new-child-rexpr child-context)))))
        (catch UnificationFailure err nil)))
    ;; set the values of variables which are the same across all branches
    (assert (= (map get-value dj-vars) dj-vars-vals-init))
    (doseq [i (range (count dj-vars))]
      (let [dv (nth child-var-values i)]
        (when (and (not= dv not-seen-in-trie) (not (nil? dv)) (is-variable? (nth dj-vars i)))
          (ctx-set-value! outer-context (nth dj-vars i) dv))))
    (case @num-children
      0 (make-multiplicity 0)
      1 (let [[[child-bindings child]] (trie-get-values @ret-children nil)]
          ;; return the child directly as there is only a single child and there is no need for the disjunction
          child)
      (let [ret (make-disjunct-op dj-vars @ret-children nil)]
        ;(println "making new trie with " @num-children)
        ret))))



(declare run-trie-iterator-from-node
         run-trie-iterator-from-node-unconsolidated)

;; this function is also used by memoization_v2
(defn trie-diterator-instance [remains node variable-order]
  (reify DIterator
    (iter-run-cb [this cb-fn]
      (doseq [v (iter-run-iterable this)]
        (cb-fn v)))
    (iter-run-iterable [this]
      (run-trie-iterator-from-node remains node variable-order))
    (iter-run-iterable-unconsolidated [this]
      (run-trie-iterator-from-node-unconsolidated remains node variable-order))
    (iter-bind-value [this value]
      (let [wild (get node nil)
            v (get node value)]
        (cond (and (not (nil? v)) (nil? wild))
              (trie-diterator-instance (- remains 1) v (next variable-order))

              (and (nil? v) (not (nil? wild)))
              (trie-diterator-instance (- remains 1) wild (next variable-order))

              (and (not (nil? v)) (not (nil? wild))) ;; need to run both branches of the trie at the same time in this case
              (iterator-disjunct-diterator [(trie-diterator-instance (- remains 1) v (next variable-order))
                                            (trie-diterator-instance (- remains 1) wild (next variable-order))]))))
    (iter-debug-which-variable-bound [this] (first variable-order))
    (iter-estimate-cardinality [this]
      (count node))))


;; return a lazy sequence over bindings
(defn- run-trie-iterator-from-node [remains trie-node variable-order]
  (dyna-assert (not (contains? trie-node nil))) ;; if this happens, this means
                                                ;; that it is trying to iterate
                                                ;; over something which would
                                                ;; not be able to ground the
                                                ;; variable
  (for [[key next-node] trie-node]
    (reify DIteratorInstance
      (iter-variable-value [this] key)
      (iter-continuation [this]
        (if (= 0 remains)
          nil  ;; there are going to be more disjuncts here
          (trie-diterator-instance (- remains 1) next-node (next variable-order)))))))

(defn- run-trie-iterator-from-node-unconsolidated [remains trie-node variable-order]
  (for [[key next-node] trie-node]
    (reify DIteratorInstance
      (iter-variable-value [this] key)
      (iter-continuation [this]
        (if (= 0 remains)
          nil
          (trie-diterator-instance (- remains 1) next-node (next variable-order)))))))

(def-iterator
  :match (disjunct-op (:any-list dj-vars) (:unchecked ^PrefixTrie rexprs) metadata)
  (let [contains-wildcard (.contains-wildcard ^PrefixTrie rexprs)
        trie-root (.root ^PrefixTrie rexprs)]
    (when (not= contains-wildcard (- (bit-shift-left 1 (count dj-vars)) 1))
      ;; then there exists at least one variable which does not contain a whild card, so it could be iterated
      #{(reify DIterable
          (iter-what-variables-bound [this]
            (let [ret (into #{} (for [idx (range (count dj-vars))
                                      :when (and (= 0 (bit-and contains-wildcard (bit-shift-left 1 idx)))
                                                 (is-variable? (nth dj-vars idx)))]
                                  (nth dj-vars idx)))]
              #_(when (and (not (empty? ret)) (not= 0 (.contains-wildcard rexprs)))
                (debug-repl "trie iter"))
              ret))
          (iter-variable-binding-order [this] [dj-vars])
          (iter-create-iterator [this which-binding]
            (when-not(.contains (iter-variable-binding-order this) which-binding)
              (throw (IteratorBadBindingOrder.)))
            (let [ret (trie-diterator-instance (count dj-vars) trie-root dj-vars)]
              ;(debug-repl "creating iterator from trie")
              ret)))})))





#_(def-deep-equals disjunct-op [a b]
  (when (instance? disjunct-rexpr b)
    ;; in the case of the origional disjunct, this is going to have that
    ;; unification between variables is represented as unify expressions instead
    ;; of as a trie.  I suppose that we could attempt to construct a representation and then compare between them

    ;; if there is a single value in the expression, I suppose that this could also result in creating which of the values would get represented
    ;; though that would potentially result in a lot of expensive compare options, in the case that it would be constantly looking through the trie
    (debug-repl "disjunct and disjunct-op deep equals")
    (???)
    ))

#_(def-deep-equals disjunct-op [a b]
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
  :match {:rexpr (disjunct-op (:any-list var-list) ^PrefixTrie rexprs metadata)
          :check *disjunct-op-remove-if-single*}
  :run-at :construction
  (loop [vars var-list
         node (.root rexprs)]
    (if (empty? vars)
      (if (= 1 (count node))
        (first node))
      (let [v (first vars)]
        (if (= 1 (count node))
          (let [[k n2] (first node)]
            (if (nil? k)
              (recur (rest vars)
                     n2)
              (when (context/has-context)
                (set-value! v k)
                (recur (rest vars)
                       n2)))))))))

(def-rewrite
  :match (disjunct-op (:any-list var-list) rexprs metadata)
  :run-at :construction
  :is-debug-check-rewrite true
  :run-in-jit false
  (let [var-set (into #{} var-list)]
    (when-not (every? (fn [[var-bindings x]] (if (and (rexpr? x)
                                                      ;; the variables which are exposed should be a subset of what is not ground
                                                      ;; or are we going to have to represent which of the values are represented with
                                                      (subset? (exposed-variables x) var-set))
                                               true
                                               (do
                                                 (debug-repl "disjunct gg1")
                                                 false)))
                      (trie-get-values rexprs nil))
      (let [rx (into [] (map second (trie-get-values rexprs nil)))]
        (debug-repl "R-expr in trie has extra exposed variables"))
      (???))))
