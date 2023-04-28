(ns dyna.iterators
  (:require [dyna.utils :refer :all])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.rexpr-constructors :refer :all])
  (:require [dyna.context :as context])
  (:require [clojure.set :refer [union intersection subset? difference]])
  ;(:require [clojure.tools.macro :refer [macrolet]])
  (:import [dyna DIterable DIterator DIteratorInstance]))

;; iterators are going to allow for there to efficiently loop over the values which are assigned to variables

;; should the iterators assume the context?  in which case it can have that the
;; iterator can just set values into the context when it is doing iteration.  If
;; we don't assume a context, then we will find that there is some

;; the context should eventually be something that can be represented as an
;; array or some "efficient" structure where we can access different fields.
;; This means that we would like to be able to have that the iterator will not
;; be tied to using the variable name (per-se), or there should be some

;; this could be like a map function?  This would have that it returns a
;; possibly lazy serquence over the values returned by the run-cb?
;; this will want to find which of the values will have this binding





(defn make-unit-iterator [variable value]
  #{(reify DIterable
      (iter-what-variables-bound [this] #{variable})
      (iter-variable-binding-order [this] [[variable]])
      (iter-create-iterator [this which-binding]
        (assert (or (= which-binding [variable])))
        (reify DIterator
          (iter-run-cb [this cb-fun]
            (cb-fun (reify DIteratorInstance
                      (iter-variable-value [this]
                        value)
                      (iter-continuation [this] nil))))
          (iter-bind-value [this v]
            (if (= value v)
              iterator-empty-instance))
          (iter-run-iterable [this]
            ;; return a sequence of the values from this iterator
            [(reify DIteratorInstance
               (iter-variable-value [this] value)
               (iter-continuation [this] nil))])
          (iter-run-iterable-unconsolidated [this]
            (iter-run-iterable this))
          (iter-debug-which-variable-bound [this]
            variable))))})

(defn- iterator-conjunction-orders [iterators]
  ;; figure out what orders of iterators can be run
  (if (= 1 (count iterators))
    (iter-variable-binding-order (first iterators))
    (let [variable-binding-orders (apply union (map iter-variable-binding-order iterators))
          first-variable-bindable (into #{} (map first variable-binding-orders))  ;; variables which this iterator can start with
          ]
      (for [v first-variable-bindable
            fv ((fn following-variables [bound-vars]
                  (let [possible-iters (map (fn [x]
                                              ;; drop out variables which are contained in the bound vars, so that we can
                                              (filter #(not (contains? bound-vars %)) x)
                                              ) variable-binding-orders)
                        all-done (every? empty? possible-iters)]
                    (if all-done
                      (list ()) ;; there are no more iterators which can be bound using this, so return an empty sequency
                      (for [nv (into #{} (remove empty? (map first possible-iters)))
                            seqs (following-variables (conj bound-vars nv))]
                        (cons nv seqs)))))
                #{v})]
        ;; figure out which variables can be bound next
        (cons v fv)))))

(defn- iterator-conjunction-start-sub-iterators [iterators order]
  ;; in there are many conjunctive iterators that we want to combine into a single iterator, this will
  ;; identify how to construct the sub iterators with different orders

  (let [;variable-binding-orders (apply union (map iter-variable-binding-order iterators))
        binding-order-iter (into {} (for [iter iterators
                                          itorder (iter-variable-binding-order iter)]
                                      [(vec itorder) iter]))
        order-map (zipmap order (range))
        usable-bindings (filter (fn [b]
                                  (loop [idx 0
                                         ord b]
                                    (if (empty? ord)
                                      true
                                      (let [new-idx (order-map (first ord))]
                                        (if (< new-idx idx)
                                          false
                                          (recur new-idx (next ord)))))))
                                (keys binding-order-iter))
        picked-bindings (loop [bo order
                               bound #{}
                               picked-map {}]
                          (if (empty? bo)
                            picked-map
                            (let [nv (first bo)]
                              (if (some (fn [[k v]] (some #{nv} k)) picked-map)
                                ;; then there is nothing that we need to add to the map
                                (recur (next bo)
                                       (conj bound nv)
                                       picked-map)
                                ;; need to determine some usable binding
                                (let [can-bind (first (filter #(some #{nv} %) usable-bindings))
                                      can-bind-iter (binding-order-iter (vec can-bind))]
                                  (assert (not (nil? can-bind-iter)))
                                  (recur (next bo)
                                         (conj bound nv)
                                         (assoc picked-map can-bind can-bind-iter)))))))
        ]
    ;(debug-repl "used bindings")
    (into {} (for [[k v] picked-bindings]
               [k (iter-create-iterator v k)]))))

(defn- iterator-conjunction-diterator [iterators order]
  ;; iterators is a map where the key is the order of the variables which get bound, and the value is the nested diterator object
  ;; when running through a conjunction of multiple iterators, we can bind all of the iterators which match for a given variable
  (reify DIterator
    (iter-run-cb [this cb-fn] (doseq [v (iter-run-iterable this)] (cb-fn v)))
    (iter-run-iterable [this]
      (let [picked-var (first order)
            remains-var (next order)
            possible-iterators (filter (fn [[k v]] (= (first k) picked-var)) iterators)
            [picked-it-order picked-iterator] (first possible-iterators) ;; this should select the one that has the lowest cardinality or something....
            picked-it-order-remains (next picked-it-order)
            ret
            ((fn run [iter]
               (let [iter-val (first iter)]
                 (if (nil? iter-val)
                   () ;; then we have reached the end of the sequence, so we just stop
                   (let [iter-var-val (iter-variable-value iter-val)
                         new-bindings (into {} (map (fn [[k v]]
                                                      (if (= (first k) picked-var)
                                                        [(next k) (iter-bind-value v iter-var-val)]
                                                        [k v]))
                                                    iterators))]
                     (if (some (fn [[k v]] (nil? v)) new-bindings)
                       ;; then one of the conjuncts failed to bind, so we just are going to skip this value
                       (recur (next iter))
                       ;; the binding was successful, so we will return a continuation
                       (cons (reify DIteratorInstance
                               (iter-variable-value [this] iter-var-val)
                               (iter-continuation [this] (iterator-conjunction-diterator new-bindings remains-var)))
                             (lazy-seq (run (next iter)))))))))
             (iter-run-iterable picked-iterator))]
                                        ;(debug-repl "g2")
        ret))
    (iter-run-iterable-unconsolidated [this]
      ;; this should use the unconsolidated iterators to make this work?  though this would just pick something I suppose
      (iter-run-iterable this))
    (iter-bind-value [this value]
      (let [picked-var (first order)
            new-bindings (into {} (map (fn [[k v]]
                                         (if (= (first k) picked-var)
                                           [(next k) (iter-bind-value v value)]
                                           [k v]))
                                       iterators))]
        (if (some (fn [[k v]] (nil? v)) new-bindings)
          nil
          (iterator-conjunction-diterator new-bindings (next order)))))))

(defn- iterator-intersect-orders [iterator-orders-set]
  (if (<= (count iterator-orders-set) 1)
    (first iterator-orders-set)
    (let [lorders (ensure-set (first iterator-orders-set))]
      (into #{}
            (remove empty?
                    (for [porder (iterator-intersect-orders (rest iterator-orders-set))
                          ll lorders]
                      ;; this should look at the set of values which are already
                      ;; present, and then figure what is something that could be
                      ;; returned from
                      (for [[a b] (zipseq porder ll)
                            :while (= a b)]
                        a)))))))

;; the other make-*-iterator return a (possibly empty) set, whereas this just
;; returns the iterator directly.
;; TODO: this should also return a set which contains the itertor
(defn make-conjunction-iterator [iterators]
  (case (count iterators)
    0 nil
    1 (first iterators)
    (reify DIterable
      (iter-what-variables-bound [this] (apply union (map iter-what-variables-bound iterators)))
      (iter-variable-binding-order [this] (iterator-conjunction-orders iterators))
      (iter-create-iterator [this which-binding]
                                        ;(debug-repl "vv")
        (let [existing (loop [itrs iterators]
                         (if (empty? itrs)
                           nil
                           (if (some #{which-binding} (iter-variable-binding-order (first itrs)))
                             (iter-create-iterator (first itrs) which-binding)
                             (recur (next itrs)))))]
          (if-not (nil? existing)
            existing
            (do
                                        ;(debug-repl "finish writing this")
                                        ;(???) ;; TODO: finish writing this code
              (iterator-conjunction-diterator
               (iterator-conjunction-start-sub-iterators iterators which-binding)
               which-binding))))))))


(defn- build-skip-trie [^DIterator iterator arity skips]
  (let [ret (volatile! {})]
    ((fn rec [binding iter idx]
       (if (= idx arity)
         (vswap! ret assoc-in (reverse binding)
                 :value-exists ;; we don't use this value, but it has to be something (other than nil) otherwise we assume that there is nothing in the trie
                 )
         (if (= 0 (bit-and skips (bit-shift-left 1 idx)))
           ;; this variable is something that we are interested in
           (doseq [i (iter-run-iterable-unconsolidated iter)
                   :let [val (iter-variable-value i)]]
             ;(dyna-assert (not (nil? val)))  ;; this is allowed to be nil
             ;(dyna-assert (not (nil? (iter-continuation i)))) ;; this can happen in the case that (= idx (- arity 1))
             (rec (cons val binding) (iter-continuation i) (+ idx 1)))
           ;; this is some variable that we would like to skip
           (doseq [i (iter-run-iterable-unconsolidated iter)]
             (dyna-assert (not (nil? (iter-continuation i))))
             (rec binding (iter-continuation i) (+ idx 1))))))
     () iterator 0)
    @ret))

(defn- iterator-over-trie [trie]
  (reify DIterator
    (iter-run-cb [this cb-fn]
      (doseq [v (iter-run-iterable this)] (cb-fn v)))
    (iter-run-iterable [this]
      (dyna-assert (not (contains? trie nil)))  ;; otherwise we can only run the unconsolidated version
      (iter-run-iterable-unconsolidated this)
      )
    (iter-run-iterable-unconsolidated [this]
      (for [[k v] trie]
        (reify DIteratorInstance
          (iter-variable-value [this] k)
          (iter-continuation [this]
            (when (map? v)
              (iterator-over-trie v))))))
    (iter-bind-value [this value]
      (let [v (get trie value)]
        (if (nil? v) nil
            (iterator-over-trie v))))
    (iter-debug-which-variable-bound [this] [:trie-iterator trie])
    (iter-estimate-cardinality [this] (count trie))))

(defn- iterator-skip-variables [^DIterator underlying binding-order skipped-variables]
  (if (skipped-variables (first binding-order))
    (let [skips (reduce bit-or 0 (for [i (range (count binding-order))]
                                   (if (skipped-variables (nth binding-order i))
                                     (bit-shift-left 1 i)
                                     0)))
          ;zzz (debug-repl)
          trie (if (= skips (dec (bit-shift-left 1 (inc (count binding-order)))))
                 (do
                   (???);(debug-repl "??? skip all")
                   {}) ;; meaning that we are skipping all of the variables??? wtf
                 (build-skip-trie underlying (count binding-order) skips))]
      (iterator-over-trie trie))
    (reify DIterator
      (iter-run-cb [this cb-fn] (doseq [v (iter-run-iterable this)] (cb-fn v)))
      (iter-run-iterable [this]
        (let [r (rest binding-order)]
          (for [v (iter-run-iterable underlying)]
            (reify DIteratorInstance
              (iter-variable-value [this] (iter-variable-value v))
              (iter-continuation [this] (iterator-skip-variables (iter-continuation v) r skipped-variables))))))
      (iter-run-iterable-unconsolidated [this]
        (let [r (rest binding-order)]
          (for [v (iter-run-iterable-unconsolidated underlying)]
            (reify DIteratorInstance
              (iter-variable-value [this] (iter-variable-value v))
              (iter-continuation [this] (iterator-skip-variables (iter-continuation v) r skipped-variables))))))
      (iter-bind-value [this value]
        (let [v (iter-bind-value underlying value)]
          (if (nil? v) nil
              (iterator-skip-variables v (rest binding-order) skipped-variables))))
      (iter-debug-which-variable-bound [this] [:iter-skip-variables underlying binding-order skipped-variables])
      (iter-estimate-cardinality [this] (iter-estimate-cardinality underlying)))))

(defn make-skip-variables-iterator [^DIterable iterator skipped-variables]
  (reify DIterable
    (iter-what-variables-bound [this] (remove skipped-variables (iter-what-variables-bound iterator)))
    (iter-variable-binding-order [this] (let [ret (into [] (map #(remove skipped-variables %) (iter-variable-binding-order iterator)))]
                                          ;(debug-repl "bo")
                                          ret))
    (iter-create-iterator [this which-binding]
      (let [selected-binding (first (filter #(= which-binding (into [] (remove skipped-variables %))) (iter-variable-binding-order iterator)))
            underlying (iter-create-iterator iterator selected-binding)]
        (iterator-skip-variables underlying selected-binding skipped-variables)))))

(defn iterator-disjunct-diterator [branch-iters]
  (reify DIterator
    (iter-run-cb [this cb-fn]
      (doseq [v (iter-run-iterable this)]
        (cb-fn v)))
    (iter-run-iterable [this]
      ((fn rec [completed-iterators next-iterators current-iterable current-diterable]
         (let [iter-val (first current-iterable)
               iter-rest (next current-iterable)]
           (if (nil? iter-val)
             ;; this needs to move to the next iterator
             (if (empty? next-iterators)
               () ;; then we are done iterating, so just return the empty sequence which will be the tail of the list
               (rec (conj completed-iterators current-diterable)
                    (next next-iterators)
                    (iter-run-iterable (first next-iterators))
                    (first next-iterators)))
             (let [var-val (iter-variable-value iter-val)
                   existing-can-bind (some #(iter-bind-value % var-val) completed-iterators)]
               ;; then we have some value, so we need to check if the existing iterators already processed this value
               ;; also the continuation is going to have to
               (if existing-can-bind
                 ;; then this value has already been seen, so we are going to use tail recursion to try for another value
                 (recur completed-iterators next-iterators iter-rest current-diterable)
                 ;; then this value is new, so we are going to return it, through, we have to build a new continuation for this based off what can bind
                 (cons (reify DIteratorInstance
                         (iter-variable-value [this] var-val)
                         (iter-continuation [this]
                           (let [other-iters (filter #(iter-bind-value % var-val) next-iterators)]
                             (if (empty? other-iters)
                               (iter-continuation iter-val) ;; this is the only iterator that can bind to this given value, so we just return it directly
                               ;; there are mutliple iterators
                               (iterator-disjunct-diterator (conj other-iters (iter-continuation iter-val)))))))
                       ;; the continuation for these values
                       (lazy-seq (rec completed-iterators next-iterators iter-rest current-diterable))))))))
       [] (next branch-iters) (iter-run-iterable (first branch-iters)) (first branch-iters)))
    (iter-run-iterable-unconsolidated [this]
      (for [b branch-iters
            v (iter-run-iterable b)]
        v))
    (iter-bind-value [this value]
      (let [new-branches (remove nil? (map #(iter-bind-value % value) branch-iters))]
        (cond (empty? new-branches) nil
              (= (count new-branches) 1) (first new-branches)
              :else (iterator-disjunct-diterator new-branches))))
    (iter-debug-which-variable-bound [this] (???))
    (iter-estimate-cardinality [this]
      (reduce + (map iter-estimate-cardinality branch-iters)))))



(defn make-disjunct-iterator [branches]
  (let [branch-variables (vec (map #(apply union (map iter-what-variables-bound %)) branches))
        all-variables-bindable  (apply intersection (map ensure-set branch-variables))]
    (when-not (empty? all-variables-bindable)
      #{(reify DIterable
          (iter-what-variables-bound [this] all-variables-bindable)
          (iter-variable-binding-order [this]
            (let [mm (map #(ensure-set (iterator-conjunction-orders %)) branches)
                  ret (iterator-intersect-orders mm)]
              (dyna-assert (not (empty? ret)))
              ret))
          (iter-create-iterator [this which-binding]
            ;; this should do the trick to figure out if it has already bound some
            ;; value, though if the set of values is sufficiently small, then it
            ;; might be ebtter if it would just track the set of values that it has
            ;; already processed?  might also be nice if there was some way in which
            ;; this could efficiently make use of the disjuncts.  though I suppose that this will have to
            (let [branch-iters (map #(iter-create-iterator (make-conjunction-iterator %) which-binding) branches)]
              (iterator-disjunct-diterator branch-iters))))})))



#_(defn iterator-variable-can-not-bind [var]
  ;; something like the variable is required by the iterator (to be efficient)
  ;; but it is not bindable, this would be something like it would have that
  {:not-bindinable-var var})



(defn pick-iterator [iterators binding-variables]
  (let [bv (into #{} binding-variables)
        ;; we are going to consider some of the iterators which would be able to bind something
        ;; in the case that there are still values which are still unbound, it should just keep running
        iters (if (empty? bv)
                 ;; if there are no requirements on the iterators, then we can just pick anything
                (filter #(not (empty? (iter-what-variables-bound %))) iterators)
                (filter #(some bv (iter-what-variables-bound %)) iterators))
        ]
    ;; this should somehow identify a preference bteween the different binding
    ;; orders I suppose that if the code is going to get copiled, then it should
    ;; also identify which of the iterators are going to bindin the order that
    ;; we need.  Where that iterator comes from is also going to be something
    ;; that is important to identify, such that it doesn't just run all of the
    ;; iterators through

    (if (empty? iters)
      ;; in this case, we might want to attempt to find if there is some way to
      ;; construct a conjunctive iterator using this there might also be
      ;; something with
      ;;
      ;; I suppose that this could return an empty iterator where there would be
      ;; no variables to bind and nothing to do the binding.  This would cause
      ;; the system to directly callback the wrapped function such that it would directly evaluate the result
      (do
        ;(debug-repl "did not find iterator to pick")
        [nil nil])
      (let [picked-iter (first iters)
            can-bind-variables (into #{} (iter-what-variables-bound picked-iter))
            binding-order (first (iter-variable-binding-order picked-iter))
            ]
        (dyna-assert (and (seqable? binding-order)
                          (not (empty? binding-order)))) ;; this should be a sequence of variables in the order that they are bound
        (if (every? #(or (can-bind-variables %) (is-constant? %)) binding-order)
          [picked-iter binding-order] ;; then we can just use this iterator directly as all of the variables are bindable
          (let [dd (difference (into #{} binding-order) can-bind-variables)
                                        ;zzz (debug-repl)
                siter (make-skip-variables-iterator picked-iter dd)
                siter-order (first (iter-variable-binding-order siter))]
                                        ;(debug-repl "unbindable variable in iterator")
            ;; this iterator will only represent the variables that we are allowed to bind using this iterator
            [siter siter-order])
          )
                                        ;(debug-repl "pick iterator")
                                        ;[picked-iter binding-order]
        ))
    ))


;; TODO: can-bind-variables can be removed now I think..
(defn- run-iterator-fn [picked-iterator picked-binding-order can-bind-variables rexpr ctx callback-fn simplify-fn]
  ((fn rec [iter bind-order rexpr]
     (if (empty? bind-order)
       ;; then we have reached the end of this expression, so we are going to callback
       (callback-fn rexpr)
       (let [v (first bind-order)
             r (rest bind-order)
             is-bound (is-bound-in-context? v ctx)]
         (if is-bound
           ;; then we are going do bind the variable in the iterator to the current value and keep running the recursion
           ;; we do not resimplify the R-expr as we have not made any changes
           (let [it-bound (iter-bind-value iter (get-value-in-context v ctx))]
             ;(debug-repl)
             (if-not (nil? it-bound) ;; if the binding failed, then the iterator should return nil to indicate that there is nothing here
               (rec it-bound r rexpr)
               (do
                 ;; in the case that a binding failed, this just means that the iterator does not support this value, hence the multiplicity
                 ;; of the resulting rexpr would be zero.  In this case, we can just do nothing
                 )))
           (if (some #{v} can-bind-variables) ;(contains? can-bind-variables v)
             (doseq [val (iter-run-iterable iter)]
               (let [dctx (context/make-nested-context-disjunct rexpr)] ;; this should take the context as an argument?
                 (context/bind-context-raw
                  dctx
                  (ctx-set-value! dctx v (iter-variable-value val))
                  (let [new-rexpr (simplify-fn rexpr)] ;; would be nice if the simplify could track which branches would depend on the value and ignore the rest. I suppose that would really be something that we should do compilation.  There is no need to increase the complexity of the standard simplify method
                    (if-not (is-empty-rexpr? new-rexpr)
                      (rec (iter-continuation val) r new-rexpr)
                      (do
                        ;(debug-repl "empty after simplify")
                        ))
                    ))))
             (do
               (debug-repl "not able to bind variable")
               (???))
             ))
         )))
   (iter-create-iterator picked-iterator picked-binding-order) ;; create the start of the iterator
   (let [bo (apply list picked-binding-order)]
     (dyna-assert (not (empty? bo)))
     bo)  ;; make this a linked list so that it will quickly be able to pull items off the head of the list
   rexpr))



;; there should be something which allows this to "know" what variables are
;; going to be around/bindable, and then that could be used inside of the JIT
;; for generating code.

;; Question: should the iterator return a disjunct of the result?  It would
;; basically already have the disjunct, but I suppose that it could find that
;; some of the expressions might not require that

;; when returning a disjunct, should this return an optimized disjunct?
;; this would make it into somewhat of a circular implementation issue?
;; I suppose that there could be another macro which wraps this to make it return a disjunct

(defn- iter-encode-state-as-rexpr [root-iter-context picked-binding-order ignore-vars]
  (let [ctx-value-map (ctx-get-value-map-upto-context (context/get-context) root-iter-context)
        ;encode-vars (filter is-variable? picked-binding-order)
                                        ;vs (remove ignore-vars encode-vars)
        vs (apply dissoc ctx-value-map ignore-vars)
        c (vec (for [[k v] vs]
                 (make-no-simp-unify k (make-constant v))))
        r (make-conjunct c)]
    ;(debug-repl "encode state")
    r))

(defmacro run-iterator [& args]
  (let [kw-args (apply hash-map (drop-last args))
        body (last args)
        assign-to-context (:use-context kw-args true) ;; if the variables should get set into the context when they are bound
        iter-collection (:iterators kw-args) ;; this is going to be a list/set of iterators which are possible iterators to look at
        ;bind-all (:bind-all kw-args false) ;; if this should bind all of the variables before this calls back into the function, or if this should
        required-binding (:required kw-args)
        rexpr-to-simplify (:rexpr-in kw-args `(make-multiplicity 1))  ;; if there is no R-expr, then we can just use mult 1 which should just do "nothing"
        rexpr-callback-var (:rexpr-result kw-args (if (simple-symbol? rexpr-to-simplify)
                                                    rexpr-to-simplify
                                                    (gensym 'callback-rexpr)))
        ctx (gensym 'ctx)
        rexpr (gensym 'rexpr)
        simplify-method (:simplify kw-args 'simplify)
        ;; the macro let does not work with the debug-repl.  I suppose that
        ;; there could be something simpler which woul djust keep the same form,
        ;; but would expand the macro in place?  Or that it would
        ;; callback-body (macroexpand `(macrolet [~'iterator-encode-state-as-rexpr
        ;;                                        ([] `(do
        ;;                                               (debug-repl "encode state as r-expr not implemented")
        ;;                                               (???)))]
        ;;                                       ~body))
        ]
    (let [ret `(let [iters# ~iter-collection
                     ~rexpr ~rexpr-to-simplify
                     ~ctx ~(if assign-to-context
                             `(context/get-context) ;; use the existing "global" context
                             `(context/make-empty-context ~rexpr))
                     [picked-iterator# picked-binding-order#] (pick-iterator iters# ~required-binding)
                     callback-fn# (fn [~rexpr-callback-var]
                                    ;; could use macrolet here to define the
                                    ;; encode-state-as-rexpr and then it can
                                    ;; expand into whatever is required we know
                                    ;; the variables for the expression and what
                                    ;; is bound.  I suppose that we can also use
                                    ;; the origional R-expr when doing the encoding
                                    (function-let [iterator-encode-state-as-rexpr (~iter-encode-state-as-rexpr ~ctx picked-binding-order# #{})
                                                   iterator-encode-state-ignore-vars (~iter-encode-state-as-rexpr ~ctx picked-binding-order# %)]
                                                  ~body))
                     ]
                 (if (nil? picked-iterator#)
                   (callback-fn# ~rexpr) ;; there is nothing to iterate, so just run the callback function
                   (do ;(dyna-assert (subset? picked-binding-order# (ensure-set (iter-what-variables-bound picked-iterator#))))
                       (~run-iterator-fn
                        picked-iterator#
                        picked-binding-order#
                        (iter-what-variables-bound picked-iterator#)
                        ~rexpr
                        ~ctx
                        callback-fn#
                        ~simplify-method)))
                 )]
      ;(debug-repl "iter runner")
      ret)
    ))


;; the iterators which bind variables that are "hidden" might still be useful,
;; but these variables are not something that can be bound yet.  This must
;; deduplicate the values which result from the other variables first.
(defn filter-variables-from-iterators [variables iterators]
  (filter #(not (contains? (iter-what-variables-bound variables) %)) iterators))
