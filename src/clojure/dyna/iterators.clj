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


;; should we run all of the possible iterators?  that would



(defn- iterator-conjunction-orders [iterators]
  ;; figure out what orders of iterators can be run
  (let [variable-binding-orders (apply union (map #(iter-variable-binding-order %) iterators))
        first-variable-bindable (into #{} (map first variable-binding-orders))  ;; variables which this iterator can start with
        ]
    (for [v first-variable-bindable]
      ;; figure out which variables can be bound next
      ((fn following-variables [bound-vars]
         (let [possible-iters (map (fn [x]
                                     ;; drop out variables which are contained in the bound vars, so that we can
                                     (filter #(not (contains? bound-vars %)) x)
                                     ) variable-binding-orders)
               all-done (every? empty? possible-iters)]
           (if all-done
             () ;; there are no more iterators which can be bound using this, so return an empty sequency
             (for [nv (into #{} (remove empty? (map first possible-iters)))
                   seqs (following-variables (conj bound-vars nv))]
               (cons nv seqs))))
         ) #{v}))))

(defn make-unit-iterator [variable value]
  #{(reify DIterable
      (iter-what-variables-bound [this] #{variable})
      (iter-variable-binding-order [this] [[variable]])
      (iter-create-iterator [this which-binding]
        (assert (or (nil? which-binding) (= which-binding [variable])))
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

(defn make-disjunct-iterator [branches]
  (let [branch-variables (vec (map #(apply union (map iter-what-variables-bound %)) branches))
        all-variables-bindable  (apply intersection branch-variables)]
    (when-not (empty? all-variables-bindable)
      #{(reify DIterable
          (iter-what-variables-bound [this] all-variables-bindable)
          (iter-variable-binding-order [this]
            (let [ret (apply intersection (map #(iterator-conjunction-orders %)) branches)]
              (debug-repl)
              ret))
          (iter-create-iterator [this which-binding]
            ;; this should do the trick to figure out if it has already bound some
            ;; value, though if the set of values is sufficiently small, then it
            ;; might be ebtter if it would just track the set of values that it has
            ;; already processed?  might also be nice if there was some way in which
            ;; this could efficiently make use of the disjuncts.  though I suppose that this will have to
            (???)
            (reify DIterator
              (iter-run-cb [this cb-fun]
                ;; is this just going to run the sequence? or is there something more efficient that this can do here?
                ;; I suppose that this is simpler for now
                (doseq [v (iter-run-iterable this)]
                  (cb-fun v))
                )
              (iter-run-iterable [this]
                ;; return a sequence of what can be bound
                (let [iterators-run-already (transient [])]
                  ;; this is going to have to pick which iterator is going to be used
                  (???)
                  []))
              (iter-run-iterable-unconsolidated [this]
                (???))
              )))})))


(defn- build-skip-trie [^DIterator iterator arity skips]
  (let [ret (volatile! {})]
    ((fn rec [binding iter idx]
       (if (= idx arity)
         (vswap! ret assoc-in (reverse binding) nil)
         (if (= 0 (bit-and skips (bit-shift-left 1 idx)))
           ;; this variable is something that we are interested in
           (doseq [i (iter-run-iterable iter)]
             (rec (cons (iter-variable-value i) binding) (iter-continuation i) (+ idx 1)))
           ;; this is some variable that we would like to skip
           (doseq [i (iter-run-iterable-unconsolidated iter)]
             (rec binding (iter-continuation i) (+ idx 1))))))
     () iterator 0)
    @ret))

(defn- iterator-over-trie [trie]
  (reify DIterator
    (iter-run-cb [this cb-fn]
      (doseq [v (iter-run-iterable this)] (cb-fn v)))
    (iter-run-iterable [this]
      (for [[k v] trie]
        (reify DIteratorInstance
          (iter-variable-value [this] k)
          (iter-continuation [this]
            (if (nil? v) nil
                (iterator-over-trie v))))))
    (iter-run-iterable-unconsolidated [this] (iter-run-iterable this))
    (iter-bind-value [this value]
      (let [v (get trie value)]
        (if (nil? v) nil
            (iterator-over-trie v))))
    (iter-debug-which-variable-bound [this] (???))
    (iter-estimate-cardinality [this] (count trie))))

(defn- iterator-skip-variables [^DIterator underlying binding-order skipped-variables]
  (let [trie (delay (let [skips (apply bit-or (for [i (range (count binding-order))]
                                                (if (skipped-variables (nth binding-order i))
                                                  (bit-shift-left 1 i)
                                                  0)))]
                      (build-skip-trie underlying (count binding-order) skips)))]
    (if (skipped-variables (first binding-order))
      (iterator-over-trie @trie)
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
            (for [v (iter-run-iterable-unconsolidated this)]
              (reify DIteratorInstance
                (iter-variable-value [this] (iter-variable-value v))
                (iter-continuation [this] (iterator-skip-variables (iter-continuation v) r skipped-variables))))))
        (iter-bind-value [this value]
          (let [v (iter-bind-value underlying value)]
            (if (nil? v) nil
                (iterator-skip-variables v (rest binding-order) skipped-variables))))
        (iter-estimate-cardinality [this] (iter-estimate-cardinality underlying))))))

(defn make-skip-variables-iterator [^DIterable iterator binding-order skipped-variables]
  (reify DIterable
    (iter-what-variables-bound [this] (into #{} (remove skipped-variables binding-order)))
    (iter-variable-binding-order [this] [(into [] (remove skipped-variables binding-order))])
    (iter-create-iterator [this which-binding]
      (let [underlying (iter-create-iterator iterator binding-order)
            bding (apply list binding-order)]
        #_(reify DIterator
          (iter-run-cb [this cb-fn]
            (doseq [v (iter-run-iterable this)]
              (cb-fn v)))
          (iter-run-iterable [this]
            ;; if the variable that we are binding
            (iterator-skip-variables underlying binding-order skipped-variables))
            )
        (iterator-skip-variables underlying binding-order skipped-variables)
        ))))

(defn iterator-variable-can-not-bind [var]
  ;; something like the variable is required by the iterator (to be efficient)
  ;; but it is not bindable, this would be something like it would have that
  {:not-bindinable-var var})



(defn pick-iterator [iterators binding-variables]
  (let [bv (into #{} binding-variables)
        ;; we are going to consider some of the iterators which would be able to bind something
        ;; in the case that there are still values which are still unbound, it should just keep running
        iters (filter #(intersection bv (iter-what-variables-bound %)) iterators)
        ]
    ;; this should somehow identify a preference bteween the different binding
    ;; orders I suppose that if the code is going to get copiled, then it should
    ;; also identify which of the iterators are going to bindin the order that
    ;; we need.  Where that iterator comes from is also going to be something
    ;; that is important to identify, such that it doesn't just run all of the
    ;; iterators through

    (when (empty? iters)
      ;; in this case, we might want to attempt to find if there is some way to
      ;; construct a conjunctive iterator using this there might also be
      ;; something with
      ;;
      ;; I suppose that this could return an empty iterator where there would be
      ;; no variables to bind and nothing to do the binding.  This would cause
      ;; the system to directly callback the wrapped function such that it would directly evaluate the result

      (debug-repl "did not find iterator to pick"))
    (let [picked-iter (first iters)
          can-bind-variables (iter-what-variables-bound picked-iter)
          binding-order (first (iter-variable-binding-order picked-iter))
          ]
      (dyna-assert (seqable? binding-order)) ;; this should be a sequence of variables in the order that they are bound
      (if (every? #(or (can-bind-variables %) (is-constant? %)) binding-order)
        [picked-iter binding-order] ;; then we can just use this iterator directly as all of the variables are bindable
        (let [dd (difference (into #{} binding-order) can-bind-variables)
              ;zzz (debug-repl)
              siter (make-skip-variables-iterator picked-iter binding-order dd)]
          ;(debug-repl "unbindable variable in iterator")
          ;; this iterator will only represent the variables that we are allowed to bind using this iterator
          [siter (first (iter-variable-binding-order siter))])
        )
      ;(debug-repl "pick iterator")
      ;[picked-iter binding-order]
      )
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
             (when-not (nil? it-bound) ;; if the binding failed, then the iterator should return nil to indicate that there is nothing here
               (rec it-bound r rexpr)))
           (if (contains? can-bind-variables v)
             (doseq [val (iter-run-iterable iter)]
               (let [dctx (context/make-nested-context-disjunct rexpr)] ;; this should take the context as an argument?
                 (context/bind-context-raw
                  dctx
                  (ctx-set-value! dctx v (iter-variable-value val))
                  (let [new-rexpr (simplify-fn rexpr)] ;; would be nice if the simplify could track which branches would depend on the value and ignore the rest. I suppose that would really be something that we should do compilation.  There is no need to increase the complexity of the standard simplify method
                    (when-not (is-empty-rexpr? new-rexpr)
                      (rec (iter-continuation val) r new-rexpr))
                    ))))
             (do
               (debug-repl "not able to bind variable")
               (???))
             ))
         )))
   (iter-create-iterator picked-iterator picked-binding-order) ;; create the start of the iterator
   (apply list picked-binding-order)  ;; make this a linked list so that it will quickly be able to pull items off the head of the list
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

(defn- iter-encode-state-as-rexpr [picked-binding-order ignore-vars]
  (let [encode-vars (filter is-variable? picked-binding-order)
        vs (remove ignore-vars encode-vars)
        c (vec (for [v vs]
                 (make-no-simp-unify v (make-constant (get-value v)))))
        r (make-conjunct c)]
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
                                    (function-let [iterator-encode-state-as-rexpr (~iter-encode-state-as-rexpr picked-binding-order# #{})
                                                   iterator-encode-state-ignore-vars (~iter-encode-state-as-rexpr picked-binding-order# %)]
                                                  ~body))
                     ]
                 (~run-iterator-fn
                  picked-iterator#
                  picked-binding-order#
                  (iter-what-variables-bound picked-iterator#)
                  ~rexpr
                  ~ctx
                  callback-fn#
                  ~simplify-method)
                 )]
      ;(debug-repl "iter runner")
      ret)
    ))


;; the iterators which bind variables that are "hidden" might still be useful,
;; but these variables are not something that can be bound yet.  This must
;; deduplicate the values which result from the other variables first.
(defn filter-variables-from-iterators [variables iterators]
  (filter #(not (contains? (iter-what-variables-bound variables) %)) iterators))
