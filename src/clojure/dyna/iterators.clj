(ns dyna.iterators
  (:require [dyna.utils :refer :all])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.rexpr-constructors :refer :all])
  (:require [dyna.context :as context])
  (:require [clojure.set :refer [union intersection subset?]])
  (:require [clojure.tools.macro :refer [macrolet]])
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
                  [])))))})))

(defn iterator-variable-can-not-bind [var]
  ;; something like the variable is required by the iterator (to be efficient)
  ;; but it is not bindable, this would be something like it would have that
  {:not-bindinable-var var})


#_(defn make-unit-iterator [variable value]
  #{(reify DIterable
      (iter-what-variables-bound [this] #{variable})
      (iter-variable-binding-order [this] [[variable]]) ;; could do something like {#{} #{variable}}
      (iter-create-iterator [this which-binding]
        (assert (or (nil? which-binding) (= which-binding [variable])))
        (reify DIterator
          (iter-run-cb [this cb-fun] (cb-fun {variable value}))
          ;(iter-has-next [this] false)
          ))
      Object
      (toString [this] (str "(unit-iterator " variable " " value ")")))})


#_(defn make-disjunct-iterator [branches]
  (let [branch-variables (vec (map (fn [b] (apply union (map iter-what-variables-bound b)))
                                   branches))
        all-variable-bindable (apply intersection branch-variables)
        ret (into #{} (for [var all-variable-bindable]
                        (reify DIterable
                          (iter-what-variables-bound [this] #{var})
                          (iter-variable-binding-order [this] [[var]])
                          (iter-create-iterator [this which-binding]
                            (assert (or (nil? which-binding) (= which-binding [var])))
                            (reify DIterator
                              (iter-run-cb [this cb-fun]
                                ;; this has to run the first iterator and record what values are contained
                                ;; and then run the second iterator without duplicating the result
                                (let [values-seen (transient #{})]
                                  (doseq [b branches]
                                    (let [itr (filter #(contains? (iter-what-variables-bound %) var) b)]
                                      (iter-run-cb (iter-create-iterator (first itr) nil)
                                                   (fn [var-bindings]
                                                     (when-not (contains? values-seen var-bindings)
                                                       (conj! values-seen var-bindings)
                                                       (cb-fun var-bindings))))))))
                              ;(iter-has-next [this] false)
                              )))
                        ))
        ]
    ;; I suppose that this can just do this a single variable at a time for the
    ;; start?  Though when there are chains of variables which can
    ;; become bound, that becomes more complicated.  This
    ret))

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
      (debug-repl "did not find iterator to pick"))
    (let [ret (first iters)
          binding-order (first (iter-variable-binding-order ret))]
      ;(debug-repl "pick iterator")
      [ret binding-order])
    ))


(defn- run-iterator-fn [picked-iterator picked-binding-order rexpr ctx callback-fn simplify-fn]
  ((fn rec [iter bind-order rexpr]
     (if (empty? bind-order)
       ;; then we have reached the end of this expression, so we are going to callback
       (callback-fn rexpr)
       (let [v (first bind-order)
             r (rest bind-order)]
         (if (is-bound-in-context? v ctx)
           ;; then we are going do bind the variable in the iterator to the current value and keep running the recursion
           ;; we do not resimplify the R-expr as we have not made any changes
           (let [it-bound (iter-bind-value iter (get-value-in-context v ctx))]
             (debug-repl)
             (when-not (nil? it-bound) ;; if the binding failed, then the iterator should return nil to indicate that there is nothing here
               (rec it-bound r rexpr)))
           (do
             (debug-repl)
             (doseq [val (iter-run-iterable iter)]
                 (let [dctx (context/make-nested-context-disjunct rexpr)] ;; this should take the context as an argument?
                   (context/bind-context-raw
                    dctx
                    (ctx-set-value! dctx v (iter-variable-value val))
                    (let [new-rexpr (simplify-fn rexpr)] ;; would be nice if the simplify could track which branches would depend on the value and ignore the rest. I suppose that would really be something that we should do compilation.  There is no need to increase the complexity of the standard simplify method
                      (when-not (is-empty-rexpr? new-rexpr)
                        (rec (iter-continuation val) r new-rexpr))
                      ))))))
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
        callback-body (macroexpand `(macrolet [(~'iterator-encode-state-as-rexpr
                                               [] `(do
                                                     (debug-repl "encode state as r-expr not implemented")
                                                     (???)))]
                                              ~body))
        ]
    (let [ret `(let [iters# ~iter-collection
                     ~rexpr ~rexpr-to-simplify
                     ~ctx ~(if assign-to-context
                             `(context/get-context) ;; use the existing "global" context
                             `(context/make-empty-context ~rexpr))
                     callback-fn# (fn [~rexpr-callback-var]
                                    ;; could use macrolet here to define the
                                    ;; encode-state-as-rexpr and then it can
                                    ;; expand into whatever is required we know
                                    ;; the variables for the expression and what
                                    ;; is bound.  I suppose that we can also use
                                    ;; the origional R-expr when doing the encoding
                                    ~callback-body)
                     [picked-iterator# picked-binding-order#] (pick-iterator iters# ~required-binding)
                     ;; the variable that is
                     ;iterator# (iter-create-iterator picked-iterator#)
                     ]
                 ;; what this needs to do is bind the
                 ;; ((fn iter-rec# [var-bindings ])
                 ;;  picked-binding-order# ;; this is a list where the order of variables can be puled

                 ;;  )
                 (~run-iterator-fn picked-iterator# picked-binding-order# ~rexpr ~ctx callback-fn# ~simplify-method)
                 )]
      ;(debug-repl)
      ret)
    ))


;; I suppose that there could be some way of getting the variable context?  Or the binding of some variable
#_(defmacro iterator-encode-state-as-rexpr []
  `(do
     (debug-repl "iterator encode state as rexpr, not implemented")
     (???)))

;; (defmacro iterator-continue-running []
;;   ;; in the case that the iterator is going to
;;   `(???))


#_(defmacro run-iterator [iterators binding-variables & body]
  `(let [iterators# ~iterators
         binding-variables# ~binding-variables ;; should this require that all of the variables here are bound, or is it fine if the values are
         result (volatile! nil)]
     (iter-run-cb)
     ))


;; the iterators which bind variables that are "hidden" might still be useful,
;; but these variables are not something that can be bound yet.  This must
;; deduplicate the values which result from the other variables first.
(defn filter-variables-from-iterators [variables iterators]
  (filter #(not (contains? (iter-what-variables-bound variables) %)) iterators))



;; there should be some way in which we can loop over the disjunctive branches
;; of the R-expr but we should also combine the branches back together.  Should
;; those branches become combined using a new disjunct at the top level


(comment
  (defmacro loop-over-disjuncts [rexpr & args]
    (let [flags (into #{} (filter keyword? args))
          rexpr-var (gensym 'rexpr)
          argument-var (first (filter symbol? args))
          create-disjunction (contains? flags :create-disjunct)
          create-disjunct-var (gensym)
          full-binding (contains? flags :full-grounding)

          binding-body `(do ~@(drop 1 (filter #(not (keyword? %)) args)))
          cb-fun (cond create-disjunction `(fn [])
                       )
          ]
      (assert (not (and create-disjunction full-binding)))
      (cond full-binding `(let [~rexpr-var ~rexpr
                                needed-vars# (exposed-variables ~rexpr-var)
                                iterators ]))

      `(let [~rexpr-var ~rexpr]
         ~(cond full-binding)


         (let [~argument-var ~rexpr-var]
           ))
      )))
