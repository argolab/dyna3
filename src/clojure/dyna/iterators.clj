(ns dyna.iterators
  (:require [dyna.utils :refer :all])
  (:require [dyna.base-protocols :refer :all])
  (:require [clojure.set :refer [union intersection]]))

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


;; (deftype union-iterator [iter1 iter2]
;;   ())

;; (deftype unit-iterator [variable value]
;;   DIterator

;;   )

(defn make-unit-iterator [variable value]
  #{(reify DIterable
      (iter-what-variables-bound [this] #{variable})
      (iter-variable-binding-order [this] [[variable]]) ;; could do something like {#{} #{variable}}
      (iter-create-iterator [this which-binding] (reify DIterator
                                                   (iter-run-cb [this cb-fun] (cb-fun {variable value}))
                                                   (iter-has-next [this] false)))
      Object
      (toString [this] (str "(unit-iterator " variable " " value ")")))})


(defn make-disjunct-iterator [branches]
  (let [branch-variables (vec (map (fn [b] (apply union (map iter-what-variables-bound b)))
                                   branches))
        all-variable-bindable (apply intersection branch-variables)
        ret (into #{} (for [var all-variable-bindable]
                        (reify DIterable
                          (iter-what-variables-bound [this] #{var})
                          (iter-variable-binding-order [this] [[var]])
                          (iter-create-iterator [this which-binding] (reify DIterator
                                                                       (iter-run-cb [this cb-fun]
                                                                         ;; this has to run the first iterator and record what values are contained
                                                                         ;; and then run the second iterator without duplicating the result
                                                                         (let [values-seen (transient #{})]
                                                                           (doseq [b branches]
                                                                             (let [itr (filter #(contains? (iter-what-variables-bound %) var) b)]
                                                                               (debug-repl "inside constructing union iterator")
                                                                               (???)))))
                                                                       (iter-has-next [this] false))))
                        ))
        ]
    ;; I suppose that this can just do this a single variable at a time for the
    ;; start?  Though when there are chains of variables which can
    ;; become bound, that becomes more complicated.  This
    ret))


(defmacro run-iterator [iterators binding-variables & body]
  `(let [iterators# ~iterators
         binding-variables# ~binding-variables ;; should this require that all of the variables here are bound, or is it fine if the values are
         result (volatile! nil)]
     (iter-run-cb)
     ))



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
