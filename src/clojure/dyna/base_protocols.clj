(ns dyna.base-protocols
  (:require [dyna.utils :refer [import-interface-methods]])
  (:import [dyna DIterable DIterator DIteratorInstance Dynabase]))

;; this file defines the base protocols (interfaces) which are referenced
;; throughout the rest of the project in different files.  The implementations
;; for these methods are scattered around

(defprotocol Rexpr
  (primitive-rexpr [this]) ;; return a primitive r-expr for the expression
  ;;(replace-expressions [this expressions-map]) ;; replace a given nested expression
  (get-variables [this])  ;; get the variables from the current rexpr
  (get-children [this])
  (get-argument [this n])
  (get-argument-name [this name])
  (get-arguments [this])
  (as-list [this]) ; use for printing out the structure

  (exposed-variables [this])        ; return variables values that are exposed externally (so hide aggregators and proj)
  (get-all-variables-rec [this])

  ;; these functions can recursivy walk the R-expr and rewmap the different variables which appear
  ;; if there is something that


  (remap-variables [this variable-renaming-map])
  (rewrite-rexpr-children [this remap-function])
  (rewrite-rexpr-children-no-simp [this remap-function])
  (remap-variables-func [this remap-function])

  ;; in the case of hidden variables, those re something which need to get added to the map when it recurses through
  (remap-variables-handle-hidden [this variable-renaming-map])

  ;; meaning that the multiplicity of this expression will be at most 1.  allows
  ;; for other additional rewrites to be applied to this expression
  (is-constraint? [this])

  ;; return the name of this type of R-expr as a string, can be used by external
  ;; code.  internally it is more efficient to use match or is-X? for matching
  ;; against the type of R-expr
  (rexpr-name [this])

  (is-empty-rexpr? [this]) ;; if the multiplicity of this expression is zero
  (is-non-empty-rexpr? [this]) ;; if there is some branch of the disjunct which is non-zero

  ;; return a map of the internal values which are stored, and it .
                                        ;(get-arguments-map [this])

  (rexpr-map-function-with-access-path [this cb-fn])

  (all-conjunctive-rexprs [this]
    ;; return [set-of-projected-out-variables, The rexpr]
    )

  (rexpr-jit-info [this])
  )

  ;; (visit-rexpr-children [this remap-function]) ;; this will visit any nested R-exprs on the expression, and return a new expression of the same type with
  ;(visit-all-children [this remap-function]) ;; this will visit



;; should change this to an interface...
(defprotocol RexprValue
  (get-value [this])
  (get-value-in-context [this ctx])
  (get-representation-in-context [this ctx])
  (set-value! [this value])
  (is-bound? [this])
  (is-bound-in-context? [this ctx])
  (all-variables [this]))


(defprotocol RContext
  (ctx-get-rexpr [this])
  (ctx-get-value [this variable])
  (ctx-is-bound? [this variable])
  (ctx-set-value! [this variable value])
  (ctx-add-rexpr! [this rexpr])
  (ctx-add-context! [this other-context])
  (ctx-all-rexprs [this])
  (ctx-exit-context [this resulting-rexpr])
  ;(construct-context-rexpr [this])
  (ctx-intersect [this other])
  (ctx-subtract [this other])

  (ctx-scan-through-conjuncts [this scan-fn])
  (ctx-contains-rexpr? [this rexpr])

  ;; for debugging
  (ctx-get-inner-values [this])
  (ctx-get-all-bindings [this])

  (ctx-get-value-map-upto-context [this parent-context])
  )



;; (defrecord Dynabase [access-map]
;;   Object
;;   (toString [this]
;;     (str "(Dynabase " access-map ")")))

(def undefined-dynabase (Dynabase. nil))

;(import-interface-methods)


(import-interface-methods DIterable)
#_(defprotocol DIterable
  (iter-what-variables-bound [this])
  (iter-variable-binding-order [this])

  (iter-create-iterator [this which-binding]))

(import-interface-methods DIterator)

;; should this also
#_(defprotocol DIterator
  (iter-run-cb [this ^clojure.lang.IFn cb-fun]) ;; call back the function with the value
  (iter-run-iterable [this]) ;; return an iterable (possibly a lazy seq) for the different bindings
  ;;(iter-has-next [this])
  (iter-bind-value [this value]) ;; return DIteratorInstance
  (iter-debug-which-variable-bound [this]) ;; which variable is bound by this iterator
  (iter-estimate-cardinality [this])) ;; estimate the number of values which will get bound by this iterator


(import-interface-methods DIteratorInstance)
#_(defprotocol DIteratorInstance
  (iter-variable-value [this]) ;; return Object which corresponds with the value from the iterator
  (iter-continuation [this])) ;; return an DIterator which is the next iterator


(def iterator-empty-instance
  (reify DIterator
    (iter-run-cb [this cb-fun])
    (iter-bind-value [this value]
      (throw (RuntimeException. "nothing to bind a value to")))
    (iter-debug-which-variable-bound [this] nil)))


(comment
  (defsimpleinterface DIterable
    (iter-what-variables-bound []) ;; return a set of which variables can be bound
    (iter-variable-binding-order []) ;; return a list of lists, where the second list represents which order the variables will get bound in

    ;; maybe this should instead select which option it will be going for

    (iter-create-iterator [which-binding])) ;; create an iterator which can do the binding of different variables


  (defsimpleinterface DIterator
    (iter-run-cb [^clojure.lang.IFn cb-fun]) ;; the function will get passed the value

    (iter-bind-value [value]))


  ;; this can just be a seq in clojure
  (defsimpleinterface DIteratorVariable
    (^boolean iter-has-next [])
    (iter-next []))


  ;; this could just be returned as a pair.  It does not have to be its own class?
  (defsimpleinterface DIteratorInstance
    (iter-variable-value []) ;; return the value for which an expression has been bound
    (iter-continuation []))) ;; return the next iterator in the sequence of binding multiple values




;; (defrecord MemoizationContainer [RConditional
;;                                  Rmemo
;;                                  Rorig
;;                                  assumption])
