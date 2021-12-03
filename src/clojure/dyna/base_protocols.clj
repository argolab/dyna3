(ns dyna.base-protocols)

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

  ;; these functions can recursivy walk the R-expr and rewmap the different variables which appear
  ;; if there is something that


  (remap-variables [this variable-renaming-map])
  (rewrite-rexpr-children [this remap-function])
  ;; (visit-rexpr-children [this remap-function]) ;; this will visit any nested R-exprs on the expression, and return a new expression of the same type with
  ;(visit-all-children [this remap-function]) ;; this will visit
  )


(defprotocol RexprValue
  (get-value [this])
  (get-value-in-context [this ctx])
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

  ;; for debugging
  (ctx-get-inner-values [this])
  (ctx-get-all-bindings [this]))



(defrecord Dynabase [access-map])

(def undefined-dynabase (Dynabase. nil))
