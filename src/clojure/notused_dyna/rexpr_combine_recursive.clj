(ns dyna.rexpr-combine-recursive
  (:require [dyna.rexpr :refer :all]))

;; in the case of a recursive function, we should combine the rexprs together
;; and propagate any information such as structured terms and constants.  This
;; will allow for osmething like `list(&int, X)` to be efficient as the `int`
;; part would get propagated as a constant.  This would essentially become a
;; distinct type on the expression.



;; this is going to also want to check a recursive user call for base cases in
;; the case that a new expression is formed.  This is essentially "type
;; checking" for us when it comes to recursive types.
