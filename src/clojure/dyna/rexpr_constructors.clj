(ns dyna.rexpr-constructors)

(defmacro declare-rexprs [& x]
  `(declare ~@(for [z x] (symbol (str "make-" z)))
            ~@(for [z x] (symbol (str "make-no-simp-" z)))
            ~@(for [z x] (symbol (str "is-" z "?")))
            ))

;; the implementation is in rexpr.clj.  This file just exists so that we can
;; reference the methods which construct the R-expr before clojure has loaded in
;; the impementation of the methods

(declare-rexprs
 multiplicity
 conjunct
 disjunct
 unify
 unify-structure
 unify-structure-get-meta
 proj
 aggregator
 if
 user-call
 )

(declare make-variable
         is-variable?
         is-variable-set?
         make-constant
         is-constant?)
