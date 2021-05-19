(ns dyna-backend.rexpr
  (:require [dyna-backend.rexpr :refer :all]))

(in-ns 'dyna-backend.rexpr)

(defmacro def-rewrite [& args]

  nil)


(defmacro def-rewrite-matcher [name var & body]
  nil)

;; there should be some matcher which is going to identify which expression.
;; this would have some which expressions are the expressions
;; this is going to have to have some context in which an expression

(def-rewrite-matcher :ground [var-name]
  ;; is-variable-set? is going to have to take
  (if (and (is-variable? var-name) (is-variable-set? var-name))
    (get-variable-value var-name)
    (if (is-constant? var-name)
      (.value var-name))))

(def-rewrite-matcher :free [var-name]
  (and (is-variable? var-name) (not (is-variable-set? var-name)) var-name))

(def-rewrite-matcher :rexpr [rexpr]
  (not (or (is-variable? rexpr) (is-constant? rexpr))))

;; this should either return nil which means that there is no match
;; or this should match which expression has some

(def-rewrite
  :match (if (:rexpr A) (:rexpr B) (:rexpr C)) ;; with the (:match pattern being something that allows it to select the correct matcher for a given expression
  )

;; something that has a name first followed by a number of different unified expressions
(def-rewrite-matcher :structured [rexpr]
  (and (not (is-variable? rexpr))s
       (not (isinstance? Rexpr rexpr))
       (or (list? rexpr) (vector? rexpr))))

(def-rewrite
  :match (unify (:structured A) (:structured B))
  ;; that this should run early, when invoked by the make method call.
  ;; there should be some methods like
  :run-at :construction
  (if (or (not= (count A) (count B)) (not= (car A) (car B)))
    (multiplicity 0) ;; meaning that the names on these expressions does not match.
    ;; return the original rexpr
    rexpr))

(def-rewrite
  ;; the matched variable should have what value is the result of the matched expression.
  :match (unify (:ground A) (:ground B))
  (if (= A B)
    (multiplicity 1)
    (multiplicity 0)))

(def-rewrite
  :match (* :any)  ;; the conjuncts and the disjuncts are going to have to have some expression wihch
)


;; this is something that can be automatically generated in the case that
(def-rewrite
  :match (add (:ground A) (:ground B) (:non-ground C))
  (make-unify C `(+ ~A ~B)))
