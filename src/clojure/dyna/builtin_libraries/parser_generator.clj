(ns dyna.builtin-libraries.parser-generator)

;; could use something like https://github.com/Engelberg/instaparse which would
;; allow for generating a parser on the fly from a string which defines the
;; rules.  This would make it easy to define little DSLs in dyna by including
;; that as something.

;; being able to evaluate an expression


(def generate-parser [Grammar Result]
  ;; this can return an R-expr which corresponds with what the computation is represented as
  (make-unify Result (make-constant true))
  )


;; there should be some make function thing which would allow for it to make a new R-expr which just delays the calling until it has something that it can do
