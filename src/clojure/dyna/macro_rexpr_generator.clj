(ns dyna.macro-rexpr-generator
  (:require [dyna.rexpr :refer :all]))

;; genreate macro R-exprs which are compositions of many smaller R-exprs this
;; could be used in the case that an expression appears mutliple times when
;; stored in a memo table.  and also can be a prerequisit for when we are going
;; to JIT compile something.  Where the JIT compilation step would just be
;; generating an optimized rewrite for one of these expressions.

(def-base-rexpr rexpr-placeholder [:str name
                                   :var-list arguments])

(defn generate-macro-rexpr [rexpr generated-name]
  (let [variables (sort (vec (into #{} (exposed-variables rexpr))))
        nested-rexprs (transient #{})]
    (rewrite-rexpr-children-no-simp rexpr (fn rrf [r] (if (is-rexpr-placeholder? r)
                                                        (conj! nested-rexprs r)
                                                        (rewrite-rexpr-children-no-simp r rrf))))

    `(do
       (def-base-rexpr ~generated-name ~(conj (vec (for [v variables] `[:var ~(gensym)]))
                                              (vec (for [r nested-rexprs] `[:rexpr ~(gensym)])))
         (primitive-rexpr [this]
                          ;; this needs to return
                          (???))
         )
       (def-rewrite
         :match ~existing-rexpr

         :gc-able ~generated-name ;; something such that it knows that this R-expr can be deleted when the name is also deleted
         :run-at :compress-rexpr  ;; there needs to be some point where the R-expr is "optimized" into a smaller R-expr.  This is likely going to be an "expensive" operation, and this is different from running with the infers, as this is not creating a new R-expr

         (~(symbol (str "make-" ~generated-name))
          ~@(for [v variables]
              the-name-of-the-variable)
          ~@(for [r nested-rexprs]
              the-name-of-the-rexpr)
          ))

       ;; something that is able to convert the R-expr back into its origional basic form
       ;; if there is nothing which is represented, then it would have some of the expression
       (def-rewrite
         :match (~generated-name ~@(for [v variables] '_) ~@(for [r nested-rexprs] '_))
         :run-at :decompress-rexpr
         (simplify (primitive-rexpr rexpr)))

       )))


;; how is this going to decided when it should "compress/decompress" I suppose
;; that it could have that there is some expression which corresponds with
;; expression would correspond with a given expression.

;; in the case that the decompression would generate a new R-expr
