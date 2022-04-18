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
       (def-base-rexpr ~generated-name []))
    ))
