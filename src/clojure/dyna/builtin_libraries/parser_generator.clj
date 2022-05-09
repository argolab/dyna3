(ns dyna.builtin-libraries.parser-generator
  (:require [instaparse.core :as insta])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.rexpr :refer :all])
  (:require [dyna.user-defined-terms :refer [def-user-term]])
  (:import [dyna DynaTerm]))

;; could use something like https://github.com/Engelberg/instaparse which would
;; allow for generating a parser on the fly from a string which defines the
;; rules.  This would make it easy to define little DSLs in dyna by including
;; that as something.
;; being able to evaluate an expression



(def-base-rexpr instaparse-construct-parser [:var grammar
                                             :var out])

(def-base-rexpr instaparse-run-parser [:var parser
                                       :var input
                                       :var out])

(def-rewrite
  :match (instaparse-construct-parser (:ground grammar) (:any out))
  (let [g (get-value grammar)]
    (if-not (string? g)
      (make-multiplicity 0)
      (make-unify out (make-constant {:instaparse-parser (insta/parser g)})))))

(defn convert-to-dyna [ast]
  (if (vector? ast)
    (DynaTerm. (.toLowerCase ^String (name (first ast))) (vec (map convert-to-dyna (rest ast))))
    ast))

(def-rewrite
  :match (instaparse-run-parser (:ground parser) (:ground input) (:any out))
  (let [parser (:instaparse-parser (get-value parser))
        in (get-value input)]
    (if (or (nil? parser) (not (string? in)))
      (make-multiplicity 0)
      (make-unify out (make-constant (convert-to-dyna (parser in)))))))

(def-user-term "$$__instaparse_construct_parser" 1 (make-instaparse-construct-parser v0 v1))
(def-user-term "$$__instaparse_run_parser" 2 (make-instaparse-run-parser v0 v1 v2))

(println "loaded parser generator clojure file")
