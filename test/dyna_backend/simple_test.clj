(ns dyna-backend.simple-test
  (:require [clojure.test :refer :all])
  (:require [dyna-backend.core])
  (:require [dyna-backend.ast-to-rexpr :refer [eval-string]]))

(deftest basic-assert-test
  (eval-string "assert 1 = 1.")
  (is true)
  (try (do
         (eval-string "assert 1 = 0.") ;; this should fail
         (is false))
       (catch RuntimeException e
         (is (not= -1 (.indexOf (.toString e) "assert on line "))))))


(deftest simple-math
  (eval-string "assert 1 + 2 * 3 = 7."))
