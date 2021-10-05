(ns dyna.simple-test
  (:require [clojure.test :refer :all])
  (:require [dyna.core])
  (:require [dyna.ast-to-rexpr :refer [eval-string]]))

(deftest basic-assert-test
  (eval-string "assert 1 = 1.")
  (is true)
  (try (do
         (eval-string "assert 1 = 0.") ;; this should fail, and it will run an assert
         (is false))
       (catch RuntimeException e
         (is (not= -1 (.indexOf (.toString e) "assert on line "))))))

(defmacro str-test [name str]
  `(deftest ~name
     (try
       (do (eval-string ~str)
           (is true))
       (catch RuntimeException e#
         (is false (.toString e#))))))


(str-test simple-math
          "assert 1 + 2 * 3 = 7.")


(str-test define-function
"
def_fun1(X, Y, Z) = X + Y * Z.
assert def_fun1(1,2,3) = 7.
")
