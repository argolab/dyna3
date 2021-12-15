(ns dyna.simple-test
  (:require [clojure.test :refer :all])
  (:require [dyna.core])
  (:require [dyna.system :refer [make-new-dyna-system run-under-system]])
  (:require [dyna.ast-to-rexpr :refer [eval-string]])
  (:import [dyna DynaUserAssert]))

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
       (let [sstate# (make-new-dyna-system)]
         (run-under-system sstate#
          (eval-string ~str))
         (is true))
       (catch DynaUserAssert e#
         (is false (str (.toString e#) "\nREXPR: " (.assert_rexpr e#)))))))


(str-test simple-math
          "assert 1 + 2 * 3 = 7.")


(str-test define-function "
def_fun1(X, Y, Z) = X + Y * Z.
assert def_fun1(1,2,3) = 7.
")

(str-test simple-disjunct "
def_fun2(1) = 11.
def_fun2(2) = 22.
assert def_fun2(1) = 11.
assert def_fun2(2) = 22.
")


(str-test simple-aggregator "
def_agg(1) += 11.
def_agg(1) += 11.
def_agg(2) += 33.
assert def_agg(1) = 22.
assert def_agg(2) = 33.
")

(str-test factorial-program "
fact(1) = 1.
fact(N) = fact(N-1)*N for N > 1.

assert fact(1) = 1.

%print fact(1).
%print fact(2).
%print fact(3).

assert fact(2) = 2.
assert fact(3) = 6.
")

(str-test fib-program "
fib(0) = 0.
fib(1) = 1.
fib(X) = fib(X-1) + fib(X-2) for X > 1.

assert fib(2) = 1.
assert_fails fib(2) = 10.
assert fib(5) = 5.
")

(str-test structure-unification "
foo = &f(1,2).
assert foo = &f(X,Y), X = 1, Y > 1.
assert_fails foo = &f(X, Y), Y < 1.
")
