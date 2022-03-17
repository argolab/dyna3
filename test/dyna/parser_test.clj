(ns dyna.parser-test
  (:require [clojure.test :refer :all])
  (:require [dyna.core])
  (:require [dyna.ast-to-rexpr :refer [parse-string]]))


(deftest basic-parser
  (parse-string "foo1 = 123."))

(deftest dynabase-test
  (parse-string "db_baz(X) = Y = 9, { something(W) = W*44. }."))


(deftest call-no-args
  (parse-string "a = matrix()."))

(deftest bracket-pass
  (do
    (parse-string "a = m {}.")
    (parse-string "a = m { foo(X) = baz. }.")
    (parse-string "a = m { 123 -> 456, 789 -> 111, \"another\" -> \"what\" }.")))

(deftest inline-aggregator
  (do
    (parse-string "foo(X) = (min= X;Y).")
    (parse-string "foo2(X,Y) = Func=((Z) min= X,Z ), Func(Y).")))

(deftest dynabase
  (parse-string "a = new {}.")
  (parse-string "
a = new {
f(X) = 123.
}.

v = {f = 123.}.

b = {
c = 3.
}.

f = new(b).

z = foo {
f = 123.
}.

w = f.a.b.c(123,456).e.w(9).
"))
