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
