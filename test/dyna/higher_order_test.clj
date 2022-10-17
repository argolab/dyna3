(ns dyna.higher-order-test
  (:require [clojure.test :refer :all])
  (:require [dyna.core])
  (:require [dyna.simple-test :refer [str-test]]))


(str-test unification-type "
a += X=&f(Z), X=&g(W), 1.  % should unify to nothing,
a += 0.

%debug_repl a.

assert a = 0.
")


(str-test lessthan-combine "
a := 1.
a := 0 for A < B, B < A.

assert a = 1.
")

(str-test unification-partial-args "
a += X=&f(1,Z), X=&f(Y,2), Z+Y.

assert a = 3.
")

(str-test combine-range "
a += X for X >= 0, X < 10, int(X).

assert a = 45.")
