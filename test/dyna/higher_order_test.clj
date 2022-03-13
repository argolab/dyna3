(ns dyna.higher-order-test
  (:require [clojure.test :refer :all])
  (:require [dyna.core])
  (:require [dyna.simple-test :refer [str-test]]))


(str-test unification-type "
a += X=&f(Z), X=&g(W), 1.  % should unify to nothing,
a += 0.

debug_repl a.

assert a = 0.
")
