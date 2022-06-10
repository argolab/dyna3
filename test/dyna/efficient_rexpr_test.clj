(ns dyna.efficient-rexpr-test
  (:require [clojure.test :refer :all])
  (:require [dyna.core])
  (:require [dyna.rexpr-disjunction])
  (:require [dyna.system :as system])
  (:require [dyna.simple-test :refer [run-string str-test]]))

(deftest make-disjunct
  (binding [system/*use-optimized-rexprs* true]
    (run-string "
f(1) = 2.
f(2) = 3.
f(3) = 4.

assert f(1) = 2.
")))

(deftest make-disjunct2
  (binding [system/*use-optimized-rexprs* true]
    (run-string "
f(X) += 1.
f(X) += X.

r(X) = X.

assert r(f(5)) = 6.
")))


(deftest make-disjunct3
  (binding [system/*use-optimized-rexprs* true]
    (run-string "
f(0,0) = 1.
f(0,1) = 2.
f(1,0) = 3.
f(1,1) = 4.

a(X,Y) += f(X,Z) * f(Z,Y).

b += a(X,1).

print b.

")))
