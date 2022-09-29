(ns dyna.efficient-rexpr-test
  (:require [clojure.test :refer :all])
  (:require [dyna.utils :refer [debug-repl]])
  (:require [dyna.core])
  (:require [dyna.base-protocols :refer [is-empty-rexpr? is-non-empty-rexpr?]])
  (:require [dyna.rexpr :refer [make-disjunct make-multiplicity make-unify make-variable make-constant make-conjunct make-proj-many make-aggregator simplify]])
  (:require [dyna.rexpr-builtins :refer [make-times make-range]])
  (:require [dyna.rexpr-disjunction :refer [is-disjunct-op?]])
  (:require [dyna.rexpr-aggregators-optimized :refer [is-aggregator-op-outer?]])
  (:require [dyna.system :as system])
  (:require [dyna.context :as context])
  (:require [dyna.simple-test :refer [run-string str-test]]))

(deftest make-disjunct1
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

c += f(X,Y).

%print c.
assert c = 10.

%print a(0,0).

assert a(0,0) = 1 + 2*3.
assert a(1,0) = 3 + 4*3.

b += a(X,0).

assert b = 22. %1 + 2*3 + 3 + 4*3.
%print b.
")))


(deftest disjunct-op-empty
  (binding [system/*use-optimized-rexprs* true]
    (let [r (make-disjunct [(make-multiplicity 1) (make-unify (make-variable 'a) (make-constant 1))])]
      (is (is-disjunct-op? r))
      (is (is-non-empty-rexpr? r))
      (is (not (is-empty-rexpr? r))))))


(deftest efficient-aggregator1
  (binding [system/*use-optimized-rexprs* true]
    (let [r (make-aggregator "+=" (make-variable 'result) (make-variable 'incoming) true
                             (make-disjunct [(make-proj-many [(make-variable 'A)] (make-conjunct [(make-range (make-constant 0) (make-constant 10) (make-constant 1) (make-variable 'A) (make-constant true))
                                                                                                  (make-times (make-variable 'A) (make-constant 7) (make-variable 'incoming))]))

                                             (make-proj-many [(make-variable 'A)] (make-conjunct [(make-range (make-constant 20) (make-constant 30) (make-constant 1) (make-variable 'A) (make-constant true))
                                                                                                  (make-times (make-variable 'A) (make-constant 13) (make-variable 'incoming))]))
                                             ]))]
      (is (is-aggregator-op-outer? r))
      (let [ctx (context/make-empty-context r)
            res (context/bind-context-raw ctx (simplify r))]
        (debug-repl "drtest")


        ))))
