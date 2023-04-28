(ns dyna.higher-order-test
  (:require [clojure.test :refer :all])
  (:require [dyna.core])
  (:require [dyna.simple-test :refer [str-test]]))

(deftest dummy) ;; intellij seems to need this to recognize this file

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


(str-test agg-elem-branch-colon "
fact(N) := fact(N-1) * N.
fact(0) := 1.  % if this branch matches, then we can stop processing the other branch which recurses

assert fact(5) = 120.
")


(str-test agg-elem-branch-max "
rec_forever(X) = rec_forever(X).
m(X) max= 0 for rec_forever(X).
m(1) max= 1.  % if this branch matches, then it can figure out that the other branch will not be used.  additionally, having this property will give stuff like alpha-beta pruning \"for free\"

assert m(1) = 1.
")

(str-test alpha-beta-prune "
foo(X) = foo(X). % we can not figure out the value of this because it keeps recursing

maxs max= foo(X).
maxs max= 1.  % we can figure out that the value of this is at least 1

mins min= 0.
mins min= maxs.  % this is going to be greater than the known 0 value

assert mins = 0.
")


(str-test saturated-or "
foo(X) = foo(X).

f |= foo(123).
f |= true.

assert f = true.
")

(str-test saturated-any "
foo(X) = foo(X).

f ?= foo(123).
f ?= 1.

assert f = 1.
")

(str-test type-structure-confict "
f := 1.
f := 0 for X:int = foo[Z].

assert f = 1.")
