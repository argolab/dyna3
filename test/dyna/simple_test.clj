(ns dyna.simple-test
  (:require [clojure.test :refer :all])
  (:require [dyna.core])
  (:require [dyna.system :refer [make-new-dyna-system run-under-system]])
  (:require [dyna.ast-to-rexpr :refer [eval-string]])
  (:import [dyna DynaUserAssert DynaUserError]))

(deftest basic-assert-test
  (eval-string "assert 1 = 1.")
  (eval-string "assert_fails 1 = 0.")
  (is true)
  (try (do
         (binding [dyna.utils/debug-on-assert-fail false]
           (eval-string "assert 1 = 0.")) ;; this should fail, and it will run an assert
         (is false))
       (catch DynaUserAssert e
         (is (not= -1 (.indexOf (.toString e) "Assert "))))))

(defn run-string [test-str]
  (try
    (let [sstate (make-new-dyna-system)]
      (run-under-system sstate
                        (eval-string test-str))
      (is true))
    (catch DynaUserAssert e
      (is false (str (.toString e) "\nREXPR: " (.assert_rexpr e))))))

(defmacro str-test [name test-str]
  `(deftest ~name
     (println ~(str "Running test " name))
     (run-string ~test-str)))


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

(str-test simple-list "
f = [1,2,3,4,5].
assert f=[X,Y|Z], X=1, Y=2, Z=[3,4,5].
assert_fails f=[3,2|Y].
")

(str-test list-length "
simple_list_length([]) := 0.
simple_list_length([X]) := 1.

assert 0 = simple_list_length([]).
assert 1 = simple_list_length([1]).

list_length_test([]) := 0.
list_length_test([X|Y]) := list_length_test(Y) + 1.

assert 0 = list_length_test([]).
assert 1 = list_length_test([1]).

assert 3 = list_length_test([1,2,3]).
")

(deftest system-list-length
  (eval-string "assert list_length([1,2,3]) = 3.")
  (try
    (do (eval-string "list_length(X) = 456.")
        (assert false))
    (catch DynaUserError err
      (do
        (assert (.contains (.toString err) "is a system defined term"))))))

(str-test compiler-expression-export "
:- export foo/1.

foo(X) = 123.
:- make_system_term foo/1.
")


(str-test colon-aggregator "
z := 1.
assert z = 1.

z := 2.
assert z = 2.
assert_fails z = 1.

f(X) := 1 for X > 0.

assert f(1) = 1.
assert_fail _ is f(-1).
")



(str-test concat-list "
concat([X|Y], Z) := [X|concat(Y,Z)].
concat(X, []) := X.
concat([], Y) := Y.

assert concat([1,2,3], []) = [1,2,3].
assert concat([], [1,2,3]) = [1,2,3].
assert_fails concat([1,2,3], []) = [1,2,3,4].

assert concat([1,2,3], [4,5,6]) = [1,2,3,4,5,6].
")


(str-test list-val-inequality "
ineq([X|Y], Z, 2) :- X < Z.
ineq([X|Y], Z, 3) :- X > Z.

rr(A, B) := W for ineq(A, B, W).  %  force the third argument to be the result instead of driving the query

assert ineq([1], 2, 2).
assert_fails ineq([2], 2, 2).
assert ineq([3], 2, 3).

assert rr([1], 2) = 2.
")

(str-test list-copy "
list_copy([], []).
list_copy([A|B], [A|C]) :- list_copy(B, C).

assert list_copy([1,2,3], [1,2,3]).
assert_fail X=[1], Y=[], list_copy(X, Y).
assert_fail X=[1,2,3,4], Y=[1,2,3], list_copy(X, Y).

rr(X) := Y for list_copy(X, Y).
assert rr([1,2,3]) = [1,2,3].
")

(str-test partition-list-test "
partition([], _, [], []).

partition([X|Xs], Pivot, [X|S], B) :-
    partition(Xs, Pivot, S, B) for X < Pivot.

partition([X|Xs], Pivot, S, [X|B]) :-
    partition(Xs, Pivot, S, B) for X >= Pivot.

%%%%%%%%%%%%%%%%%%%

assert partition([], [], Y, Z), Z = [].
assert partition([],0,[],Z).
assert partition([1,2,3], 2, [1], [2,3]).
")


(str-test min-aggregator "
foo(X) min= X.
foo(X) min= 7.

assert foo(1) = 1.
assert foo(10) = 7.

mm(X) max= X.
mm(X) max= 7.

assert mm(10) = 10.
assert mm(1) = 7.
")


(str-test dispose-parser "
:- dispose my_pair(&,&).
my_pair(A, B) = &pair(A, B).

assert my_pair(foo(1), bar(2)) = &pair(&foo(1), &bar(2)).
")



(str-test simple-macro "
:- macro my_macro/1.
my_macro(X) = &'*'(&$constant(2), X).

test(X) = my_macro(X).

assert test(5) = 10.
")

(str-test macro2 "
:- macro my_macro/1.
my_macro(X) := X.
my_macro(`(`X + 2)) := `(`X + 3).

f1(W) = my_macro(W + 1).
f2(W) = my_macro(W + 2).

assert f1(3) = 4.
assert f2(3) = 6.
")


(str-test lessthan-construct  "
a := 1.
a := 0 for A < A.

assert a = 1.
")


(str-test map-type "
m = {\"A\" -> 123, \"B\" -> 456}.

get_a({\"A\" -> X | _}) = X.
assert get_a(m) = 123.

get_b({B | _}) = B.
assert get_b(m) = 456.

get_c({C | _}) = C.
assert get_c({\"C\" -> 789 | m}) = 789.
assert get_c({\"C\" -> 333}) = 333.

")


(str-test dynabase1 "
dbase = {
a = 123.
b = 456.
}.

assert dbase.a = 123.
assert dbase.b = 456.
")

(str-test dynabase2 "
f(X) = {
z = X*2.
}.

baz = f(10).

assert baz.z = 20.
assert f(3).z = 6.
")

(str-test dynabase3 "
a = {
z += 1.
}.

b = new a {
w += 2.
}.

assert b.z = 1.
assert b.w = 2.
assert_fail _ = a.w.
")

(str-test dynabase4 "
a = {z += 1.}.
b = {z += 2.}.
c = new a { z += 3.}.

assert a.z = 1.
assert b.z = 2.
assert c.z = 4.
")

(str-test dynabase5 "
a = {z += 1.}.
b = {z *= 2.}.

assert a.z = 1.
assert b.z = 2.
")

(str-test dynabase6 "
f(X) = new X { z += 1. }.

a = f(f(f(new {}))).

assert a.z = 3.
")

(str-test dynabase-indirect "
f(X) = {
g(Y) = X + Y.
}.

a = &f(5).g.

assert (a)(6) = 11.
")


(str-test clojure-eval "
f(X) = $clojure'{
  (+ X 2)
}.

assert f(4) = 6.
")

(str-test reflect1 "
r(X) = $reflect(X, \"foo\", [Y]), Y.

print r(&foo(77)).

%assert r(&foo(77)) = 77.
")


(str-test reflect2 "
r(&foo(X)) = X.

assert $reflect(S, \"foo\", [77]), r(S) = 77.
")

(comment
  (str-test reflect3 "
r(X) := 0.
r(&foo(X,Y,Z)) := 1.

assert $reflect(S, $nil, \"baz\", 2, Arr), r(S) = 0.  % this should be able to resolve this using the name and arity

"))


(str-test call-indirect1 "
foo(X,Y) = X + Y.

assert F=&foo(1), F(2) = 3.
")

(comment
 (str-test call-indirect2 "
foo(1, 2).

r(Z) := Z. % used to make sure we don't unify \"backwards\"

assert F=&foo(X), F(Y), r(X) = 1.

"))


(comment
  (str-test with-key "
f([]) max= 123 arg 456.

assert $arg(f([])) = 456.
assert f([]) = 123.
"))

(str-test ref-self-term "
f(X) = *.

assert f(1) = f(1).
")


(str-test random-gen "
print random.
")


(str-test aggregator-sum-many "
f(1) += 1.
f(1) += 2.
f(1) += 3.
f(2) += 4.
f(2) += 5.
f(2) += 6.

assert f(1) = 6.
")


(str-test aggregator-range "
a += X: range(0,10).
%print a.
assert a = 45.  % 0 + . . . + 9 = 45
")
