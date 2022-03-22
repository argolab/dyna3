(ns dyna.simple-test
  (:require [clojure.test :refer :all])
  (:require [dyna.core])
  (:require [dyna.system :refer [make-new-dyna-system run-under-system]])
  (:require [dyna.ast-to-rexpr :refer [eval-string]])
  (:import [dyna DynaUserAssert]))

(deftest basic-assert-test
  (eval-string "assert 1 = 1.")
  (eval-string "assert_fails 1 = 0.")
  (is true)
  (try (do
         (binding [dyna.system/debug-on-assert-fail false]
           (eval-string "assert 1 = 0.")) ;; this should fail, and it will run an assert
         (is false))
       (catch DynaUserAssert e
         (is (not= -1 (.indexOf (.toString e) "Assert "))))))

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

list_length([]) := 0.
list_length([X|Y]) := list_length(Y) + 1.

assert 0 = list_length([]).
assert 1 = list_length([1]).

assert 3 = list_length([1,2,3]).
")


(str-test compiler-expression-export "
:- export foo/1.
:- make_system_term foo/1.

foo(X) = 123.
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

f1(X) = my_macro(X + 1).
f2(X) = my_macro(X + 2).

assert f1(3) = 4.
assert f2(3) = 6.
")


(str-test lessthan-construct  "
a := 1.
a := 0 for A < A.

assert a = 1.
")

(str-test lessthan-combine "
a := 1.
a := 0 for A < B, B < A.

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

(comment)
(str-test dynabase6 "
f(X) = new X { z += 1. }.

a = f(f(f(new {}))).

assert a.z = 3.
")
