(ns dyna.memoization-test
  (:require [dyna.core])
  (:require [dyna.simple-test :refer [str-test]]))


(str-test memoization1 "
foo(1) += 123.
foo(2) += 456.

:- memoize_unk foo/1.

assert foo(1) = 123.
")

(str-test memoization2 "
:- memoize_unk f/1.
f(1) = 1.

assert f(1) = 1.

:- print_memo_table f/1.
")

(str-test memoization3 "
:- memoize_unk f/1.
f(1) = 1.

assert f(1) = 1.
f(2) = 2.

%:- run_agenda.
%:- print_memo_table f/1.

assert f(2) = 2.
")

(str-test factorial "
fact(0) := 1.
fact(N) := fact(N-1)*N for N > 0.

:- memoize_unk fact/1.

assert fact(5) = 120.")


(str-test fibonacci "
:- memoize_unk fib/1.
fib(0) := 0.
fib(1) := 1.
fib(N) := fib(N-2) + fib(N-1) for N > 1.

print fib(3).

print fib(10).

assert fib(10) = 55.

%print fib(100).
%debug_repl X=fib(100), Z = 354224848179261915075.

% if this is not memoized, then this will take too long to run
assert fib(100) = 354224848179261915075.
")

(str-test factorial-null "
:- memoize_null fact/1.
fact(0) := 1.
fact(N) := fact(N-1)*N for N < 4.

:- run_agenda.

%debug_repl fact(2).

assert fact(2) = 2.

:- print_memo_table fact/1.
")


(str-test memoization-v2 "
fact(N) := fact(N-1)*N for N > 0.
fact(0) := 1.


$memo(fact[N:$ground]) = \"unk\".

assert fact(10) = 3628800.
")

;; check that we can have the aggregator not go back and compute negative numbers
(str-test memoization-v2-t2 "
fact(N) := fact(N-1)*N.
fact(0) := 1.


$memo(fact[N:$ground]) = \"unk\".

assert fact(10) = 3628800.
")
