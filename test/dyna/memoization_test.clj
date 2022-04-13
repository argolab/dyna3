(ns dyna.memoization-test
  (:require [dyna.simple-test :refer [str-test]]))

(str-test memoization1 "
foo(1) += 123.
foo(2) += 456.

:- memoize_unk foo/1.

assert foo(1) = 123.
")
