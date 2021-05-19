;; this file will contain _optimized_ R-expresion that we included this should
;; be something like a table (prefix-trie) representation which is able to store
;; multiple values at the same time

;; there is also an optimized version of the aggregator that should be
;; implemeneted.  Something which allows for an expression to be solved using
;; loops over the domains of variables rather than having to perform lots of
;; rewrites in the process

(ns dyna-backend.rexpr
  (:require [dyna-backend.utils :refer :all]))

(in-ns 'dyna-backend.rexpr)
