(ns dyna.memoization
  (:require [dyna.core])
  (:require [dyna.utils :refer :all])
  (:require [dyna.rexpr :refer :all]))

;; this is going to have to have some way in which the expression can be updated
;; in the case that the assumption is updated, then it would have that there are
;; some expressions which are represented with
(comment
  (def-base-rexpr memoizd-rexpr [:rexpr R
                                 :rexpr origional
                                 :unchecked assumption]))
