(ns dyna.memoization
  (:require [dyna.core])
  (:require [dyna.utils :refer :all])
  (:require [dyna.rexpr :refer :all]))

;; this is going to have to have some way in which the expression can be updated
;; in the case that the assumption is updated, then it would have that there are
;; some expressions which are represented with
(comment
  (def-base-rexpr memoized-rexpr [:rexpr Rmemo ;; the R-expr which contains the memoized
                                  :rexpr Rorig
                                  :unchecked assumption])


  (def-rewrite
    :match memoized-rexpr (:rexpr Rmemo) (:rexpr Rorig))

  )
