(ns dyna.rexpr-jit
  (:require [dyna.rexpr :refer :all]))

;; this is going to want to cache the R-expr when there are no arguments which are "variables"
;; so something like multiplicy can be just a constant value


(def ^:dynamic *ground-variables* {}) ;; some binding for the current variales which are ground

(declare get-ground-variables ;; something which
         get-variable

         )
