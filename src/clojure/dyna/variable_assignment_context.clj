(ns dyna.variable-assignment-context
  (:require [dyna.rexpr :refer :all]))


;; there should be some representation which allows for the different values
;; to get the contextual info

(def-base-rexpr contextual-info [:unchecked contextual-bindings
                                 :rexpr R])

;(def-rewrite
;  :match (contextual-info (:unchecked LContext) (:rexpr R)))
;
;
;
;
;(comment
;  (def-nesting-rewrite
;    :match (contextual-info (:unchecked LContext) (:rexpr R))))
;
;
;
