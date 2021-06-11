(ns dyna-backend.context
  (:require [dyna-backend.utils :refer :all])
  )


(deftype context
    [^:unsynchronized-mutable rexprs]
  )

(defn make-empty-context [rexpr]
  (???))
