(ns dyna-backend.interface
  (:require [dyna-backend.core])
  (:require [dyna-backend.rexpr :refer :all])
  )

(gen-class
  :name "dyna_backend.DynaInterface"
  :prefix "-"
  :methods [[make_rexpr [String "[Ljava.lang.Object;"] Object]
            [make_variable [String] Object]
            [make_constant [Object] Object]
            [simplify [Object] Object]])

;; this is such a hack using resolve to avoid the ahead of time operation for resolving these symbols
;; would be better to maybe define local variables which reference these functions, and then just call those
(defn -make_rexpr [this ^String name args]
  (apply construct-rexpr name args))

(defn -make_variable [this ^String name]
  (make-variable name))

(defn -make_constant [this ^String value]
  (make-constant value))


;; there needs to be simplification methods as well as methods for dealing with the context
;; though we might just make it such that the context is an implementation detail that
;; gets embedded into the rexpr such that simplify that is exposed to the python program does not have
;; the ability to access this information

(defn -simplify [this rexpr]
  (simplify rexpr))