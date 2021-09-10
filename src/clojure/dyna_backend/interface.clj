(ns dyna-backend.interface
  (:require [dyna-backend.core])
  (:require [dyna-backend.rexpr :refer :all])
  (:require [dyna-backend.system :as system])
  (:require [dyna-backend.assumptions :as assumptions])
  )

(gen-class
  :name "dyna_backend.DynaInterfaceImpl"
  :prefix "-"
  :implements [dyna_backend.DynaInterface]
  ;; :methods [[make_rexpr [String "[Ljava.lang.Object;"] Object]
  ;;           [make_variable [String] Object]
  ;;           [make_constant [Object] Object]
  ;;           [simplify [Object] Object]
  ;;           [parse_program [String] void]
  ;;           [parse_program_file [String] void]]
  )

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


(defn set-user-expression [name rexpr]
  (swap! system/user-defined-expressions
         (fn [prev]
           (let [pv (get prev name)]
             (if (not (nil? pv))
               (assumptions/invalidate! pv))
             (assert false) ; the assumption that is made needs to be newly constructed
             ; when the assumption is read from something, this will have
             (assoc prev name (assumptions/make-assumption-wrapper rexpr)))))
  )

(defn add-to-user-expression [name rexpr]
  ;; this should add an expression to an aggregator
  (swap! system/user-defined-expressions
         (fn [prev]
           (let [pv (get prev name)]
             (if (nil? pv)
               (assoc prev name rexpr)
               (do
                 ;; this needs determine if the aggregator is the same, and then combine the expressions together
                 (assert false)
                 )
               ))
           ))
  )


(defn make-query [this rexpr]
  ;; return the R-expr which represents this as a query if we assume that this
  ;; is from the java interface, then there should be some wrapper which
  ;; represents that this is going to have
  )


(defn -parse_program [this ^String text]
  )

(defn -parse_program_file [this ^String filename]
  )
