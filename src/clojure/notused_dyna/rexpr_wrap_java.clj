(ns dyna.rexpr-wrap-java
  (:require [dyna.rexpr :refer :all])
  )

(assert false) ;; this is not used the $clojure builtin could be used instead
;; when calling something from java?  Though might still be nicer if there was
;; something specific to java?

;; would be nice if there were some operations which wrapped java operations.
;; That way there could be some ability to have callouts to matrix libraries or
;; other useful libraries.  One issue is that dyna is potentially running things
;; out of order, and something which gets its arguments read is going to try and
;; run.  So how will this

(defrecord DynaWrappedJavaObject [obj])


(def-base-rexpr java-new-instance [:var out
                                   :var string-class-name
                                   :var arguments])

(def-base-rexpr java-call-method [:var out
                                  :var method-name
                                  :var this-object
                                  :var arguments])

;; if the type of some expression is known, then it does not have to use reflection to perform the call, so it would be better with it handling some
;; of the different expressions.

;; (def-base-rexpr java-call-type [:out])


;; would be nice if there was some way of passing around opaque python objects
;; in the dyna runtime also.  That would be nice for interface with python,
;; though that makes things a bit more annowing

;; if there are some expressions which correspond with



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; could do something like a `$clojure_eval(A,B,C)'{ (+ A B C) }`
;; Where A, B, C would become bindings to the variables.  The result of this expression would
