(ns dyna-backend.UnificationFailure
  (:gen-class :extends java.lang.RuntimeException))

;; prevent the stack trace for being generated when the exception is created
;; this this makes these exceptions "faster"
(defn -fillInStackTrace ^java.lang.Throwable [this] nil)
