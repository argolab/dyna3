;; this file is a public interface to the dyna runtime.  Assuming that someone
;; is not using the repl (defined in repl.clj), then we should be able to assume
;; that all interaction with the system will run through this interface

(ns dyna.public-interface
  (:require [dyna.utils :refer :all])
  (:require [dyna.core :refer :all])
  (:require [dyna.system :refer :all])
  (:require [dyna.rexpr :refer :all])
  (:require [dyna.ast-to-rexpr :refer [import-file-url
                                       eval-string]])
  (:import [dyna DynaInterface]))


(defmacro maybe-sys [sys & body]
  `(if (nil? ~sys)
     (do ~@body)
     (run-under-system ~sys ~@body)))

(defn run-string [sys prog external-values]
  (maybe-sys sys
             (binding [system/parser-external-value (fn [index]
                                                      (get external-values index))]
               (eval-string prog))))

(defn run-file [sys prog]
  (maybe-sys sys
             (import-file-url prog)))

(defn run-query [sys query external-values]
  (let [query-result (volatile! [])]
    (maybe-sys sys
               (binding [system/parser-external-value (fn [index]
                                                        (get external-values index))
                         system/query-output (fn [qr]
                                               (vreset! query-result qr))]
                 ;; the query needs to get run and the result will then be returned
                 (???)))))

(defn make-rexpr [name args] ;; name is a string, and args should be an array of arguments which are passed into the R-expr
  (apply construct-rexpr name args))

(defn create-system []
  (make-new-dyna-system))

;; (defn get-backend-interface []
;;   (reify dyna.DynaInterface
;;     (run-string [system program]
;;       (???))
;;     (run-file [system filename]
;;       (???))
;;     (run-query [system query]
;;       (???))
;;     (make-rexpr [name args]
;;       (???))
;;     (make-variable [name]
;;       (???))
;;     (make-constant [value]
;;       (???))
;;     (simplify [system rexpr]
;;       (???))
;;     (get-term-name [^DynaTerm term]
;;       (.name term))
;;     (get-term-arity [^DynaTerm term]
;;       (.arity term))
;;     (get-term-argument [^DynaTerm term arg]
;;       (get term arg))

;;     (create-dyna-system []
;;       (???))))
