;; this file is a public interface to the dyna runtime.  Assuming that someone
;; is not using the repl (defined in repl.clj), then we should be able to assume
;; that all interaction with the system will run through this interface

(ns dyna.public-interface
  (:require [dyna.core])
  (:require [dyna.utils :refer :all])
  (:require [dyna.system :as system])
  (:require [dyna.base-protocols :refer [get-value-in-context is-empty-rexpr?]])
  (:require [dyna.rexpr :refer [construct-rexpr make-variable]])
  (:require [dyna.ast-to-rexpr :refer [import-file-url
                                       eval-string]])
  (:import [dyna DynaInterface]))


(defmacro maybe-sys [sys & body]
  `(if (nil? ~sys)
     (do ~@body)
     (system/run-under-system ~sys ~@body)))

(defn run-string [sys prog external-values]
  (maybe-sys sys
             (binding [system/parser-external-value (fn [index]
                                                      (get external-values index))]
               (eval-string prog))))

(defn run-file [sys prog]
  (maybe-sys sys
             (import-file-url prog)))

(defn run-query [sys query external-values]
  (let [query-result (volatile! {})]
    (maybe-sys sys
               (binding [system/parser-external-value (fn [index]
                                                        (get external-values index))
                         system/query-output (fn [[dyna-code line-number] result-info]
                                               (let [val (get-value-in-context (make-variable "$query_result_var") (:context result-info))]
                                                 (vswap! query-result assoc line-number val)))]
                 ;; any queries made when evaluating the string are going to be passed to the query-output function
                 (eval-string query)
                 ;; convert the results of the different queries to a java Object array
                 (into-array Object (for [k (sort (keys @query-result))]
                                      (get @query-result k)))))))

(defn make-rexpr [name args] ;; name is a string, and args should be an array of arguments which are passed into the R-expr
  (apply construct-rexpr name args))

(defn create-system []
  (system/make-new-dyna-system))
