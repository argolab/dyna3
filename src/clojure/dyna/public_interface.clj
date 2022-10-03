;; this file is a public interface to the dyna runtime.  Assuming that someone
;; is not using the repl (defined in repl.clj), then we should be able to assume
;; that all interaction with the system will run through this interface

(ns dyna.public-interface
  (:require [dyna.core])
  (:require [dyna.utils :refer :all])
  (:require [dyna.system :as system])
  (:require [dyna.base-protocols :refer [is-bound-in-context? get-value-in-context is-empty-rexpr?]])
  (:require [dyna.rexpr :refer [construct-rexpr make-variable make-function-call]])
  (:require [dyna.ast-to-rexpr :refer [import-file-url
                                       eval-string
                                       eval-ast
                                       current-dir]])
  (:require [dyna.user-defined-terms :refer [add-to-user-term]])
  (:import [dyna DynaInterface ExternalFunction DynaTerm]))


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
                                               (let [ctx (:context result-info)
                                                     qv (make-variable "$query_result_var")
                                                     val (if (is-bound-in-context? qv ctx)
                                                           (get-value-in-context qv ctx)
                                                           (:rexpr result-info))]
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

(defn define-external-function [sys ^String name arity ^ExternalFunction func]
  (maybe-sys sys
             (assert (and (string? name) (int? arity)))
             (let [vars (vec (for [i (range arity)]
                               (make-variable (str "$" i))))
                   out (make-variable (str "$" arity))
                   ff (fn [& args]
                        (.call func (into-array Object args)))
                   rexpr (make-function-call ff out vars)]

               (add-to-user-term current-dir DynaTerm/null_term name arity rexpr)
               (eval-ast (make-term ("$compiler_expression" ("make_system_term" ("/" name arity))))))))
