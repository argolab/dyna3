(ns dyna.core
  (:require [aprint.core :refer [aprint]])
  (:require [clojure.tools.namespace.repl :refer [refresh]])
  (:require [clj-java-decompiler.core :refer [decompile]])
  (:require [clojure.java.io :refer [resource]])

  (:require [dyna.utils :refer :all])
  (:require [dyna.rexpr :refer :all])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.rexpr-builtins :refer :all])
  (:require [dyna.context :as context])
  (:require [dyna.aggregators])
  (:require [dyna.rexpr-dynabase])
  (:require [dyna.ast-to-rexpr :refer [parse-string
                                       import-file-url
                                       eval-string
                                       eval-ast]])

  (:require [dyna.repl :refer [repl]])
  (:import [dyna DynaTerm]))


(defn main [args]
  ;; (println args)

  ;; load the prelude file into the runtime before we start loading stuff
  ;;(import-file-url (resource "dyna/prelude.dyna"))

  (loop [i 0]
    (when (< i (count args))
      ;; the command line arguments can just be special shortcuts for commands that could have been run via the repl
      (case (get args i)
        "--import" (let [fname (get args (+ i 1))]
                     (println "importing file " fname)
                     (eval-ast (make-term ("$compiler_expression" ("import" fname))))
                     (recur (+ i 2)))
        "--csv-import" (let [term (get args (+ i 1))
                             file-name (get args (+ i 2))
                             [_ term-name term-arity] (re-matches #"(.+)/([0-9]+)" term)]
                         (if (nil? term-name)
                           (print "csv-import did not match the expected argument")
                           (assert false))
                         (eval-ast (make-term ("$compiler_expression" ("import_csv" term-name (int term-arity) file-name))))
                         (recur (+ i 3)))
        "--csv-export" (let [term (get args (+ i 1))
                             file-name (get args (+ i 2))
                             [_ term-name term-arity] (re-matches #"(.+)/([0-9]+)" term)]
                         (eval-ast (make-term ("$compiler_expression" ("save_csv" term-name (int term-arity) file-name))))
                         (recur (+ i 3)))
        (println "argument ???" (get args i)))))

  ;; (eval-ast (make-term ("$define_term" ("$command_line_args") DynaTerm/null_term "=" ("$constant" (DynaTerm/make_list args)))))
  ;; (eval-ast (make-term ("$compiler_expression" ("make_system_term" "$command_line_args" 0))))

  ;; (println "math mode" *unchecked-math*)
  (repl)
  (println "this is the main function for dyna"))

(defn main2 [& args]
  (main (vec args)))
