(ns dyna.core
  (:require [aprint.core :refer [aprint]])
  (:require [clojure.tools.namespace.repl :refer [refresh]])
  (:require [clj-java-decompiler.core :refer [decompile]])
  (:require [clojure.java.io :refer [resource file]])

  (:require [dyna.system :as system])
  (:require [dyna.utils :refer :all])
  (:require [dyna.rexpr])
  (:require [dyna.rexpr-constructors :refer :all])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.context :as context])
  (:require [dyna.rexpr-builtins])
  (:require [dyna.rexpr-aggregators])
  (:require [dyna.rexpr-dynabase])
  (:require [dyna.rexpr-meta-programming])
  (:require [dyna.memoization-v1])
  (:require [dyna.rexpr-disjunction])
  (:require [dyna.rexpr-aggregators-optimized])
  (:require [dyna.memoization-v2]) ;; requires disjunct opt and aggregators opt

  ;; (:require [dyna.rexpr-jit])
  (:require [dyna.ast-to-rexpr :refer [parse-string
                                       import-file-url
                                       eval-string
                                       eval-ast]])
  (:require [dyna.repl :refer [repl]])
  (:import [dyna DynaTerm StatusCounters]))


(defn init-system []
  ;;(println "----------->>>>>>>>>>>>>>>>>>>>>>>>> init method on current system")
  (import-file-url (resource "dyna/prelude.dyna")))

(defn exit-system []
  ;; there should be something for when the system is going to be destroyed.
  ;; this can run stuff like saving the files?
  )


(init-system)


(defn real-main [args]
  ;(println (vec args))

  ;; load the prelude file into the runtime before we start loading stuff
  ;;(import-file-url (resource "dyna/prelude.dyna"))

  (let [run-file (volatile! nil)
        other-args (transient [])]
    (loop [i 0]
      (when (< i (count args))
        ;; the command line arguments can just be special shortcuts for commands that could have been run via the repl
        (case (get args i)
          "--import" (let [fname (get args (+ i 1))]
                       (println "importing file " fname)
                       ;; this is going to be a file, as we have already checked in the standalone-header
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
                           (eval-ast (make-term ("$compiler_expression" ("export_csv" term-name (int term-arity) file-name))))
                           (recur (+ i 3)))
          "--run" (let [fname (get args (+ i 1))]
                    (when-not (nil? @run-file)
                      (println "the --run argument is specified more than once")
                      (System/exit 1))
                    (vreset! run-file fname)
                    (recur (+ i 2)))
          (do ;; just collect the other arguments into an array
            (conj! other-args (get args i))
            (recur (+ i 1))))))

    (let [other-args (persistent! other-args)]
      (if (or (not (empty? other-args)) (not (nil? @run-file)))
        (let [[run-file args] (if-not (nil? @run-file)
                                 [@run-file other-args]
                                 [(get other-args 0) (vec (drop 1 other-args))])
              run-filef (file run-file)]
          (when-not (.isFile run-filef)
            (println "Unable to find file " run-file " to run")
            (System/exit 1))
          (let [arg-list (DynaTerm/make_list args)]
            ;; define $command_line_args = ["arg1", "arg2", ..., "argN"]
            ;; and make it a global that can be access anywhere
            (eval-ast (make-term (","
                                  ("$define_term" ("$command_line_args") DynaTerm/null_term "=" ("$constant" arg-list))
                                  ("$compiler_expression" ("make_system_term" ("/" "$command_line_args" 0))))))
            (when system/status-counters
              (StatusCounters/program_start))
            (import-file-url (.toURL run-filef))
            ;; TODO: this needs to handle the csv export functions
            (when system/status-counters
              (StatusCounters/print_counters))
            (System/exit 0)))
        (do
          (eval-string "$command_line_args = [].
:- make_system_term $command_line_args/0.")
          ;; then there are no arguments, so just start the repl9
          (repl)

          ;; TODO: is there some exception that can be caught in the case that the repl is getting quit, in which case, we should run the
          ;; csv save file operations at that point?

          (if system/status-counters
            (StatusCounters/print_counters))
          )))))

(defn main [args]
  (try
    (real-main args)
    (finally (exit-system))))



;; (defn main2 [& args]
;;   (main (vec args)))

(defn -main [] (main []))
