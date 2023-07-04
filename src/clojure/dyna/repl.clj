(ns dyna.repl
  (:import [org.jline.terminal TerminalBuilder])
  (:import [org.jline.reader.impl DefaultParser DefaultParser$Bracket])
  (:import [org.jline.reader LineReader LineReader$Option LineReaderBuilder EOFError UserInterruptException EndOfFileException])

  (:require [dyna.ast-to-rexpr :refer [eval-string print-parser-errors parse-string import-file-url]])
  (:require [dyna.system :as system])
  (:require [dyna.rexpr :refer [find-iterators simplify]])
  (:require [dyna.base-protocols :refer [is-empty-rexpr? exposed-variables ctx-get-all-bindings]])
  (:require [dyna.context :as context])
  (:require [dyna.rexpr-constructors :refer [make-multiplicity is-unify? is-conjunct? is-multiplicity?]])
  (:require [dyna.iterators :refer [run-iterator]])
  (:require [dyna.utils :refer [debug-repl]])
  (:require [dyna.rexpr-pretty-printer :refer [print-rexpr *print-variable-name*]])
  (:require [clojure.string :refer [trim join split]])
  (:require [clojure.java.io :refer [file]])
  (:import [dyna DynaUserAssert DynaUserError])
  (:import [org.antlr.v4.runtime InputMismatchException]))

;; if this is a command and not something that we want to run through the parser, then it should still accept the input
;; I suppose there could be things like a help command or some list table command.
(defn- is-command? [line]
  (contains? #{"exit" "quit" "run-agenda" "clear-agenda" "help"
               "debug-clojure-repl" "debug-print-raw"
               "run" "reset"}
             (first (split (trim line) #" "))))

(defn- repl-help []
  (println "Dyna help:

Commands:
    exit/quit/Ctrl-D  quit the Dyna REPL
    run-agenda        Run the agenda immeditly (the agenda will be automattically run before a query is answered)
    clear-agenda      Delete everything on the agenda.  Note: this can leave the systen in an inconsistent state
    run               Run/import a file into the repl
    reset             Reset the Dyna REPL back to a clean initial state
    Ctrl-C            Stop processing

Example programs:

:- import \"some_file.dyna\".

fib(0) += 0.
fib(1) += 1.
fib(N) += fib(N-1) for N > 1.
fib(N) += fib(N-2) for N > 1.
$memo(fib[N:$ground]) = \"unk\".
print fib(100).
"))

(def ^{:private true}
  print-symbols
  {:empty "\u2205  (NO RESULTS)"
   :tuple-left "\u3008"
   :tuple-right "\u3009"
   :at-mult "@"
   :bag-left "\u27c5"
   :bag-right "\u27c6"})

(def ^{:private true :dynamic true} *terminal*)
(def ^{:private true} print-raw-rexprs false)

#_(defn- print-break [msg]
  (let [m (count msg)
        w (min (.getWidth *terminal*) 80)]
    (if (= m 0)
      (println (apply str (repeat w "~")))
      (println (str (apply str (repeat (quot (- w m 2) 2) "~")) " " msg " " (repeat (quot (- w m 2) 2) "~"))))))

(def ^:dynamic *terminal-print-width* 80)

(def ^:dynamic *repl-evaluate-string* (fn [s]
                                        (eval-string s :fragment-allowed false)))

(defn pretty-print-query-result [print-id result]
  (let [rexpr (:rexpr result)]
    (if (is-empty-rexpr? rexpr)
      (println print-id " " (:empty print-symbols))
      (let [ctx (:context result)
            ;; these variables should be sorted in a nice order
            variables (vec (exposed-variables rexpr))
            to-print (volatile! [])
            var-print (fn [vars [var val]]
                        (if (= (:varname var) "$query_result_var")
                          (if (<= (count print-id) 25)
                            (let [pi (loop [pi print-id
                                            v (seq vars)]
                                       (if (empty? v)
                                         pi
                                         (let [[[vf vv] & vr] v]
                                           (recur (clojure.string/replace pi (str (:varname vf)) (if (string? vv)
                                                                                                   (str "\"" vv "\"")
                                                                                                   (str vv)))
                                                  vr))))]
                              (str pi "=" (if (string? val)
                                            (str "\"" val "\"")
                                            val)))
                            (str "RESULT=" (if (string? val)
                                             (str "\"" val "\"")
                                             val)))
                          (if (not= \$ (first (:varname var)))
                            (str (:varname var) "=" (if (string? val)
                                                      (str "\"" val "\"")
                                                      val)))))
            ]
        (context/bind-context-raw
         ctx
         (let [iters (find-iterators rexpr)]
           (run-iterator
            :bind-all true
            :iterators iters
            :rexpr-in rexpr
            :rexpr-result rexpr-out
            (let [sr (simplify rexpr-out)]
              (vswap! to-print conj [(ctx-get-all-bindings (context/get-context)) sr])))))
        (assert (> (count @to-print) 0))
        (print (trim print-id) " ?\n")
        (if (and (= 1 (count @to-print)) (= (make-multiplicity 1)(second (first @to-print))) )
          (let [vbinds (remove nil? (map #(var-print (first (first @to-print)) %) (first (first @to-print))))]
            (case (count vbinds)
              0 (print "  " (:tuple-left print-symbols) " " (:tuple-right print-symbols) "     (ONE RESULT WITH NO VARIABLES ASSIGNED)\n")
              1 (print "  " (:tuple-left print-symbols) (first vbinds) (:tuple-right print-symbols) "\n")
              (do
                (print "  " (:tuple-left print-symbols) (first vbinds) " ")
                (doseq [v (rest vbinds)]
                  (print "\n     " v " "))
                (print (:tuple-right print-symbols) "\n"))))
          (let [all-1 (every? #(= (make-multiplicity 1) (second %)) @to-print)
                print-r (fn [[vars rexpr]]
                          (let [var-str (str (:tuple-left print-symbols) " "
                                             (let [aa (join ", " (map #(var-print vars %) vars))
                                                   bb (join ", " (map #(:varname %) (remove #(or (contains? vars %)
                                                                                                 (= (:varname %) "$query_result_var"))
                                                                                            (exposed-variables rexpr))))]
                                               (if (empty? aa)
                                                 (if (empty? bb)
                                                   ""
                                                   (str bb " "))
                                                 (if (empty? bb)
                                                   (str aa " ")
                                                   (str aa ", " bb " "))))
                                             (:tuple-right print-symbols))]
                            (if all-1
                              (print var-str)
                              (do
                                (print var-str)
                                (print (:at-mult print-symbols) " ")
                                ;; TODO: this has to indent the R-expr and make it look decent
                                (binding [*print-variable-name* (fn [var]
                                                                  (if (= (:varname var) "$query_result_var")
                                                                    (if (<= (count print-id) 25)
                                                                      (loop [pi print-id
                                                                             v (seq vars)]
                                                                        (if (empty? v)
                                                                          pi
                                                                          (let [[[vf vv] & vr] v]
                                                                            (recur (clojure.string/replace pi (str (:varname vf)) (if (string? vv)
                                                                                                                                    (str "\"" vv "\"")
                                                                                                                                    (str vv)))
                                                                                   vr))))
                                                                      "RESULT")
                                                                    (:varname var)))]
                                  (print (print-rexpr rexpr :width (max 80 (- *terminal-print-width* (count var-str) 2)))))))))]
            (print "  " (:bag-left print-symbols))
            (print-r (first @to-print))
            (doseq [v (rest @to-print)]
              (print "\n    ")
              (print-r v))
            (print " "(:bag-right print-symbols) "\n")))
                                        ;(debug-repl "print r")
        (flush)))))

(defn- print-query-result [print-id result]
  (if print-raw-rexprs
    (do (println print-id)
        (println (:context result))
        (println (:rexpr result)))
    (binding [*terminal-print-width* (.getWidth *terminal*)]
      (pretty-print-query-result print-id result))))

;; https://github.com/jline/jline3/blob/master/console/src/test/java/org/jline/example/Console.java
;; https://github.com/jline/jline3/blob/master/demo/src/main/java/org/jline/demo/Repl.java
(defn- repl-core []
  (let [active-system (volatile! system/*dyna-active-system*)
        terminal (-> (TerminalBuilder/builder)
                     (.name "dyna")
                     (.build))
        parser (let [p (proxy [DefaultParser] []
                         (parse [line cursor context]
                           (let [res (proxy-super parse line cursor context)
                                 pres (try (binding [print-parser-errors false]
                                             (parse-string line :fragment-allowed false))
                                           (catch RuntimeException e nil)
                                           ;(catch InputMismatchException e nil)
                                           ;(catch StringIndexOutOfBoundsException e nil)
                                           )]
                             (when (and (nil? pres) (not (is-command? line)))
                               ;; if the expression does not parse, then we are
                               ;; going to throw an exception so that the user
                               ;; can keep entering input
                               (throw (EOFError. -1 -1 "incomplete expression"))) ;; this stack trace gets printed atm?
                             res)))]
                 (.setEofOnUnclosedBracket p (let [a (make-array DefaultParser$Bracket 3)]
                                               (aset a 0 DefaultParser$Bracket/CURLY)
                                               (aset a 1 DefaultParser$Bracket/ROUND)
                                               (aset a 2 DefaultParser$Bracket/SQUARE)
                                               a))
                 (.setQuoteChars p (char-array "\"")) ;; a single quote can stand alone on '{}
                 (.setEofOnUnclosedQuote p true)
                 p)
        line-reader (-> (LineReaderBuilder/builder)
                        (.terminal terminal)
                        (.parser parser)
                        (.option LineReader$Option/INSERT_BRACKET true)
                        (.variable LineReader/INDENTATION 2)
                        (.variable LineReader/HISTORY_FILE (System/getProperty "dyna.history_file"
                                                                               (str (System/getProperty "user.home") "/.dyna3_history")))
                        (.build))]
    (binding [*terminal* terminal]
      (try
        (let [buffer-query-results (volatile! true)
              query-buffer (volatile! [])
              flush-query-buffer (fn []
                                   (doseq [[query-text query-line-number result] @query-buffer]
                                     (print-query-result query-text result))
                                   (vreset! query-buffer []))
              query-output-fn (fn [[query-text query-line-number] result]
                                (vswap! query-buffer conj [query-text query-line-number result])
                                (if @buffer-query-results
                                  (vreset! buffer-query-results false)
                                  (flush-query-buffer)))]
          (loop []
            (let [input (loop [did-ctrlc false]
                          (let [v (try (.readLine line-reader "dyna> ")
                                       (catch UserInterruptException err
                                         (if-not did-ctrlc
                                           nil
                                           (throw err))))]
                            (if (nil? v)
                              (recur true)
                              v)))]
                                        ;(println "read input" input)
              (when (#{"exit" "quit"} (trim input))
                (System/exit 0))
              (when-not (contains? #{"exit" "quit" "continue"} (trim input))
                (if (is-command? input)
                  (case (first (split (trim input) #" "))
                    "run" (let [fname (second (split (trim input) #" " 2))]
                            (if (nil? @active-system)
                              (binding [system/query-output query-output-fn]
                                (import-file-url (.toURL (file fname))))
                              (system/run-under-system @active-system
                                                       (binding [system/query-output query-output-fn]
                                                         (import-file-url (.toURL (file fname)))))))
                    "reset" (do (vreset! active-system (system/make-new-dyna-system))
                                (println "System state has been reset.  All user defined functors have been deleted."))
                    "run-agenda" (system/run-agenda)
                                        ;"run_agenda" (system/run-agenda)
                    "debug-clojure-repl" (debug-repl)
                    "debug-print-raw" (def print-raw-rexprs true)
                    "clear-agenda" (do
                                     (.clear_agenda system/work-agenda)
                                     (println "Agenda cleared\nWARNING: this can cause the system to return incorrect results as some updates will not have been processed"))
                    "help" (repl-help))

                  (try
                    (let [cthread (Thread/currentThread)]
                      (sun.misc.Signal/handle (sun.misc.Signal. "INT")
                                              (proxy [sun.misc.SignalHandler] []
                                                (handle [sig]
                                                  (.interrupt cthread))))
                      (vreset! buffer-query-results true)
                      (vreset! query-buffer [])
                      (let [rexpr-result (if (nil? @active-system)
                                           (binding [system/query-output query-output-fn]
                                             (*repl-evaluate-string* input))
                                           (system/run-under-system @active-system
                                                                    (binding [system/query-output query-output-fn]
                                                                      (*repl-evaluate-string* input))))]
                        (if (= (make-multiplicity 1) rexpr-result)
                          (if (and (empty? @query-buffer) @buffer-query-results)
                            (println "ok")
                            (do
                              (doseq [[query-text query-line-number result] @query-buffer]
                                (print-query-result query-text result))
                              (vreset! query-buffer [])))
                          (println rexpr-result))))
                    (catch DynaUserAssert e
                      (println (.getMessage e)))
                    (catch DynaUserError e
                      (println (.getMessage e)))
                    (catch InterruptedException e
                      (println "Interrupted"))))
                (recur)))))
        (catch UserInterruptException err nil)
        (catch EndOfFileException err nil)))))

(defn repl []
  (println "To exit press ctrl-D.  Type \"help\" for help")
  (repl-core))

(defn repl-in-file [file-name]
  (binding [*repl-evaluate-string* (fn [s] (eval-string :fragment-allowed false :file-name file-name))]
    (println "To continue running type \"continue\" or press ctrl-D")
    (println "To kill the program type \"exit\" or \"quit\"")
    (repl-core)))
