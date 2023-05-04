(ns dyna.repl
  (:import [org.jline.terminal TerminalBuilder])
  (:import [org.jline.reader.impl DefaultParser DefaultParser$Bracket])
  (:import [org.jline.reader LineReader LineReader$Option LineReaderBuilder EOFError UserInterruptException EndOfFileException])

  (:require [dyna.ast-to-rexpr :refer [eval-string print-parser-errors parse-string]])
  (:require [dyna.system :as system])
  (:require [dyna.rexpr-constructors :refer [make-multiplicity]])
  (:require [dyna.utils :refer [debug-repl]])
  (:require [clojure.string :refer [trim]])
  (:import [dyna DynaUserAssert DynaUserError])
  (:import [org.antlr.v4.runtime InputMismatchException]))

;; if this is a command and not something that we want to run through the parser, then it should still accept the input
;; I suppose there could be things like a help command or some list table command.
(defn- is-command? [line]
  (contains? #{"exit" "quit" "run-agenda" "clojure-debug-repl" "clear-agenda" "help"} (trim line)))

(defn- repl-help []
  (println "Dyna help:

Commands:
    exit/quit/Ctrl-D  quit the Dyna REPL
    run-agenda        Run the agenda immeditly (the agenda will be automattically run before a query is answered)
    clear-agenda      Delete everything on the agenda.  Note: this can leave the systen in an inconsistent state
    Ctrl-C            Stop processing

Example programs:

:- import \"some_file.dyna\".

fib(0) += 0.
fib(1) += 1.
fib(N) += fib(N-1) for N > 1.
fib(N) += fib(N-2) for N > 1.
$memo(fib[N:$ground]) = \"unk\".
print fib(100).
")

  )

;; https://github.com/jline/jline3/blob/master/console/src/test/java/org/jline/example/Console.java
;; https://github.com/jline/jline3/blob/master/demo/src/main/java/org/jline/demo/Repl.java
(defn repl []
  (let [terminal (-> (TerminalBuilder/builder)
                     ;(.name "dyna")
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
    (println "To exit press ctrl-D.  Type \"help\" for help")
    (try
      (binding [system/query-output (fn [[query-text query-line-number] result]
                                      ;; ignore the line number as this is running interc
                                      (println "========== Query ==========")
                                      (println query-text)
                                      (println)
                                      (println "Variable assignments:" (:context-value-map result))
                                      (when (not= (make-multiplicity 1) (:rexpr result))
                                        (println "Rexpr:" (:rexpr result)))
                                      (println "==========================="))]
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
            (when-not (contains? #{"exit" "quit"} (trim input))
              (if (is-command? input)
                (case (trim input)
                  "run-agenda" (system/run-agenda)
                  ;"run_agenda" (system/run-agenda)
                  "clojure-debug-repl" (debug-repl)
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
                    (let [rexpr-result (eval-string input :fragment-allowed false)]
                      (if (= (make-multiplicity 1) rexpr-result)
                        (println "ok")
                        (println rexpr-result))))
                  (catch DynaUserAssert e
                    (println (.getMessage e)))
                  (catch DynaUserError e
                    (println (.getMessage e)))
                  (catch InterruptedException e
                    (println "Interrupted"))))
              (recur)))))
      (catch UserInterruptException err nil)
      (catch EndOfFileException err nil))))


#_(defn repl []
  (let [repl-thread (Thread. repl-run)]
    #_(sun.misc.Signal/handle (sun.misc.Signal. "INT")
                            (proxy [sun.misc.SignalHandler] []
                              (handle [sig]
                                (println "in sig int handler"))))
    (.start repl-thread)))
