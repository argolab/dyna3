(ns dyna.repl
  (:import [org.jline.terminal TerminalBuilder])
  (:import [org.jline.reader.impl DefaultParser DefaultParser$Bracket])
  (:import [org.jline.reader LineReader LineReader$Option LineReaderBuilder EOFError UserInterruptException])

  (:require [dyna.ast-to-rexpr :refer [eval-string print-parser-errors parse-string]])
  (:require [dyna.system :as system])
  (:require [dyna.rexpr-constructors :refer [make-multiplicity]])
  (:require [dyna.utils :refer [debug-repl]])
  (:require [clojure.string :refer [trim]])
  (:import [dyna DynaUserAssert DynaUserError])
  (:import [org.antlr.v4.runtime InputMismatchException]))


;; there should be some REPL which is based off jline or something which allows
;; for commands to be input into a terminal and then evaluated against the
;; system

;; if this is a command and not something that we want to run through the parser, then it should still accept the input
;; I suppose there could be things like a help command or some list table command.
(defn is-command? [line]
  (contains? #{"exit" "quit" "run-agenda" "run_agenda" "clojure-debug-repl"} (trim line)))


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
    (println "To exit press ctrl-d")
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
          (let [input (.readLine line-reader "dyna> ")]
            ;(println "read input" input)
            (when-not (contains? #{"exit" "quit"} (trim input))
              (if (is-command? input)
                (case (trim input)
                  "run-agenda" (system/run-agenda)
                  "run_agenda" (system/run-agenda)
                  "clojure-debug-repl" (debug-repl))

                (try
                  (let [rexpr-result (eval-string input :fragment-allowed false)]
                    (if (= (make-multiplicity 1) rexpr-result)
                      (println "ok")
                      (println rexpr-result)))
                  (catch DynaUserAssert e
                    (println (.getMessage e)))
                  (catch DynaUserError e
                    (println (.getMessage e)))))
              (recur)))))
      (catch UserInterruptException err nil))))
