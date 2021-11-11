(ns dyna.repl
  (:import [org.jline.terminal TerminalBuilder])
  (:import [org.jline.reader.impl DefaultParser DefaultParser$Bracket])
  (:import [org.jline.reader LineReader LineReader$Option LineReaderBuilder EOFError])

  (:require [dyna.ast-to-rexpr :refer [eval-string print-parser-errors parse-string]])
  (:require [dyna.system :as system])
  (:import [dyna DynaUserAssert]))


;; there should be some REPL which is based off jline or something which allows
;; for commands to be input into a terminal and then evaluated against the
;; system



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
                                           (catch RuntimeException e nil))]
                             (when (nil? pres)
                               ;; if the expression does not parse, then we are
                               ;; going to throw an exception so that the user
                               ;; can keep entering input
                               (throw (EOFError. -1 -1 "incomplete expression")))
                             res)))]
                 (.setEofOnUnclosedBracket p (let [a (make-array DefaultParser$Bracket 3)]
                                               (aset a 0 DefaultParser$Bracket/CURLY)
                                               (aset a 1 DefaultParser$Bracket/ROUND)
                                               (aset a 2 DefaultParser$Bracket/SQUARE)
                                               a))
                 (.setEofOnUnclosedQuote p true)
                 p)
        line-reader (-> (LineReaderBuilder/builder)
                        (.terminal terminal)
                        (.parser parser)
                        (.option LineReader$Option/INSERT_BRACKET true)
                        (.variable LineReader/INDENTATION 2)
                        (.build))]
    (binding [system/query-output (fn [query-text ctx rexpr]
                                    (println query-text ": " ctx rexpr))]
      (loop []
        (let [input (.readLine line-reader "dyna> ")]
                                        ;(println "read input" input)
          (when-not (contains? #{"exit" "quit"} input)
            (try
              (println (eval-string input :fragment-allowed false))
              (catch DynaUserAssert e
                (println (.getMessage e))))
            (recur)))))))
