(ns dyna-backend.ast-to-rexpr
  (:require [dyna-backend.utils :refer :all])
  (:require [dyna-backend.rexpr :refer :all])
  (:import [org.antlr.v4.runtime CharStream CharStreams UnbufferedTokenStream]))


;; if we provide some way for a string to be converted into an AST, and then
;; some way to evaluate an AST, then that means that there is enough for this to
;; have runtime reflection of the values.  This could just be calling the parser
;; on some entry point which either allows for it to just be the body of some
;; expression or it can do multiple terms all at once.
;;
;; in the case that it was just a single expression, then I suppose that is a
;; query, so maybe that should have some question mark which is required as the
;; last expression in the statement.
;;
;; assuming that we can do lazy evaluation, and if we added some readline
;; support, then this could allow for an entire repl to be written in dyna where
;; it would just be calling the evaluate statement to get to the next step
(def-base-rexpr ast-from-string [:var out
                                 :var string])

;; by having macros, this can make some operations more efficient, like map
;; elements where there are constant values could be constructed in a single
;; step.  So there could be some metadata which defines that something should
;; operate as a macro.  It would have something like `:- macro key/1` which
;; would mean that it gets the ast of its arguments, and that it must be defined
;; with `=` aggregator.  How would macros work in the case of
;; assumptions/invalidations.  I suppose that the macro could add assumptions to
;; the rule just like anything else?  But that would mean that we are having to
;; keep around the original ASTs of the program, in addition to the R-exprs.


;; this takes an AST which is represented as Dyna Terms, and rewrites itself as a R-expr.
(def-base-rexpr eval-from-ast [:var out-variable ;; the ast is structured such that everything returns some value.  This is the variable which is returned
                               :var ast
                               :unchecked variable-name-mapping ;; these are variable names which are in scope and the associated R-expr variable/constant
                               :unchecked source-file ;; this is the filename of the current item, so if we do $load, then we can have that get the relative file path
                               ])


(defn load-top-ast [ast]
  (let [erexpr (make-eval-from-ast (make-constant true) ;; the result variable for the top level expressions should just evaluate to true
                                   (make-constant ast)
                                   {})]
    ;; running simplify should force all of these expressions to get loaded into the system
    ;; this is going
    (simplify erexpr)
    ))


(defn run-parser [^CharStream stream]
  (let [lexer (dyna_backend.dyna_grammar2Lexer. ^CharStream stream)
        token-stream (UnbufferedTokenStream. lexer)
        parser (dyna_backend.dyna_grammar2Parser. token-stream)]
    (comment
      (if run-parser-fast ;; there needs to be some way in which this can be
                          ;; configured or something.  I suppose that this could
                          ;; happen via flags or for large inputs
        (.setErrorHandler parser (BailErrorStrategy.))))
    (let [r (.program parser)
          e (.getNumberOfSyntaxErrors parser)]
      (if (not= e 0)
        (throw (RuntimeException. "syntax error"))
        (.rterm r)))))



(defn parse-string [^String s]
  (let [char-stream (CharStreams/fromString ^String (str s "\n% end of string"))]
    (run-parser char-stream)))


(defn parse-file [file-url]
  ;; this is going to want to take a java url object, and then parse that into something
  )
