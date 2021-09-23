(ns dyna-backend.ast-to-rexpr
  (:require [dyna-backend.utils :refer :all])
  (:require [dyna-backend.rexpr :refer :all])
  (:require [dyna-backend.rexpr-dynabase :refer :all])
  (:require [dyna-backend.system :as system])
  (:require [dyna-backend.user-defined-terms :refer [add-to-user-term update-user-term def-user-term]])
  (:require [clojure.set :refer [union]])
  (:require [clojure.string :refer [join]])
  (:require [clojure.java.io :refer [resource]])
  (:import [org.antlr.v4.runtime CharStream CharStreams UnbufferedTokenStream])
  (:import [org.antlr.v4.runtime.misc Interval])
  (:import [dyna_backend DynaTerm])
  (:import [java.net URL]))



(def pending-parser-work (atom clojure.lang.PersistentQueue/EMPTY))

(defn push-parser-work [w] (swap! pending-parser-work conj w))
(defn pop-parser-work []
  (let [[old new] (swap-vals! pending-parser-work pop)]
    (peek old)))


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

;; some method which takes an AST and returns a string
(def-user-term "$ast" 1 (make-ast-from-string v1 v0))


;; these have to be defined below, as they are going to want to have references to the current file and the current variables which are in scope
;; (def-user-term "$eval" 1 ...)
;; (def-user-term "$eval_from_ast" 1)



;; by having macros, this can make some operations more efficient, like map
;; elements where there are constant values could be constructed in a single
;; step.  So there could be some metadata which defines that something should
;; operate as a macro.  It would have something like `:- macro key/1` which
;; would mean that it gets the ast of its arguments, and that it must be defined
;; with `=` aggregator.  How would macros work in the case of
;; assumptions/invalidations.  I suppose that the macro could add assumptions to
;; the rule just like anything else?  But that would mean that we are having to
;; keep around the original ASTs of the program, in addition to the R-exprs.


;; I suppose that this is having to resolve the calls for an expression.  This means that it is attempting to find


;; this takes an AST which is represented as Dyna Terms, and rewrites itself as a R-expr.
(def-base-rexpr eval-from-ast [:var out-variable ;; the ast is structured such that everything returns some value.  This is the variable which is returned
                               :var ast
                               :unchecked variable-name-mapping ;; these are variable names which are in scope and the associated R-expr variable/constant
                               :unchecked source-file ;; this is the filename of the current item, so if we do $load, then we can have that get the relative file path
                               ]
  (get-variables [this] (into #{} (filter variable?
                                          (concat (vals variable-name-mapping)
                                                  [out-variable ast]))))
  (remap-variables [this variable-map]
                   (make-eval-from-ast
                    (get variable-map out-variable out-variable)
                    (get variable-map ast ast)
                    (into {} (for [[k v] variable-name-mapping]
                               [k (get variable-map v v)]))
                    source-file ;; this is just some constant
                    ))

  ;; this is going to need something custom for the variable-name-mapping so that it is able to get the values for the variables when it comes
  )

(declare import-file)



(def empty-ast-context
  {:variables {}  ;; a map from variable string names to some R-expr object
   :filename nil ;; object which is hash-able and equals-able to identify where this function comes from, what name-space this exists in
   })



(def true-constant-dterm (DynaTerm. "$constant" [true]))

(defn make-comma-conjunct
  ([] true-constant-dterm)
  ([a] (if (nil? a)
         true-constant-dterm
         a))
  ([a & args]
   (if (or (nil? a) (= a true-constant-dterm))
     (apply make-comma-conjunct args)
     (DynaTerm. "," [a (apply make-comma-conjunct args)]))))


;; special variables
;; $0, .., $n-1 the arguments to an n-arity function
;; $n           the return value of an n-arity function
;; $self        the dynabase which is being called.  This variable is unified in by the outer context
;; $dynabase    the context by which function calls that are not marked explicity with a particular dynabase should be conducted from
;;              a function like `a(X) = f(X).` should include the hidden unification `$self = $dynabase` which will enforce that we call to the same dynabase


;; $define_term --> the object which is constructed from the parser
;; $define_term_dynabase --> object constructed from parser when explicit dynabase annotation is present
;; $define_term_dynabase_added --> object after $self and $dynabase have been setup
;; $define_term_normalized --> term after normalization is complete, ready to get converted into an R-expr and loaded into the system

(defn find-all-variables [ast]
  (if (instance? DynaTerm ast)
    (if (= (.name ^DynaTerm ast) "$variable")
      #{(get (.arguments ^DynaTerm ast) 0)}
      (apply union (map find-all-variables (.arguments ^DynaTerm ast))))
    ;; this is something else, like maybe the inside of a constant or something
    #{}))

(defn find-term-variables [ast]
  (if (instance? DynaTerm ast)
    (let [name (.name ^DynaTerm ast)]
      (case name
        "$variable" #{(get ast 0)}
        "$dynabase_create" #{}  ;; do not look through a dynabase create
        "$inline_aggregate" #{}  ;; do not look through an inline aggregator
        (apply union (map find-term-variables (.arguments ^DynaTerm ast)))))))


(defn convert-from-ast [^DynaTerm ast out-variable variable-name-mapping source-file]
  ;; convert from the ast into an R-expr which can then be evaluated
  ;; the AST is a DynaTerm object, it should come from the parser.  It could also get generated by the user's program
  ;; out-variable is whatever variable represents the resulting expression.  In the AST, everything returns a "value", so
  (let [project-out-vars (transient #{})
        other-conjunctive-rexprs (transient [])
        make-intermediate-var (fn []
                                (let [tmp-var-name (str (gensym "$intermediate_var_"))
                                      var (make-variable tmp-var-name)]
                                  (conj! project-out-vars var)
                                  var))
        get-value (fn [^DynaTerm a]
                    ;; conver an AST in its value.  This can either just return something from the AST if it is a variable or a constant, otherwise
                    ;; this has to construct other R-exprs which correspond with the evaluating of the node
                    (case (.name a)
                      "$variable" (let [[name] (.arguments a)
                                        var (get variable-name-mapping name)]
                                    (assert (not (nil? var)))
                                    var)
                      "$constant" (let [[val] (.arguments a)]
                                    (make-constant val))
                      ;; this is something else which is getting called.  This means that we have to recurse into the structure and add the arguments
                      (let [ret-var (make-intermediate-var)]
                        (conj! other-conjunctive-rexprs
                               (convert-from-ast a ret-var variable-name-mapping source-file))
                        ret-var)))
        get-arg-values (fn [args]
                         ;; map from a list of arguments to their values represented as variables in R-exprs
                         (doall (for [a args] (get-value a))))
        ;; make-call (fn [^DynaTerm term]
        ;;             (let [avals (get-arg-values (.arguments term))]
        ;;               (make-user-call))
        ;;             )
        ]

    (let [constructed-rexpr
          (case (.name ast)
            "$compiler_expression" (let [^DynaTerm arg1 (get ast 1)]
                                     (case (.name ^DynaTerm (get ast 0))
                                       "import" (???) ;; import some file, or some symbols from another file

                                       ;; use like `:- export name/arity`.  we
                                       ;; will have a set of symbols which are
                                       ;; exported from a given file.  Those
                                       ;; symbols can then be imported using an
                                       ;; import statement.  But if the file
                                       ;; isn't processed at the time that the
                                       ;; import statement is handled, how is
                                       ;; that going to work?  I suppose that
                                       ;; there can just be a function which is
                                       ;; called by import to do the importing
                                       ;; of a function in place.  That will
                                       "export" (swap! system/user-exported-terms
                                                       (fn [o]
                                                         (assoc o source-file (conj [(get arg1 0) (get arg1 1)] (get o source-file #{})))))

                                        ;(???) ;; list some symbols as getting exported

                                       ;; some of the arugments to a function should get escaped escaped, or quoted
                                       ;; used like `:- dispose foo(quote1,eval).`
                                       "dispose" (update-user-term {:name (.name ^DynaTerm arg1)
                                                                    :arity (.arity ^DynaTerm arg1)
                                                                    :source-file source-file}
                                                                   (fn [o]
                                                                     (assoc o :dispose-arguments (.arguments ^DynaTerm arg1))))

                                       ;; mark a function as being a macro, meaning that it gets its argument's AST and will return an AST which should get evaluated
                                       ;; used like `:- macro foo/3.`
                                       "macro" (update-user-term {:name (get arg1 0)
                                                                  :arity (get arg1 1)
                                                                  :source-file source-file}
                                                                 (fn [o]
                                                                   (assoc o :is-macro true)))

                                       ;; make a term global so that it can be referenced form every file
                                       ;; I suppose that there should be some global list of terms which will get resolved at every possible point
                                       ;; use like `:- make_global_term foo/3.`
                                       "make_global_term" (???)


                                       "memoize_unk" (???) ;; mark some function as being memoized
                                       "memoize_null" (???)

                                       "import_csv" (???) ;; import some CSV file as a term
                                       "export_csv" (???) ;; export a CSV file for a term after the program is done running

                                       (???) ;; there should be some invalid parse expression or something in the case that this fails at this point
                                       )
                                     (make-unify out-variable (make-constant true)) ;; just return that we processed this correctly?  I suppose that in
                                     )

            "$define_term" (let [[head dynabase aggregator body] (.arguments ^DynaTerm ast)
                                 new-body (make-comma-conjunct
                                           (apply make-comma-conjunct (for [[arg idx] (zipmap (.arguments ^DynaTerm head) (range))]
                                                                        (DynaTerm. "$unify" [(DynaTerm. "$variable" [(str "$" idx)])
                                                                                             arg])))
                                           (when (not (nil? dynabase))
                                             (DynaTerm. "$unify" [(DynaTerm. "$variable" ["$self"])
                                                                  (DynaTerm. "$dynabase_access" [dynabase])]))
                                           body)
                                 new-ast (DynaTerm. "$define_term_normalized"
                                                    [(.name ^DynaTerm head)
                                                     (- (.arity ^DynaTerm head) 1)
                                                     source-file
                                                     dynabase
                                                     aggregator
                                                     new-body])]
                             (make-eval-from-ast out-variable (make-constant new-ast) {} source-file))
            "$define_term_normalized" (let [[functor-name functor-arity source-file dynabase aggregator body] (.arguments ^DynaTerm ast)
                                            all-variables (find-term-variables body)
                                            project-variables (filter #(not (re-matcher #"\$self|\$[0-9]+" %)) all-variables)
                                            project-variables-map (into {} (for [v project-variables]
                                                                            [v (make-variable v)]))
                                            incoming-variable (make-variable (gensym "$incoming_variable_"))
                                            body-rexpr (convert-from-ast body
                                                                         incoming-variable
                                                                         project-variables-map
                                                                         source-file)
                                            rexpr (make-aggregator aggregator
                                                                   out-variable
                                                                   incoming-variable
                                                                   (make-proj-many (vals project-variables-map)
                                                                                   body-rexpr))]
                                        (add-to-user-term source-file dynabase functor-name functor-arity rexpr)
                                        ;; the result from the expression should just be to unify the out variable with true
                                        ;; ideally, this would check if the expression corresponds with
                                        (make-unify out-variable (make-constant true)))

            ;; it is possible to just write something like `X,123`, but that is odd....
            ;; I suppose that we might as well suppot this here, but I don't think this will actually get used
            "$constant" (let [[value] (.arguments ast)]
                          (make-unify (make-constant value) out-variable))

            "$variable" (let [[name] (.arguments ast)
                              var (get variable-name-mapping name)]
                          (assert (not (nil? var)))
                          (assert (string? name))  ;; we should not be allowing variables to take on the names of structures
                          (make-unify var out-variable))

            "$quote1" (let [[^DynaTerm quoted-structure] (.arguments ast)
                            name (.name quoted-structure)
                            vals (get-arg-values (.arguments quoted-structure))
                            ;; in the case that something comes from a top level
                            dynabase (if (contains? variable-name-mapping "$self")
                                       (get variable-name-mapping "$self")
                                       (make-constant nil))
                            structure (make-unify-structure out-variable
                                                            dynabase
                                                            (.name quoted-structure)  ;; the name of the structure
                                                            vals)]
                        structure)

            "$dynabase_call"  (let [[dynabase-var call-term] (.arguments ast)
                                    dynabase-val (get-value dynabase-var)
                                    call-vals (get-arg-values (.arguments call-term))
                                    arity (count call-vals)]
                                (make-user-call
                                 {:name (.name call-term)   ;; the name arity.  When a dynabase is called, there is no filename on the name qualifier, as it requires that it can be exported across files etc
                                  :arity arity}
                                 (merge
                                  {(make-variable "$self") dynabase-val
                                   (make-variable (str "$" arity)) out-variable}
                                  (into {} (for [[v i] (zipmap call-vals (range))]
                                             [(make-variable (str "$" i)) v]))))
                                0 ;; the call depth
                                )

            ;; we special case the ,/2 operator as this allows us to pass the info that the first expression will get unified with a constant true earlier
            ;; this should make some generation steps more efficient
            ","  (let [[a b] (.arguments ast)]
                   (make-conjunct [(convert-from-ast a
                                                     (make-constant true)
                                                     variable-name-mapping
                                                     source-file)
                                   (convert-from-ast b
                                                     out-variable
                                                     variable-name-mapping
                                                     source-file)]))

            ;; call without any qualification on it.  Just generate the user term
            (let [call-vals (get-arg-values (.arguments ast))
                  arity (count call-vals)]
              (make-user-call
               {:name (.name ast) ;; the name, arity and file name.  This makes the file work as a hard local scope for the function
                :arity arity
                :source-file source-file}
               (merge {(make-variable (str "$" arity)) out-variable}
                      (into {} (for [[v i] (zipmap call-vals (range))]
                                 [(make-variable (str "$" i)) v])))
               0 ;; call depth
               ))
            )]

      ;; add the R-expr that we constructed to the conjunctive R-exprs
      (conj! other-conjunctive-rexprs constructed-rexpr)
      ;; project out all of the variables which were added as intermediate expressions along the way
      (let [pvars (persistent! project-out-vars)
            cr (make-conjunct (persistent! other-conjunctive-rexprs))]
        (println "making many project" pvars cr)
        (make-proj-many pvars cr)))))


;; $define_term(foo(X,Y,Z), "=", 123).
;; $define_term_normalized("foo", 3, "=", $0=X,$1=Y,$2=Z,123).  ;; so this is moving the things in the head into unifications on the right hand side


(def ast-conversions
  {"$define_term" nil
   "$dynabase_create" nil
   "$constant" (fn [^DynaTerm ast context] (make-constant (get (.arguments ast) 0)))
   "$variable" (fn [^DynaTerm ast context] (make-variable (get (.arguments ast) 0)))
   "$with_key" nil
   "$annon_variable" nil
   "$quote1" (fn [^DynaTerm ast context] )
   "$quote" (fn [^DynaTerm ast context] (make-constant ast)) ;; just return the ast node for this expression
   "$dynabase_call" nil
   })

(defn make-rexpr-user-call [^DynaTerm ast context]

  )


;; this will be something that could be used by some user level operation
;; the program will have that the names of variables can be controlled
(def-base-rexpr eval-from-ast-dmap [:var out-variable
                                    :var ast
                                    :var dyna-variable-name-mapping ;; this is like the above, but the map should instead be a dynaMap which means that it can be constructed by the user to set the "context" in which some ast would be evaluated in
                                    :unchecked source-file])


;; (defn load-top-ast [ast]
;;   (let [erexpr (make-eval-from-ast (make-constant true) ;; the result variable for the top level expressions should just evaluate to true
;;                                    (make-constant ast)
;;                                    {})]
;;     ;; running simplify should force all of these expressions to get loaded into the system
;;     ;; this is going
;;     (simplify erexpr)
;;     ))


;; (def-rewrite
;;   :match (:any out-variable) (:ground ast) (:unchecked variable-name-mapping) (:unchecked source-file)
;;   (do

;;     ))


(defn get-parser-print-name [token]
  (.getDisplayName dyna_backend.dyna_grammar2Lexer/VOCABULARY token))

(def parse-error-handler
  (proxy [org.antlr.v4.runtime.DefaultErrorStrategy] []
    ;; (reportError [recognizer exception]
    ;;   ;; this is going to just be called in the general case, so I suppose that if this is not defined, then
    ;;   ;; this is going to try and report some error
    ;;   (debug-repl)
    ;;   (println "report error" exception))
    (reportFailedPredicate [recognizer exception]
                                        ;(debug-repl)
      (println "==========> report failed predicate" exception))
    (reportInputMismatch [recognizer exception]
      ;(debug-repl)
      (println "==========> report input missmatch" exception))
    (reportNoViableAlternative [recognizer exception]
      (let [token (.getStartToken exception)
            offending (.getOffendingToken exception)
            stream (.getInputStream token)
            continuations (map get-parser-print-name (.toList (.getExpectedTokens exception)))]
        (println "====================================================================================================")
        (println "PARSER ERROR -- invalid input")
        (println "")
        (println "Input was incomplete")
        (println "")
        (println (str "Line: " (.getLine token) ":" (.getCharPositionInLine token) "-" (.getLine offending) ":" (.getCharPositionInLine offending)))
        (println "--------------------")
        (println (.getText stream (Interval. ^int (.getStartIndex token) ^int (.getStopIndex offending))))
        (println "--------------------")
        (println "possible missing tokens: " (join " OR " continuations))
        (println "====================================================================================================")))
    (reportUnwantedToken [recognizer]
      (debug-repl)
      (println "=============> unwanted token"))
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
    (.setErrorHandler parser parse-error-handler)
    (let [r (.program parser)
          e (.getNumberOfSyntaxErrors parser)]
      (if (not= e 0)
        (throw (RuntimeException. "syntax error")) ;; this would be nice if
                                                   ;; there was more of an error
                                                   ;; message, but this should
                                                   ;; get printed out by the
                                                   ;; parser I suppose
        (.rterm r)))))




(defn parse-string [^String s]
  (let [char-stream (CharStreams/fromString ^String (str s "\n% end of string\n"))]
    (run-parser char-stream)))

(defn parse-stream [istream]
  (let [stream (java.io.BufferedInputStream istream 4096)
        cstream (java.io.SequenceInputStream stream
                                             (java.io.ByteArrayInputStream.
                                              (.getBytes (str "\n\n%end of file\n\n"))))
        astream (dyna_backend.ParserUnbufferedInputStream. cstream 1024)]
    (run-parser astream)))


(defn parse-file [file-url]
  ;; this is going to want to take a java url object, and then parse that into something
  (let [url (if (string? (URL. file-url))
              (do (assert (instance? URL file-url))
                  file-url))]
    (parse-stream (.openStream url))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn eval-string [^String s]
  (let [ast (parse-string s)
        rexpr (make-eval-from-ast (make-constant true)
                                  (make-constant ast)
                                  {}
                                  "REPL")]
    rexpr))

(defn import-parse [file-url ast]
  ;; this needs to construct the evaluate AST object, and then pass it to simplify to make sure that it gets entirely evaluated
  ;; into something that can be usedl
  (let [rexpr (make-eval-from-ast (make-constant true)
                                  (make-constant ast)
                                  {}
                                  file-url)]
    (simplify-top rexpr)))

(defn import-file-url [url]
  (let [do-import (atom false)]
    (swap! system/imported-files
           (fn [o]
             (if (contains? url)
               (do (reset! do-import false)
                   o)
               (do
                 (reset! do-import true)
                 (conj o url)))))
    (if @do-import
      ;; then we have to be the one to import this file
      (let [parse (parse-file url)]

        )
      (assert false)
      )))

;; (defn import-file [from-file name]
;;   (import-file-url
;;    (if (instance? URL name) name
;;        ;; we need to conver this to a URL
;;        (let [rurl (URL. from-file name)
;;              rstream (try (.openStream rurl)
;;                           (catch java.io.FileNotFoundException e nil))]
;;          (if (nil? rstream)
;;            (let [res (resource (str "dyna_backend/builtin_libraries/" name ".dyna"))]
;;              (if res
;;                (parse-stream))
;;              )
;;            )
;;          )
;;        (assert false)
;;        )))

(defn import-file [from-file name]
  (assert false))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-rewrite
  :match (ast-from-string (:any out) (:ground in))
  (let [s (get-value in)]
    (if (string? s)
      (make-unify out
                  (make-constant
                   (try
                     (parse-string s)
                     (catch RuntimeException e (make-structure "$error" [])))))
      (make-multiplicity 0) ;; the input is not a string, there is no way in which this is going to parse
      )))

(def-rewrite
  :match (eval-from-ast (:any out-variable) (:ground ast) (:unchecked variable-name-mapping) (:unchecked source-file))
  :run-at :construction ;; this should run at both standard time and construction
  ;:run-at :standard-and-construction ;; this should run when it is constructed and when it might have a ground variable
  (let [a (get-value ast)]
    (convert-from-ast a out-variable variable-name-mapping source-file)))


;; (def-rewrite
;;   :match (eval-from-ast (:any out) (:ground ast) ))
