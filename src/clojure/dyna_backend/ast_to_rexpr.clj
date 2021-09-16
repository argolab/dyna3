(ns dyna-backend.ast-to-rexpr
  (:require [dyna-backend.utils :refer :all])
  (:require [dyna-backend.rexpr :refer :all])
  (:require [dyna-backend.rexpr-dynabase :refer :all])
  (:require [clojure.set :refer [union]])
  (:import [org.antlr.v4.runtime CharStream CharStreams UnbufferedTokenStream])
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
                               ]
  ;; this is going to need something custom for the variable-name-mapping so that it is able to get the values for the variables when it comes
  )


(def empty-ast-context
  {:variables {}  ;; a map from variable string names to some R-expr object
   :filename nil ;; object which is hash-able and equals-able to identify where this function comes from, what name-space this exists in
   })

;; there needs to be some queue of

(defn make-comma-conjunct
  ([a] a)
  ([a & args] (DynaTerm. "," [a (make-comma-conjunct args)])))

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


(defn conversion-from-ast [^DynaTerm ast out-variable variable-name-mapping source-file]
  (let [project-out-vars (transient {})
        get-variable (fn [name]
          (if (contains? variable-name-mapping name)
            (get variable-name-mapping name)
            (if (contains? project-out-vars name)
              (get project-out-vars name)
              (let [nv (make-variable name)]
                (assoc! project-out-vars name nv)
                nv))))
        get-variable-mapping (fn [] (merge project-out-vars variable-name-mapping))]
    (let [constructed-rexpr
          (case (.name ast)
            ;; $define_term is the standard define term expression, this not have some dynabase additional reference or anything else yet
            "$define_term" (let [[head aggregator body] (.arguments ast)
                                 new-body (make-comma-conjunct
                                           (DynaTerm. "$unify" [(DynaTerm. "$variable" "$self")
                                                                (DynaTerm. "$variable" "$dynabase")])
                                           (DynaTerm. "$dynabase_access_file" [(DynaTerm. "$variable" "$dynabase")])
                                           body)
                                 new-ast (DynaTerm. "$define_term_dynabase_added"
                                                    (.dynabase ast)
                                                    (.from_file ast)
                                                    new-body)]
                             (make-eval-from-ast out-variable new-ast variable-name-mapping source-file))
            "$define_term_dynabase" (let [[head aggregator dynabase-ref body] (.arguments ast)
                                          db-unify (DynaTerm. "$unify" [dynabase-ref (DynaTerm. "$variable" "$self")])
                                          new-ast (DynaTerm. "$define_term"
                                                             (.dynabase ast)
                                                             (.from_file ast)
                                                             [head aggregator (DynaTerm. "," [db-unify body])])]
                                      ;; this should probably not get called in this case? or should this
                                      (make-eval-from-ast out-variable new-ast variable-name-mapping source-file))
            "$define_term_dynabase_added" (let [[head aggregator body] (.arguments ast)
                                                name (.name head)
                                                arity (.arity head)
                                                head-args (.arguments head)
                                                head-unifies (map (fn [i v]
                                                                    (DynaTerm. "$unify" [(DynaTerm. "$variable" (str "$" i))
                                                                                         v])
                                                                    ) (range arity) head-args)
                                                head-combined (reduce (fn [a b] (DynaTerm. "," [a b])) head-unifies)
                                                new-body (if (nil?  head-combined) body (DynaTerm. "," [head-combined body]))
                                                new-ast (DynaTerm. "$define_term_normalized"
                                                                   (.dynabase ast)
                                                                   (.from_file ast)
                                                                   [name arity aggregator new-body])]
                                            ;; this returns a new ast element as we have not fully constructed this object yet
                                            (make-eval-from-ast out-variable new-ast variable-name-mapping source-file))
            "$define_term_normalized" (let [[name arity aggregator body] (.arguments ast)
                                            agg-in-var (make-variable "$result")
                                            agg-out-var (make-variable (str "$" arity))
                                            variables (assoc
                                                       (into {} (for [i (range arity)] [(str "$" i) (make-variable (str "$" i))]))
                                                       "$self" (make-variable "$self") ;; this is the variable which represents what dynabsae is calling into this
                                                       )
                                            ;; we have to make the aggregator also
                                            inner-rexpr (make-eval-from-ast body agg-in-var variables source-file)
                                            full-rexpr (make-aggregator aggregator agg-out-var agg-in-var inner-rexpr)]
                                        (assert false) ;; this needs to combine this
                                        ;; expression with any existing
                                        ;; expression which might be
                                        ;; represented under some name in
                                        ;; the system.  This will then want to have some expression for which
                                        (make-unify (make-constant true) out-variable))

            "$dynabase_create" (let [[parent-variable & body] (.arguments ast)
                                     ;; the first thing this needs to do is figure out which variables this needs to track for the expression
                                     ;; the variables $0,....,$n are required as those are the head variables, so those expressions should be unique
                                     ;; but then there are any other variables which are referenced in the expression which might be useful
                                     inner-variables (apply union find-all-variables body)
                                     selected-variables (into {} (filter #(contains? inner-variables (first %)) variable-name-mapping))

                                     ;; this will have to generate a new name for the dynabase, and then will have to create an R-expr which represents
                                     ;; the dynabase with it finding which of the expressions correspond with it handling how

                                     ]
                                 (assert false) ;;
                                 )

            "$dynabase_access" (let [[name dynabase-variable & args] (.arguments ast)
                                     db-var (get-variable dynabase-variable)
                                     ]
                                 ;; this is going to have to be added to all of the ast function nodes in the program.  This will have that those expressions
                                 ;; correspond with it having to define which of the expressions correspond with it
                                 (make-dynabase-access name )
                                 )

            "$dynabase_access_file" (let [[dynabase-variable] (.arguments ast)
                                          db-var (get-variable dynabase-variable)]
                                      ;; this means that the dynabase variable is just something that is contained in the top level file
                                      ;; so we are going to need to look up the file name to identify which expression contains this

                                      )

            ;; default constructor which is just going to construct a user call
            (let [name (.name ast)
                  args (.arguments ast)
                  other-conjunct-rexprs (transient []) ;; other R-exprs which are now conjunctive with this expression
                  new-variables (transient {})
                  args-values (map (fn [^DynaTerm v]
                                     (case (.name v)
                                       "$variable" (let [[name] (.arguments v)]
                                                     (if (contains? variable-name-mapping name)
                                                       (get variable-name-mapping name)
                                                       (if (contains? new-variables name)
                                                         (get new-variables name)
                                                         (let [nv (make-variable name)]
                                                           (assoc! new-variables name nv)
                                                           nv))))
                                       "$constant" (let [[val] (.arguments v)]
                                                     (make-constant val))
                                       "$annon_variable" (let [tmp-name (gensym)
                                                               tmp-var (make-variable tmp-name)]
                                                           (assoc! new-variables tmp-name tmp-var)
                                                           tmp-var)
                                       (let [tmp-name (gensym)
                                             tmp-var (make-variable tmp-name)]
                                         ;; in this case, a new variable is created which is used for the return value of the expression
                                         (assoc! new-variables tmp-name tmp-var) ;; indicate that this variable was created so it will be hidden
                                         (conj! other-conjunct-rexprs [tmp-var v])
                                         tmp-var)
                                       )
                                     ))
                  dynabase-variable (get )

                  ]

              (doseq [rexpr other-conjunct-rexprs]
                ;; this is going to have to add these R-exprs to the body of the expression
                ;; these R-exprs are
                )

              )
            )]

      ;; any new variables which are introduced need to be projected out of the expression
      (reduce (fn [R var] (make-proj var R)) constructed-rexpr (vals project-out-vars)))))

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
        (throw (RuntimeException. "syntax error")) ;; this would be nice if
                                                   ;; there was more of an error
                                                   ;; message, but this should
                                                   ;; get printed out by the
                                                   ;; parser I suppose
        (.rterm r)))))




(defn parse-string [^String s]
  (let [char-stream (CharStreams/fromString ^String (str s "\n% end of string\n"))]
    (run-parser char-stream)))


(defn parse-file [file-url]
  ;; this is going to want to take a java url object, and then parse that into something
  (let [url (if (string? (URL. file-url))
              (do (assert (instance? URL file-url))
                  file-url))
        stream (java.io.BufferedInputStream (.openStream url) 4096)
        cstream (java.io.SequenceInputStream stream
                                             (java.io.ByteArrayInputStream.
                                              (.getBytes (str "\n\n%end of file\n\n"))))
        astream (dyna_backend.ParserUnbufferedInputStream. cstream 1024)
        ]
    (run-parser astream)))


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



;; (def-rewrite
;;   :match (eval-from-ast (:any out) (:ground ast) ))
