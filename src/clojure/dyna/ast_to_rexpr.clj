(ns dyna.ast-to-rexpr
  (:require [dyna.utils :refer :all])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.rexpr :refer :all])
  (:require [dyna.rexpr-dynabase :refer :all])
  (:require [dyna.system :as system])
  (:require [dyna.context :as context])
  (:require [dyna.user-defined-terms :refer [add-to-user-term update-user-term! def-user-term get-user-term]])
  (:require [dyna.memoization :refer [set-user-term-as-memoized print-memo-table]])
  (:require [clojure.set :refer [union intersection difference rename-keys]])
  (:require [clojure.string :refer [join]])
  (:require [clojure.java.io :refer [resource]])
  (:require [aprint.core :refer [aprint]])
  (:import [org.antlr.v4.runtime CharStream CharStreams UnbufferedTokenStream])
  (:import [org.antlr.v4.runtime.misc Interval])
  (:import [dyna DynaTerm DynaUserAssert ParserUnbufferedInputStream DynaUserError])
  (:import [java.net URL])
  (:import [java.nio.file Paths])
  (:import [java.io FileNotFoundException]))


(def ^:dynamic print-parser-errors true)



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


;; $eval etc are are defined inside of the function convert-from-ast.  These are not "normal" functions as they can reference other variables which are in the context rather than what was just passed as an argument.
;; meaning that something like `f(X) = $eval("X").`  will still reference the same variable X
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
                               :file-name source-file ;; this is the filename of the current item, so if we do $load, then we can have that get the relative file path
                               ]
  (get-variables [this] (into #{} (filter is-variable?
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
  (remap-variables-handle-hidden [this variable-map]
                                 (remap-variables this variable-map)))


(declare import-file-url)



;; would like to remove excess proj statements which unify with a constant and
;; unifications between two variables, as we can just select one of the
;; variables and remove the other from the expression.
;;
;; the reason we do this here instead of letting the standard simplification
;; handle this is that the parser will generate many intermediate values that
;; are "useless"
(defn optimize-rexpr
  ([rexpr] (let [[unified-vars new-rexpr] (optimize-rexpr rexpr #{})]
             new-rexpr))
  ([rexpr proj-out-vars]
   (let [var-unifies (transient {})
         mr (cond
              (is-proj? rexpr) (let [ufv (:var rexpr)
                                     prexpr (:body rexpr)
                                     [nested-unifies nested-rexpr] (optimize-rexpr prexpr
                                                                                   (conj proj-out-vars ufv))
                                     self-var (disj (get nested-unifies ufv) ufv)
                                     ret-rexpr (if (not (empty? self-var))
                                                 ;; then there is some variable that we can use to replace this statement
                                                 ;; if it is a constant, then we can do the replacement such that it will avoid
                                                 (let [const (some is-constant? self-var)
                                                       replace-with (if const
                                                                      (first (filter is-constant? self-var))
                                                                      (first self-var))]
                                                   (remap-variables nested-rexpr {ufv replace-with}))

                                                 (if (= nested-rexpr prexpr)
                                                   rexpr
                                                   (make-proj ufv nested-rexpr)))]
                                 ;; we need to take the nested-unifies and add
                                 ;; in the info here, but filter out any
                                 ;; information which references our variable
                                 (doseq [[k v] nested-unifies]
                                   (when (not= k ufv)
                                     (assoc! var-unifies k (union (get var-unifies k) (disj v ufv)))))
                                 ret-rexpr)
              (is-unify? rexpr) (let [[a b] (get-arguments rexpr)]
                                  (assoc! var-unifies a (conj (get var-unifies a #{}) b))
                                  (assoc! var-unifies b (conj (get var-unifies b #{}) a))
                                  rexpr) ;; there is no change to the expression here
              (is-disjunct? rexpr) rexpr ;; we do not evaluate disjunctions for variables which might get unified together
              :else ;; otherwise we should check all of the children of the expression to see if there is some structure
              (rewrite-rexpr-children-no-simp rexpr
                                      (fn [r]
                                        (let [[unifies nr] (optimize-rexpr r proj-out-vars)]
                                          (doseq [[k v] unifies]
                                            (assoc! var-unifies k (union v (get var-unifies k))))
                                          nr))))]
     [(persistent! var-unifies) mr])))


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

(defn- recurse-through-escaped [ast fun]
  (if (instance? DynaTerm ast)
    (case [(.name ^DynaTerm ast) (.arity ^DynaTerm ast)]
      ["$escaped" 1] (fun (get ast 0))
      (apply union (map #(recurse-through-escaped % fun) (.arguments ^DynaTerm ast))))
    #{}))

(defn- find-all-variables [ast]
  (if (instance? DynaTerm ast)
    (case [(.name ^DynaTerm ast) (.arity ^DynaTerm ast)]
      ["$variable" 1] #{(get ast 0)}
      ["$constant" 1] #{}  ;; no variables in a constant
      ["$quote1" 1] (apply union (map find-all-variables (.arguments ^DynaTerm (get ast 0))))
      ["$dynabase_quote1" 2] (union (apply union (map find-all-variables (.arguments ^DynaTerm (get ast 1))))
                                    (find-all-variables (get ast 0)))
      ["$escaped" 1] (recurse-through-escaped (get ast 0) find-all-variables)
      (apply union (map find-all-variables (.arguments ^DynaTerm ast)))
    ;; this is something else, like maybe the inside of a constant or something
    #{})))

(defn- find-term-variables [ast]
  (if (instance? DynaTerm ast)
    (case [(.name ^DynaTerm ast) (.arity ^DynaTerm ast)] ;; put the arity into the expression
      ["$variable" 1] #{(get ast 0)}
      ["$constant" 1] #{}
      ["$dynabase_create" 2] (find-term-variables (get ast 0))  ;; the first argument could reference a parent variable name
      ;;"$inline_aggregated_function" #{}  ;; do not look through an inline aggregator
      ["$inline_function" 3] #{}
      ["$quote1" 1] (let [qs (get ast 0)
                          args (.arguments ^DynaTerm qs)
                          res (apply union (map find-term-variables args))]
                      res) ;; if the quote is $variale, skip that
      ["$dynabase_quote1" 2] (let [dynabase (get ast 0)
                                   qs (get ast 1)
                                   args (.arguments ^DynaTerm qs)
                                   res (union (apply union (map find-term-variables args) (find-term-variables dynabase)))]
                               res)
      ["$escaped" 1] (recurse-through-escaped (get ast 0) find-term-variables)
      (let [res (apply union (map find-term-variables (.arguments ^DynaTerm ast)))]
        ;; (when-not (empty? res)
        ;;   (debug-repl))
        res))
    #{}))

(def current-dir (-> (java.io.File. (System/getProperty "user.dir")) .toURI .toURL))
(def current-dir-path (Paths/get (.toURI current-dir)))

(defn- convert-from-escaped-ast-to-ast [^DynaTerm ast source-file]
  (if-not (instance? DynaTerm ast)
    (DynaTerm. "$constant" DynaTerm/null_term source-file [ast])
    (case [(.name ast) (.arity ast)]
      ["$escaped" 1] (get ast 0) ;; then this is hitting something that is "unescaped" so we do not have to keep this around
      (let [arguments (doall (map #(convert-from-escaped-ast-to-ast % source-file) (.arguments ast)))
            ;; the arguments are going to be wrapped in $quote if they are the same
            ;; so if all of the
            all-consts (every? true? (map #(and (= "$constant" (.name ^DynaTerm %))
                                                (= 1 (.arity ^DynaTerm %)))
                                          arguments))]
        (if all-consts
          (DynaTerm. "$constant" [(DynaTerm. (.name ast) DynaTerm/null_term source-file (vec (map #(get % 0) arguments)))]) ;; if this does not have nested structure, then can optimize and just use a constant structure
          (DynaTerm. "$quote1" [(DynaTerm. (.name ast) DynaTerm/null_term source-file arguments)]))))))

(def ^{:private true :dynamic true} *do-not-use-with-key* false)

(defn convert-from-ast [^DynaTerm ast out-variable variable-name-mapping source-file]
  ;; convert from the ast into an R-expr which can then be evaluated
  ;; the AST is a DynaTerm object, it should come from the parser.  It could also get generated by the user's program
  ;; out-variable is whatever variable represents the resulting expression.  In the AST, everything returns a "value", so
  (let [source-file (cond
                      (instance? URL source-file) source-file
                      (= "REPL" source-file) current-dir
                      :else (???) ;; unsure what to do in this case?
                      )
        project-out-vars (transient #{})
        other-conjunctive-rexprs (transient [])
        make-intermediate-var (fn []
                                (let [tmp-var-name (str (gensym "$intermediate_var_"))
                                      var (make-variable tmp-var-name)]
                                  (conj! project-out-vars var)
                                  var))
        get-value (fn [^DynaTerm a]
                    ;; conver an AST in its value.  This can either just return something from the AST if it is a variable or a constant, otherwise
                    ;; this has to construct other R-exprs which correspond with the evaluating of the node
                    (when-not (instance? DynaTerm a)
                      (throw (RuntimeException. (str "badly formed AST\nexpected a value such as $variable(\"name\") or $constant(123)\ninstead got: " a))))
                    (case (.name a)
                      "$variable" (let [[name] (.arguments a)
                                        var (get variable-name-mapping name)]
                                    (when (nil? var)
                                      (throw (RuntimeException. (str "Did not find variable " name))))
                                    var)
                      "$constant" (let [[val] (.arguments a)]
                                    (when (is-constant? val)
                                      (debug-repl))
                                    (make-constant val))
                      ;; this is something else which is getting called.  This means that we have to recurse into the structure and add the arguments
                      (let [ret-var (make-intermediate-var)]
                        (conj! other-conjunctive-rexprs
                               (binding [*do-not-use-with-key* false]
                                 (convert-from-ast a ret-var variable-name-mapping source-file)))
                        ret-var)))
        get-arg-values (fn [args]
                         ;; map from a list of arguments to their values represented as variables in R-exprs
                         (map get-value args))
        ]
    (let [constructed-rexpr
          (case [(.name ast) (.arity ast)] ;; this should match on name and arity
            ["$compiler_expression" 1] (let [^DynaTerm arg1 (get ast 0)]
                                         (case (.name arg1)
                                           "import" (let [imported-filename (if (= (.arity arg1) 2)
                                                                              (get arg1 1)
                                                                              (get arg1 0))
                                                          lfilename (if-not (.endsWith ^String imported-filename ".dyna")
                                                                                   (str imported-filename ".dyna")
                                                                                   imported-filename)
                                                          file (URL. source-file lfilename)
                                                          file (try
                                                                 (do (import-file-url file)
                                                                     file)
                                                                 (catch FileNotFoundException e
                                                                   ;; attempt to import a file from the resources which are built in
                                                                   (let [rf (resource (str "dyna/builtin_libraries/" lfilename))]
                                                                     (try
                                                                       (do (import-file-url rf)
                                                                           rf)
                                                                       (catch FileNotFoundException e2
                                                                         (throw e))))))]
                                                      ;(import-file-url file)
                                                      (let [imported-names (if (= (.arity arg1) 2)
                                                                             (.list_to_vec ^DynaTerm (get arg1 0))
                                                                             ;; then this should lookup the exported terms
                                                                             (get @system/user-exported-terms file))]
                                                        (doseq [imported-term imported-names]
                                                          (match-term imported-term ("/" name arity)
                                                                      (update-user-term! {:name name
                                                                                         :arity (int arity)
                                                                                         :source-file source-file}
                                                                                        (fn [o]
                                                                                          (assoc o :imported-from-another-file {:source-file file
                                                                                                                                :name name
                                                                                                                                :arity arity})))))))

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
                                           ;; of a function in place.
                                           "export" (match-term arg1 ("export" ("/" lname larity))
                                                                (swap! system/user-exported-terms
                                                                       (fn [o]
                                                                         (assoc o source-file (conj (get o source-file #{})
                                                                                                    (DynaTerm. "/" [lname larity]))))))

                                           ;; some of the arugments to a function should get escaped escaped, or quoted
                                           ;; used like `:- dispose foo(quote1,eval).`
                                           "dispose" (let [^DynaTerm disp-term (get arg1 0)
                                                           disp-arg-map (vec (map #({"*" "$eval"
                                                                                     "&" "$quote1"
                                                                                     "&&" "$constant"
                                                                                     "eval" "$eval"
                                                                                     "quote1" "$quote1"
                                                                                     "quote" "$constant"
                                                                                     (DynaTerm. "quote1" []) "$quote1"
                                                                                     (DynaTerm. "quote" []) "$constant"
                                                                                     (DynaTerm. "eval" []) "$eval"} % "$eval")
                                                                                  (.arguments disp-term)))]
                                                       (update-user-term! {:name (.name disp-term)
                                                                          :arity (.arity disp-term)
                                                                          :source-file source-file}
                                                                         (fn [o]
                                                                           (let [ret (assoc o :dispose-arguments disp-arg-map)]
                                                                             ret))))

                                                       ;; mark a function as being a macro, meaning that it gets its argument's AST and will return an AST which should get evaluated
                                                       ;; used like `:- macro foo/3.`

                                           "macro" (match-term arg1 ("macro" ("/" name arity))
                                                               (update-user-term! {:name name
                                                                                  :arity arity
                                                                                  :source-file source-file}
                                                                                 (fn [o]
                                                                                   (assoc o :is-macro true))))
                                           ;; make a term global so that it can be referenced form every file
                                           ;; I suppose that there should be some global list of terms which will get resolved at every possible point
                                           ;; use like `:- make_global_term foo/3.`
                                           "make_system_term" (match-term arg1 ("make_system_term" ("/" name arity))
                                                                          (let [call-name {:name name
                                                                                           :arity arity
                                                                                           :source-file source-file}
                                                                                rexpr (make-no-simp-user-call call-name
                                                                                                      (into {} (map #(let [x (make-variable (str "$" %))] [x x])
                                                                                                                    (range (+ arity 1))))
                                                                                                      0 {})
                                                                                ]
                                                                            (when (is-multiplicity? rexpr) (debug-repl))
                                                                            (swap! system/globally-defined-user-term
                                                                                   assoc [name arity] rexpr)))

                                           "make_global_term" (match-term arg1 ("make_global_term" ("/" name arity))
                                                                          (debug-repl)
                                                                          ;; a global term should represent something like $memo or $priority which can be defined anywhere
                                                                          ;; but should still reference the same functor.

                                                                          ;; I suppose that we can also define something like $memo_internal which would reference $memo by directing through the prelude or something
                                                                          (???) ;; TODO
                                                                          )

                                           "memoize_unk" (match-term arg1 ("memoize_unk" ("/" name arity))
                                                                     (let [call-name {:name name
                                                                                      :arity arity
                                                                                      :source-file source-file}]
                                                                       (set-user-term-as-memoized call-name :unk)))
                                           "memoize_null" (match-term arg1 ("memoize_null" ("/" name arity))
                                                                      (let [call-name {:name name
                                                                                       :arity arity
                                                                                       :source-file source-file}]
                                                                        (set-user-term-as-memoized call-name :null)))

                                           "memoize_none" (match-term arg1 ("memoize_none" ("/" name arity))
                                                                      (let [call-name {:name name
                                                                                       :arity arity
                                                                                       :source-file source-file}]
                                                                        (set-user-term-as-memoized call-name :none)))

                                           "print_memo_table" (match-term arg1 ("print_memo_table" ("/" name arity))
                                                                          (let [call-name {:name name
                                                                                           :arity arity
                                                                                           :source-file source-file}]
                                                                            (print-memo-table call-name)))

                                           ;; "import_csv" (let [[term-name term-arity file-name] (.arguments ^DynaTerm (get arg1 0))]
                                           ;;                ;; import some CSV file as a term
                                           ;;                ;; this could get represented as a R-expr?  In which case it would not be represented
                                           ;;                (???))
                                           "export_csv" (???) ;; export a CSV file for a term after the program is done running

                                           "run_agenda" (system/run-agenda)

                                           "load_clojure" (match-term arg1 ("load_clojure" cfile)
                                                                      (load cfile))

                                           "$clojure" (match-term arg1 ("$clojure" clojure-string)
                                                                  (let [clj-code (read-string clojure-string)]
                                                                    (binding [*ns* (create-ns 'dyna.evaluated-user-code)]
                                                                      (require '[clojure.core :refer :all])
                                                                      (require '[dyna.core :refer :all])
                                                                      (eval clj-code))))

                                           "optimized_rexprs" (match-term arg1 ("optimized-rexprs" c)
                                                                          (alter-var-root system/*use-optimized-rexprs* (if c true false)))

                                           (let [arity (.arity arg1)
                                                 call-name {:name (str "$pragma_" (.name arg1))
                                                            :arity arity
                                                            :source-file (or (.from_file ast) source-file)}
                                                 user-term (get-user-term call-name)]
                                             (when-not (:is-macro user-term false)
                                               (throw (DynaUserError. (str "pragma " (.name arg1) "/" arity " not found"))))

                                             (let [call-vals (map make-constant (.arguments arg1))
                                                   macro-out (make-intermediate-var)
                                                   var-map (merge {(make-variable (str "$" arity)) macro-out}
                                                                  (zipmap (map #(make-variable (str "$" %)) (range)) call-vals))
                                                   ret (make-conjunct [(make-user-call
                                                                        call-name
                                                                        var-map
                                                                        0 {})
                                                                       (make-eval-from-ast out-variable
                                                                                           macro-out
                                                                                           variable-name-mapping
                                                                                           source-file)])]
                                               (assert (empty? variable-name-mapping))
                                               (let [rr (simplify-top ret)]
                                                 (assert (= (make-multiplicity 1) rr))
                                                 #_(debug-repl "compiler expression macro")
                                                 rr)))

                                           #_(do
                                             ;; in the case that this is invalid, we can raise an exception that should report the error to the user
                                             (when print-parser-errors
                                               (println (str "Compiler operation " (.name arg1) "not found")))
                                             )
                                           ;(???) ;; there should be some invalid parse expression or something in the case that this fails at this point
                                           )
                                         (make-unify out-variable (make-constant true)) ;; just return that we processed this correctly?  I suppose that in
                                         )

            ["$define_term" 4] (let [[head dynabase aggregator body] (.arguments ^DynaTerm ast)
                                     new-body (make-comma-conjunct
                                               (apply make-comma-conjunct (for [[idx arg] (zipseq (range) (.arguments ^DynaTerm head))]
                                                                            (DynaTerm. "$unify" [(DynaTerm. "$variable" [(str "$" idx)])
                                                                                                 arg])))
                                               (DynaTerm. "$unify" [(DynaTerm. "$variable" ["$self"])
                                                                    ;; if this is unified with a constant, then it can get removed via project?
                                                                    ;; but $self isn't projected out...., so it doesn't get removed
                                                                    (if (not (dnil? dynabase))
                                                                      (DynaTerm. "$dynabase_access" [dynabase])
                                                                      (DynaTerm. "$constant" [DynaTerm/null_term]))])
                                               body)
                                     ;dynabase-name (if-not (dnil? dynabase) (.name ^DynaTerm dynabase) DynaTerm/null_term)
                                     new-ast (DynaTerm. "$define_term_normalized"
                                                        [(.name ^DynaTerm head)
                                                         (.arity ^DynaTerm head)
                                                         source-file
                                                         dynabase
                                                         aggregator
                                                         new-body])]
                                 (make-eval-from-ast out-variable (make-constant new-ast) {} source-file))
            ["$define_term_normalized" 6] (let [[functor-name functor-arity source-file dynabase aggregator body] (.arguments ^DynaTerm ast)
                                                all-variables (find-term-variables body)
                                                aggregator-result-variable (make-variable (str "$" functor-arity))
                                                argument-variables (merge ;; these are the variables which are arguments to this
                                                                    (into {} (for [i (range functor-arity)]
                                                                               [(str "$" i) (make-variable (str "$" i))]))
                                                                    {"$self" (make-variable "$self")})
                                                ;; anything which matches these patterns should not be the variables which are present
                                                project-variables (filter
                                                                   #(not (re-matches #"\$self|\$[0-9]+" %)) ;; if dynabase, then self is also a parameter
                                                                   #_(if (not (dnil? dynabase))

                                                                     #(not (re-matches #"\$[0-9]+" %)))
                                                                   all-variables)
                                                project-variables-map (into {} (for [v project-variables]
                                                                                 [v (make-variable v)]))
                                                incoming-variable (make-variable (str (gensym "$incoming_variable_")))
                                                body-rexpr (convert-from-ast body
                                                                             incoming-variable
                                                                             (merge {"$functor_name" (make-constant functor-name)
                                                                                     "$functor_arity" (make-constant functor-arity)}
                                                                                    project-variables-map
                                                                                    argument-variables
                                                                                    (when (dnil? dynabase)
                                                                                      {"$self" (make-constant DynaTerm/null_term)}))
                                                                             source-file)
                                                rexpr (make-no-simp-aggregator aggregator
                                                                               aggregator-result-variable
                                                                               incoming-variable
                                                                               true ;; meaning that the body is conjunctive, so if the result of the body is 0, the the aggregator will be 0 also (instead of identity)
                                                                               (make-proj-many (vals project-variables-map)
                                                                                               body-rexpr))]
                                            (when (get @system/globally-defined-user-term [functor-name functor-arity])
                                              (throw (DynaUserError. (str "The term " functor-name "/" functor-arity " is a system defined term, unable to redefine"))))

                                            (add-to-user-term source-file dynabase functor-name functor-arity
                                                              (optimize-rexpr rexpr))
                                            ;; the result from the expression should just be to unify the out variable with true
                                            ;; ideally, this would check if the expression corresponds with
                                            (make-unify out-variable (make-constant true)))

            ["$inline_function" 3] (let [[extra-head-args agg disjuncts] (.arguments ast)
                                         has-extra-args (not= DynaTerm/null_term extra-head-args)
                                         extra-var-list (if has-extra-args (.arguments ^DynaTerm extra-head-args))
                                         disjunct-v (.list_to_vec ^DynaTerm disjuncts)
                                         all-c-vars (apply union (map find-all-variables disjunct-v))
                                         pass-ctx-vars (vec (difference
                                                             (intersection all-c-vars (into #{} (keys variable-name-mapping)))
                                                             (into #{} extra-var-list)))
                                         arg-vars (concat pass-ctx-vars (map #(get % 0) extra-var-list))
                                         generated-name (str (gensym "$anon_function_"))
                                         new-head (DynaTerm. generated-name (vec (map #(DynaTerm. "$variable" [%]) arg-vars)))
                                         call-ast (DynaTerm. generated-name (vec (map #(DynaTerm. "$variable" [%]) pass-ctx-vars)))]
                                     (doseq [d disjunct-v]
                                       (let [r (convert-from-ast (DynaTerm. "$define_term" [new-head
                                                                                            DynaTerm/null_term
                                                                                            agg
                                                                                            d])
                                                                 (make-constant true)
                                                                 {} source-file)]
                                         (assert (= r (make-multiplicity 1)))))
                                     ;; if () is present for the arguments, then that will make the expression quote the reference to the anon function
                                     ;; rather than just evaluate it in place
                                     (convert-from-ast (if has-extra-args (DynaTerm. "$quote1" [call-ast]) call-ast)
                                                       out-variable
                                                       variable-name-mapping
                                                       source-file))

            ;; it is possible to just write something like `X,123`, but that is odd....
            ;; I suppose that we might as well suppot this here, but I don't think this will actually get used
            ["$constant" 1] (let [[value] (.arguments ast)]
                              (make-unify (make-constant value) out-variable))

            ["$variable" 1] (let [[name] (.arguments ast)
                                  var (get variable-name-mapping name)]
                              (assert (not (nil? var)))
                              (assert (string? name)) ;; we should not be allowing variables to take on the names of structures
                              (make-unify var out-variable))

            ["$quote1" 1] (let [[^DynaTerm quoted-structure] (.arguments ast)
                                name (.name quoted-structure)
                                vals (get-arg-values (.arguments quoted-structure))
                                ;; in the case that something comes from a top level
                                ;; dynabase (if (contains? variable-name-mapping "$self")
                                ;;            (get variable-name-mapping "$self")
                                ;;            (make-constant DynaTerm/null_term))
                                structure (make-unify-structure out-variable
                                                                source-file
                                                                (make-constant DynaTerm/null_term) ;dynabase
                                                                name ;; the name of the structure
                                                                vals)]
                            structure)

            ;; ["$quote" 1] (let [[^DynaTerm quoted-structure] (.arguments ast)]
            ;;                (make-unify out-variable (make-constant quoted-structure)))

            ["$escaped" 1] (let [[escaped-expression] (.arguments ast)
                                 basic-ast (convert-from-escaped-ast-to-ast escaped-expression source-file)]
                             (convert-from-ast basic-ast out-variable variable-name-mapping source-file))

            ["$dynabase_quote1" 2] (let [[dynabase ^DynaTerm quoted-structure] (.arguments ast)
                                         name (.name quoted-structure)
                                         vals (get-arg-values (.arguments quoted-structure))
                                         dbval (get-value dynabase)
                                         structure (make-unify-structure out-variable
                                                                         source-file
                                                                         dbval
                                                                         name
                                                                         vals)
                                         ;; we have to do this twice, as make-unify-structure can ignore dbval to make the unification "go through"
                                         ;; meta-struct (make-unify-structure-get-meta out-variable
                                         ;;                                            dbval
                                         ;;                                            (make-intermediate-var) ;; we do not care about the file which this comes from, so we just ignore this
                                         ;;                                            )
                                         ]
                                     ;; (debug-repl "db quote")
                                     ;; (???)
                                     ;(make-conjunct [structure meta-struct])
                                     structure)

            ["$dynabase_call" 2] (let [[dynabase-var call-term] (.arguments ast)
                                       dynabase-val (get-value dynabase-var)
                                       call-vals (get-arg-values (.arguments call-term))
                                       arity (count call-vals)
                                       call-name {:name (.name call-term) ;; the name arity.  When a dynabase is called, there is no filename on the name qualifier, as it requires that it can be exported across files etc
                                                  :arity arity}
                                       ;; I suppose that a dynabase could also have some additional variable like :dynabase true so that the functor names of a dynabase are seperate from other terms?
                                       ]
                                   (make-user-call
                                    call-name
                                    (merge
                                     {(make-variable "$self") dynabase-val
                                      (make-variable (str "$" arity)) out-variable}
                                     (into {} (for [[i v] (zipseq (range) call-vals)]
                                                [(make-variable (str "$" i)) v]))
                                     (when *do-not-use-with-key*
                                       {(make-variable "$do_not_use_with_key") (make-constant true)}))
                                    0 ;; the call depth
                                    {})  ;; the set of arguments which need to get avoid
                                   )

            ;; TODO: we shouldn't have to capure constant values into the
            ;; dynabase representation.  Each dynabase can only be created at
            ;; one point in the program.  This means that the constant values would not need to get captured
            ["$dynabase_create" 2] (let [[extended-dynabase-value dynabase-terms] (.arguments ast)
                                         remap-captured-name (fn [n]
                                                               (cond (= n "$self") "$parent"
                                                                     (re-matches #"\$[0-9]+" n) (str "$construct_arg_" n)
                                                                     :else n))
                                         dynabase-captured-variables (into {} (for [[k v] variable-name-mapping]
                                                                                (when-not (is-constant? v)
                                                                                  [(remap-captured-name k) (DynaTerm. "$variable" [k])])))
                                         has-super (not= DynaTerm/null_term extended-dynabase-value)
                                         referenced-variables (vec (keys dynabase-captured-variables))
                                         dbase-name (make-new-dynabase-identifier has-super referenced-variables)
                                         dynabase-term-access (DynaTerm. dbase-name (vec (map #(DynaTerm. "$variable" [%]) referenced-variables)))
                                         dynabase-term-create (DynaTerm. dbase-name (vec (map dynabase-captured-variables referenced-variables)))
                                         rexpr (make-dynabase-constructor dbase-name
                                                                          (vec (map #(get-value (dynabase-captured-variables %)) referenced-variables))
                                                                          (if (not= DynaTerm/null_term extended-dynabase-value)
                                                                            (get-value extended-dynabase-value)
                                                                            (make-constant DynaTerm/null_term))
                                                                          out-variable)]
                                     (when (not= dynabase-terms DynaTerm/null_term)
                                       ((fn mkt [^DynaTerm trm]
                                          (let [^DynaTerm dt (if (= "," (.name trm)) (get trm 0) trm)]
                                            (cond (= (.name dt) ",") (do (mkt (get dt 0))
                                                                         (mkt (get dt 1)))
                                                  (= (.name dt) "$define_term") (let [[name odb aggregator body] (.arguments dt)]
                                                                                  (assert (= odb DynaTerm/null_term))
                                                                                  (let [res (convert-from-ast (DynaTerm. "$define_term"
                                                                                                                         [name
                                                                                                                          dynabase-term-access
                                                                                                                          aggregator
                                                                                                                          body])
                                                                                                              (make-constant true)
                                                                                                              ;; constant values can just be passed through duing the conversion
                                                                                                              (into {}
                                                                                                                    (map (fn [[a b]] [(remap-captured-name a) b])
                                                                                                                         (filter #(is-constant? (second %))
                                                                                                                                 variable-name-mapping)))
                                                                                                              source-file)]
                                                                                    (assert (= res (make-multiplicity 1)))))
                                                  :else (do
                                                          (debug-repl "dynabase unsupported body type")
                                                          (???)))
                                            (when (= "," (.name trm)) (recur (get trm 1)))))
                                        dynabase-terms))
                                     rexpr)

            ["$dynabase_access" 1] (let [[^DynaTerm dbase] (.arguments ast)
                                         dbase-name (.name dbase)
                                         dbase-arity (.arity dbase)
                                         args (vec (map get-value (.arguments dbase)))
                                         rexpr (make-dynabase-access dbase-name out-variable args)]
                                     rexpr)

            ["$self" 0] (let [svar (get-value (DynaTerm. "$variable" ["$self"]))]
                          ;; $self looks like an atom, but it is actually a variable that is getting remapped..
                          ;; this could probably also be done using a macro in the prelude, but I don't want to have dynabases be dependent on the prelude loading
                          (make-unify out-variable svar))

            ;; this is only taking the "named" variables, so something that is "returned" is not included.  I suppose that should be ok?
            ;; the return variables are also going
            ["$self_term_uid" 0] (let [tkeys (sort (keys variable-name-mapping))
                                       tvals (conj (vec (map #(get variable-name-mapping %) tkeys))
                                                   (make-constant source-file))]
                                   ;; this should capture all of the variable names.  This would be used by random or something
                                   ;; if there was random(0,1), I suppose that could just be a macro which expands into something which will also
                                   ;; reference this variable
                                   (make-unify-structure out-variable
                                                         source-file
                                                         (make-constant DynaTerm/null_term) ;; no dynabase
                                                         "$term_ref"
                                                         tvals))

            ;; the assert can run inline, so it will check some statement before everything has been parsed
            ;; this will make writing tests for something easy
            ["$assert" 4] (let [[expression text-rep line-number wants-to-succeed] (.arguments ast)
                                all-variable-names (find-term-variables expression)
                                ;; this should construct some assert= aggregator, which will check some expression for "all" of the values
                                ;; which would mean that it identifies which of the expressions
                                variable-name-mapping (into {} (for [n all-variable-names] [n (make-variable n)]))
                                rexpr (make-proj-many (vals variable-name-mapping)
                                                      (convert-from-ast expression (make-constant true) variable-name-mapping source-file))
                                run-agenda-zzz (system/maybe-run-agenda)
                                result (simplify-top rexpr)]
                            (when-not (= wants-to-succeed (= result (make-multiplicity 1)))
                              (if dyna.utils/debug-on-assert-fail
                                (debug-repl (str "user program assert failed: " text-rep))) ;; when in debug mode, stop here when an assert fails
                              (throw (DynaUserAssert. source-file line-number text-rep result)))
                            (make-unify out-variable (make-constant true))) ;; if the assert fails, then it will throw some exception

            ["$warning" 3] (let [[warning-text line-number check-expression] (.arguments ast)]
                             ;; should a warning somehow check arguments to a dynabase or something?
                             ;; I suppose at the top level, this can just check the current assignments to variables and print something
                             ;; inside of a dynabase, it might want to defer the checking until there are bindings to variables?  Though that
                             ;; would be like haivng some function which defers until there is a construction of a dynabase.

                             (???))

            ["$print" 3] (let [[expression text-rep line-number] (.arguments ast)
                               all-variable-names (find-term-variables expression)
                               result-variable (make-variable 'Result)
                               variable-map (into {} (for [v all-variable-names] [v (make-variable v)]))
                               rexpr (convert-from-ast expression result-variable variable-map source-file)
                               agenda-run-zzz (system/maybe-run-agenda)
                               ctx (context/make-empty-context rexpr)
                               result (context/bind-context-raw ctx (simplify-fully rexpr))
                               rel-path (if (instance? URL source-file)
                                          (str (.relativize current-dir-path (Paths/get (.toURI source-file))))
                                          (str source-file))]
                           (println "=================================================")
                           (println "Print from line" (str "`" rel-path ":" line-number "`") "Query:" text-rep )
                           (if (= (make-multiplicity 1) result)
                             (println (ctx-get-value ctx result-variable))
                             (println "Rexpr:" (ctx-exit-context ctx result)))
                           (println "=================================================")
                           (make-unify out-variable (make-constant true)))

            ["$_debug_repl" 3] (let [[expression text-rep line-number] (.arguments ast)
                                     all-variable-names (find-term-variables expression)
                                     result-variable (make-variable 'Result)
                                     variable-map (into {} (for [v all-variable-names] [v (make-variable v)]))
                                     rexpr (convert-from-ast expression result-variable variable-map source-file)
                                     ctx (context/make-empty-context rexpr)
                                     result (context/bind-context-raw ctx (simplify-fully rexpr))]
                                 (debug-repl "user program debug repl")
                                 (make-unify out-variable (make-constant true)))

            ["$query" 3] (let [[expression text-rep line-number] (.arguments ast)
                               all-variables-names (find-term-variables expression)
                               result-var (make-variable "$query_result_var")
                               all-variables (find-term-variables expression) ;; if there is an nested aggregator, those are not found, just the exposed variables
                               variable-map (into {} (map (fn [x] [x (make-variable x)]) all-variables))
                               rexpr (convert-from-ast expression result-var variable-map source-file)]
                           (simplify-rexpr-query [text-rep line-number] rexpr)
                           (make-unify out-variable (make-constant true)))

            ["$external_value" 1] (let [[value-index] (.arguments ast)]
                                    (make-unify
                                     out-variable
                                     (make-constant (system/parser-external-value value-index))))

            ["$with_key" 2] (let [[expression-value with-key-expression] (.arguments ast)
                                  has-dynabase (not (and (is-constant? (get variable-name-mapping "$self"))
                                                         (dnil? (:value (get variable-name-mapping "$self") :not-found))))
                                  call-name (if has-dynabase
                                              {:name (:value (get variable-name-mapping "$functor_name"))
                                               :arity (:value (get variable-name-mapping "$functor_arity"))}
                                              {:name (:value (get variable-name-mapping "$functor_name"))
                                               :arity (:value (get variable-name-mapping "$functor_arity"))
                                               :source-file source-file})
                                  rterm (make-term ("$quote1" ("$with_key" expression-value with-key-expression)))]
                              ;; this needs to mark a functor as using with-key.  This will let the aggregator wrap the result in $value to unpack it
                              (update-user-term! call-name (fn [x] (assoc x :has-with-key true)))
                              (convert-from-ast rterm out-variable variable-name-mapping source-file)
                              ;(debug-repl "TODO: getting value from with_key")
                              ;(???)
                              )

            ["$call_without_with_key" 1] (let [[rterm] (.arguments ast)]
                                           ;; generate a call expression which marks that it should not use with-key
                                           (binding [*do-not-use-with-key* true]
                                             (convert-from-ast rterm out-variable variable-name-mapping source-file)))


            ;; we special case the ,/2 operator as this allows us to pass the info that the first expression will get unified with a constant true earlier
            ;; this should make some generation steps more efficient
            ["," 2]  (let [[a b] (.arguments ast)]
                       (make-conjunct [(convert-from-ast a
                                                         (make-constant true)
                                                         variable-name-mapping
                                                         source-file)
                                       (convert-from-ast b
                                                         out-variable
                                                         variable-name-mapping
                                                         source-file)]))

            ;; the evaluate statements need to have additional context such as the variables from the local context
            ;; or the reference to the current file
            ["$eval" 1] (let [[string-arg] (.arguments ast)
                              arg-val (get-value string-arg)
                              ast-var (make-intermediate-var)]
                          (make-conjunct [(make-ast-from-string ast-var arg-val)
                                          (make-eval-from-ast out-variable
                                                              ast-var
                                                              variable-name-mapping
                                                              source-file)]))
            ["$eval_ast" 1] (let [[ast-arg] (.arguments ast)
                                  ast-var (get-value ast-arg)]
                              (make-eval-from-ast out-variable
                                                  ast-var
                                                  variable-name-mapping
                                                  source-file))
            ["$eval_toplevel" 1] (let [[string-arg] (.arguments ast) ;; this could just be a normal function, as it does not require
                                       arg-val (get-value string-arg)
                                       ast-var (make-intermediate-var)]
                                   (make-conjunct [(make-ast-from-string ast-var arg-val)
                                                   (make-eval-from-ast out-variable
                                                                       ast-var
                                                                       {}
                                                                       source-file)]))
            ["$eval_toplevel_ast" 1] (let [[ast-arg] (.arguments ast)
                                           ast-var (get-value ast-arg)]
                                       (make-eval-from-ast out-variable
                                                           ast-var
                                                           {}
                                                           source-file))
            ["$file" 0] (make-unify out-variable (make-constant source-file))

            ;; TODO: this should better support stuff like require and using, where it would lift the require statements outside of the function
            ["$clojure" 1] (let [[clojure-const-str] (.arguments ast)]
                             (when (not= (.name ^DynaTerm clojure-const-str) "$constant")
                               (throw (RuntimeException. "Syntax error, $clojure only works on constant strings")))
                             (let [clojure-str (get clojure-const-str 0)
                                   arguments (vec (filter #(re-matches #"[\$a-zA-Z][\$a-zA-Z0-9\-\_]*" %) (keys variable-name-mapping)))
                                   arguments-symbols (vec (map symbol arguments))
                                   arguments-vars (vec (map variable-name-mapping arguments))
                                   clojure-sl (read-string clojure-str)
                                   func (binding [*ns* (create-ns 'dyna.evaluated-user-code)]
                                          (require '[clojure.core :refer :all])
                                          (require '[dyna.core :refer :all])
                                          (eval `(fn ~arguments-symbols
                                                   ~clojure-sl)))
                                   ret (make-function-call func out-variable arguments-vars)]
                               ret))


            #_(let [[clojure-string] (.arguments ast)

                                 string-val (get-value clojure-string)
                                 zzz (debug-repl)
                                        ;clojure-ast (read-string clojure-string)
                                 arguments (vec (filter #(re-matches #"[\$a-zA-Z][\$a-zA-Z0-9\-\_]*" %) (keys variable-name-mapping)))
                                 arguments-symbols (vec (map symbol arguments))
                                 arguments-vars (vec (map variable-name-mapping arguments))
                                 clojure-str (read-string (dyna.base-protocols/get-value string-val))
                                 clojure-fn (eval `(fn ~arguments-symbols
                                                     ~clojure-str))
                                 #_(do (???) ;; require the string is a constant for now to make this simpler
                                     ;; (eval `(fn ~(conj arguments-symbols '$$clojure-eval-string)
                                     ;;            (eval-with-locals {~@(flatten (for [a arguments-symbols]
                                     ;;                                            [`(quote ~a) a]))}
                                     ;;                              (read-string ~'$$clojure-eval-string))))
                                     )
                                 ret (make-function-call clojure-fn out-variable arguments-vars)
                                 ]
                             ret)

            ["$syntax_error" 1] (let [[message] (.arguments ast)]
                                  (throw (RuntimeException. (str "Syntax Error: " message))))

            ;; call without any qualification on it.  Just generate the user term
            (let [arity (.arity ast)
                  call-name {:name (.name ast) ;; the name, arity and file name.  This makes the file work as a hard local scope for the function
                             :arity arity
                             :source-file (or (.from_file ast) source-file) ;; the if there file name annotation on the term, then use that rather than the local file
                             }
                  user-term (get-user-term call-name) ;; this can return a user or system term
                  is-macro (:is-macro user-term false)
                  dispose-arguments (:dispose-arguments user-term)
                  call-vals (doall (if is-macro
                                     (map make-constant (.arguments ast))
                                     (get-arg-values
                                      (if dispose-arguments
                                        ;; if the nested term is a variable, then we don't want to quote it or something???
                                        (map (fn [arg disp] (if (not= disp "$eval")
                                                              (DynaTerm. disp [arg])
                                                              arg))
                                             (.arguments ast) dispose-arguments)
                                        (.arguments ast)))))
                  local-out (if is-macro
                              (make-intermediate-var)
                              out-variable)
                  var-map (merge {(make-variable (str "$" arity)) local-out}
                                 (zipmap (map #(make-variable (str "$" %)) (range)) call-vals)
                                 (when *do-not-use-with-key*
                                   {(make-variable "$do_not_use_with_key") (make-constant true)})
                                 #_(when is-macro
                                   ;; only variables that match $[0-9]+ are exposed... so will pass these with large values
                                   {(make-variable "$1000000") (make-constant (str source-file))
                                    (make-variable "$1000001") (get variable-name-mapping "$functor_name" (make-constant "REPL"))
                                    (make-variable "$1000002") (get variable-name-mapping "$functor_arity" (make-constant 0))
                                    (make-variable "$1000003") (make-constant (DynaTerm/make_list (keys variable-name-mapping)))}))
                  call-rexpr (make-user-call
                              call-name
                              var-map
                              0 ;; call depth
                              {}
                              )
                  full-rexpr (if is-macro
                               (make-conjunct [call-rexpr
                                               (make-eval-from-ast out-variable
                                                                   local-out
                                                                   variable-name-mapping
                                                                   source-file)])
                               call-rexpr)]
              full-rexpr))]
      ;; add the R-expr that we constructed to the conjunctive R-exprs
      (conj! other-conjunctive-rexprs constructed-rexpr)
      ;; project out all of the variables which were added as intermediate expressions along the way
      (let [pvars (persistent! project-out-vars)
            cr (make-conjunct (persistent! other-conjunctive-rexprs))]
        (make-proj-many pvars cr)))))


;; this will be something that could be used by some user level operation
;; the program will have that the names of variables can be controlled
;; (def-base-rexpr eval-from-ast-dmap [:var out-variable
;;                                     :var ast
;;                                     :var dyna-variable-name-mapping ;; this is like the above, but the map should instead be a dynaMap which means that it can be constructed by the user to set the "context" in which some ast would be evaluated in
;;                                     :file-name source-file])



(defn get-parser-print-name [token]
  (.getDisplayName dyna.dyna_grammar2Lexer/VOCABULARY token))

(def parse-error-handler
  (proxy [org.antlr.v4.runtime.DefaultErrorStrategy] []
    ;; (reportError [recognizer exception]
    ;;   ;; this is going to just be called in the general case, so I suppose that if this is not defined, then
    ;;   ;; this is going to try and report some error
    ;;   (debug-repl)
    ;;   (println "report error" exception))
    (reportFailedPredicate [recognizer exception]
                                        ;(debug-repl)
      (when print-parser-errors
        (println "==========> report failed predicate" exception)))
    (reportInputMismatch [recognizer exception]
                                        ;(debug-repl)
      (when print-parser-errors
        (println "==========> report input missmatch" exception)))
    (reportNoViableAlternative [recognizer exception]
      (when print-parser-errors
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
          (println "===================================================================================================="))))
    (reportUnwantedToken [recognizer]
      (when print-parser-errors
        (println "=============> unwanted token")))))

(def lexer-error-handler
  (proxy [org.antlr.v4.runtime.ConsoleErrorListener] []
    (syntaxError [recognizer offendingSymbol line charPositionInLine msg e]
      (when print-parser-errors
        (proxy-super syntaxError recognizer offendingSymbol line charPositionInLine msg e))
      (throw (RuntimeException. "syntax error" e)))))



(defn run-parser [^CharStream stream & {:keys [fragment-allowed] :or {fragment-allowed false}}]
  (let [lexer (doto (dyna.dyna_grammar2Lexer. ^CharStream stream)
                (.removeErrorListeners)
                (.addErrorListener lexer-error-handler))
        token-stream (UnbufferedTokenStream. lexer)
        parser (dyna.dyna_grammar2Parser. token-stream)]
    (comment
      (if run-parser-fast ;; there needs to be some way in which this can be
        ;; configured or something.  I suppose that this could
        ;; happen via flags or for large inputs
        (.setErrorHandler parser (BailErrorStrategy.))))
    (.setErrorHandler parser parse-error-handler)
    (let [r (if fragment-allowed
              (.eval_entry parser)
              (.program parser))
          e (.getNumberOfSyntaxErrors parser)]
      (if (not= e 0)
        (throw (RuntimeException. "syntax error")) ;; this would be nice if
        ;; there was more of an error
        ;; message, but this should
        ;; get printed out by the
        ;; parser I suppose
        (.rterm r)))))




(defn parse-string [^String s & {:keys [fragment-allowed] :or {fragment-allowed true}}]
  (let [char-stream (CharStreams/fromString ^String (str s "\n% end of string\n"))]
    (run-parser char-stream :fragment-allowed fragment-allowed)))

(defn parse-stream [istream & {:keys [fragment-allowed] :or {fragment-allowed false}}]
  (let [stream (java.io.BufferedInputStream. istream 4096)
        cstream (java.io.SequenceInputStream. stream
                                             (java.io.ByteArrayInputStream.
                                              (.getBytes ^String (str "\n\n%end of file\n\n"))))
        astream (dyna.ParserUnbufferedInputStream. cstream 1024)]
    (run-parser astream :fragment-allowed fragment-allowed)))


(defn parse-file [file-url]
  ;; this is going to want to take a java url object, and then parse that into something
  ;; this should consider using the file stream to handle
  ;;(println file-url)
  (let [url ^URL (if (string? file-url)
                   (URL. ^String file-url)
                   (do (assert (instance? URL file-url))
                     file-url))]
    (parse-stream (.openStream url)
                  :fragment-allowed false)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn eval-ast [ast]
  (make-eval-from-ast (make-constant true)
                      (make-constant ast)
                      {}
                      "REPL"))

(defn eval-string [^String s & {:keys [fragment-allowed] :or {fragment-allowed true}}]
  (eval-ast (parse-string s
                          :fragment-allowed fragment-allowed)))

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
             (if (contains? o url)
               (do (reset! do-import false)
                   o)
               (do
                 (reset! do-import true)
                 (conj o url)))))
    (if @do-import
      ;; then we have to be the one to import this file
      (let [parse (parse-file url)]
        (if (nil? parse)
          (when print-parser-errors
            (println (str "WARNING: file " url " did not contain any dyna rules")))
          (let [result (convert-from-ast parse (make-constant true) {} url)]
            (when-not (= result (make-multiplicity 1))
              (when print-parser-errors
                (println (str "failed to load file " url))
                (aprint result))
              ;(debug-repl "failed to load properly")
              (assert false))))))))



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
  :run-at [:standard :construction] ;; this should run at both standard time and construction
                                        ;:run-at :standard-and-construction ;; this should run when it is constructed and when it might have a ground variable
  (let [a (get-value ast)]
    (convert-from-ast a out-variable variable-name-mapping source-file)))


;; (def-rewrite
;;   :match (eval-from-ast (:any out) (:ground ast) ))
