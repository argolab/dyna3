(ns dyna.parser_interface)
;;   (:require [dyna.utils :refer :all])
;;   (:require [dyna.core])
;;   (:require [dyna.rexpr :refer :all])
;;   (:require [dyna.aggregators :refer [get-colon-equals-count]])
;;   (:require [clojure.set :refer [union difference]])
;;   (:import [org.antlr.v4.runtime CharStream CharStreams UnbufferedTokenStream]))

;; (gen-class
;;  :name "dyna.DynaParserInterfaceImpl"
;;  :prefix "-"
;;  :init "init"
;;  :constructors {[Object] []}
;;  :state state
;;  :implements [dyna.DynaParserInterface])

;; (def ^:private atom-init-state
;;   {:name nil
;;    :arguments []
;;    :aggregator nil
;;    :result-variable nil
;;    :conjunct-rexprs (list)
;;    :all-variables #{}
;;    :variables-unified {} ;; map of variables and anything that they are unified with
;;    :dynabase-unify-from-parent-variable nil ;; the variable which represents what we are called into from
;;    :dynabase-call-into-others-variable nil ;; what variable we should use in the case that we are generating a call

;;    :dynabase-name nil ;; the name which should be passed to the unify with dynabase object
;;    :dynabase-variables-names [] ;; the variable names which are present on this dynabase

;;    :is-annon-atom false
;;    })

;; (defn -init [arg]
;;   (require 'dyna.core)
;;   [[] (atom (if (map? arg)
;;               {:current-system arg
;;                ;; :dynabase {:variables []  ;; the variables which are externally referenced for the currnt dynabase
;;                ;;            :dynabase-value nil ;; if this is some file, then this should just be a value that can be unified in place for the dynabase
;;                ;;            :dynabase-name "-"} ;; whatever the generated name or filename is for the current dynabase
;;                :head-variable-names []
;;                :system nil ;; some pointer to whatever is the current collection of user defined expressions / system
;;                :current-filename "REPL" ;; what the current file name is that this is parsing from.  So $load should allow for relatitive imports of a file
;;                ;; something like $load() takes either 1 sor 2 arguments, this would return the handle to the root dynabase which represents the file
;;                ;; in the case that this has something that would represent which of the expressions might find
;;                :current-atom atom-init-state
;;                :current-dynabase {:inherits-from-variable nil
;;                                   :externally-visable-variables []  ;; these are names of variables in the order in which they are referenced from the surrounding context.  We might not know this until later, so should instead use the end-of-dynabase-callback to handle this

;;                                   }
;;                :parent-parser nil
;;                :end-of-atom-callbacks [] ;; functions which are called once all of the variables to the current atom are knwon
;;                :end-of-dynabase-callback nil

;;                }))])


;; ;; (defmacro update-interface [this & body]
;; ;;   `(swap! (.state ~this) (fn -'[old] ~@body)))

;; (defn -make_rexpr [^dyna.DynaParserInterfaceImpl this ^String name args]
;;   (apply construct-rexpr name args))

;; (defn -make_variable [^dyna.DynaParserInterfaceImpl this ^String name]
;;   (make-variable name))

;; (defn -make_unnamed_variable [^dyna.DynaParserInterfaceImpl this]
;;   ;; if there are things which are seralized and loaded from disk, then those might need to have their own variable names rather than the gensym names
;;   (make-variable (gensym)))

;; (defn -make_constant [^dyna.DynaParserInterfaceImpl this value]
;;   (make-constant value))

;; (defn- add-rexpr [^dyna.DynaParserInterfaceImpl this rexpr]
;;   (assert (satisfies? Rexpr rexpr))
;;   (if (not= rexpr (make-multiplicity 1))
;;     (swap! (.state this) (fn [old]
;;                            (let [new-state1 (assoc-in (assoc-in old [:current-atom :conjunct-rexprs]
;;                                                      (cons rexpr (get-in old [:current-atom :conjunct-rexprs])))
;;                                            [:current-atom :all-variables] (union (get-in old [:current-atom :all-variables])
;;                                                                                  (get-variables rexpr))
;;                                            )]
;;                              (if (is-unify? rexpr)
;;                                ;; then we should also track this with the unified expressions
;;                                (let [[var0 var1] (get-arguments rexpr)
;;                                      ufv0 (get-in new-state1 [:current-atom :variables-unified])
;;                                      ufv1 (if (is-constant? var0) ufv0
;;                                               (assoc ufv0 var0 (conj (get ufv0 var0 #{}) var1)))
;;                                      ufv2 (if (is-constant? var1) ufv1
;;                                               (assoc ufv1 var1 (conj (get ufv1 var1 #{}) var0)))
;;                                      ]
;;                                  (assoc-in new-state1 [:current-atom :variables-unified] ufv2))
;;                                new-state1
;;                                ))))))

;; (defn- get-with-default-var [^dyna.DynaParserInterfaceImpl this path]
;;   (let [x (get-in @(.state this) path)]
;;     (if (nil? x)
;;       (let [new-var (make-variable (gensym))]
;;         (swap! (.state this) assoc-in path new-var)
;;         new-var)
;;       x)))

;; (defn- named-varibles [^dyna.DynaParserInterfaceImpl this]
;;   (let [c (get-in @(.state this) [:current-atom :conjunct-rexprs])]
;;     (filter (fn [v] (and (variable? v) (string? (.-varname v)))) (apply union (map exposed-variables c)))))

;; (defn -make_call [^dyna.DynaParserInterfaceImpl this ^String name args]
;;   (let [ret-var (make-variable (gensym))
;;         rexpr (make-user-call name (conj (vec args) ret-var) 0)]
;;     (add-rexpr this rexpr)
;;     ret-var))


;; (defn -make_structure [^dyna.DynaParserInterfaceImpl this ^String name args]
;;   (let [ret-var (make-variable (gensym))
;;         rexpr (make-unify ret-var (make-structured-value name (vec args)))]
;;     (add-rexpr this rexpr)
;;     ret-var))

;; (defn -make_rexpr_add [^dyna.DynaParserInterfaceImpl this ^String name args]
;;   (let [rexpr (apply construct-rexpr name args)]
;;     (add-rexpr this rexpr)
;;     rexpr))

;; (defn -unify_with_true [^dyna.DynaParserInterfaceImpl this value]
;;   (add-rexpr this (make-unify value (make-constant true))))

;; ;; (defn -enter_dynabase_context [^dyna.DynaParserInterfaceImpl this]
;; ;;   (dyna.DynaParserInterfaceImpl. (assoc (deref (.state this))
;; ;;                                :current-dynbase (gensym)  ;; this will want to have
;; ;;                                )))

;; (defn -copy_interface [^dyna.DynaParserInterfaceImpl this]
;;   (dyna.DynaParserInterfaceImpl. (assoc (deref (.state this))
;;                                                 :parent-parser this
;;                                                 )))

;; ;; (defn -set_atom [^dyna.DynaParserInterfaceImpl this ^String name arguments ^String aggregator]
;; ;;   (update-interface this )

;; ;;   (swap! (.state this) assoc :current-atom {:name name :arguments (vec arguments) :aggregator aggregator}))

;; ;; (defn -construct_atom [^dyna.DynaParserInterfaceImpl this return-value]
;; ;;   (???))

;; (defn -start_new_atom [^dyna.DynaParserInterfaceImpl this]
;;   (swap! (.state this) assoc :current-atom atom-init-state))

;; (defn -start_new_annon_atom [^dyna.DynaParserInterfaceImpl this]
;;   (swap! (.state this) assoc :current-atom (assoc atom-init-state :is-annon-atom true)))

;; (defn -set_atom_name [^dyna.DynaParserInterfaceImpl this ^String name]
;;   (swap! (.state this) assoc-in [:current-atom :name] name))

;; (defn -set_atom_args [^dyna.DynaParserInterfaceImpl this args]
;;   (swap! (.state this) assoc-in [:current-atom :arguments] (vec args))
;;   (doall (map (fn [a b] (add-rexpr this (make-unify a b))) (vec args) (map #(make-variable (str "$" %)) (range (count args))))))

;; (defn -set_atom_aggregator [^dyna.DynaParserInterfaceImpl this ^String name]
;;   (assert (string? name))
;;   (swap! (.state this) assoc-in [:current-atom :aggregator] name))

;; (defn -set_atom_result_variable [^dyna.DynaParserInterfaceImpl this value]
;;   (swap! (.state this) assoc-in [:current-atom :result-variable] value)
;;   (swap! (.state this) assoc-in [:current-atom :all-variables]
;;          (conj
;;           (get-in @(.state this) [:current-atom :all-variables])
;;           value)))

;; (defn- make-new-atom [this]

;;   )

;; (defn -finish_atom [^dyna.DynaParserInterfaceImpl this]
;;   ;; we are going to need to add some $self variable which represents the current dynabase.  The dynabase will want to combine with the expression such that
;;   (if (get-in @(.state this) [:current-atom :is-annon-atom])
;;     ;; then there needs to be something that stores this for later
;;     (do)
;;     )
;;   (while (not (empty? (:end-of-atom-callbacks @(.state this))))
;;     (let [rf (:end-of-atom-callbacks @(.state this))]
;;       (swap! (.state this) assoc :end-of-atom-callbacks [])  ; clear out what is currently there
;;       (doseq [func rf]
;;         (func))))
;;   (if (= ":=" (get-in @(.state this) [:current-atom :aggregator]))
;;     (swap! (.state this) assoc-in [:current-atom :result-variable] (-make_structure "$colon_line_tracking")))
;;   (let [state @(.state this)
;;         arity (count (get-in state [:current-atom :arguments]))
;;         name (get-in state [:current-atom :name])
;;         signature [name arity]
;;         arg-variables (set (map (fn [x] (make-variable (str "$" x))) (range arity)))
;;         rexpr-body (make-conjunct (get-in state [:current-atom :conjunct-rexprs]))
;;         all-vars (exposed-variables rexpr-body)
;;         project-out-vars (difference all-vars arg-variables)
;;         rexpr-body-proj (reduce (fn [rexpr var] (make-proj var rexpr)) rexpr-body project-out-vars)
;;         rexpr (make-aggregator (get-in state [:current-atom :aggregator])
;;                                (make-variable (str "$" arity))  ;; the result variable is just the last variable in the expression which is one more than the arity.
;;                                (get-in state [:current-atom :result-variable])
;;                                rexpr-body-proj
;;                                )
;;         ]
;;     (debug-repl)))

;; (defn -finish_annon_atom [this]
;;   (assert false))


;; (defn -start_new_dynabase [^dyna.DynaParserInterfaceImpl this]
;;   (swap! (.state this) assoc :current-dynabase
;;          {:inherits-from-variable nil
;;           :externally-visable-variables #{}
;;           }
;;          )
;;   (assert (nil? (:end-of-dynabase-callback (.state this))))
;;   ;; we want an empty array which represents what dynabase this files has
;;   (swap! (.state this) assoc :end-of-dynabase-callback []))

;; (defn -set_dynabase_inherits_variable [^dyna.DynaParserInterfaceImpl this var]
;;   (swap! (.state this) assoc-in [:current-dynbase :inherits-from-variable] var))

;; (defn -get_dynabase_construct_variable [^dyna.DynaParserInterfaceImpl this]
;;   ;; if the variable already exists then this could get read it, otherwise maybe it should generate a new variable?
;;   (get-with-default-var this [:current-dynbase :constructs-variable]))

;; (defn -finish_dynabase [^dyna.DynaParserInterfaceImpl this]
;;   (let [state @(.state this)
;;         process (fn [state]

;;                  )]
;;     (swap! (.state this) update :end-of-atom-callbacks conj process)
;;     )
;;   )


;; (defn -run_query [^dyna.DynaParserInterfaceImpl this rexpr]
;;   ;; this is going to want to take the R-expr and simplify it against the
;;   ;; current database.  This will thne allow for it to print the results or
;;   ;; return the results to the user somehow.

;;   ;; I suppose that for this interface this could just be looking at

;;   nil
;;   )



;; ;; (defn run-parser [^CharStream stream]
;; ;;   (let [lexer (dyna.dyna_grammarLexer. ^CharStream stream)
;; ;;         token-stream (UnbufferedTokenStream. lexer)
;; ;;         parser (dyna.dyna_grammarParser. token-stream)
;; ;;         iface (dyna.DynaParserInterfaceImpl. nil)]
;; ;;     (comment
;; ;;       (if run-parser-fast ;; there needs to be some way in which this can be
;; ;;                           ;; configured or something.  I suppose that this could
;; ;;                           ;; happen via flags or for large inputs
;; ;;         (.setErrorHandler parser (BailErrorStrategy.))))
;; ;;     (.program parser iface)
;; ;;     (.getNumberOfSyntaxErrors parser)
;; ;;     )
;; ;;   )


;; ;; (defn parse-string
;; ;;   "Run the parser on a string of code"
;; ;;   [^String s]
;; ;;   (let [char-stream (CharStreams/fromString ^String (str s "\n% end of string"))]
;; ;;     (run-parser char-stream)
;; ;;     ))
