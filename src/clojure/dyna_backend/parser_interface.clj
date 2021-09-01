(ns dyna-backend.parser_interface
  (:require [dyna-backend.core])
  (:require [dyna-backend.rexpr :refer :all]))

(gen-class
 :name "dyna_backend.DynaParserInterface"
 :prefix "-"
 :init "init"
 :constructors {[Object] []}
 :state state
 :methods [[make_rexpr [String "[Ljava.lang.Object;"] Object]
           [make_rexpr_add [String "[Ljava.lang.Object;"] void]
           [make_variable [String] Object]
           [make_unnamed_variable [] Object]
           [make_constant [Object] Object]
           [make_call [String Object] Object]
           [unify_with_true [Object] void]
           ;; this should return the same class, but not able to do that self reference here
           [enter_dynabase_context [] Object]
           [copy_interface [] Object]
           [set_atom_name [String Long String] void]
           ])

(defn -init [arg]
  [[] (atom (if (map? arg)
              {:current-system arg
               :dynabase {:variables []  ;; the variables which are externally referenced for the currnt dynabase
                          :dynabase-value nil ;; if this is some file, then this should just be a value that can be unified in place for the dynabase
                          :dynabase-name "-"} ;; whatever the generated name or filename is for the current dynabase
               :head-variable-names []
               :system nil ;; some pointer to whatever is the current collection of user defined expressions / system
               :current-filename "REPL" ;; what the current file name is that this is parsing from.  So $load should allow for relatitive imports of a file
               ;; something like $load() takes either 1 or 2 arguments, this would return the handle to the root dynabase which represents the file
               ;; in the case that this has something that would represent which of the expressions might find
               :conjunctive-rexprs []
               :current-atom {:name nil :arity nil :aggregator nil}
               }))])

(defn -make_rexpr [this ^String name args]
  (apply construct-rexpr name args))

(defn -make_variable [this ^String name]
  (make-variable name))

(defn -make_unnamed_variable [this]
  (make-variable (gensym)))

(defn -make_constant [this value]
  (make-constant value))

(defn add-rexpr [this rexpr]
  (if (not= rexpr (make-multiplicity 1))
    (swap! (.state this)
           (fn [old] (assoc old :conjunctive-rexprs
                            (conj (:conjunctive-rexprs old) rexpr)
                            )))))

(defn -make_call [this ^String name args]
  (let [ret-var (make-variable (gensym))
        rexpr (make-user-call name (conj (vec args) ret-var) 0)]
    (add-rexpr this rexpr)
    ret-var))


(defn -make_structure [this ^String name args]
  (let [ret-var (make-variable (gensym))
        rexpr (make-unify ret-var (make-structured-value name (vec args)))]
    (add-rexpr this rexpr)
    ret-var))

(defn -make_rexpr_add [this ^String name args]
  (let [rexpr (apply construct-rexpr name args)]
    (add-rexpr this rexpr)
    rexpr))


(defn -unify_with_true [this value]
  (conj! (:conjunctive-rexprs (.state this))
         (make-unify value (make-constant true))))

(defn -enter_dynabase_context [this]
  (dyna_backend.DynaParserInterface. (assoc (deref (.state this))
                               :current-dynbase (gensym)  ;; this will want to have
                               )))

(defn -copy_interface [this]
  (dyna_backend.DynaParserInterface. (deref (.state this))))

(defn -set_atom_name [this ^String name ^long arity ^String aggregator]
  (swap! (.state this) assoc :current-atom {:name name :arity arity :aggregator aggregator}))

(defn -run_query [this rexpr]
  ;; this is going to want to take the R-expr and simplify it against the
  ;; current database.  This will thne allow for it to print the results or
  ;; return the results to the user somehow.

  ;; I suppose that for this interface this could just be looking at

  nil
  )
