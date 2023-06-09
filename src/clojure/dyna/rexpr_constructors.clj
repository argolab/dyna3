(ns dyna.rexpr-constructors)

(defmacro ^{:private true} declare-rexprs [& x]
  `(declare ~@(for [z x] (symbol (str "make-" z)))
            ~@(for [z x] (symbol (str "make-no-simp-" z)))
            ~@(for [z x] (symbol (str "is-" z "?")))
            ~@(for [z x] (symbol (str "simplify-" z)))
            ~@(for [z x] (symbol (str "simplify-construct-" z)))
            ~@(for [z x] (symbol (str "simplify-inference-" z)))
            ))

;; the implementation is in rexpr.clj.  This file just exists so that we can
;; reference the methods which construct the R-expr before clojure has loaded in
;; the impementation of the methods

(declare-rexprs
 multiplicity
 conjunct
 disjunct
 unify
 unify-structure
 ;unify-structure-get-meta
 proj
 aggregator
 if
 user-call)

(declare make-variable
         make-unique-variable
         is-variable?
         ;is-variable-set?
         make-constant
         is-constant?
         make-structure
;         is-empty-rexpr?
                                        ;        is-non-empty-rexpr?
         get-user-term
         )


(def modification-lock (Object.))

(defmacro expose-globally
  ;; this namespace basically contains references to variables which need to be access from other files
  ;; this means that some function contained in this file might have multiple variables which reference it....
  ([name]
   `(do (intern 'dyna.rexpr-constructors (quote ~(symbol name)) ~name)
        (alter-meta! (var ~name) assoc :all-vars #{(var ~(symbol "dyna.rexpr-constructors" (str name)))
                                                   (var ~name)})
        (alter-meta! (var ~(symbol "dyna.rexpr-constructors" (str name)))
                     merge (dissoc (meta (var ~name)) :ns)))))
