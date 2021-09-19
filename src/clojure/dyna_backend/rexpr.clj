(ns dyna-backend.rexpr
  (:require [dyna-backend.utils :refer :all])
  (:require [dyna-backend.context :as context])
  (:require [dyna-backend.system :as system])
             ;:rename '{get-value context-get-value,
             ;          is-bound? context-is-bound?
             ;          set-value! context-set-value!}

  (:require [clojure.set :refer [union difference]])
  (:require [aprint.core :refer [aprint]])
  (:import (dyna_backend UnificationFailure))
  (:import (dyna_backend DynaTerm)))


(declare simplify)
(def simplify-construct identity)
(declare find-iterators)


;; maybe this should recurse through the structure and make a nice print out of the term objets
(defmethod print-method DynaTerm [this ^java.io.Writer w] (.write w (.toString this)))

;(defn simplify-construct [r] r)

(defprotocol Rexpr
  (primitive-rexpr [this]) ;; return a primitive r-expr for the expression
  ;;(replace-expressions [this expressions-map]) ;; replace a given nested expression
  (get-variables [this])  ;; get the variables from the current rexpr
  (get-children [this])
  (get-argument [this n])
  (get-arguments [this])
  (as-list [this]) ; use for printing out the structure

  (exposed-variables [this])        ; return variables values that are exposed externally (so hide aggregators and proj)

  ;; these functions can recursivy walk the R-expr and rewmap the different variables which appear
  ;; if there is something that


  (remap-variables [this variable-renaming-map])
  ;; (visit-rexpr-children [this remap-function]) ;; this will visit any nested R-exprs on the expression, and return a new expression of the same type with
  ;(visit-all-children [this remap-function]) ;; this will visit
  )



;; the annotation on a variable can be one of
;;; :var, :rexpr, :var-list, :rexpr-list
;;; other annotations are ignored for the time being

(def rexpr-containers (atom #{}))
(def rexpr-constructors (atom {}))

(defn construct-rexpr [name & args]
  (apply (get @rexpr-constructors name) args))


(defmacro def-base-rexpr [name args & optional]
  (let [vargroup (partition 2 args)
        rname (str name "-rexpr")
        opt (if (not (nil? optional)) (vec optional) [])]
    `(do
       (declare ~(symbol (str "make-" name))
                ~(symbol (str "make-no-simp-" name))
                ~(symbol (str "is-" name "?")))
       (deftype-with-overrides ~(symbol rname) ~(vec (concat (quote [^int cached-hash-code ^:unsynchronized-mutable cached-exposed-variables])
                                                             (map cdar vargroup)))
         ~opt
         Rexpr
         ~'(primitive-rexpr [this] this) ;; this is a primitive expression so we are going to just always return ourselves
         (~'get-variables ~'[this]
          (filter variable?
                  (union #{~@(map cdar (filter #(contains?  #{:var :value} (car %1)) vargroup))}
                         ~@(map cdar (filter #(= :var-list `(set ~(car %1))) vargroup))
                         )))

         (~'get-children ~'[this]
          (concat
           (list ~@(map cdar (filter #(= :rexpr (car %1)) vargroup)))
           ~@(map cdar (filter #(= :rexpr-list (car %1)) vargroup))))

         ;; might be better if there was some case and switch statement for get-argument
         ;; constructing the vector is likely going to be slow.  Would be nice if there was some array representation or something
         (~'get-argument ~'[this n] ;; trying to add a type hit to this makes it such that the interface will not get cast correctly
          (case ~'n
            ~@(apply concat (for [[var idx] (zipmap vargroup (range))]
                              `(~idx ~(cdar var))))
            (throw (RuntimeException. "invalid index for get-argument"))))

         ;(~'get-argument ~'[this n] (nth ~(vec (map cdar vargroup)) ~'n))
         (~'get-arguments ~'[this] ~(vec (map cdar vargroup)))

         (~'as-list ~'[this]
          (list (quote ~(symbol name))
                ~@(for [v vargroup]
                    (case (car v)
                      :rexpr `(as-list ~(cdar v))
                      :rexpr-list `(map as-list ~(cdar v))
                      (cdar v)))))

         (~'exposed-variables ~'[this]
          (cache-field ~'cached-exposed-variables
                       (set
                        (filter variable?
                                (difference (union (get-variables ~'this)
                                                   ~@(keep
                                                      #(if (= :rexpr (car %))
                                                         `(exposed-variables ~(cdar %)))
                                                      vargroup)
                                                   ~@(keep
                                                      #(if (= :rexpr-list (car %))
                                                         `(apply union (map exposed-variables ~(cdar %)))) vargroup))
                                            #{~@(keep
                                                 #(if (= :hidden-var (car %)) (cdar %))
                                                 vargroup)})))))
         (~'remap-variables ~'[this variable-map]
          (if (empty? ~'variable-map)
            ~'this ;; in this case, there are no variables in the expression to rename, so don't do any replacements and just return our selves
            (let ~(vec (apply concat (for [v vargroup]
                                       [(symbol (str "new-" (cdar v)))
                                        (case (car v)
                                          :var `(get ~'variable-map ~(cdar v) ~(cdar v))
                                          :hidden-var `(get ~'variable-map ~(cdar v) ~(cdar v))
                                          :var-list `(map #(get ~'variable-map % %) ~(cdar v))
                                          :rexpr `(remap-variables ~(cdar v) ~'variable-map)
                                          :rexpr-list `(map #(remap-variables % ~'variable-map) ~(cdar v))
                                          (cdar v) ;; the default is that this is the same
                                          )])))
              (if (and ~@(for [v vargroup]
                           `(= ~(cdar v) ~(symbol (str "new-" (cdar v))))
                           ))
                ~'this ;; then there was no change, so we can just return ourself
                ;; there was some change, so we are going to need to create a new object with the new values
                (~(symbol (str "make-no-simp-" name)) ~@(for [v vargroup]
                                                          (symbol (str "new-" (cdar v)))))))))
         Object
         (equals ~'[this other]
           (or (identical? ~'this ~'other)
               (and (instance? ~(symbol rname) ~'other)
                    (= (hash ~'this) (hash ~'other))
                    ~@(for [[var idx] (zipmap vargroup (range))]
                        `(= ~(cdar var) (get-argument ~'other ~idx))))))

         (hashCode [this] ~'cached-hash-code) ;; is this something that should only be computed on demand instead of when it is constructed?
         (toString ~'[this] (str (as-list ~'this))))

       (defn ~(symbol (str "make-no-simp-" name))
         {:rexpr-constructor (quote ~name)
          :rexpr-constructor-type ~(symbol rname)}
         ~(vec (map cdar vargroup))
         ~@(map (fn [x] `(if (not (~(resolve (symbol (str "check-argument-" (symbol (car x))))) ~(cdar x)))
                           (do (.printStackTrace (Throwable. (str "Argument value check failed: " ~(car x) ~(cdar x))) System/err)
                               (debug-repl ~(str "check argument " (car x)))
                               (assert false)))) vargroup)
         (~(symbol (str rname "."))
          ;; this hash implementation needs to match the one below....
          (unchecked-int (+ ~(hash rname) ~@(for [[var idx] (zipmap vargroup (range))]
                                              `(* (hash ~(cdar var)) ~(+ 3 idx)))))

          nil                           ; the cached unique variables
          ~@(map cdar vargroup))
         )

       (defn ~(symbol (str "make-" name))
         {:rexpr-constructor (quote ~name)
          :rexpr-constructor-type ~(symbol rname)}
         ~(vec (map cdar vargroup))
         ~@(map (fn [x] `(if (not (~(resolve (symbol (str "check-argument-" (symbol (car x))))) ~(cdar x)))
                           (do (debug-repl ~(str "check argument " (car x)))
                               (assert false)))) vargroup)

         (simplify-construct (~(symbol (str rname "."))
                              ;; this might do the computation as a big value, would be nice if this could be forced to use a small int value
                              ;; I suppose that we could write this in java and call out to some static function if that really became necessary
                              ;; this hash implementation needs to match the one above....
                              (unchecked-int (+ ~(hash rname) ~@(for [[var idx] (zipmap vargroup (range))]
                                                                  `(* (hash ~(cdar var)) ~(+ 3 idx)))))

                              nil       ; the cached unique variables
                              ~@(map cdar vargroup))))
       (swap! rexpr-constructors assoc ~(str name) ~(symbol (str "make-" name)))
       (defn ~(symbol (str "is-" name "?")) ~'[rexpr]
         (instance? ~(symbol rname) ~'rexpr))
       (defmethod print-method ~(symbol rname) ~'[this ^java.io.Writer w]
         (aprint (as-list ~'this) ~'w)))))


(defprotocol RexprValue
  (get-value [this])
  (set-value! [this value])
  (is-bound? [this])
  (all-variables [this]))

;; this is the value of the object itself
;; this will want to keep a reference to which dynabase it was constructed in, as we might be using this
;; as a reference to some function.  In which case, there might be multiple arguments for this.  How this object is constructed
;;(defrecord structured-term-value [name constructing-dynabase arguments])


(defn make-structure [name args]
  (DynaTerm. name nil nil args))

(def ^:const null-term (DynaTerm/null_term))


;;;;;;;;;;;;;;;;;;;;;;;;;;
;; things like variables and constants should instead be some other type rather than an R-expr
;; this could be something


(defrecord variable-rexpr [varname]
  RexprValue
  (get-value [this] (context/get-value context/*context* this))
  (set-value! [this value]
    (context/set-value! context/*context* this value))
  (is-bound? [this]  (context/need-context (context/is-bound? context/*context* this)))
  (all-variables [this] #{this})
  Object
  (toString [this] (str "(variable " varname ")")))

(defn make-variable [varname]
  (variable-rexpr. varname))

(defmethod print-method variable-rexpr [^variable-rexpr this ^java.io.Writer w]
  (.write w (str "(variable " (.varname this) ")")))

;; there should be some version of bound/unbound variables which are designed to access slots in the expression

(defrecord constant-value-rexpr [value]
  RexprValue
  (get-value [this] value)
  (set-value! [this v]
    (if (not= v value)
      (throw (UnificationFailure. "can not assign value to constant"))))
  (is-bound? [this] true)
  (all-variables [this] #{})
  Object
  (toString [this] (str "(constant " value ")")))



(defn make-constant [val]
  (constant-value-rexpr. val))

(let [tv (make-constant true)
      fv (make-constant false)]
  (defn make-constant-bool [val]
    (if val tv fv)))

(defmethod print-method constant-value-rexpr [^constant-value-rexpr this ^java.io.Writer w]
  (.write w (str "(constant " (.value this) ")")))


;; should the structured types have their own thing for how their are represented
;; though these will want to have some e
(defrecord structured-rexpr [name arguments]
  RexprValue
  (get-value [this]
    ;; this is going to have to construct the structure for this
    ;; which means that it has to get all of the values, and then flatten it to a structure
    (make-structure name (doall (map get-value arguments))))

  (set-value! [this v]
    (if (or (not= (car v) name) (not= (+ 1 (count arguments)) (count v)))
      (throw (UnificationFailure. "name/arity does not match structure"))
      (doall (map set-value! arguments (cdr v)))
      ))

  (is-bound? [this]
    (context/need-context (every? is-bound? arguments)))
  (all-variables [this] (apply union (map all-variables arguments)))
  Object
  (toString [this] (str "(structure " name " " arguments ")")))

(defn make-structured-rexpr [name arguments]
  (assert (string? name))
  (assert (every? (partial satisfies? RexprValue) arguments))
  (structured-rexpr. name arguments))

(defmethod print-method structured-rexpr [^structured-rexpr this ^java.io.Writer w]
  (.write w (.toString this)))

(defn make-structured-value [name values]
  (assert (every? (partial satisfies? RexprValue) values))
  (assert (string? name))
  (structured-rexpr. name values))

(defn is-constant? [x] (instance? constant-value-rexpr x))

(defn variable? [variable]
  (instance? variable-rexpr variable))

(defn rexpr? [rexpr]
  (and (satisfies? Rexpr rexpr)
       (not (or (variable? rexpr) (is-constant? rexpr)))))


(defn check-argument-mult [x] (or (and (int? x) (>= x 0)) (= ##Inf x)))
(defn check-argument-rexpr [x] (rexpr? x))
(defn check-argument-rexpr-list [x] (every? rexpr? x))
(defn check-argument-var [x] (or (variable? x) (is-constant? x))) ;; a variable or constant of a single value.  Might want to remove is-constant? from this
(defn check-argument-var-list [x] (every? variable? x))
(defn check-argument-value [x] (satisfies? RexprValue x)) ;; something that has a get-value method (possibly a structure)
(defn check-argument-hidden-var [x] (check-argument-var x))
(defn check-argument-str [x] (string? x))
(defn check-argument-unchecked [x] true)
(defn check-argument-opaque-constant [x] ;; something that is not in the R-expr language
  (not (or (satisfies? Rexpr x) (satisfies? RexprValue x))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(def-base-rexpr multiplicity [:mult m])

;; there is meta information on this which needs to be carried forward
(let [prev make-multiplicity
      true-mul (prev 1)
      false-mul (prev 0)]
  (defn make-multiplicity
    {:rexpr-constructor 'multiplicity
     :rexpr-constructor-type multiplicity-rexpr}
    [x]
    (case x
      true true-mul
      false false-mul
      0 false-mul ; we can special case the common values to avoid creating these objects many times
      1 true-mul
      (prev x))))

(def-base-rexpr conjunct [:rexpr-list args])

(def make-* make-conjunct)

(def-base-rexpr disjunct [:rexpr-list args])

(def make-+ make-disjunct)


;; there should be a more complex expression for handling this in the case of a if statement or something
;; this will want for this to somehow handle if there are some ways in which this can handle if there
(defn is-empty-rexpr? [rexpr]
  (and (rexpr? rexpr) (= (make-multiplicity 0) rexpr)))

(defn is-non-empty-rexpr? [rexpr]
  (and (rexpr? rexpr)
       (or (and (is-multiplicity? rexpr) (> (get-argument rexpr 0) 0))
           (and (is-disjunct? rexpr) (some is-non-empty-rexpr? (get-argument rexpr 0)))
           )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-base-rexpr unify [:value a
                       :value b])

(def-base-rexpr unify-structure [:var out
                                 :var dynabase ;; the dynabase variable is only
                                               ;; used for reading.  When
                                               ;; destrcturing a term, this will
                                               ;; _not_ unify with this variable
                                 :str name
                                 :var-list arguments])

;; read the dynabase from a particular constructed structure.  This will require that structure become ground
;; the file reference is also required to make a call to a top level expression
(def-base-rexpr unify-structure-get-meta [:var structure
                                          :var dynabase
                                          :var from-file])



(def-base-rexpr proj [:hidden-var v
                      :rexpr body])

(def-base-rexpr aggregator [:str operator
                            :var result
                            :hidden-var incoming
                            :rexpr body])

(def-base-rexpr if [:rexpr cond
                    :rexpr true-branch
                    :rexpr false-branch])



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; the user call object will figure out which information is getting called, this also will resolve
(def-base-rexpr user-call [:str name
                           :var from-file ;; which file is this call from.
                                          ;; There might be import statements
                                          ;; that we have to resolve.  This will
                                          ;; control what something is going to
                                          ;; be resolved as.  So collecing the
                                          ;; resulting R-expr can be done when
                                          ;; the user-call is resolved rather
                                          ;; than having this done ahead of
                                          ;; time?
                           :var dynabase  ;; have a variable which referneces
                                          ;; what dynabase this call is being
                                          ;; made from.  This will be unfied
                                          ;; with $self on the other end.  In
                                          ;; the case that this is calling
                                          ;; something that is "primitive" or a
                                          ;; builtin, then the $self parameter can be ignored in those cases.
                           :var-list args  ;; the arguments which are passed
                                           ;; through via positions.  This will
                                           ;; be $0, $1, ....  The last variale
                                           ;; will be the returned value by
                                           ;; convention.
                           :unchecked call-depth])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; an optimized version of aggregation which does projection and the aggregation in the same operator
;; the aggregator outer should only have a list of aggregator-op-inner as its arguments
(def-base-rexpr aggregator-op-outer [:str operator
                                     :var result
                                     :rexpr bodies])

(def-base-rexpr aggregator-op-inner [:var incoming
                                     :var-list projected
                                     :rexpr body])

;; multiple levels of matching variables should also be a thing that was
;; integrated into the aggregator before, or the disjunction included that it
;; was matching the expression

(defn- recurse-values-depth [m depth]
  (if (= depth 0)
    (vals m)
    (lazy-seq (map #(recurse-values-depth % (- depth 1)) (vals m)))))


;; I suppose that in the case that there are non-ground disjunction-variables, then this would still need this structure
;; once all of the disjunct variables are ground, then this can just rewrite as the wrapped R-expr.  I suppose that this can
;; also consider which of the variables are forced to take a particular value.  Then those can be created as unification expressions
;; such that it will take which of the values might corresponds with it having some of the different
(def-base-rexpr disjunct-op [:var-list disjunction-variables
                             ;:disjunct-trie rexprs
                             :unchecked rexprs
                             ]
  ;; (primitive-rexpr [this] (assert false))
  ;; (get-children [this] (assert false))
  ;; (primitive-rexpr [this] ;; this would have to construct many disjuncts for the given expression.
  ;;                  )

  ;; this will need to walk through all of the rexprs trie and find the depth in
  ;; which an expression corresponds with it.  I suppose that we do not need to
  ;; have a list of disjuncts, as those can just be other disjunctive R-exprs in
  ;; the case that there is more than 1 thing
  (get-children [this] (let [depth (count disjunction-variables)]

                         (assert false))))




;; (def-base-rexpr proj-all-except [:var-list exposed-vars
;;                                     :rexpr R]
;;   (exposed-variables [this] exposed-vars))

;; this is going to project many of the variables in the expression
;; (def-base-rexpr proj-many [:var-list projected-vars
;;                               :rexpr R]
;;   (exposed-variables [this] (different (exposed-variables R) projected-vars))
;;   )

(defn make-proj-many [vars R]
  (if (empty vars) R
      (make-proj (first vars) (make-proj-many (rest vars) R))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; functions which are used to perform matchings against a given Rexpr
(def rexpr-matchers (atom {}))
(def rexpr-matchers-mappers (atom {}))
(def rexpr-matchers-meta (atom {}))

;; functions which actually perform rewrites against an Rexpr
;; these functions perform their own internal matching
(def rexpr-rewrites (atom {})) ; run at standard time
(def rexpr-rewrites-construct (atom {})) ; run at the time of construction
(def rexpr-rewrites-inference (atom {})) ; run to construct new objects, but there are

;; functions which define how iterators are accessed for a given Rexpr
(def rexpr-iterators-accessors (atom {}))


(defmacro def-rewrite-matcher
  ([name var body mapper-func]
   `(do (swap! rexpr-matchers assoc (quote ~name)
               (fn ~var ~body))
        (swap! rexpr-matchers-mappers (quote ~name)
               (fn ~var ~mapper-func))
        ;;; when putting the meta information directly onto the function
        ;; then it seems that it creates a new object, so it is not able to pass the pointer
        ;; to the function as the first argument
        (swap! rexpr-matchers-meta assoc (quote ~name)
               {:matcher-name   (quote ~name)
                :matcher-args   (quote ~var)
                :matcher-body   (quote ~body)
                :matcher-mapper (quote ~mapper-func)})))

  ([name var body]
   `(def-rewrite-matcher ~name ~var ~body identity)))


(defn save-defined-rewrite
  [collection functor-name rewriter]
  (swap-vals! collection
              (fn [old] (assoc old functor-name
                               (conj (get old functor-name #{}) rewriter)))))



;; (defn- replace-with-matcher-functions [expr]
;;   (map (fn [x] (if (contains? @rexpr-matchers x)
;;                  (get @rexpr-matchers x)
;;                  (if (list? x) (replace-with-matcher-functions x)
;;                      x))) expr))

(defn make-rewriter-function [matcher body]
  ;; this needs to go through and define something where the different functions
  ;; are invoked on the relvant parts of the expression.  Because the
  ;; expressions have different field values, and are not positional, this means
  ;; that those matchers will have to extract the right values (or something
  (let [n-args (- (count matcher) 1)
        ;args (for [_ (range n-args)] (gensym))
        named-args (for [v (cdr matcher)]
                     (if (seq? v) ;; if this is something like (:ground v0) then we just want the v0 part
                       (cdar v)
                       v))]

    `(fn ~'[rexpr]
       (let [~(vec named-args) (get-arguments ~'rexpr)] ; unsure if using the global function vs the .func is better?
         (if (and ~@(map (fn [arg mat]
                           `(~(get @rexpr-matchers mat mat)
                              ~arg)) named-args (for [m (cdr matcher)]
                                                  (if (seq? m) (car m) m))))
           ; call the implementation of the rewrite function
           (do ~body)
           ; return that there is nothing
           nil)))))



(defmacro def-rewrite [& args]
  (let [kw-args (apply hash-map (drop-last args))
        rewrite (last args)
        functor-name (car (:match kw-args))
        arity (if (= (cdar (:match kw-args)) :any) nil (- (count (:match kw-args)) 1))
        matcher (:match kw-args)
        rewriter-function (make-rewriter-function matcher rewrite)]


    ;; this is going to have to identify which expressions are going to do the matching, then it will find which expressions

    ;; todo: this needs to handle the other kinds of times when we want to do the rewrites
    `(save-defined-rewrite
       ~(case (:run-at kw-args :standard)
          :standard 'rexpr-rewrites
          :construction 'rexpr-rewrites-construct
          :standard-and-construction 'rexpr-rewrites-construct ;; this should also run these when their variables become ground
          :construction-and-grounding-change nil ;; this could run it when there is a new variable which is ground, which might be useful in avoiding running sutff too much?
          :inference 'rexpr-rewrites-inference)
       ~(symbol (str functor-name "-rexpr"))
       ~rewriter-function)))

(defmacro def-iterator [& args]
  (let [kw-args (apply hash-map (drop-last args))
        func-body (last args)
        functor-name (car (:match kw-args))
        arity (if (= (cdar (:match kw-args)) :any) nil (- (count (:match kw-args)) 1))
        matcher (:matcher kw-args)
        func (make-rewriter-function matcher func-body)]
    ;; there needs to be some find iterator method
    ;; we could use the same methods to construct the function for getting the iterators
    ;; then it would have the same access methods.  I suppose that there could be some base methods
    ;; where it would call the base insteace, but we would like to union across the different methods
    ;; for constructing something where

    `(save-defined-rewrite
      'rexpr-iterators-accessors
      ~(symbol (str functor-name "-rexpr"))
      ~func)

    nil))

(defn make-iterator [variable iterator]
  ;; these are going to need to be hashable, otherwise this would mean that we can't use the set to identify which expressions are iterable
  ;; there are some values which
  #{[variable iterator]})


(defn is-variable-set? [variable]
  (or (instance? constant-value-rexpr variable)
      (context/need-context
        (context/is-bound? context/*context* variable))))

(defn is-constant? [variable]
  (instance? constant-value-rexpr variable))

(defn get-variable-value [variable]
  (if (instance? constant-value-rexpr variable)
    (.value ^constant-value-rexpr variable)
    (context/get-value context/*context* variable)))


(defn simplify
  [rexpr]
  ;; this should just match the given type and identify if there are rewrites defined for this

  (let [typ (type rexpr)
        rrs (get @rexpr-rewrites typ)]
    (if (nil? rrs)
      rexpr ;; there is nothing here so we are just going to return the r-expr unmodified
      (or (first (filter (complement nil?)
                         (for [rw rrs]
                           (let [res (rw rexpr)]
                             (if (not= rexpr res) res)))))
          rexpr))))

(defn simplify-construct [rexpr]
  (let [typ (type rexpr)
        rrs (get @rexpr-rewrites-construct typ)]
    (if (nil? rrs)
      rexpr
      (or (first (filter (complement nil?)
                         (for [rw rrs]
                           (let [res (rw rexpr)]
                             (if (not= rexpr res) res)))))
          rexpr))))


;; simplification which takes place a construction time
;; (defn simplify-construct [rexpr]
;;   rexpr)

(defn simplify-top [rexpr]
  (let [ctx (context/make-empty-context rexpr)]
    (context/bind-context ctx
                          (simplify rexpr))))


;; the context is assumed to be already constructed outside of this function
;; this will need for something which needs for the given functionq
(defn simplify-fully [rexpr]
  (let [prev (atom nil)
        cr (atom rexpr)]
    (while (not= @cr @prev)
      (reset! prev @cr)
      (swap! cr simplify))
    @cr))

(defn find-iterators [rexpr]
  (let [typ (type rexpr)
        rrs (get @rexpr-iterators-accessors typ)]
    (apply union (for [rs rrs] (rs rexpr)))))


;; there should be some matcher which is going to identify which expression.
;; this would have some which expressions are the expressions
;; this is going to have to have some context in which an expression

(defn is-ground? [var-name]
  (if (and (variable? var-name) (is-variable-set? var-name))
    (get-variable-value var-name)
    (if (is-constant? var-name)
      (.value var-name))))

(def-rewrite-matcher :ground [var-name]
                                        ; this should be redfined such that it will return the ground value for the variable
                                        ; though we might not want to have the matchers identifying a given expression
  (is-ground? var-name))

(def-rewrite-matcher :not-ground [var]
  (and (variable? var) (not (is-bound? var))))

(def-rewrite-matcher :free [var-name]
                     (and (variable? var-name) (not (is-variable-set? var-name)) var-name))


(def-rewrite-matcher :rexpr [rexpr] (rexpr? rexpr))

(def-rewrite-matcher :rexpr-list [rexpr-list]
                     (and (seqable? rexpr-list) (every? rexpr? rexpr-list)))


;; something that has a name first followed by a number of different unified expressions
(def-rewrite-matcher :structured [rexpr]
  (instance? structured-rexpr rexpr))
;; this could have that there is some meta-data that is contained in the context
;; then this will have to look at those values

(def-rewrite-matcher :variable [var]
  (variable? var))

(def-rewrite-matcher :varible-list [var-list]
  (every? variable? var-list))

(def-rewrite-matcher :ground-var-list [var-list]
  (every? is-ground? var-list))

(def-rewrite-matcher :any [v]
                     (or (variable? v) (is-constant? v)))

;; just match anything
(def-rewrite-matcher :unchecked [x] true)

;; this are things which we want to iterate over the domain for
;; this should
(def-rewrite-matcher :iterate [x]
  (and (variable? x) (not (is-bound? x))))

(def-rewrite-matcher :type-known [x]
  ;; if there is meta data present for an expression in which case we can just use this
  (do (or (is-ground? x))
      (assert false)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-rewrite
  :match (unify (:structured A) (:structured B))
  ;; that this should run early, when invoked by the make method call.
  ;; there should be some methods like
  :run-at :construction
  (if (or (not= (count A) (count B)) (not= (car A) (car B)))
    (make-multiplicity 0) ;; meaning that the names on these expressions does not match.
    (make-conjunct (doall (map make-unify (cdar A) (cdar B)))) ; then make a bunch of smaller unifications on the variables themselves directly
    ))

(def-rewrite
  ;; the matched variable should have what value is the result of the matched expression.
  :match (unify (:ground A) (:ground B))
  :run-at :construction
  (if (= A B)
    (make-multiplicity 1)
    (make-multiplicity 0)))

(def-rewrite
  :match (unify (:ground A) (:not-ground B))
  :run-at :construction
  (make-unify B A))


(def-rewrite
  :match (unify (:structured B) (:ground A))
  :run-at :construction
  (let [Av (get-value A)]
    (if (not (and (instance? DynaTerm Av)
                  (= (.name ^DynaTerm B) (.name ^DynaTerm Av))
                  (= (count (.arguments ^DynaTerm B)) (count (.arguments ^DynaTerm Av)))))
      (make-multiplicity 0)
      (make-conjunct (doall (map make-unify (.arguments ^DynaTerm B) (.arguments ^DynaTerm Av))))
      )))

; this should run at both, so there should be a :run-at :both option that can be selected
(def-rewrite
  :match (unify (:free A) (:ground B))
  :run-at :construction ; this will want to run at construction and when it encounters the value so that we can use it as early as possible
  (do
    ; record that a value has been assigned with the context
    (if (context/has-context)
      (do (set-value! A (get-value B))
          (make-multiplicity 1))
      nil)))

(def-rewrite
  :match (unify (:free A) (:ground B))
  :run-at :standard
  (if (context/has-context)
    (do (set-value! A (get-value B))
        (make-multiplicity 1))))

(def-iterator
  :match (unify (:iterate A) (:ground B))
  (make-iterator A [(get-value B)]))


(def-rewrite
  :match (conjunct (:rexpr-list children))  ;; the conjuncts and the disjuncts are going to have to have some expression wihch
  :run-at :standard
  (do ;(debug-repl "conj")
      (make-conjunct (for [child children]
                       (do ;(debug-repl)
                           (simplify child))))))
;
;(def-rewrite
;  :match (conjunct (:rexpr-list children))
;  :run-at :construction
;  (if (exists? (fn [x] (or (instance? conjunct-rexpr x) (instance? multiplicity-rexpr x))) children)
;      ;; then this should flatten the children out such that
;    ))

(def-rewrite
  ; in the case that there is only 1 argument, this will just run that single argument
  :match (conjunct ((fn [x] (= (count x) 1)) children))
  :run-at :construction
  (car children))

(def-rewrite
  :match (conjunct ((fn [x] (= (count x) 0)) children))
  :run-at :construction
  (make-multiplicity 1))


(def-rewrite
  ;; handle the R* M case where M is a multipilcity
  :match (conjunct ((fn [x] (some (partial instance? multiplicity-rexpr) x))
                    children))
  :run-at :construction
  (let [mult (atom 1)
        num-mults (atom 0)
        others (vec (filter (fn [x] (if (instance? multiplicity-rexpr x)
                                        (do
                                          (swap! mult * (get-argument x 0))
                                          (swap! num-mults inc)
                                          nil)
                                      x)) children))]
    (case @mult
      0 (make-multiplicity 0)
      1 (if (empty? others)
          (make-multiplicity 1)
          (make-conjunct others))
      ;; this should not rerun the simplifications as this might get itself stuck into some loop
      ;; with trying to resimplify at construction this again
      (if (not= num-mults 1) ;; if there is only 1 mult, then we should just keep the same expression
        (make-conjunct (cons (make-multiplicity @mult) others))))))

(def-rewrite
  ;; handle if there is a nested conjunct inside of another conjunct
  :match (conjunct ((fn [x] (some (partial instance? conjunct-rexpr) x))
                        children))
  :run-at :construction
  (make-conjunct (vec (mapcat (fn [x] (if (instance? conjunct-rexpr x)
                                         (get-argument x 0)
                                         [x])) children))))


(def-iterator
  :match (conjunct (:rexpr-list children))
  (apply union (map find-iterators children)))


;; (def-rewrite
;;   :match (disjunct (:rexpr-list children))
;;   :run-at :standard
;;   (make-disjunct (for [child children]
;;                    (let [ctx (context/make-nested-context child)]
;;                      (context/bind-context ctx (simplify child))))))

;; this needs to have some additional combining of the rules.  In the case that there is some

;; (def-rewrite
;;   :match (disjunct (:rexpr-list children))
;;   (case (count children)
;;     0 (make-multiplicity 0)
;;     1 (car children)
;;     :else rexpr))

(def-rewrite
  :match (disjunct ((fn [x] (= 1 (count x))) children))
  :run-at :construction
  (car children))

(def-rewrite
  :match (disjunct ((fn [x] (= 0 (count x))) children))
  :run-at :construction
  (make-multiplicity 0))


(def-rewrite
  :match (disjunct (:rexpr-list children))
  :run-at :standard
  (do
    ;; this is going to have to construct a nested context for everything that it goes into, and then
    (let [found (transient [])]
      (doseq [c children]
           (let [ctx (context/make-nested-context c)
                 ns (context/bind-context ctx (simplify c))]
             (if (not (is-empty-rexpr? ns))
               (do ; then we want to save these rexpr into the list of objects that we have constructed
                 (conj! found [ctx ns])
                 )
               )
             )
           )
      (case (count found)
        0 (make-multiplicity 0)
        1 (do
            ;; then this should just return this single item, there is no need to keep the disjunct aronud in this case
            ;; this will have to move the context info up
            (let [[ctx r] (get found 0)]
              (context/add-context! context/*context* ctx)
              r)
            (assert false))
        (do
          ;; then there are two or more values, so this needs to intersect all of the contexts and
          (let [same-context (reduce context/intersect (map car found))]
            ;; the new intersection is going to be added to the global context
            (context/add-context! context/*context* same-context)
            (make-disjunct (doall (for [[ctx r] found]
                                    ;; this is going to have to make an r-expr for the stuff that this wants to save behind
                                    ;; in the case that there are bindings to a value, then this should
                                    (assert false)
                                    )))
            )
          (assert false)
          ))
      (if (empty? found)
        (make-multiplicity 0)
        (do
          ;; then there is one or more found objects
          ))
      )

    nil))

(def-rewrite
  ;; this is proj(A, 0) -> 0
  :match (proj (:variable A) (is-empty-rexpr? R))
  :run-at :construction
  (make-multiplicity 0))

(def-rewrite
  ;; proj(A, 1) -> inf
  :match (proj (:variable A) (is-multiplicity? M))
  :run-at :construction
  (if (not= (get-argument M 0) 0)
    (make-multiplicity ##Inf)))

(def-rewrite
  :match (proj (:variable A) (:rexpr R))
  :run-at :standard
  (do
    (let [ctx (context/make-nested-context-introduce-variable R A)
          nR (context/bind-context ctx (simplify R))]
      (if (context/is-bound? ctx A)
        ;; then this could just replace the value in the remainder of the expression
        ;; otherwise this can just return the value back
        (do (???))
        (do (make-proj A nR))
        )
      )

    nil
    ))

;; there neeeds to be a projection rewrite for moving expressions out which do not
;; depend on the variable which is getting projected
(def-rewrite
  :match (proj (:variable A) (is-conjunct? R))
  :run-at :construction
  (let [inner (transient [])
        outer (transient [])]
    (doseq [c (get-argument R 0)]
      (if (contains? (exposed-variables c) A)
        (conj! inner c)
        (conj! outer c)))
    (if (empty? outer)
      nil ; then there is nothing for us to move out of the expression
      (make-conjunct (cons outer (make-proj A inner))) ; make a new rexpr with the outer expressions moved out
      )
    ))

(def-rewrite
  :match (if (is-empty-rexpr? A) (:rexpr B) (:rexpr C))
  :run-at :construction
  C)

(def-rewrite
  :match (if (is-non-empty-rexpr? A) (:rexpr B) (:rexpr C))
  :run-at :construction
  B)

(def-rewrite
  :match (if (:rexpr A) (:rexpr B) (:rexpr C))
  :run-at :standard
  (make-if (let [ctx (context/make-nested-context A)]
             (context/bind-context ctx (simplify A)))
           B C))


;
;(def-rewrite
;  :match (proj (:variable A) (:rexpr R))
;  (if (context/has-context)
;    (context/bind-context (context/make-nested-context))
;    )
;  (do
;    (context/make-nested-context-introduce-variable)))


;; this should either return nil which means that there is no match
;; or this should match which expression has some

;; (def-rewrite
;;   :match (if (:rexpr A) (:rexpr B) (:rexpr C)) ;; with the (:match pattern being something that allows it to select the correct matcher for a given expression
;;   (let [rr (bind-context (make-nested-context A)
;;             (simplify A))]
;;     ;; this is going to need to have some rewrite context which masks out the current value
;;     nil

;;     ))





;; ;; this is something that can be automatically generated in the case that
;; (def-rewrite
;;   :match (add (:ground A) (:ground B) (:non-ground C))
;;   (make-unify C `(+ ~A ~B)))


;; (comment

;; (def-rewrite
;;   :match (proj (:var A) (:rexpr R))
;;   :run-at :standard
;;   ;; this needs to make sure that the variable is shaddowed in the context.
;;   ;; which means that this is going to have
;;   (bind-context
;;    (make-nested-context-introduce-variable *context* rexpr A)
;;    (let [nR (simplify R)]
;;      (if (is-ground A)
;;        ;; then the projected variable is now ground, so we should remove the
;;        ;; projection expression though there might be multiple places where the
;;        ;; variable appears so we want to be able to handle that the variable
;;        ;; should still be maintained in such a way that we track the value


;;   (let [ncontext (make-nested-context-introduce-variable *context* rexpr A)]
;;     (bind-context
;;         result (bind-context ncontext
;;                              (simplify R))]
;;     (if

;;   (make-proj A (simplify B)))

;;     )))))

;; )


;; (def-rewrite
;;   :match (user-call (:str name) args call-depth)
;;   :run-at :standard
;;   (let [n [name (count args)]
;;         expr (system/lookup-named-expression name)]
;;     ;; this needs to rename the variables which represent the expression
;;     nil
;;     )
;;   )


;; (def-rewrite
;;   :match (user-call (:unchecked a) (:unchecked b) (:unchecked c) (:unchecked d) (:unchecked e))
;;   :run-at :construction
;;   (make-multiplicity 0))


;; this rewrite finds buitin expressions and replaces them once they are created.  There is no need to delay expanding these expressions
(def-rewrite
  :match (user-call (:unchecked name) (:unchecked from-file) (:unchecked dynabase) (:unchecked args) (:unchecked call-depth))
  :run-at :construction
  (let [n [name (- (count args) 1)]
        s (get @system/system-defined-user-term n)]
    (when (not (nil? s))
      ;; here we can just replace the expression with the variable names
      (let [vmap (zipmap (map #(make-variable (str "$" %)) (range)) args)]
        (remap-variables s vmap)))))
