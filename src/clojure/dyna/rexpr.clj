(ns dyna.rexpr
  (:require [dyna.utils :refer :all])
  (:require [dyna.context :as context])
  (:require [dyna.system :as system])
             ;:rename '{get-value context-get-value,
             ;          is-bound? context-is-bound?
             ;          set-value! context-set-value!}

  (:require [clojure.set :refer [union difference]])
  (:require [aprint.core :refer [aprint]])
  (:import (dyna UnificationFailure))
  (:import (dyna DynaTerm)))


(declare simplify)
(def simplify-construct identity)
(declare find-iterators)


;; maybe this should recurse through the structure and make a nice print out of the term objets
(defmethod print-method DynaTerm [^DynaTerm this ^java.io.Writer w]
  (.write w (.toString this)))

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
  (rewrite-rexpr-children [this remap-function])
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
                ~(symbol (str "make-no-simp-" name)) ;; this should really be something that is "require context"
                ~(symbol (str "is-" name "?")))
       (deftype-with-overrides ~(symbol rname) ~(vec (concat (quote [^int cached-hash-code ^:unsynchronized-mutable cached-exposed-variables])
                                                             (map cdar vargroup)))
         ~opt
         Rexpr
         ~'(primitive-rexpr [this] this) ;; this is a primitive expression so we are going to just always return ourselves
         (~'get-variables ~'[this]
          (filter variable?
                  (union #{~@(map cdar (filter #(contains?  #{:var :value} (car %1)) vargroup))}
                         ~@(map (fn [x] `(set ~(cdar x))) (filter #(= :var-list (car %1)) vargroup))
                         )))

         (~'get-children ~'[this]
          (concat
           (list ~@(map cdar (filter #(= :rexpr (car %1)) vargroup)))
           ~@(map cdar (filter #(= :rexpr-list (car %1)) vargroup))))

         ;; might be better if there was some case and switch statement for get-argument
         ;; constructing the vector is likely going to be slow.  Would be nice if there was some array representation or something
         (~'get-argument ~'[this n] ;; trying to add a type hit to this makes it such that the interface will not get cast correctly
          (case (unchecked-int ~'n)
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
                                          :value `(get ~'variable-map ~(cdar v) ~(cdar v))
                                          :hidden-var `(get ~'variable-map ~(cdar v) ~(cdar v))
                                          :var-list `(map #(get ~'variable-map % %) ~(cdar v))
                                          :var-map `(into {} (for [~'[kk vv] ~(cdar v)] [~'kk (get ~'variable-map ~'vv ~'vv)]))
                                          :rexpr `(remap-variables ~(cdar v) ~'variable-map)
                                          :rexpr-list `(map #(remap-variables % ~'variable-map) ~(cdar v))
                                          (cdar v) ;; the default is that this is the same
                                          )])))
              (if (and ~@(for [v vargroup]
                           `(= ~(cdar v) ~(symbol (str "new-" (cdar v))))))
                ~'this ;; then there was no change, so we can just return ourself
                ;; there was some change, so we are going to need to create a new object with the new values
                (~(symbol (str "make-" name)) ~@(for [v vargroup]
                                                          (symbol (str "new-" (cdar v)))))))))
         (~'rewrite-rexpr-children ~'[this remap-function]
          (let ~(vec (apply concat
                            (for [v vargroup]
                              (when (contains? #{:rexpr :rexpr-list} (car v))
                                [(symbol (str "new-" (cdar v)))
                                 (case (car v)
                                   :rexpr `(~'remap-function ~(cdar v))
                                   :rexpr-list `(map ~'remap-function ~(cdar v)))]
                                ))))
            (if (and ~@(for [v vargroup]
                         (when (contains? #{:rexpr :rexpr-list} (car v))
                           `(= ~(cdar v) ~(symbol (str "new-" (cdar v)))))))
              ~'this ;; return unchanged
              ;; this might want to use the simplification method on the returned result.  That will let it get the at construction
              ;; time rewrites
              (~(symbol (str "make-" name)) ~@(for [v vargroup]
                                                        (if (contains? #{:rexpr :rexpr-list} (car v))
                                                          (symbol (str "new-" (cdar v)))
                                                          (cdar v))))
              )))

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
         ~@(when system/check-rexpr-arguments
             (map (fn [x] `(if (not (~(resolve (symbol (str "check-argument-" (symbol (car x))))) ~(cdar x)))
                             (do (.printStackTrace (Throwable. (str "Argument value check failed: " ~(car x) ~(cdar x))) System/err)
                                 (debug-repl ~(str "check argument " (car x)))
                                 (assert false)))) vargroup))
         (~(symbol (str rname "."))
          ;; this hash implementation needs to match the one below....
          (unchecked-int ~(reduce (fn [a b] `(unchecked-add-int ~a ~b))
                                  (hash rname)
                                  (for [[var idx] (zipmap vargroup (range))]
                                    `(unchecked-multiply-int (hash ~(cdar var)) ~(+ 3 idx)))))

          nil                           ; the cached unique variables
          ~@(map cdar vargroup))
         )

       (defn ~(symbol (str "make-" name))
         {:rexpr-constructor (quote ~name)
          :rexpr-constructor-type ~(symbol rname)}
         ~(vec (map cdar vargroup))
         ~@(when system/check-rexpr-arguments
            (map (fn [x] `(if (not (~(resolve (symbol (str "check-argument-" (symbol (car x))))) ~(cdar x)))
                            (do (debug-repl ~(str "check argument " (car x)))
                                (assert false)))) vargroup))

         (simplify-construct (~(symbol (str rname "."))
                              ;; this might do the computation as a big value, would be nice if this could be forced to use a small int value
                              ;; I suppose that we could write this in java and call out to some static function if that really became necessary
                              ;; this hash implementation needs to match the one above....
                              (unchecked-int ~(reduce (fn [a b] `(unchecked-add-int ~a ~b))
                                  (hash rname)
                                  (for [[var idx] (zipmap vargroup (range))]
                                    `(unchecked-multiply-int (hash ~(cdar var)) ~(+ 3 idx)))))
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
  (get-value [this] (context/get-value (context/get-context) this))
  (set-value! [this value]
    (context/set-value! (context/get-context) this value))
  (is-bound? [this]  (context/need-context (context/is-bound? (context/get-context) this)))
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
  (.write w (.toString ^Object this)))

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


;; these are checks which are something that we might want to allow ourselves to turn off
(defn check-argument-mult [x] (or (and (int? x) (>= x 0)) (= ##Inf x)))
(defn check-argument-rexpr [x] (rexpr? x))
(defn check-argument-rexpr-list [x] (and (seqable? x) (every? rexpr? x)))
(defn check-argument-var [x] (or (variable? x) (is-constant? x))) ;; a variable or constant of a single value.  Might want to remove is-constant? from this
(defn check-argument-var-list [x] (and (seqable? x) (every? variable? x)))
(defn check-argument-var-map [x] (and (map? x) (every? (fn [[a b]] (and (check-argument-var a)
                                                                        (check-argument-var b)))
                                                       x)))
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


(defn set-variable [var value]
  ;; would be nice if there was a bit more efficient approach to this method?
  ;; this might be something where we can handle which of the expressions
  (make-unify var (make-constant value)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(def-base-rexpr user-call [:unchecked name  ;; the name for this call object.  Will include the name, arity and file for which this call is being performed from
                            ;; :str name ;; the name for this call represented as a string
                            ;; :int arity  ;; the arity for this call
                            ;; :var from-file
                            :var-map args-map ;; the arguments which are present for this call
                            :unchecked call-depth]
  (get-variables [this] (into #{} (vals args-map))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; an optimized version of aggregation which does projection and the aggregation in the same operator
;; the aggregator outer should only have a list of aggregator-op-inner as its arguments
(def-base-rexpr aggregator-op-outer [:str operator
                                     :var result
                                     :rexpr bodies])

(def-base-rexpr aggregator-op-inner [:var incoming
                                     :var-list projected
                                     :rexpr body])


;; would be nice if we knew which of the variables were required for an
;; expression to be externally satasified I suppose that could just be all of
;; the variables which are not projected out of an expression so it could go
;; through and attempt to identify which of the expressions are more efficiently
;; represented by some expression.  This will correspond with



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
  (get-children [this] (recurse-values-depth rexprs (count disjunction-variables)))

  (remap-variables
   [this variable-renaming-map]
   (if (empty? variable-renaming-map) this
       (let [new-disjuncts (map #(get variable-renaming-map % %) disjunction-variables)]
         ;; if one of the variables is a constant, then we can avoid keeping the entire structure
         ;; also we might want to have some of the expressions

         (assert false)
         )
       )
   )

  )


(defn make-proj-many [vars R]
  (if (empty? vars)
    R
    (make-proj (first vars)
               (make-proj-many (rest vars) R))))


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
          :standard `(var-get #'rexpr-rewrites)
          :construction `(var-get #'rexpr-rewrites-construct)
          :standard-and-construction `(var-get #'rexpr-rewrites-construct) ;; this should also run these when their variables become ground
          :construction-and-grounding-change nil ;; this could run it when there is a new variable which is ground, which might be useful in avoiding running sutff too much?
          :inference `(var-get #'rexpr-rewrites-inference))
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
       (context/is-bound? (context/get-context) variable))))

(defn is-constant? [variable]
  (instance? constant-value-rexpr variable))

(defn get-variable-value [variable]
  (if (instance? constant-value-rexpr variable)
    (.value ^constant-value-rexpr variable)
    (context/get-value (context/get-context) variable)))


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

;; the context is assumed to be already constructed outside of this function
;; this will need for something which needs for the given functionq
(defn simplify-fully [rexpr]
  (let [prev (atom nil)
        cr (atom rexpr)]
    (while (not= @cr @prev)
      (reset! prev @cr)
      (swap! cr simplify))
    @cr))

(defn simplify-top [rexpr]
  (let [ctx (context/make-empty-context rexpr)]
    (context/bind-context ctx
                          (simplify-fully rexpr))))

(defn simplify-rexpr-query [query-id rexpr]
  ;; TODO: we might want to make this construct some table for the expression.  So what representation would come back from the expression
  (let [ctx (context/make-empty-context rexpr)
        res (context/bind-context ctx
                                  (simplify-fully rexpr))]
    ;; there needs to be a better way to get the bindigns to variables rather than doing this "hack" to get the map
    (system/query-output query-id (get (context/get-inner-values ctx) 3) res)))


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
      (boolean (.value ^constant-value-rexpr var-name)))))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-rewrite
  :match (unify (:any A) (:any B))
  :run-at :construction
  (if (= A B) ;; these two structures are equal to each other, so we can just remove the expression
    (make-multiplicity 1)))

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
  (make-conjunct (doall (map simplify children))))

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
      (when (not= @num-mults 1) ;; if there is only 1 mult, then we should just keep the same expression
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
              (context/add-context! (context/get-context) ctx)
              r)
            (assert false))
        (do
          ;; then there are two or more values, so this needs to intersect all of the contexts and
          (let [same-context (reduce context/intersect (map car found))]
            ;; the new intersection is going to be added to the global context
            (context/add-context! (context/get-context) same-context)
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

  (let [ctx (context/make-nested-context-introduce-variable R A)
        nR (context/bind-context ctx
                                 (simplify R))]
    (if (context/is-bound? ctx A)
      ;; if there is some unified expression, it would be nice if we could also attempt to identify if some expression is unified together
      ;; in which case we can remove the proj using the expression of
      (let [var-val (context/get-value ctx A)
            replaced-R (remap-variables nR {A (make-constant var-val)}) ;; this is a bit annoying as it is going through and doing replacements
            ;; vvv (context/get-inner-values ctx)
            ;; all-bindings (context/get-all-bindings ctx)
            ]
          ;(debug-repl) ;; this is going to have to propagate the value of the new variable into the body
          ;; this is either already done via the context?  Or this is going to be slow if we have a large expression where we have to do lots of
          ;; replacements of the variables
          replaced-R)
        (make-proj A nR))))


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

(def-rewrite
  :match (user-call (:unchecked name) (:unchecked var-map) (:unchecked call-depth))
  :run-at :construction
  (let [n [(:name name) (:arity name)] ;; this is how the name for built-in R-exprs are represented.  There is no info about the file
        s (get @system/system-defined-user-term n)]
    (when s
      (remap-variables s var-map))))


(def-rewrite
  :match (aggregator (:unchecked operator) (:any result-variable) (:any incoming-variable) (:rexpr R))
  (let [ctx (context/make-nested-context-introduce-variable R incoming-variable)
        nR (context/bind-context ctx (simplify R))]
    (if (and (context/is-bound? ctx incoming-variable) (= (make-multiplicity 1) nR))
      (make-unify result-variable (make-constant (context/get-value ctx incoming-variable)))
      (do
        ;; if there is more stuff, then this will which of the expressions corresponds with it having either higher multiplicies, or more disjunctions
        ;; that need to get handled here
        (assert (not (context/is-bound? ctx incoming-variable))) ;; todo
        (make-aggregator operator result-variable incoming-variable nR)))))
