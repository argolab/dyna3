(ns dyna.rexpr
  (:require [dyna.utils :refer :all])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.rexpr-constructors])
  (:require [dyna.context :as context])
  (:require [dyna.system :as system])
  (:require [dyna.iterators :as iterators])
  (:require [clojure.set :refer [union difference subset?]])
  (:require [clojure.string :refer [trim]])
  (:require [aprint.core :refer [aprint]])
  (:import (dyna UnificationFailure))
  (:import (dyna DynaTerm)))

(defn simplify-identity [a b] a)

(declare simplify
         simplify-inference)
(def simplify-construct identity)
(declare find-iterators)


;; maybe this should recurse through the structure and make a nice print out of the term objets
(defmethod print-method DynaTerm [^DynaTerm this ^java.io.Writer w]
  (.write w (.toString this)))


(def rexpr-containers (atom #{}))
(def rexpr-constructors (atom {}))
(def rexpr-containers-signature (atom {}))

(def ^:dynamic *current-matched-rexpr* nil)
(def ^:dynamic *current-top-level-rexpr* nil)
(def ^:dynamic *current-simplify-stack* [])

(when system/track-where-rexpr-constructed  ;; meaning that the above variable will be defined
  (swap! debug-useful-variables assoc
         'rexpr (fn [] *current-matched-rexpr*)
         'rexpr-top-level (fn [] *current-top-level-rexpr*)
         'top-level-rexpr (fn [] *current-top-level-rexpr*)
         'simplify-stack (fn [] *current-simplify-stack*)))

(defn construct-rexpr [name & args]
  (apply (get @rexpr-constructors name) args))

(defmacro def-base-rexpr [name args & optional]
  (let [vargroup (partition 2 args)
        rname (str name "-rexpr")
        flags (into #{} (filter keyword? optional))
        opt (if (not (nil? optional)) (vec (filter #(not (keyword? %)) optional)) [])]
    `(do
       (swap! rexpr-containers-signature assoc '~name (quote ~vargroup))
       (declare ~(symbol (str "make-" name))
                ~(symbol (str "make-no-simp-" name)) ;; this should really be something that is "require context"
                ~(symbol (str "is-" name "?")))
       (intern 'dyna.rexpr-constructors '~(symbol (str "simplify-" name)) simplify-identity)
       (intern 'dyna.rexpr-constructors '~(symbol (str "simplify-construct-" name)) simplify-identity)
       (intern 'dyna.rexpr-constructors '~(symbol (str "simplify-inference-" name)) simplify-identity)

       (deftype-with-overrides ~(symbol rname) ~(vec (concat (quote [^int cached-hash-code ^:unsynchronized-mutable cached-exposed-variables])
                                                             (if system/track-where-rexpr-constructed (quote [traceback-to-construction traceback-to-rexpr]))
                                                             (map cdar vargroup)))
         ~opt
         clojure.lang.ILookup
         (~'valAt ~'[this name-to-lookup-gg not-found]
          (case ~'name-to-lookup-gg
            ~@(apply concat (for [[idx var] (zipmap (range) vargroup)]
                              `[~idx ~(cdar var)]))
            ~@(apply concat (for [var vargroup]
                              `[~(keyword (cdar var)) ~(cdar var)]))
            ~@(if system/track-where-rexpr-constructed `[:constructed-where ~'traceback-to-construction
                                                         :where-constructed ~'traceback-to-construction
                                                         :constructing-rexpr ~'traceback-to-rexpr
                                                         :constructed-from ~'traceback-to-rexpr])
            ~'not-found))
         ~'(valAt [this name] (let [r (.valAt this name :not-found-result)]
                                (assert (not= :not-found-result r))
                                r))
         Rexpr
         ~'(primitive-rexpr [this] this) ;; this is a primitive expression so we are going to just always return ourselves
         (~'get-variables ~'[this]
          (filter is-variable?
                  (union (set (list ~@(map cdar (filter #(contains?  #{:var :value} (car %1)) vargroup))))
                         ~@(map (fn [x] `(set ~(cdar x))) (filter #(= :var-list (car %1)) vargroup))
                         ~@(map (fn [x] `(set (values ~(cdar x)))) (filter #(= :var-map (car %1)) vargroup))
                         ;; TODO: this needs to handle the case where there is the var-set-map which will have nested variable inside of the arguments
                         ;;~@(map (fn [x] `(set (values ))))
                         )))
         (~'get-all-variables-rec ~'[this]
          (apply union (get-variables ~'this)
                 (map get-all-variables-rec (get-children ~'this))))
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
          (debug-try
           (cache-field ~'cached-exposed-variables
                        (set
                         (filter is-variable?
                                 (difference (union (set (get-variables ~'this))
                                                    ~@(keep
                                                       #(if (= :rexpr (car %))
                                                          `(exposed-variables ~(cdar %)))
                                                       vargroup)
                                                    ~@(keep
                                                       #(if (= :rexpr-list (car %))
                                                          `(apply union (map exposed-variables ~(cdar %)))) vargroup))
                                             #{~@(keep
                                                  #(if (= :hidden-var (car %)) (cdar %))
                                                  vargroup)}))))
           (catch java.lang.ClassCastException ~'error
             (do (debug-repl "class cast exception")
                 (throw ~'error)))
           ))
         (~'remap-variables ~'[this variable-map]
          (context/bind-no-context  ;; this is annoying, this will want to be
                                    ;; something that we can avoid doing
                                    ;; multiple times.  Which rewrites that we
                                    ;; can perform should be something that is
                                    ;; collected ahead of time, so there will be
                                    ;; some rewrites which are "renaming-safe",
                                    ;; or it will want to denote that it
                                    ;; requires a context
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
                                           :var-set-map `(into #{} (for [~'s ~(cdar v)]
                                                                     (into {} (for [~'[kk vv] ~'s] [~'kk (get ~'variable-map ~'vv ~'vv)]))))
                                           :rexpr `(remap-variables ~(cdar v) ~'variable-map)
                                           :rexpr-list `(map #(remap-variables % ~'variable-map) ~(cdar v))
                                           (cdar v) ;; the default is that this is the same
                                           )])))
               (if (and ~@(for [v vargroup]
                            `(= ~(cdar v) ~(symbol (str "new-" (cdar v))))))
                 ~'this ;; then there was no change, so we can just return ourself
                 ;; there was some change, so we are going to need to create a new object with the new values
                 (~(symbol (str "make-" name)) ~@(for [v vargroup]
                                                   (symbol (str "new-" (cdar v))))))))))
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

         (~'rewrite-rexpr-children-no-simp ~'[this remap-function]
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
              (~(symbol (str "make-no-simp-" name)) ~@(for [v vargroup]
                                                        (if (contains? #{:rexpr :rexpr-list} (car v))
                                                          (symbol (str "new-" (cdar v)))
                                                          (cdar v))))
              )))

         (~'remap-variables-handle-hidden ~'[this variable-map-in]
          ;; this is not allowed to stop early, as in the case that there is  somethign which
          (let [~'variable-map ~(if (some #{:hidden-var} (map car vargroup))
                                  `(assoc ~'variable-map-in ;; generate new names for
                                          ~@(apply concat (for [v vargroup]
                                                            (when (= :hidden-var (car v))
                                                              [(cdar v) `(make-variable (gensym ~(str "remap-hidden-" name "-" (cdar v))))]))))
                                  'variable-map-in  ;; there is nothing new for this, so can't use assoc
                                  )]
            (let ~(vec (apply concat (for [v vargroup]
                                       [(symbol (str "new-" (cdar v)))
                                        (case (car v)
                                          :var `(get ~'variable-map ~(cdar v) ~(cdar v))
                                          :value `(get ~'variable-map ~(cdar v) ~(cdar v))
                                          :hidden-var `(get ~'variable-map ~(cdar v) ~(cdar v))
                                          :var-list `(map #(get ~'variable-map % %) ~(cdar v))
                                          :var-map `(into {} (for [~'[kk vv] ~(cdar v)] [~'kk (get ~'variable-map ~'vv ~'vv)]))
                                          :var-set-map `(into #{} (for [~'s ~(cdar v)]
                                                                    (into {} (for [~'[kk vv] ~'s] [~'kk (get ~'variable-map ~'vv ~'vv)]))))
                                          :rexpr `(remap-variables-handle-hidden ~(cdar v) ~'variable-map)
                                          :rexpr-list `(map #(remap-variables-handle-hidden % ~'variable-map) ~(cdar v))
                                          (cdar v) ;; the default is that this is the same
                                          )])))
              (let [result# (~(symbol (str "make-" name)) ~@(for [v vargroup]
                                                              (symbol (str "new-" (cdar v)))))]
                (if (= result# ~'this) ;; because something internal might need
                                       ;; to rename its variables, we can't stop
                                       ;; early, but we can check that the
                                       ;; result is different before we return
                                       ;; something new, so hopefully avoid
                                       ;; creating too many similar objects
                  ~'this
                  result#)))))

         Object
         (equals ~'[this other]
           (or (identical? ~'this ~'other)
               (and (instance? ~(symbol rname) ~'other)
                    (= (hash ~'this) (hash ~'other))
                    ~@(for [[var idx] (zipmap vargroup (range))]
                        `(= ~(cdar var) (get-argument ~'other ~idx))))))

         (hashCode [this] ~'cached-hash-code) ;; is this something that should only be computed on demand instead of when it is constructed?
         (toString ~'[this] (trim (str (as-list ~'this)))))

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
          ~@(if system/track-where-rexpr-constructed `[(Throwable.) dyna.rexpr/*current-matched-rexpr*])
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
                              ~@(if system/track-where-rexpr-constructed `[(Throwable.) dyna.rexpr/*current-matched-rexpr*])
                              ~@(map cdar vargroup))))
       (swap! rexpr-constructors assoc ~(str name) ~(symbol (str "make-" name)))
       (defn ~(symbol (str "is-" name "?")) ~'[rexpr]
         (instance? ~(symbol rname) ~'rexpr))
       (defmethod print-method ~(symbol rname) ~'[this ^java.io.Writer w]
         (assert (not (nil? ~'w)))
         (aprint (as-list ~'this) ~'w))
       (intern 'dyna.rexpr-constructors '~(symbol (str "make-" name)) ~(symbol (str "make-" name)))
       (intern 'dyna.rexpr-constructors '~(symbol (str "make-no-simp-" name)) ~(symbol (str "make-no-simp-" name)))
       (intern 'dyna.rexpr-constructors '~(symbol (str "is-" name "?")) ~(symbol (str "is-" name "?")))
       ;; (swap! rexpr-rewrites-func assoc ~(symbol (str name "-rexpr")) identity)
       ;; (swap! rexpr-rewrites-construct-func assoc ~(symbol (str name "-rexpr")) identity)
       ;; (swap! rexpr-rewrites-inference-func assoc ~(symbol (str name "-rexpr")) identity)
       )))


(defn make-structure [name args]
  (DynaTerm. name nil nil args))
(intern 'dyna.rexpr-constructors 'make-structure make-structure)

(def ^:const null-term (DynaTerm/null_term))

(defmethod print-dup DynaTerm [^DynaTerm term ^java.io.Writer w]
  (.write w "(dyna.DynaTerm. ")
  (print-dup (.name term) w)
  (.write w " ")
  (print-dup (.dynabase term) w)
  (.write w " ")
  (print-dup (.from_file term) w)
  (.write w " ")
  (print-dup (vec (.arguments term)) w)
  (.write w ")"))


;;;;;;;;;;;;;;;;;;;;;;;;;;
;; things like variables and constants should instead be some other type rather than an R-expr
;; this could be something


(defrecord variable-rexpr [varname]
  RexprValue
  (get-value [this] (ctx-get-value (context/get-context) this))
  (get-value-in-context [this ctx] (ctx-get-value ctx this))
  (set-value! [this value]
    (ctx-set-value! (context/get-context) this value))
  (is-bound? [this]  (context/need-context (ctx-is-bound? (context/get-context) this)))
  (is-bound-in-context? [this context] (ctx-is-bound? context this))
  (all-variables [this] #{this})
  Object
  (toString [this] (str "(variable " varname ")")))

(defn make-variable [varname]
  (variable-rexpr. varname))
(intern 'dyna.rexpr-constructors 'make-variable make-variable)

(defmethod print-method variable-rexpr [^variable-rexpr this ^java.io.Writer w]
  (.write w (str "(variable " (.varname this) ")")))

;; we can just use (Object.) to create a unique object name.  This will be aster
;; than having a global counter, but will be "more annoying" to print stuff out...
(defn make-unique-variable
  ([] (make-variable (gensym 'unique-var)))
  ([base-name] (variable-rexpr. (gensym base-name))))
(intern 'dyna.rexpr-constructors 'make-unique-variable make-unique-variable)

(defrecord constant-value-rexpr [value]
  RexprValue
  (get-value [this] value)
  (get-value-in-context [this ctx] value)
  (set-value! [this v]
    (if (not= v value)
      (throw (UnificationFailure. "can not assign value to constant"))))
  (is-bound? [this] true)
  (is-bound-in-context? [this context] true)
  (all-variables [this] #{})
  Object
  (toString [this] (str "(constant " value ")")))


(defn make-constant [val]
  (when (nil? val) (debug-repl))
  (assert (not (nil? val))) ;; otherwise this is a bug
  (constant-value-rexpr. val))
(intern 'dyna.rexpr-constructors 'make-constant make-constant)

(let [tv (make-constant true)
      fv (make-constant false)]
  (defn make-constant-bool [val]
    (if val tv fv)))

(defmethod print-method constant-value-rexpr [^constant-value-rexpr this ^java.io.Writer w]
  (.write w (str "(constant " (.value this) ")")))


;; ;; should the structured types have their own thing for how their are represented
;; ;; though these will want to have some e
;; (defrecord structured-rexpr [name arguments]
;;   RexprValue
;;   (get-value [this]
;;     ;; this is going to have to construct the structure for this
;;     ;; which means that it has to get all of the values, and then flatten it to a structure
;;     (make-structure name (doall (map get-value arguments))))
;;   (get-value-in-context [this ctx]
;;     (make-structure name (doall (map #(get-value-in-context % ctx) arguments))))

;;   (set-value! [this v]
;;     (if (or (not= (car v) name) (not= (+ 1 (count arguments)) (count v)))
;;       (throw (UnificationFailure. "name/arity does not match structure"))
;;       (doall (map set-value! arguments (cdr v)))
;;       ))

;;   (is-bound? [this]
;;     (context/need-context (every? is-bound? arguments)))
;;   (is-bound-in-context? [this context]
;;     (every? #(is-bound-in-context? % context) arguments))
;;   (all-variables [this] (apply union (map all-variables arguments)))
;;   Object
;;   (toString [this] (str "(structure " name " " arguments ")")))

;; (defn make-structured-rexpr [name arguments]
;;   (???) ;; not used anymore
;;   (assert (string? name))
;;   (assert (every? (partial satisfies? RexprValue) arguments))
;;   (structured-rexpr. name arguments))

;; (defmethod print-method structured-rexpr [^structured-rexpr this ^java.io.Writer w]
;;   (.write w (.toString ^Object this)))

;; (defn make-structured-value [name values]
;;   (assert (every? (partial satisfies? RexprValue) values))
;;   (assert (string? name))
;;   (structured-rexpr. name values))

(defn is-constant? [x] (instance? constant-value-rexpr x))

(defn is-variable? [variable]
  (instance? variable-rexpr variable))
(intern 'dyna.rexpr-constructors 'is-variable? is-variable?)

(defn rexpr? [rexpr]
  (and (satisfies? Rexpr rexpr)
       (not (or (is-variable? rexpr) (is-constant? rexpr)))))


;; these are checks which are something that we might want to allow ourselves to turn off
(defn check-argument-mult [x] (or (and (int? x) (>= x 0)) (= ##Inf x)))
(defn check-argument-rexpr [x] (rexpr? x))
(defn check-argument-rexpr-list [x] (and (seqable? x) (every? rexpr? x)))
(defn check-argument-var [x] (or (is-variable? x) (is-constant? x))) ;; a variable or constant of a single value.  Might want to remove is-constant? from this
(defn check-argument-var-list [x] (and (seqable? x) (every? check-argument-var x)))
(defn check-argument-var-map [x] (and (map? x) (every? (fn [[a b]] (and (check-argument-var a)
                                                                        (check-argument-var b)))
                                                       x)))
(defn check-argument-var-set-map [x] (and (set? x) (every? check-argument-var-map x)))
(defn check-argument-value [x] (satisfies? RexprValue x)) ;; something that has a get-value method (possibly a structure)
(defn check-argument-hidden-var [x] (check-argument-var x))
(defn check-argument-str [x] (string? x))
(defn check-argument-unchecked [x] true)
(defn check-argument-opaque-constant [x] ;; something that is not in the R-expr language
  (not (or (satisfies? Rexpr x) (satisfies? RexprValue x))))
(defn check-argument-boolean [x] (boolean? x))
(defn check-argument-file-name [x]
  (or (nil? x)
      (= "REPL" x)
      (instance? java.net.URL x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(def-base-rexpr multiplicity [:mult mult])

;; there is meta information on this which needs to be carried forward
(when-not system/track-where-rexpr-constructed ;; if we are tracing where it was
                                               ;; constructed from, then we do
                                               ;; not want to have the thing
                                               ;; used a cached representation
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
        0 (do
            false-mul) ; we can special case the common values to avoid creating these objects many times
        1 true-mul
        (prev x)))))

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
           (and (is-disjunct? rexpr) (some is-non-empty-rexpr? (get-argument rexpr 0))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-base-rexpr unify [:value a ;; this should be changed to just use :var
                       :value b])

(def-base-rexpr unify-structure [:var out
                                 :file-name file-name
                                 :var dynabase ;; the dynabase variable is only
                                               ;; used for reading when
                                               ;; constructing a new structure.
                                               ;; When destrcturing a term, this
                                               ;; will _not_ unify with this
                                               ;; variable
                                 :str name
                                 :var-list arguments])

;; read the dynabase from a particular constructed structure.  This will require that structure become ground
;; the file reference is also required to make a call to a top level expression
;; (def-base-rexpr unify-structure-get-meta [:var structure
;;                                           :var dynabase
;;                                           :var from-file])



(def-base-rexpr proj [:hidden-var var
                      :rexpr body]
  (remap-variables-handle-hidden [this variable-map]
                                 (let [new-hidden-name (make-variable (gensym 'proj-hidden))]
                                   (make-proj new-hidden-name (remap-variables-handle-hidden body (assoc variable-map var new-hidden-name)))))
  (remap-variables [this variable-map]
                   (dyna-debug (when-not (not (some #{var} (vals variable-map)))
                                 (debug-repl "bad remap")))

                   (make-proj var (remap-variables body variable-map))))

(def-base-rexpr aggregator [:str operator
                            :var result
                            :hidden-var incoming
                            ;; if the body-is-conjunctive == true, then there are additional optimizations that we can perform
                            :boolean body-is-conjunctive
                            :rexpr body])

(def-base-rexpr if [:rexpr cond
                    :rexpr true-branch
                    :rexpr false-branch])


;; (defn set-variable [var value]
;;   ;; would be nice if there was a bit more efficient approach to this method?
;;   ;; this might be something where we can handle which of the expressions
;;   (make-unify var (make-constant value)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(def-base-rexpr user-call [:unchecked name  ;; the name for this call object.  Will include the name, arity and file for which this call is being performed from
                           ;; :str name ;; the name for this call represented as a string
                           ;; :int arity  ;; the arity for this call
                           ;; :var from-file
                           :var-map args-map ;; the arguments which are present for this call
                           :unchecked call-depth
                           :var-set-map args-parent-map ;; this needs to track which
                           ]
  (get-variables [this] (into #{} (vals args-map))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;; an optimized version of aggregation which does projection and the aggregation in the same operator
;; ;; the aggregator outer should only have a list of aggregator-op-inner as its arguments
;; (def-base-rexpr aggregator-op-outer [:str operator
;;                                      :var result
;;                                      :rexpr bodies])

;; (def-base-rexpr aggregator-op-inner [:var incoming
;;                                      :var-list projected
;;                                      :rexpr body])


;; would be nice if we knew which of the variables were required for an
;; expression to be externally satasified I suppose that could just be all of
;; the variables which are not projected out of an expression so it could go
;; through and attempt to identify which of the expressions are more efficiently
;; represented by some expression.  This will correspond with


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

(def rexpr-rewrites-func (atom {}))
(def rexpr-rewrites-construct-func (atom {}))
(def rexpr-rewrites-inference-func (atom {}))

;; functions which define how iterators are accessed for a given Rexpr
(def rexpr-iterators-accessors (atom {}))

;; make a linked list of functions which match against a given type
(defn- combine-rewrite-function [first-function second-function]
  (fn [rexpr simplify]
    (let [res (first-function rexpr simplify)]
      (if (or (nil? res) (= res rexpr))
        (second-function rexpr simplify) ;; second function will likely be the new added function
        (do
          (assert (rexpr? res))
          res)))))


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


(declare make-matching-function
         make-rexpr-matching-function
         make-context-matching-function)


(defn- make-context-matching-function [present-variables context-match body]
  (let [rexpr-context (gensym 'rexpr-context)]
    `(context/scan-through-context-by-type (context/get-context)
                                           ~(symbol (str (car context-match) "-rexpr"))
                                           ~rexpr-context
                                           (when (and ~@(for [pv present-variables]  ;; do not want to match something that has already been matched
                                                          `(not= ~pv ~rexpr-context)))
                                                 ~(make-rexpr-matching-function rexpr-context (conj present-variables rexpr-context) context-match body)))))


(defn- make-rexpr-matching-function [source-variable present-variables matcher body]
  (let [rexpr-match (if (map? matcher) (:rexpr matcher) matcher)
        context-matcher (if (map? matcher) (:context matcher))
        rexpr-type-matched (car rexpr-match)
        match-args (vec (map (fn [a]
                               (cond
                                 (and (symbol? a) (contains? present-variables a)) (let [r (gensym 'match-equals-var)]
                                                                                     [`(= ~a ~r) r nil])
                                 (= a '_) [`true (gensym 'do-not-care) nil]
                                 (symbol? a) [`true a nil]
                                 (and (= 2 (count a)) (not (contains? @rexpr-containers (car a))) (symbol? (cdar a)))
                                   (let [var (if (= (cdar a) '_) (gensym 'do-not-reuse) (cdar a))
                                         checker (get @rexpr-matchers (car a) (car a))]
                                     [`(~checker ~var) var nil])
                                 :else [`true (gensym 'more-match) a]))
                             (cdr rexpr-match)))
        present-variables (union present-variables (into #{} (map cdar match-args)))
        body2 (if (and (map? matcher) (contains? matcher :check))
                (fn [pv]
                  `(when ~(:check matcher) ~(body pv)))
                body)
        generate-body (loop [matchers (reverse match-args)
                             body-fn body2]
                        (if (empty? matchers) body-fn
                            (if (nil? (caddar matchers)) (recur (cdr matchers) body-fn)
                                (recur (cdr matchers)
                                       (fn [c-present-vars]
                                         (make-rexpr-matching-function (cadar matchers) c-present-vars (caddar matchers) body-fn))))))]
    (assert (= (count (get @rexpr-containers-signature (symbol rexpr-type-matched))) (- (count rexpr-match) 1))
            "The R-expr match expression does not contain the right number of arguments, it will never match")
    (assert (or (not (map? matcher)) (subset? (keys matcher) #{:rexpr :context :check}))
            "matcher map contains unexepxected key")
    `(when (~(symbol (str "is-" rexpr-type-matched "?")) ~source-variable)
       (let [~(vec (map cdar match-args)) (get-arguments ~source-variable)]
         (when (and ~@(remove true? (map car match-args)))
           ~(if (not (nil? context-matcher))
              (make-context-matching-function present-variables context-matcher generate-body)
              (generate-body present-variables)))))))

(defn- match-rexpr-fn [source-variable matcher body]
  (let [source (gensym 'source)]
    `(let [~source ~source-variable] ;; copying the variable is probably not necessary in most cases???
       ~(make-rexpr-matching-function source #{source source-variable} matcher (fn [pv] body)))))

(defn- get-match-base-type [matcher]
  (car (if (map? matcher) (:rexpr matcher) matcher)))

(defmacro match-rexpr [source-variable matcher & body]
  (match-rexpr-fn source-variable matcher `(do ~@body)))

(defn- make-rewriter-function [matcher body from-file]
  ;; this needs to go through and define something where the different functions
  ;; are invoked on the relvant parts of the expression.  Because the
  ;; expressions have different field values, and are not positional, this means
  ;; that those matchers will have to extract the right values (or something
  (let [res (gensym 'res)
        do-rewrite-body `(let [~res (do ~body)]
                           ~(when system/print-rewrites-performed
                              `(when (and (not (nil? ~res)) (not= ~res ~'rexpr))
                                 (print ~(str "Performed rewrite:"  (meta from-file) "\nOLD: ") ~'rexpr "NEW: " ~res "CONTEXT:" (context/get-context))))
                           ~res)]
    `(fn (~'[rexpr simplify]
          (match-rexpr ~'rexpr ~matcher ~do-rewrite-body)))))

(defn- make-rewrite-func-body [kw-args body]
  (cond
    (:infers kw-args) `(let [infered-rexpr# ~(:infers kw-args)]
                         (when (or (is-empty-rexpr? infered-rexpr#) (not (ctx-contains-rexpr? (context/get-context) infered-rexpr#)))
                           (make-conjunct [(~'simplify infered-rexpr#) ~'rexpr])))
    :else body))

(defmacro def-rewrite [& args]
  (let [kw-args (apply hash-map (if (= (mod (count args) 2) 0)
                                  args
                                  (drop-last args)))
        rewrite (make-rewrite-func-body kw-args (last args)) ;; in the case that there is not a last argument, then this will want to match against hte value.
        matcher (:match kw-args)
        matcher-rexpr (if (map? matcher) (:rexpr matcher) matcher)
        functor-name (car matcher-rexpr)
        arity (if (= (cdar matcher-rexpr) :any) nil (- (count matcher-rexpr) 1))
        runs-at (:run-at kw-args :standard)
        rewriter-function (make-rewriter-function matcher rewrite &form)
        rewrite-func-var (gensym 'rewrite-func)]
    (let [ret `(let [~rewrite-func-var ~rewriter-function]
                 (locking dyna.rexpr-constructors/modification-lock
                   ~@(for [run-at (if (seqable? runs-at) runs-at [runs-at])]
                       `(let [[rewrite-collection# rewrite-collection-func#]
                              ~(case run-at
                                 :standard `[(var-get #'rexpr-rewrites) (var-get #'rexpr-rewrites-func)]
                                 :construction `[(var-get #'rexpr-rewrites-construct) (var-get #'rexpr-rewrites-construct-func)]
                                 :inference `[(var-get #'rexpr-rewrites-inference) (var-get #'rexpr-rewrites-inference-func)])
                              functor-name# ~(symbol (str functor-name "-rexpr"))]
                          ;; this is now also protected by the modification lock above???, so we don't need the atomic I guess....
                          (swap-vals! rewrite-collection# (fn [old#] (assoc old# functor-name# (conj (get old# functor-name# #{}) ~rewrite-func-var))))
                          ;; TODO: the first function is going to be the identity, which does not make since
                          (let [combined-func# (~combine-rewrite-function
                                   ~(symbol "dyna.rexpr-constructors" (str (case run-at
                                                                             :standard "simplify-"
                                                                             :construction "simplify-construct-"
                                                                             :inference "simplify-inference-")
                                                                           functor-name))
                                                ~rewrite-func-var)]
                            (intern 'dyna.rexpr-constructors '~(symbol (str (case run-at
                                                                              :standard "simplify-"
                                                                              :construction "simplify-construct-"
                                                                              :inference "simplify-inference-"
                                                                              )
                                                                            functor-name))
                                    combined-func#)
                            (swap-vals! rewrite-collection-func# assoc functor-name# combined-func#))))))]
      ret)))

(defmacro def-iterator [& args]
  (let [kw-args (apply hash-map (drop-last args))
        func-body (last args)
        matcher (:match kw-args)
        matcher-rexpr (if (map? matcher) (:rexpr matcher) matcher)
        functor-name (car matcher-rexpr)
        functor-type (symbol (str functor-name "-rexpr"))
        iter-func `(fn ~'[rexpr]
                     (match-rexpr ~'rexpr ~matcher ~func-body))
        ret `(let [iter-func# ~iter-func]
               (swap! rexpr-iterators-accessors (fn ~'[old]
                                                  (assoc ~'old ~functor-type (conj (get ~'old ~functor-type [])
                                                                                   iter-func#)))))
        ]
    ret))


(defn make-iterator [variable iterator]
  ;; these are going to need to be hashable, otherwise this would mean that we can't use the set to identify which expressions are iterable
  ;; there are some values which
  #{[variable iterator]})


(defn is-variable-set? [variable]
  (or (instance? constant-value-rexpr variable)
      (context/need-context
       (ctx-is-bound? (context/get-context) variable))))
(intern 'dyna.rexpr-constructors 'is-variable-set? is-variable-set?)

(defn is-constant? [variable]
  (instance? constant-value-rexpr variable))
(intern 'dyna.rexpr-constructors 'is-constant? is-constant?)

(defn get-variable-value [variable]
  (if (instance? constant-value-rexpr variable)
    (.value ^constant-value-rexpr variable)
    (ctx-get-value (context/get-context) variable)))


(defn simplify [rexpr]
  (assert (context/has-context))
  (let [ret  ((get @rexpr-rewrites-func (type rexpr) simplify-identity) rexpr simplify)]
    (if (or (nil? ret) (= ret rexpr))
      rexpr ;; if not changed, don't do anything
      (do
        (dyna-assert (rexpr? ret))
        (ctx-add-rexpr! (context/get-context) ret)
        ret))))

(swap! debug-useful-variables assoc 'simplify (fn [] simplify))

(defn simplify-construct [rexpr]
  (let [ret ((get @rexpr-rewrites-construct-func (type rexpr) simplify-identity) rexpr simplify-construct)]
    (if (nil? ret)
      rexpr
      (do
        (dyna-assert (rexpr? ret))
        ret))))

(defn simplify-inference [rexpr]
  (let [ctx (context/get-context)]
    (ctx-add-rexpr! ctx rexpr)
    (let [ret ((get @rexpr-rewrites-inference-func (type rexpr) simplify-identity) rexpr simplify-inference)]
      (if (nil? ret)
        rexpr
        (do (dyna-assert (rexpr? ret))
            (ctx-add-rexpr! ctx ret)
            ret)))))

;; the context is assumed to be already constructed outside of this function
;; this will need for something which needs for the given functionq
(if system/track-where-rexpr-constructed
  (defn simplify-fully [rexpr]
    (loop [cri rexpr]
      (let [nri (loop [cr cri]
                  (let [nr (binding [*current-top-level-rexpr* cr]
                             (simplify cr))]
                    (if (not= cr nr)
                      (recur nr)
                      nr)))
            nrif (binding [*current-top-level-rexpr* nri]
                   (simplify-inference nri))]
        (if (not= nrif nri)
          (recur nrif)
          nrif))))
  (defn simplify-fully [rexpr]
    (loop [cri rexpr ]
      (let [nri (loop [cr cri]
                  (let [nr (simplify cr)]
                    (if (not= cr nr)
                      (recur nr)
                      nr)))
            nrif (simplify-inference nri)]
        (if (not= nrif nri)
          (recur nrif)
          nrif)))))

(when system/track-where-rexpr-constructed
  (let [orig-simplify simplify
        orig-simplify-construct simplify-construct
        orig-simplify-inference simplify-inference]
    (defn simplify [rexpr] (binding [*current-simplify-stack* (conj *current-simplify-stack* rexpr)]
                             (orig-simplify rexpr)))
    (defn simplify-construct [rexpr] (binding [*current-simplify-stack* (conj *current-simplify-stack* rexpr)]
                                       (orig-simplify-construct rexpr)))
    (defn simplify-inference [rexpr] (binding [*current-simplify-stack* (conj *current-simplify-stack* rexpr)]
                                       (orig-simplify-inference rexpr)))))

(defn simplify-top [rexpr]
  (let [ctx (context/make-empty-context rexpr)]
    (context/bind-context ctx
                          (try (simplify-fully rexpr)
                               (catch UnificationFailure e (make-multiplicity 0))))))

(defn simplify-rexpr-query [query-id rexpr]
  ;; TODO: we might want to make this construct some table for the expression.
  ;; So what representation would come back from the expression

  ;; this could callback async, so we don't want something to depend on this
  ;; having finished a computation before the function returns.

  (let [ctx (context/make-empty-context rexpr)
        res (context/bind-context ctx
                                  (simplify-fully rexpr))]
    ;; TODO: this might not want to have the context added back into the R-expr?
    ;; in which case this is not going
    ;; there needs to be a better way to get the bindigns to variables rather than doing this "hack" to get the map
    (system/query-output query-id {:context ctx
                                   :context-value-map (get (ctx-get-inner-values ctx) 4)
                                   :rexpr res})))


(defn find-iterators [rexpr]
  (let [typ (type rexpr)
        rrs (get @rexpr-iterators-accessors typ [])]
    (apply union (for [rs rrs] (rs rexpr)))))


;; there should be some matcher which is going to identify which expression.
;; this would have some which expressions are the expressions
;; this is going to have to have some context in which an expression

(defn is-ground? [var-name]
  (or (and (is-variable? var-name) (is-variable-set? var-name))
      (is-constant? var-name)))

(def-rewrite-matcher :str [string] (string? string))

(def-rewrite-matcher :ground [var-name]
                                        ; this should be redfined such that it will return the ground value for the variable
                                        ; though we might not want to have the matchers identifying a given expression
  (is-ground? var-name))

(def-rewrite-matcher :not-ground [var] ;; TODO: I think I can just use :free instead of :not-ground, through the is only used by the unification construction
  (and (is-variable? var) (not (is-bound? var))))

(def-rewrite-matcher :free [var-name]
  (and (is-variable? var-name)
       (not (is-variable-set? var-name))
       var-name))


(def-rewrite-matcher :rexpr [rexpr] (rexpr? rexpr))

(def-rewrite-matcher :rexpr-list [rexpr-list]
                     (and (seqable? rexpr-list) (every? rexpr? rexpr-list)))

(def-rewrite-matcher :empty-rexpr [rexpr] (is-empty-rexpr? rexpr))


;; something that has a name first followed by a number of different unified expressions
;; (def-rewrite-matcher :structured [rexpr]
;;   (instance? structured-rexpr rexpr))
;; this could have that there is some meta-data that is contained in the context
;; then this will have to look at those values

(def-rewrite-matcher :variable [var]
  (is-variable? var))

(def-rewrite-matcher :variable-list [var-list]
  (every? is-variable? var-list))

(def-rewrite-matcher :ground-var-list [var-list]
  (every? is-ground? var-list))

(def-rewrite-matcher :any [v]
                     (or (is-variable? v) (is-constant? v)))

(def-rewrite-matcher :any-list [any-list]
  (every? #(or (is-variable? %) (is-constant? %)) any-list))

;; just match anything
(def-rewrite-matcher :unchecked [x] true)

;; this are things which we want to iterate over the domain for
;; this should
(def-rewrite-matcher :iterate [x]
  (and (is-variable? x) (not (is-bound? x))))

(def-rewrite-matcher :type-known [x]
  ;; if there is meta data present for an expression in which case we can just use this
  (do (or (is-ground? x))
      (assert false)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-rewrite
  :match (unify (:any A) (:any B))
  nil)

(def-rewrite
  :match (unify (:any A) (:any B))
  :run-at :construction
  (if (= A B) ;; these two structures are equal to each other, so we can just remove the expression
    (make-multiplicity 1)))

;; (def-rewrite
;;   :match (unify (:structured A) (:structured B))
;;   ;; that this should run early, when invoked by the make method call.
;;   ;; there should be some methods like
;;   :run-at :construction
;;   (if (or (not= (count A) (count B)) (not= (car A) (car B)))
;;     (make-multiplicity 0) ;; meaning that the names on these expressions does not match.
;;     (make-conjunct (doall (map make-unify (cdar A) (cdar B)))) ; then make a bunch of smaller unifications on the variables themselves directly
;;     ))

(def-rewrite
  ;; the matched variable should have what value is the result of the matched expression.
  :match (unify (:ground A) (:ground B))
  :run-at [:standard :construction]
  (if (= (get-value A) (get-value B))
    (make-multiplicity 1)
    (make-multiplicity 0)))

(def-rewrite
  :match (unify (:ground A) (:not-ground B))
  :run-at :construction
  (make-unify B A))


;; (def-rewrite
;;   :match (unify (:structured B) (:ground A))
;;   :run-at :construction
;;   (let [Av (get-value A)]
;;     (if (not (and (instance? DynaTerm Av)
;;                   (= (.name ^DynaTerm B) (.name ^DynaTerm Av))
;;                   (= (count (.arguments ^DynaTerm B)) (count (.arguments ^DynaTerm Av)))))
;;       (make-multiplicity 0)
;;       (make-conjunct (doall (map make-unify (.arguments ^DynaTerm B) (.arguments ^DynaTerm Av))))
;;       )))

; this should run at both, so there should be a :run-at :both option that can be selected
(def-rewrite
  :match (unify (:free A) (:ground B))
  :run-at [:standard :construction] ; this will want to run at construction and when it encounters the value so that we can use it as early as possible
  (when (context/has-context)
    ;;(debug-repl)
    (assert (not (is-ground? A))) ;; otherwise the setting the value into the context should fail
    (set-value! A (get-value B))
    (make-multiplicity 1)))

;; (def-rewrite
;;   :match (unify (:free A) (:ground B))
;;   :run-at :standard
;;   (when (context/has-context)
;;     ;;(debug-repl)
;;     (set-value! A (get-value B))
;;     (make-multiplicity 1)))

(def-iterator
  :match (unify (:iterate A) (:ground B))
  (iterators/make-unit-iterator A (get-value B)))

(def-rewrite
  :match (unify-structure (:free out) (:unchecked file-name) (:ground dynabase) (:unchecked name-str) (:ground-var-list arguments))
  :run-at [:construction :standard]
  (let [dbval (get-value dynabase)
        arg-vals (map get-value arguments)
        sterm (DynaTerm. name-str dbval file-name arg-vals)]
    (when (is-ground? out)
        (debug-repl "uf1"))
    (let [res (make-unify out (make-constant sterm))]
      res)))

(def-rewrite
  :match (unify-structure (:ground out) (:unchecked file-name) (:any dynabase) (:unchecked name-str) (:any-list arguments))
  :run-at [:construction :standard]
  (let [out-val (get-value out)]
    (if (or (not (instance? DynaTerm out-val))
            (not= (.name ^DynaTerm out-val) name-str)
            (not= (.arity ^DynaTerm out-val) (count arguments)))
      (make-multiplicity 0) ;; the types do not match, so this is nothing
      (let [conj-map (into [] (map (fn [a b] (make-unify a (make-constant b)))
                                   arguments (.arguments ^DynaTerm out-val)))]
        ;(when-not conj-map (debug-repl "uf2"))
        (make-conjunct conj-map)))))

(def-rewrite
  :match {:rexpr (unify-structure (:any out) (:unchecked file-name) (:any dynabase) (:unchecked name-str) (:any-list arguments))
          :context (unify-structure out (:unchecked file-name2) (:any dynabase2) (:unchecked name-str2) (:any-list arguments2))}
  :run-at :inference
  (if (or (not= name-str name-str2) (not= (count arguments) (count arguments2)))
    (make-multiplicity 0) ;; then these two failed to unify together
    (let [res  ;; this needs to unify all of the arguments together
          (make-conjunct (doall (map make-unify arguments arguments2)))]
      ;(debug-repl "unify context")
      res)))


;; (def-rewrite
;;   :match (unify-structure-get-meta (:ground struct) (:any dynabase) (:any from-file))
;;   (let [struct-val (get-value struct)]
;;     (if-not (instance? DynaTerm struct-val)
;;       (make-multiplicity 0)
;;       ;; java null should get cast to $nil as the dyna term that represents that value
;;       (make-conjunct [(make-unify dynabase (make-constant (or (.dynabase ^DynaTerm struct-val)
;;                                                               null-term)))
;;                       (make-unify from-file (make-constant (or (.from_file ^DynaTerm struct-val)
;;                                                                null-term)))]))))


(comment
  (def-rewrite
    :match (conjunct (:rexpr-list children))
    :run-at [:standard :inference]
    (let [res (make-conjunct (doall (map #(let [r (simplify %)]
                                            (if (is-empty-rexpr? r) (throw (UnificationFailure.))
                                                r)) children)))]
      res)))

(def-rewrite
  :match (conjunct (:rexpr-list children))
  :run-at [:standard :inference]
  (let [res (make-conjunct (doall (map simplify children)))]
    res))


(def-rewrite
  ; in the case that there is only 1 argument, then this doesn't need the conjunct to wrap it
  :match (conjunct ((fn [x] (= (count x) 1)) children))
  :run-at :construction
  (car children))

(def-rewrite
  ;; with no arguments, that is the same as there being no constraints, so we just return mult 1
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



;; (def-rewrite
;;   :match (disjunct (:rexpr-list children))
;;   :is-debug-rewrite true
;;   :run-at :construction
;;   (do
;;     (let [args-set (into #{} (map exposed-variables children))]
;;       (when-not (= 1 (count args-set))
;;         (debug-repl "different exposed args disjunct")))
;;     nil))


(def-rewrite
  :match (disjunct ((fn [x] (= 1 (count x))) children))
  :run-at :construction
  (car children))

(def-rewrite
  :match (disjunct ((fn [x] (= 0 (count x))) children))
  :run-at :construction
  (make-multiplicity 0))

(def-rewrite
  :match (disjunct ((fn [x] (some is-empty-rexpr? x)) children))
  :run-at :construction
  (make-disjunct (doall (filter #(not (is-empty-rexpr? %)) children))))

(def-rewrite
  ;; if there are two (or more) multiplicies in the disjunct, combine the values together
  :match (disjunct ((fn [x] (> (count (filter is-multiplicity? x)) 1)) children))
  :run-at :construction
  (let [cnt (atom 0)
        others (doall (filter (fn [x] (if (is-multiplicity? x)
                                        (do (swap! cnt + (:mult x))
                                            nil)
                                        x))
                              children))]
    (if (not= @cnt 0)
      (make-disjunct (conj others (make-multiplicity @cnt)))
      (make-disjunct others))))


(def-rewrite
  :match (disjunct (:rexpr-list children))
  :run-at [:standard :inference]
  (let [outer-context (context/get-context)
        new-children (doall (for [child children]
                              (let [ctx (context/make-nested-context-disjunct child)
                                    new-rexpr (context/bind-context-raw ctx
                                                                        (try (simplify child)
                                                                             (catch UnificationFailure e (make-multiplicity 0))))]
                                [new-rexpr ctx])))
        intersected-ctx (reduce ctx-intersect (map second new-children))
        children-with-contexts (doall
                                 (for [[child-rexpr child-ctx] new-children]
                                   (ctx-exit-context (ctx-subtract child-ctx intersected-ctx)
                                                     child-rexpr)))]
    ;; the intersected context is what can be passed up to the parent, we are going to have to make new contexts for the children
    (ctx-add-context! outer-context intersected-ctx)
    ;(debug-repl "disjunct standard")
    (make-disjunct children-with-contexts)))

(def-iterator
  :match (disjunct (:rexpr-list children))
  (let [all-iters (vec (map find-iterators children))]
    ;; this has to intersect the iterators for the same variables
    (when (every? #(not (empty? %)) all-iters)
      (iterators/make-disjunct-iterator all-iters))))

(def-rewrite
  ;; this is proj(A, 0) -> 0
  :match (proj (:any A) (is-empty-rexpr? R))
  :run-at :construction
  (make-multiplicity 0))

(def-rewrite
  ;; proj(A, 1) -> inf
  :match (proj (:free A) (is-multiplicity? M))
  :run-at :construction
  (when (not= (get-argument M 0) 0)
    (debug-repl "should not happen")
    (make-multiplicity ##Inf)))

(def-rewrite
  :match (proj (:variable A) (:rexpr R))
  :run-at [:standard :inference]

  (let [ctx (context/make-nested-context-proj rexpr [A])
        nR (context/bind-context ctx
                                 (simplify R))]
    (if (ctx-is-bound? ctx A)
      ;; if there is some unified expression, it would be nice if we could also attempt to identify if some expression is unified together
      ;; in which case we can remove the proj using the expression of
      (let [var-val (ctx-get-value ctx A)
            replaced-R (remap-variables nR {A (make-constant var-val)}) ;; this is a bit annoying as it is going through and doing replacements
            ;; vvv (context/get-inner-values ctx)
            ;; all-bindings (context/get-all-bindings ctx)
            ]
          ;(debug-repl "proj") ;; this is going to have to propagate the value of the new variable into the body
          ;; this is either already done via the context?  Or this is going to be slow if we have a large expression where we have to do lots of
          ;; replacements of the variables
        replaced-R)
      (make-proj A nR))))

(def-rewrite
  :match (proj (:ground A) (:rexpr R))
  :run-at [:standard :construction]
  (if (is-constant? A) R
      (remap-variables R {A (get-value A)})))


(def-rewrite
  ;; lift disjuncts out of projection
  :match (proj (:variable A) (disjunct (:rexpr-list Rs)))
  (let [res (make-disjunct (doall (map #(make-proj A %) Rs)))]
    ;;(debug-repl "proj disjunct")
    res))

(def-rewrite
  ;; lift conjuncts which don't depend on the variable out of the projection
  :match (proj (:variable A) (conjunct (:rexpr-list Rs)))
  (let [not-contain-var (transient [])
        conj-children (doall (remove nil? (map (fn [r]
                                                 (if (contains? (exposed-variables r) A)
                                                   r
                                                   (do
                                                     (conj! not-contain-var r)
                                                     nil)))
                                               Rs)))]
    (let [ncv (persistent! not-contain-var)]
      (when (empty? conj-children)
        (debug-repl "proj gg"))
      (when-not (empty? ncv)
        (make-conjunct (conj ncv (make-proj A (make-conjunct conj-children))))))))

(def-iterator
  :match (proj (:variable A) (:rexpr R))
  (let [iters (find-iterators R)]
    (into #{} (filter #(not (contains? (iter-what-variables-bound %) A)) iters))))

(def-rewrite
  :match (proj (:variable A) (:rexpr R))
  (let [iter (find-iterators R)
        iter-self (filter #(contains? (iter-what-variables-bound %) A) iter)]
    (when-not (empty? iter-self)
      (let [proj-vals (transient #{})
            iter-run (iter-create-iterator (first iter-self) A)] ;; the binding would need to be which variable is getting bound or something...
        (iter-run-cb iter-run #(conj! proj-vals (get % A)))

        (let [nR (make-disjunct (doall (for [val (persistent! proj-vals)]
                                         (remap-variables R {A (make-constant val)}))))]
          nR)))))


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
  (make-if (let [ctx (context/make-nested-context-if-conditional A)]
             (context/bind-context ctx (simplify A)))
           B C))

(def-rewrite
  :match (user-call (:unchecked name) (:unchecked var-map) (:unchecked call-depth) (:unchecked parent-call-arguments))
  :run-at :construction
  (let [n [(:name name) (:arity name)] ;; this is how the name for built-in R-exprs are represented.  There is no info about the file
        s (or (get @system/system-defined-user-term n)
              (get @system/globally-defined-user-term n))]
    (when (and s
               (not (and (is-user-call? s)
                         (= (:name s) name))))
      (debug-try (remap-variables s var-map)
                 (catch Exception error
                   (try (debug-repl "user call stack overflow")
                        (catch Exception error2 (throw error)))
                   (throw error))))))

;; does this want to allow for user defined system terms to expand, if something is recursive, then we don't want to expand those eagerly.  Also, we will want for those to still be stack depth limited
;; I suppose that we could have the things which bottom out in built-ins would have it can still expand these early


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-base-rexpr simple-function-call [:unchecked function
                                      :var result
                                      :var-list arguments])

(def-rewrite
  :match (simple-function-call (:unchecked function) (:any result) (:ground-var-list arguments))
  :run-at [:standard :construction]
  (make-unify result (make-constant (apply function (map get-value arguments)))))

(defn make-function-call
  {:rexpr-constructor 'simple-function-call
   :rexpr-constructor-type simple-function-call-rexpr}
  [function result args]
  (assert (fn? function))
  (make-simple-function-call function result args))
