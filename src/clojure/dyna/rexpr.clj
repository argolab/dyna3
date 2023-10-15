(ns dyna.rexpr
  (:require [dyna.utils :refer :all])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.rexpr-constructors :refer [expose-globally]])
  (:require [dyna.context :as context])
  (:require [dyna.system :as system])
  (:require [dyna.iterators :as iterators])
  (:require [dyna.assumptions :refer [depend-on-assumption]])
  (:require [dyna.rexpr-pretty-printer :refer [rexpr-printer optional-line-break indent-increase indent-decrease *print-variable-name*]])
  (:require [clojure.set :refer [union difference subset?]])
  (:require [clojure.string :refer [trim join]])
  (:require [aprint.core :refer [aprint]])
  (:import [dyna UnificationFailure DynaTerm StatusCounters Rexpr RexprValue RexprValueVariable RContext SimplifyRewriteCollection]))

(defn simplify-identity [a b] a)

(declare simplify
         simplify-inference
         simplify-fast)
(def ^{:redef true} simplify-construct identity) ;; should get rid of this and have the constructors just called directly based off the type of object which is created
(def ^{:redef true} simplify-jit-create-rewrites identity) ;; will be redefined in rexpr_jit.dyna when the jit is enabled.  This will create new rewrites for any JIT type inside of the R-expr and apply those rewrites (if they were newly created)
(declare find-iterators)


;; maybe this should recurse through the structure and make a nice print out of the term objets
(defmethod print-method DynaTerm [^DynaTerm this ^java.io.Writer w]
  (.write w (.toString this)))


;(def rexpr-containers (atom #{}))
(def rexpr-constructors (atom {}))
(def rexpr-containers-signature (atom {}))
(def rexpr-containers-class-name (atom {}))


;; functions which are used to perform matchings against a given Rexpr
(def rexpr-matchers (atom {}))
(def rexpr-matchers-mappers (atom {}))
(def rexpr-matchers-meta (atom {}))

;; functions which actually perform rewrites against an Rexpr
;; these functions perform their own internal matching
(def rexpr-rewrites (atom {})) ; run at standard time
(def rexpr-rewrites-construct (atom {})) ; run at the time of construction
(def rexpr-rewrites-inference (atom {})) ; run to construct new objects, but there are

(def rexpr-rewrites-during-jit-compilation (atom {}))

;; (def rexpr-rewrites-func (atom {}))
;; (def rexpr-rewrites-construct-func (atom {}))
;; (def rexpr-rewrites-inference-func (atom {}))

;; a map of functor type types to a list of rewrite rules bodies.  This is can be used by the JIT to combine rules
(def rexpr-rewrites-source (atom {}))

;; functions which define how iterators are accessed for a given Rexpr
(def rexpr-iterators-accessors (atom {}))
(def rexpr-iterators-source (atom {}))


                                        ;(def ^:dynamic *current-matched-rexpr* nil)
#_(def ^:dynamic *current-top-level-rexpr* nil)
#_(def ^:dynamic *current-simplify-stack* [])  ;; the last value of this is used for tracking :constructed-from
#_(def ^:dynamic *current-simplify-running* nil)
(def-tlocal current-top-level-rexpr)
(def-tlocal current-simplify-stack)
(def-tlocal current-simplify-running)


(when system/track-where-rexpr-constructed  ;; meaning that the above variable will be defined
  (swap! debug-useful-variables assoc
         'rexpr (fn [] (last (tlocal *current-simplify-stack*)))
         'rexpr-top-level (fn [] (tlocal *current-top-level-rexpr*))
         'top-level-rexpr (fn [] (tlocal *current-top-level-rexpr*))
         'simplify-stack (fn [] (tlocal *current-simplify-stack*))))

#_(def deep-equals-compare-fn (atom {}))
#_(defmacro def-deep-equals [rexpr args & body]
  `(swap! deep-equals-compare-fn update ~(symbol (str rexpr "-rexpr")) conj (fn ~args ~@body)))

#_(defn deep-equals [a b]
  (if (= a b)
    true
    (let [af (get @deep-equals-compare-fn (type a))
          bf (get @deep-equals-compare-fn (type b))]
      (or (some #(% a b) af)
          (some #(% b a) bf)))))

#_(swap! debug-useful-variables assoc 'deep-equals (fn [] deep-equals))

;; (def deep-equals-compare-fn (atom {}))
;; (defrecord deep-equals-alias-variable [^RexprValueVariable vara ^RexprValueVariable varb]
;;   RuntimeException
;;   (fillInStackTrace [this] nil))

#_(defn deep-equals
  ([a b]
   (deep-equals a b {})
   ([a b aliased]
    (if (= a b)
      [true nil]
      (let [af (get @deep-equals-compare-fn (type a))
            bf (get @deep-equals-compare-fn (type b))
            ae (exposed-variables a)
            be (exposed-variables b)
            alias-all (merge aliased
                             (into {} (first (for [k ae
                                                   :when (not (contained? aliased k))]
                                               [[k nil]]))))]
        (if-not (= (count ae) (count be))
          [false nil]
          (try
            (let [[ar mr] (first (for [f ar
                                       :let [[ar mr] (f a b)]
                                       :when ar]
                                   [ar mr]))]
              (if ar [ar mr]
                  ))
            (or
                (try
                  (let [alias2 (into {} (for [[k v] alias-all] [v k]))]
                    (some #(% b a alias2) bf))
                  (catch deep-equals-alias-variable to-alias (throw (deep-equals-alias-variable. (:varb to-alias) (:vara to-alias))))))
            (catch deep-equals-alias-variable to-alias
              (if (contains? aliased (:vara to-alias))
                (throw to-alias) ;; throw this up as something else is already handling this alias
                (loop [new-alias (assoc alias-all (:vara to-alias) (:varb to-alias))
                       already-tried #{(:varb to-alias)}]
                  (try
                    (deep-equals a b new-alias)
                    (catch deep-equals-alias-variable to-alias
                      (if (already-tried (:varb to-alias))
                        false ;; we are not going to retry this

                        )
                      )
                    )

                  )
                (let [new-alias ]

                  )))))
        )))))

(defn construct-rexpr [name & args]
  (apply (get @rexpr-constructors name) args))

(defn- make-simplify-rewrite-collection [can-make-new-rewrites]
  (SimplifyRewriteCollection/create can-make-new-rewrites))

(defmacro def-base-rexpr [name args & optional]
  (let [vargroup (partition 2 args)
        rname (str name "-rexpr")
        flags (into #{} (filter keyword? optional))
        opt (if (not (nil? optional)) (vec (filter #(not (keyword? %)) optional)) [])
        auto-create-new-rewrites (.startsWith ^String (str name) "jit-rexpr")]
    `(do
       (swap! rexpr-containers-signature (fn ~'[x]
                                           (assert (not (contains? ~'x '~name))) ;; make sure that we do not define two R-exprs with the same names
                                           (assoc ~'x '~name (quote ~(vec vargroup)))))
       (declare ~(symbol (str "make-" name))
                ~(symbol (str "make-no-simp-" name)) ;; this should really be something that is "require context"
                ~(symbol (str "is-" name "?")))
       (intern 'dyna.rexpr-constructors '~(symbol (str "simplify-" name)) (~make-simplify-rewrite-collection ~auto-create-new-rewrites))
       (intern 'dyna.rexpr-constructors '~(symbol (str "simplify-construct-" name)) (~make-simplify-rewrite-collection false))
       (intern 'dyna.rexpr-constructors '~(symbol (str "simplify-inference-" name)) (~make-simplify-rewrite-collection ~auto-create-new-rewrites))
       (intern 'dyna.rexpr-constructors '~(symbol (str "simplify-jit-compilation-step-" name)) (~make-simplify-rewrite-collection false))


       ;; (intern 'dyna.rexpr-constructors '~(symbol (str "simplify-" name)) simplify-identity)
       ;; (intern 'dyna.rexpr-constructors '~(symbol (str "simplify-construct-" name)) simplify-identity)
       ;; (intern 'dyna.rexpr-constructors '~(symbol (str "simplify-inference-" name)) simplify-identity)

       ;; used by the JIT compiler when it is rewriting the state of an R-expr for the purpose of matching some rewrite
                                        ;(intern 'dyna.rexpr-constructors '~(symbol (str "simplify-jit-compilation-step-" name)) simplify-identity)

       ;; (alter-meta! (var ~(symbol "dyna.rexpr-constructors" (str "simplify-" name))) assoc :redef true)
       ;; (alter-meta! (var ~(symbol "dyna.rexpr-constructors" (str "simplify-construct-" name))) assoc :redef true)
       ;; (alter-meta! (var ~(symbol "dyna.rexpr-constructors" (str "simplify-inference-" name))) assoc :redef true)

       ;; (alter-meta! (var ~(symbol "dyna.rexpr-constructors" (str "simplify-jit-compilation-step-" name))) assoc :redef true)


       (deftype-with-overrides ~(symbol rname) ~(vec (concat (quote [^int cached-hash-code
                                                                     ^{:tag int :unsynchronized-mutable true} cached-jittype-hash-code
                                                                     ^:unsynchronized-mutable cached-exposed-variables])
                                                             (if system/track-where-rexpr-constructed (quote [traceback-to-construction traceback-to-rexpr]))
                                                             (map cdar vargroup)))
         ~opt
         clojure.lang.ILookup
         (~'valAt ~'[this name-to-lookup-gg not-found]
          (case ~'name-to-lookup-gg
            ~@(apply concat (for [[idx var] (zipseq (range) vargroup)]
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
                                        ;~'(primitive-rexpr-jit-placeholder [this] (primitive-rexpr this))
         ~'(is-constraint? [this] false) ;; if this is going to return a multiplicity of at most 1
         ~'(variable-functional-dependencies [this] nil) ;; if this is a constraint where there is some known functional dependencies between vars
         ;; return as a map of sets to sets
         (~'rexpr-name ~'[this] (quote ~(symbol name))) ;; the name for this type of R-expr
         (~'get-variables ~'[this]
          (filter is-variable?
                  (union (set (list ~@(map cdar (filter #(contains?  #{:var :value} (car %1)) vargroup))))
                         ~@(map (fn [x] `(set ~(cdar x))) (filter #(= :var-list (car %1)) vargroup))
                         ~@(map (fn [x] `(set (vals ~(cdar x)))) (filter #(= :var-map (car %1)) vargroup))
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
            ~@(apply concat (for [[var idx] (zipseq vargroup (range))]
                              `(~idx ~(cdar var))))
            (throw (RuntimeException. "invalid index for get-argument"))))

                                        ;(~'get-argument ~'[this n] (nth ~(vec (map cdar vargroup)) ~'n))
         (~'get-arguments ~'[this] ~(vec (map cdar vargroup)))

         ;; (~'get-arguments-map ~'[this] {~@(apply concat (for [v vargroup]
         ;;                                                  `(~(keyword (name (cdar v))) ~(cdar v))))})

         (rexpr-map-function-with-access-path ~'[this local-cb-fn]
                                              ~(into {} (for [var vargroup]
                                                          [`(quote ~(cdar var)) `(~'local-cb-fn
                                                                                  ~(keyword (cdar var)) ;; the name of the field
                                                                                  ~(car var) ;; the type of the field
                                                                                  ~(cdar var))])))

         (~'rexpr-jit-info ~'[this] nil) ;; there is nothing here by default. this should return information about what this expression represents

         (~'all-conjunctive-rexprs ~'[this] [[#{} ~'this]])

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
          (debug-tbinding
           [current-simplify-stack (conj (tlocal *current-simplify-stack*) ~'this)]
           (context/bind-no-context ;; this is annoying, this will want to be
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
                                            :var-list `(into [] (map #(get ~'variable-map % %) ~(cdar v)))
                                            :var-map `(into {} (for [~'[kk vv] ~(cdar v)] [~'kk (get ~'variable-map ~'vv ~'vv)]))
                                            :var-set-map `(into #{} (for [~'s ~(cdar v)]
                                                                      (into {} (for [~'[kk vv] ~'s] [~'kk (get ~'variable-map ~'vv ~'vv)]))))
                                            :call-parent-map `(into {} (for [~'[nn ss] ~(cdar v)]
                                                                         [~'nn (into #{} (for [~'ee ~'ss]
                                                                                           (into {} (for [~'[kk vv] ~'ee]
                                                                                                      [~'kk (get ~'variable-map ~'vv ~'vv)]))))]))
                                            :rexpr `(remap-variables ~(cdar v) ~'variable-map)
                                            :rexpr-list `(vec (map #(remap-variables % ~'variable-map) ~(cdar v)))
                                            (cdar v) ;; the default is that this is the same
                                            )])))
                (if (and ~@(for [v vargroup]
                             `(= ~(cdar v) ~(symbol (str "new-" (cdar v))))))
                  ~'this ;; then there was no change, so we can just return ourself
                  ;; there was some change, so we are going to need to create a new object with the new values
                  (~(symbol (str "make-" name)) ~@(for [v vargroup]
                                                    (symbol (str "new-" (cdar v)))))))))))
         (~'remap-variables-func ~'[this remap-function]
          (debug-tbinding
           [current-simplify-stack (conj (tlocal *current-simplify-stack*) ~'this)]
           (context/bind-no-context
            (let ~(vec (apply concat (for [v vargroup]
                                       [(symbol (str "new-" (cdar v)))
                                        (case (car v)
                                          :var `(~'remap-function ~(cdar v))
                                          :value `(~'remap-function ~(cdar v))
                                          :hidden-var `(~'remap-function ~(cdar v))
                                          :var-list `(into [] (map ~'remap-function ~(cdar v)))
                                          :var-map `(into {} (for [~'[kk vv] ~(cdar v)]
                                                               [~'kk (~'remap-function ~'vv)]))
                                          :var-set-map `(into #{} (for [~'s ~(cdar v)]
                                                                    (into {} (for [~'[kk vv] ~'s]
                                                                               [~'kk (~'remap-function ~'vv)]))))
                                          :call-parent-map `(into {} (for [~'[nn ss] ~(cdar v)]
                                                                       [~'nn (into #{} (for [~'ee ~'ss]
                                                                                         (into {} (for [~'[kk vv] ~'ee]
                                                                                                    [~'kk (~'remap-function ~'vv)]))))]))
                                          :rexpr `(~'remap-variables-func ~(cdar v) ~'remap-function)
                                          :rexpr-list `(vec (map #(~'remap-variables-func % ~'remap-function) ~(cdar v)))
                                          (cdar v) ;; default to just keep it the same
                                          )
                                        ])))
              (if (and ~@(for [v vargroup]
                           `(= ~(cdar v) ~(symbol (str "new-" (cdar v))))))
                ~'this ;; nothing has changed
                (~(symbol (str "make-" name)) ~@(for [v vargroup]
                                                  (symbol (str "new-" (cdar v))))))))))

         (~'rewrite-rexpr-children ~'[this remap-function]
          ~(when (some #{:prefix-trie} (map car vargroup))
             `(throw (RuntimeException. "using rewrite-rexpr-children on a R-expr with :prefix-trie type")))
          (let ~(vec (apply concat
                            (for [v vargroup]
                              (when (contains? #{:rexpr :rexpr-list} (car v))
                                [(symbol (str "new-" (cdar v)))
                                 (case (car v)
                                   :rexpr `(~'remap-function ~(cdar v))
                                   :rexpr-list `(vec (map ~'remap-function ~(cdar v))))]
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
                                   :rexpr-list `(vec (map ~'remap-function ~(cdar v))))]
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
                                  'variable-map-in ;; there is nothing new for this, so can't use assoc
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
                                          :call-parent-map `(into {} (for [~'[nn ss] ~(cdar v)]
                                                                       [~'nn (into #{} (for [~'ee ~'ss]
                                                                                         (into {} (for [~'[kk vv] ~'ee]
                                                                                                    [~'kk (get ~'variable-map ~'vv ~'vv)]))))]))
                                          :rexpr `(remap-variables-handle-hidden ~(cdar v) ~'variable-map)
                                          :rexpr-list `(vec (map #(remap-variables-handle-hidden % ~'variable-map) ~(cdar v)))
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

         (~'rewrite-all-args ~'[this rewriting-function]
          (let [result# (~(symbol (str "make-no-simp-" name))
                         ~@(for [[typ v] vargroup]
                             `(~'rewriting-function ~typ ~v)))]
            (if (= result# ~'this)
              ~'this
              result#)))

         (~'is-empty-rexpr? ~'[this] false)
         (~'is-non-empty-rexpr? [this] false)  ;; if this has _PROVEN_ that is non-empty (Something like 1+R).  Something that is

         (~'check-rexpr-basecases ~'[this stack]
          (min 3 ;; this is the default for intersection
               ~@(for [v vargroup
                       :when (#{:rexpr} (car v))]
                   `(check-rexpr-basecases ~(cdar v) ~'stack))
               ~@(for [v vargroup
                       :when (#{:rexpr-list} (car v))]
                   `(apply min (map #(check-rexpr-basecases % ~'stack) ~(cdar v))))))

         ;; (~'simplify-fast-rexprl ~'[this simplify]
         ;;  ;; TODO: this should directly call the right method, or return a base pointer to the right type
         ;;  ;; I suppose that in the case that this is doing the call internally, then it will have that this does not
         ;;  ;; have
         ;;  (???))

         ;; (~'simplify-inference-rexprl ~'[this simplify]
         ;;  (???))

         (~'rexpr-simplify-fast-collection ~'[this]
          ~(symbol "dyna.rexpr-constructors" (str "simplify-" name)))

         (~'rexpr-simplify-construct-collection ~'[this]
          ~(symbol "dyna.rexpr-constructors" (str "simplify-construct-" name)))

         (~'rexpr-simplify-inference-collection ~'[this]
          ~(symbol "dyna.rexpr-constructors" (str "simplify-inference-" name)))

         (~'rexpr-jit-compilation-step-collection ~'[this]
          ~(symbol "dyna.rexpr-constructors" (str "simplify-jit-compilation-step-" name)))


         (~'rexpr-jittype-hash ~'[this]
          (when (= 0 ~'cached-jittype-hash-code)
            (set! ~'cached-jittype-hash-code
                  (unchecked-int
                   ~(reduce (fn [a b] `(unchecked-add-int ~a ~b))
                            (hash rname)
                            (for [[[typ var] idx] (zipseq vargroup (range))
                                  :when (#{:rexpr :rexpr-list :str :mult :boolean :file-name :var-list} typ)]
                              `(unchecked-multiply-int ~(+ 3 idx)
                                                       ~(case typ
                                                          :rexpr `(rexpr-jittype-hash ~var)
                                                          :rexpr-list `(unchecked-add-int
                                                                        (reduce bit-xor 0 (map rexpr-jittype-hash ~var))
                                                                        (count ~var))
                                                          :var-list `(count ~var) ;; the names will not matter, but the number of variables could change what we are doing
                                                          :str `(hash ~var)
                                                          :mult var
                                                          :boolean `(if ~var 7 11)
                                                          :file-name `(hash ~var))))))))
          ~'cached-jittype-hash-code)

         Object
         (~'equals ~'[this other]
          (or (identical? ~'this ~'other)
              (and (instance? ~(symbol rname) ~'other)
                   (= (hash ~'this) (hash ~'other))
                   ~@(for [[var idx] (zipseq vargroup (range))]
                       `(= ~(cdar var) (get-argument ~'other ~idx))))))

         (~'hashCode [this] ~'cached-hash-code) ;; is this something that should only be computed on demand instead of when it is constructed?
         (~'toString ~'[this] (trim (str (as-list ~'this)))))

       (defn ~(symbol (str "make-no-simp-" name))
         {:rexpr-constructor (quote ~name)
          :rexpr-constructor-type ~(symbol rname)
          :no-simp-rexpr-constructor true}
         ~(vec (map cdar vargroup))
         ~@(when system/check-rexpr-arguments
             (map (fn [x] `(if (not (~(resolve (symbol (str "check-argument-" (symbol (car x))))) ~(cdar x)))
                             (do (.printStackTrace (Throwable. (str "Argument value check failed: " ~(car x) ~(cdar x))) System/err)
                                 (debug-repl ~(str "check argument " (car x)))
                                 (assert false)))) vargroup))
         ~(if system/status-counters `(StatusCounters/rexpr_created))
         (~(symbol (str rname "."))
          ;; this hash implementation needs to match the one below....
          (unchecked-int ~(reduce (fn [a b] `(unchecked-add-int ~a ~b))
                                  (hash rname)
                                  (for [[var idx] (zipseq vargroup (range))]
                                    `(unchecked-multiply-int (hash ~(cdar var)) ~(+ 3 idx)))))
          0                             ; the jittype hash cache
          nil                           ; the cached unique variables
          ~@(if system/track-where-rexpr-constructed `[(Throwable.) (last (tlocal *current-simplify-stack*))])
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
         ~(if system/status-counters `(StatusCounters/rexpr_created))
         (simplify-construct (~(symbol (str rname "."))
                              ;; this might do the computation as a big value, would be nice if this could be forced to use a small int value
                              ;; I suppose that we could write this in java and call out to some static function if that really became necessary
                              ;; this hash implementation needs to match the one above....
                              (unchecked-int ~(reduce (fn [a b] `(unchecked-add-int ~a ~b))
                                                      (hash rname)
                                                      (for [[var idx] (zipseq vargroup (range))]
                                                        `(unchecked-multiply-int (hash ~(cdar var)) ~(+ 3 idx)))))
                              0   ;; the cached jittype hash
                              nil ; the cached unique variables
                              ~@(if system/track-where-rexpr-constructed `[(Throwable.) (do
                                                                                          ;; (when-not (or (not (nil? dyna.rexpr/*current-matched-rexpr*))
                                                                                          ;;               (empty?  dyna.rexpr/*current-simplify-stack*))
                                                                                          ;;   (throw (RuntimeException. "failed to set the matched R-expr")))
                                                                                          (last (tlocal *current-simplify-stack*)))])
                              ~@(map cdar vargroup))))
       (swap! rexpr-constructors assoc ~(str name) ~(symbol (str "make-" name)))
       (defn ~(symbol (str "is-" name "?"))
         {:inline (fn ~'[x] (list 'instance? ~(symbol rname) ~'x))}
         ~'[rexpr]
         (instance? ~(symbol rname) ~'rexpr))
       (defmethod print-method ~(symbol rname) ~'[this ^java.io.Writer w]
         (assert (not (nil? ~'w)))
         (aprint (as-list ~'this) ~'w))
       #_~(when (some #(= % :rexpr) (map car vargroup))
            `(def-deep-equals ~(symbol name) ~'[a b]
               (and (instance? ~(symbol rname) ~'b)
                    ;; check the non-rexprs first as those should be faster
                    ~@(for [[var-type vname] vargroup
                            :when (not= var-type :rexpr)] ;; this is going to end up handling lists, which likely aren't going to be equal to each other
                        `(= (~(keyword vname) ~'a) (~(keyword vname) ~'b)))
                    ~@(for [[var-type vname] vargroup
                            :when (= :rexpr var-type)]
                        `(deep-equals (~(keyword vname) ~'a) (~(keyword vname) ~'b))))))
                                        ;(intern 'dyna.rexpr-constructors '~(symbol (str "make-" name)) ~(symbol (str "make-" name)))
                                        ;(intern 'dyna.rexpr-constructors '~(symbol (str "make-no-simp-" name)) ~(symbol (str "make-no-simp-" name)))
                                        ;(intern 'dyna.rexpr-constructors '~(symbol (str "is-" name "?")) ~(symbol (str "is-" name "?")))
       (expose-globally ~(symbol (str "make-" name)))
       (expose-globally ~(symbol (str "make-no-simp-" name)))
       (expose-globally ~(symbol (str "is-" name "?")))
       ;; (swap! rexpr-rewrites-func           assoc ~(symbol rname) (fn ~'[a b] (~(symbol "dyna.rexpr-constructors" (str "simplify-" name)) ~'a ~'b)))
       ;; (swap! rexpr-rewrites-construct-func assoc ~(symbol rname) (fn ~'[a b] (~(symbol "dyna.rexpr-constructors" (str "simplify-construct-" name)) ~'a ~'b)))
       ;; (swap! rexpr-rewrites-inference-func assoc ~(symbol rname) (fn ~'[a b] (~(symbol "dyna.rexpr-constructors" (str "simplify-inference-" name)) ~'a ~'b)))
       (swap! rexpr-containers-class-name assoc (quote ~(symbol name)) (.getName ~(symbol rname)))

       ;; (swap! rexpr-rewrites-func assoc ~(symbol (str name "-rexpr")) identity)
       ;; (swap! rexpr-rewrites-construct-func assoc ~(symbol (str name "-rexpr")) identity)
       ;; (swap! rexpr-rewrites-inference-func assoc ~(symbol (str name "-rexpr")) identity)
       )))


(defn make-structure [name args]
  (DynaTerm. name args))
;(intern 'dyna.rexpr-constructors 'make-structure make-structure)
(expose-globally make-structure)

(def null-term DynaTerm/null_term)

(defmethod print-dup DynaTerm [^DynaTerm term ^java.io.Writer w]
  (if (identical? (.dynabase term) term) ;; this only happens on the root $nil term when there is no dynabase
    (.write w "#=(dyna.DynaTerm/get_null_term)")
    (do
      (.write w "#=(dyna.DynaTerm. ")
      (print-dup (.name term) w)
      (.write w " ")
      (print-dup (.dynabase term) w)
      (.write w " ")
      (print-dup (.from_file term) w)
      (.write w " ")
      (print-dup (vec (.arguments term)) w)
      (.write w ")"))))

(defmethod print-dup java.net.URL [^java.net.URL url ^java.io.Writer w]
  (.write w "#=(java.net.URL. ")
  (print-dup (.toExternalForm url) w)
  (.write w ")"))


;;;;;;;;;;;;;;;;;;;;;;;;;;
;; things like variables and constants should instead be some other type rather than an R-expr

(declare make-constant)

(defrecord variable-rexpr [varname]
  RexprValueVariable
  (get-value [this] (context/need-context (ctx-get-value (context/get-context) this)))
  (get-value-in-context [this ctx] (ctx-get-value ctx this))
  (set-value! [this value]
    (ctx-set-value! (context/get-context) this value))
  (set-value-in-context! [this ctx value]
    (ctx-set-value! ctx this value))
  (is-bound? [this] (boolean (context/need-context (ctx-is-bound? (context/get-context) this))))
  (is-bound-in-context? [this context] (ctx-is-bound? context this))
  (all-variables [this] #{this})
  (get-representation-in-context [this ctx]
    (if (is-bound-in-context? this ctx)
      (make-constant (get-value-in-context this ctx))
      this))
  Object
  (toString [this] (str "(variable " varname ")")))

(defmethod rexpr-printer variable-rexpr [v]
  (*print-variable-name* v))

(defn make-variable [varname]
  (variable-rexpr. varname))
;(intern 'dyna.rexpr-constructors 'make-variable make-variable)
(expose-globally make-variable)

(defmethod print-method variable-rexpr [^variable-rexpr this ^java.io.Writer w]
  (.write w (str "(variable " (.varname this) ")")))

;; we can just use (Object.) to create a unique object name.  This will be aster
;; than having a global counter, but will be "more annoying" to print stuff out...
(defn make-unique-variable
  ([] (make-variable (gensym 'unique-var)))
  ([base-name] (variable-rexpr. (gensym base-name))))
;(intern 'dyna.rexpr-constructors 'make-unique-variable make-unique-variable)
(expose-globally make-unique-variable)

(defrecord constant-value-rexpr [value]
  RexprValue
  (get-value [this] value)
  (get-value-in-context [this ctx] value)
  (set-value! [this v]
    (if (not= v value)
      (throw (UnificationFailure. "can not assign value to constant"))))
  (set-value-in-context! [this ctx v]
    (if (not= v value)
      (throw (UnificationFailure. "can not assign value to constant"))))
  (is-bound? [this] true)
  (is-bound-in-context? [this context] true)
  (all-variables [this] #{})
  (get-representation-in-context [this ctx] this)
  Object
  (toString [this] (str "(constant " value ")")))

(defmethod rexpr-printer constant-value-rexpr [r]
  (if (string? (:value r))
    (str "\"" (:value r) "\"")
    (str (:value r))))


(defn make-constant [val]
  (dyna-debug (when (nil? val) (debug-repl "make constant with nil")))
  (assert (and (not (nil? val)) ;; otherwise this is a bug
               (not (symbol? val))
               ))
  (dyna-debug (assert (not (instance? constant-value-rexpr val))))
  (constant-value-rexpr. val))
                                        ;(intern 'dyna.rexpr-constructors 'make-constant make-constant)
(expose-globally make-constant)

(let [tv (make-constant true)
      fv (make-constant false)]
  (defn make-constant-bool [val]
    (if val tv fv)))

(defmethod print-method constant-value-rexpr [^constant-value-rexpr this ^java.io.Writer w]
  (.write w (str "(constant " (.value this) ")")))

(defn unification-failure []
  (throw (UnificationFailure. "unification failure")))

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
;;   (assert (every? (partial instance? RexprValue) arguments))
;;   (structured-rexpr. name arguments))

;; (defmethod print-method structured-rexpr [^structured-rexpr this ^java.io.Writer w]
;;   (.write w (.toString ^Object this)))

;; (defn make-structured-value [name values]
;;   (assert (every? (partial instance? RexprValue) values))
;;   (assert (string? name))
;;   (structured-rexpr. name values))

(defn is-constant?
  {:inline (fn [x] `(instance? constant-value-rexpr ~x))}
  [x] (instance? constant-value-rexpr x))
(expose-globally is-constant?)

(defn is-variable?
  {:inline (fn [x] `(instance? RexprValueVariable ~x))}
  [variable] (instance? RexprValueVariable variable))
(expose-globally is-variable?)

(defn is-rexpr-value?
  {:inline (fn [x] `(instance? RexprValue ~x))}
  [v] (instance? RexprValue v))
(expose-globally is-rexpr-value?)

(defn rexpr?
  {:inline (fn [x] `(instance? Rexpr ~x))}
  [rexpr] (instance? Rexpr rexpr))
(expose-globally rexpr?)

;; these are checks which are something that we might want to allow ourselves to turn off
(defn check-argument-mult [x] (or (and (int? x) (>= x 0)) (= ##Inf x)))
(defn check-argument-rexpr [x] (rexpr? x))
(defn check-argument-rexpr-list [x] (and (seqable? x) (every? rexpr? x) (not (instance? clojure.lang.LazySeq x))))
(defn check-argument-var [x] (instance? RexprValue x)) ;; a variable or constant of a single value.  Might want to remove is-constant? from this
(defn check-argument-var-list [x] (and (seqable? x) (every? check-argument-var x)))
(defn check-argument-var-map [x] (and (map? x) (every? (fn [[a b]] (and (check-argument-var a)
                                                                        (check-argument-var b)))
                                                       x)))
(defn check-argument-var-set-map [x] (and (set? x) (every? check-argument-var-map x)))
(defn check-argument-call-parent-map [x] (and (map? x) (every? #(and (set? %) (every? check-argument-var-map %)) (vals x))))
(defn check-argument-value [x] (instance? RexprValue x)) ;; something that has a get-value method (possibly a structure)  I think that this is not used anymore
(defn check-argument-hidden-var [x] (check-argument-var x))
(defn check-argument-str [x] (string? x))
(defn check-argument-unchecked [x] true)
(defn check-argument-opaque-constant [x] ;; something that is not in the R-expr language
  (not (or (instance? Rexpr x) (instance? RexprValue x))))
(defn check-argument-boolean [x] (boolean? x))
(defn check-argument-file-name [x]
  (or (nil? x)
      (= "REPL" x)
      (instance? java.net.URL x)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(def-base-rexpr multiplicity [:mult mult]
  (is-constraint? [this] (<= mult 1))
  (is-empty-rexpr? [this] (= mult 0))
  (is-non-empty-rexpr? [this] (not= mult 0)))

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
        (prev x))))
  (expose-globally make-multiplicity))

(defmethod rexpr-printer multiplicity-rexpr [m]
  ;; put an overline on all of the numbers returned for the multiplicity
  (str (join "\u0305" (char-array (str (:mult m)))) "\u0305"))

(defn fixpoint-functional-dependencies-map [m]
  (loop [m m]
    (let [n (volatile! m)]
      (doseq [[k v] m
              [k2 v2] m]
        (when (subset? (union k2 v2) k)
          (vswap! n update k2 union v)))
      (if (not= @n m)
        (recur @n)
        @n))))

(def-base-rexpr conjunct [:rexpr-list args]
  (is-constraint? [this] (every? is-constraint? args))

  (all-conjunctive-rexprs [this]
                          (cons [#{} this]
                                (for [a args
                                      v (all-conjunctive-rexprs a)]
                                  v)))
  (variable-functional-dependencies [this]
                                    (let [r (volatile! {})]
                                      (doseq [x args
                                              [k v] (variable-functional-dependencies x)]
                                        (vswap! r update k union v))
                                      (fixpoint-functional-dependencies-map @r))))

(defmethod rexpr-printer conjunct-rexpr [r]
  (join (str "*" (optional-line-break)) (map rexpr-printer (:args r))))

(def-base-rexpr disjunct [:rexpr-list args]
  (remap-variables [this variable-renaming-map]
                   (context/bind-no-context
                    (make-disjunct (vec (map #(remap-variables % variable-renaming-map) args)))))
  (remap-variables-handle-hidden [this variable-renaming-map]
                   (context/bind-no-context
                    (make-disjunct (vec (map #(remap-variables-handle-hidden % variable-renaming-map) args)))))
  (rewrite-rexpr-children [this remap-function]
                          (context/bind-no-context
                           (make-disjunct (vec (map remap-function args)))))
  (remap-variables-func [this remap-function]
                        (context/bind-no-context
                         (make-disjunct (vec (map #(remap-variables-func % remap-function) args)))))
  (is-non-empty-rexpr? [this] (some is-non-empty-rexpr? args))
  ;(rexpr-jit-info [this] {:jittable false})
  (rexpr-jittype-hash [this] 0))

(defmethod rexpr-printer disjunct-rexpr [r]
  (join (str "+" (optional-line-break)) (map rexpr-printer (:args r))))

#_(defn deep-equals-list-compare [a b]
  (if (and (empty? a) (empty? b))
    true
    (let [af (first a)
          ar (next a)]
      (some (fn [x]
              (and (deep-equals af x)
                   (deep-equals-list-compare ar (remove #(identical? x %) b))))
            b))))

#_(def-deep-equals conjunct [a b]
  (when (instance? conjunct-rexpr b)
    (let [as (:args a)
          bs (:args b)]
      (if (not= (count as) (count bs))
        false
        ;; going to attempt to match against which
        (deep-equals-list-compare as bs)))))


#_(def-deep-equals disjunct [a b]
  (when (instance? disjunct-rexpr b)
    (let [as (:args a)
          bs (:args b)]
      (if (not= (count as) (count bs))
        false
        (deep-equals-list-compare as bs)))))

;; there should be a more complex expression for handling this in the case of a if statement or something
;; this will want for this to somehow handle if there are some ways in which this can handle if there
;; (defn is-empty-rexpr? [rexpr]
;;   (and (rexpr? rexpr) (= (make-multiplicity 0) rexpr)))
;; (intern 'dyna.rexpr-constructors 'is-empty-rexpr? is-empty-rexpr?)

;; ;; that we are 100% sure that this R-expr will return a non-zero multiplicity
;; (defn ^{:redef true} is-non-empty-rexpr? [rexpr]
;;   (and (rexpr? rexpr)
;;        (or (and (is-multiplicity? rexpr) (> (get-argument rexpr 0) 0))
;;            (and (is-disjunct? rexpr) (some is-non-empty-rexpr? (get-argument rexpr 0))))))
;; (intern 'dyna.rexpr-constructors 'is-non-empty-rexpr? is-non-empty-rexpr?)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-base-rexpr unify [:value a ;; this should be changed to just use :var
                       :value b]
  (is-constraint? [this] true)
  (variable-functional-dependencies [this] {#{a} #{b}
                                            #{b} #{a}}))

(defmethod rexpr-printer unify-rexpr [r]
  (str "(" (rexpr-printer (:a r)) "=" (rexpr-printer (:b r))))

#_(def-deep-equals unify [a b]
  (when (instance? unify-rexpr b)
    ;; we only have to check the args in the different order, as we have already done a check against the stanard equals expression
    (and (= (:a a) (:b b))
         (= (:b a) (:a b)))))

(def-base-rexpr unify-structure [:var out
                                 :file-name file-name
                                 :var dynabase ;; the dynabase variable is only
                                               ;; used for reading when
                                               ;; constructing a new structure.
                                               ;; When destrcturing a term, this
                                               ;; will _not_ unify with this
                                               ;; variable
                                 :str name
                                 :var-list arguments]
  (is-constraint? [this] true)
  (variable-functional-dependencies [this] (let [a (into #{} (filter is-variable? (cons dynabase arguments)))]
                                             {a #{out}
                                              #{out} a})))

(defmethod rexpr-printer unify-structure-rexpr [r]
  (if (dnil? (:dynabase r))
    (str "(" (rexpr-printer (:out r)) "=" (:name r) "[" (join ", " (map rexpr-printer (:arguments r))) "])")
    (str "(" (rexpr-printer (:dynabase r)) "." (rexpr-printer (:out r)) "=" (:name r) "[" (join ", " (map rexpr-printer (:arguments r))) "])")))

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
                   (dyna-debug
                    (when (or (some #{var} (keys variable-map))
                              (some #{var} (vals variable-map)))
                      (debug-repl "bad remap")))

                   (make-proj var (remap-variables body variable-map)))

  (all-conjunctive-rexprs [this]
                          (cons [#{} this]
                                (for [[proj-out rexpr] (all-conjunctive-rexprs body)]
                                  (if (contains? (exposed-variables rexpr) var)
                                    [(conj proj-out var) rexpr]
                                    [proj-out rexpr])))))

(defmethod rexpr-printer proj-rexpr [r]
  (str "proj(" (indent-increase) (rexpr-printer (:var r)) "," (optional-line-break) (rexpr-printer (:body r)) (indent-decrease) ")"))

(def-base-rexpr aggregator [:str operator
                            :var result
                            :hidden-var incoming
                            ;; if the body-is-conjunctive == true, then there are additional optimizations that we can perform
                            :boolean body-is-conjunctive
                            :rexpr body]

  (is-constraint? [this] true)
  (all-conjunctive-rexprs [this]
                          (cons [#{} this]
                                (when body-is-conjunctive
                                  (for [[proj-out rexpr] (all-conjunctive-rexprs body)]
                                    (if (contains? (exposed-variables rexpr) incoming)
                                      [(conj proj-out incoming) rexpr]
                                      [proj-out rexpr])))))
  ;; aggregators need to be converted to the aggregator-optimized format first before they can be JIT compiled
  (rexpr-jit-info [this] {:jittable false}))

(defmethod rexpr-printer aggregator-rexpr [r]
  (str "(" (rexpr-printer (:result r)) "=`" (:operator r) "`(" (indent-increase) (rexpr-printer (:incoming r)) "," (optional-line-break) (rexpr-printer (:body r)) (indent-decrease) "))"))

(def-base-rexpr if [:rexpr cond
                    :rexpr true-branch
                    :rexpr false-branch]
  (is-constraint? [this] (and (is-constant? true-branch) (is-constant? false-branch)))
  (rexpr-jit-info [this] {:jittable false}))

(defmethod rexpr-printer if-rexpr [r]
  (str "if(" (indent-increase)
       (rexpr-printer (:cond r)) "," (optional-line-break)
       (rexpr-printer (:true-branch r)) "," (optional-line-break)
       (rexpr-printer (:false-branch r)) (indent-decrease) ")"))

;; (defn set-variable [var value]
;;   ;; would be nice if there was a bit more efficient approach to this method?
;;   ;; this might be something where we can handle which of the expressions
;;   (make-unify var (make-constant value)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(def-base-rexpr user-call [:unchecked name ;; the name for this call object.  Will include the name, arity and file for which this call is being performed from
                           ;; :str name ;; the name for this call represented as a string
                           ;; :int arity  ;; the arity for this call
                           ;; :var from-file
                           :var-map args-map ;; the arguments which are present for this call
                           :unchecked call-depth
                           :call-parent-map args-parent-map ;; this needs to track which the values of
                           ]
                                        ;(get-variables [this] (into #{} (vals args-map)))
  (check-rexpr-basecases [this stack]
                         (if (contains? stack name)
                           0 ;; then we found ourself in the stack, so this means that there is recursion
                           (let [ut (dyna.rexpr-constructors/get-user-term name)
                                 s (conj stack name)]
                             (if (nil? ut)
                               0 ;; then there is no term defined for this, so it is just nothing
                               (apply min (map #(check-rexpr-basecases % s) (:rexprs ut)))))))
  (rexpr-jit-info [this] {:jittable false})
  (variable-functional-dependencies [this]
                                    (let [ut (dyna.rexpr-constructors/get-user-term name)]
                                      (debug-repl "user call functional deps")
                                      (???)))
  (is-constraint? [this]
                  (let [ut (dyna.rexpr-constructors/get-user-term name)]
                    (depend-on-assumption (:is-constraint ut))
                    (debug-repl "user call is constraint")
                    (???))))

(defmethod rexpr-printer user-call-rexpr [r]
  (let [nargs (:arity (:name r))
        all-normal (and (= (+ 1 nargs) (count (:args-map r)))
                        (every? #(contains? (:args-map r) %) (map #(make-variable (str "$" %)) (range (+ 1 nargs)))))]
    (if all-normal
      (str (rexpr-printer (strict-get (:args-map r) (make-variable (str "$" nargs)))) "="
           (:name (:name r))
           "("
           (join "," (for [i (range nargs)]
                       (rexpr-printer (strict-get (:args-map r) (make-variable (str "$" i))))))
           ")")
      (do
        ;; trying to print a method which as a non-standard variable mapping signature
        (str r))))
  (str r))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn make-proj-many [vars R]
  (if (empty? vars)
    R
    (make-proj (first vars)
               (make-proj-many (rest vars) R))))

;(intern 'dyna.rexpr-constructors 'make-proj-many make-proj-many)
(expose-globally make-proj-many)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; make a linked list of functions which match against a given type
(defn- combine-rewrite-function [first-function second-function]
  (cond (= first-function simplify-identity) second-function
        (= second-function simplify-identity) first-function
        :else
        (fn [rexpr simplify]
          (let [res (first-function rexpr simplify)]
            (if (or (nil? res) (= res rexpr))
              (second-function rexpr simplify) ;; second function will likely be the new added function
              (do
                (dyna-assert (rexpr? res))
                res))))))


(defmacro def-rewrite-matcher
  ([name var body mapper-func]
   (assert (= 1 (count var))) ;; I think this is always true already...
   `(do (swap! rexpr-matchers assoc (quote ~name)
               (fn ~var ~body))
        (swap! rexpr-matchers-mappers (quote ~name)  ;; I don't think that this is used atm...
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
  (if (vector? context-match)
    (let [f (first context-match)
          r (vec (rest context-match))
          ;; nf (cons (first f) (map (fn [vm]
          ;;                           (if (and (seqable? vm) (contains? present-variables (second vm)))
          ;;                             (second vm)
          ;;                             vm))
          ;;                         (rest f)))
          ]
       ;; TODO: this should allow for matching multiple values at the same time
      (if (empty? r)
        (recur present-variables f body)
        ;; then this is going to have to do multiple matches
        (make-context-matching-function
         present-variables f (fn [pv]
                               (make-context-matching-function pv r body)))))
    (let [rexpr-context (gensym 'rexpr-context)]
      `(do (dyna-debug (dyna-assert (= simplify-inference (tlocal *current-simplify-running*))))
           (context/scan-through-context-by-type (context/get-context)
                                                 ~(symbol (str (car context-match) "-rexpr"))
                                                 ~rexpr-context
                                                 (do ;(debug-repl "ctx mm")
                                                   (when (and ~@(for [pv present-variables] ;; do not want to match something that has already been matched
                                                                  ;; this should only consider the present variables which are R-exprs, whereas most of the present variables will
                                                                  `(not= ~pv ~rexpr-context)))
                                                     ~(make-rexpr-matching-function rexpr-context (conj present-variables rexpr-context) context-match body))))))))


(defn- make-rexpr-matching-function [source-variable present-variables matcher body]
  (let [matcher (if (map? matcher) matcher {:rexpr matcher})
        rexpr-match (:rexpr matcher)
        context-matcher (:context matcher)
        rexpr-type-matched (car rexpr-match)

        ;; this returns an array of [`(expression-that-checks-match) `variable-to-unpack-into expression-to-recursively-match-or-nil]
        match-args (vec (map (fn [a]
                               (cond
                                      (and (symbol? a) (contains? present-variables a)) (let [r (gensym 'match-equals-var)] ;; this will check withan existing variable being the same as this value
                                                                                          [`(= ~a ~r) r nil])
                                      (= a '_) [`true (gensym 'do-not-care) nil] ;; this is an expression like `_` where there could be many we ignore
                                      (symbol? a) [`true a nil] ;; this is an expression like `binding-var`
                                      (and (= 2 (count a)) ;; this is an expression like `(:foo binding-var)`
                                           (not (contains? @rexpr-containers-signature (car a)))
                                           (symbol? (cdar a)))
                                      (let [var (if (= (cdar a) '_) (gensym 'do-not-reuse) (cdar a))
                                            checker (get @rexpr-matchers (car a) (car a))]
                                        (dyna-assert (not (keyword? checker))) ;; this should have already been resolved
                                        [`(~checker ~var) var nil])

                                      ;; if we did not match one of the existing patterns, then this assumes that the inner part needs to get matched recursivly
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
    (dyna-assert (= (count (get @rexpr-containers-signature (symbol rexpr-type-matched))) (- (count rexpr-match) 1))
          ;  "The R-expr match expression does not contain the right number of arguments, it will never match"
                 )
    (dyna-assert (apply distinct? (map second match-args)))
    (assert (subset? (keys matcher) #{:rexpr :context :check})
            "matcher map contains unexepxected key")
    `(when (instance? ~(symbol (strict-get @rexpr-containers-class-name (symbol rexpr-type-matched))) ~source-variable)

       (let [;; this version is going to do field access directly on the class to
             ;; get the fields it is going to match against (should be easy for
             ;; the JVM compiler to handle this)
            ~@(apply concat (zipseq (map cdar match-args)
                                    (let [rexpr-sig (get @rexpr-containers-signature (symbol rexpr-type-matched))
                                          rcname (strict-get @rexpr-containers-class-name (symbol rexpr-type-matched))]
                                      (for [lname rexpr-sig]
                                        (list '.
                                              (with-meta source-variable {:tag rcname})
                                              (symbol (munge (last lname))))))))]

         (when (and ~@(remove true? (map car match-args)))
           ~(if (not (nil? context-matcher))
              (make-context-matching-function present-variables context-matcher generate-body)
              (generate-body present-variables)))))))

(defn- match-rexpr-fn [source-variable matcher body]
  (let [source (gensym 'source)]
    `(let [~source ~source-variable] ;; copying the variable is probably not necessary in most cases???
       ~(make-rexpr-matching-function source #{source source-variable} matcher (fn [pv] body)))))

;; (defn- get-match-base-type [matcher]
;;   (car (if (map? matcher) (:rexpr matcher) matcher)))

(defmacro match-rexpr [source-variable matcher & body]
  `(do ~(if system/status-counters `(StatusCounters/match_attempt))
       ~(match-rexpr-fn source-variable matcher
                        `(do
                           ~(when system/status-counters `(StatusCounters/match_sucessful))
                           ~@body))))

(defn- make-rewriter-function [kw-args matcher body form]
  ;; this needs to go through and define something where the different functions
  ;; are invoked on the relvant parts of the expression.  Because the
  ;; expressions have different field values, and are not positional, this means
  ;; that those matchers will have to extract the right values (or something
  (let [res (gensym 'res)
        ;functor-name (car (if (map? matcher) (:rexpr matcher) matcher))
        do-rewrite-body `(let [~res (do ~body)]
                           ~(when system/print-rewrites-performed
                              `(when (and (not (nil? ~res)) (not= ~res ~'rexpr))
                                 ;(debug-delay-ntimes 1000 (debug-repl))
                                 (print ~(str "Performed rewrite:"  (meta form) "\nOLD: ") ~'rexpr "NEW: " ~res "CONTEXT:" (context/get-context))))
                           ~(when system/status-counters
                              `(when (and (not (nil? ~res)) (not= ~res ~'rexpr))
                                 (StatusCounters/rewrite_performed)))
                           ~(when (:check-exposed-variables kw-args)
                              `(let [~'exposed-incoming (exposed-variables ~'rexpr)
                                     ~'result ~res
                                     ~'exposed-outgoing (exposed-variables ~res)
                                     ~'exposed-difference (difference ~'exposed-incoming ~'exposed-outgoing)]
                                 (when (and (is-non-empty-rexpr? ~'result) (some #(not (is-bound? %)) ~'exposed-difference))
                                   (debug-repl "difference in exposed-variables"))))
                           ~res)]
    `(fn (~'[rexpr simplify]
          (match-rexpr ~'rexpr ~matcher ~do-rewrite-body)))))

(defn- make-rewrite-func-body [kw-args body]
  ;; (if (map? body)
  ;;   (debug-repl "vv"))
  ;; (when (:check-expression kw-args)
  ;;   (debug-repl "v2"))
  (cond
    (:infers kw-args) `(let [infered-rexpr# ~(:infers kw-args)]
                         ;(debug-repl "doing infer1")
                         (when (or (is-empty-rexpr? infered-rexpr#)
                                   (not (ctx-contains-rexpr? (context/get-context) infered-rexpr#)))
                           ;(debug-repl "doing infer")
                           (make-conjunct [(~'simplify infered-rexpr#) ~'rexpr])))
    (:assigns kw-args) (do

                         ;(assert (map? (:assigns kw-args)))
                         ;; if there is only a single value, then this does not need a conjunct.
                         ;; would be interesting if make-conjunct was a macro  Then it could check if there is anything that could
                         ;; match at the location of the code.  That would mean that
                         (if false;(map? (:assigns kw-args))
                           `(make-conjunct [~@(for [[k v] (:assigns kw-args)]
                                                `(make-unify ~k (make-constant ~v)))])
                           `(let [map-val# ~(:assigns kw-args)]
                              ;; there could be some check here that the thing returned a map, or that this is some function
                              (make-conjunct (vec (for [[k# v#] map-val#]
                                                    (make-unify k# (make-constant v#))))))))
    (:assigns-variable kw-args) (do
                                  `(let [v# ~body]
                                     (if (context/has-context)
                                       (do
                                         (set-value! ~(:assigns-variable kw-args) v#)
                                         (make-multiplicity 1))
                                       (make-no-simp-unify ~(:assigns-variable kw-args) (make-constant v#)))))
    (:check kw-args) (do
                       `(if ~(:check kw-args)
                            (make-multiplicity 1)
                            (make-multiplicity 0)))
    :else body))

#_(defmacro def-rewrite-direct-old [functor-name runs-at function]
  ;; use like (def-rewrite-direct foo [:standard] (fn [rexpr simplify] ...))
  ;; The function is always called, so it needs to do its own pattern matching
  ;; internally
  (let [rewrite-func-var (gensym 'rewrite-func)]
    `(let [~rewrite-func-var ~function]
       (locking dyna.rexpr-constructors/modification-lock
         ~@(for [run-at (if (seqable? runs-at) runs-at [runs-at])]
             `(let [[rewrite-collection# rewrite-collection-func#] ;; the collection-func is NOT set here...... it is setup in def-base-rexpr
                    ~(case run-at
                       :standard `[(var-get #'rexpr-rewrites) (var-get #'rexpr-rewrites-func)]
                       :construction `[(var-get #'rexpr-rewrites-construct) (var-get #'rexpr-rewrites-construct-func)]
                       :inference `[(var-get #'rexpr-rewrites-inference) (var-get #'rexpr-rewrites-inference-func)]
                       :jit-compiler `[(var-get #'rexpr-rewrites-during-jit-compilation) nil])
                    functor-name# ~(symbol (str functor-name "-rexpr"))]
                ;; this is now also protected by the modification lock above???, so we don't need the atomic I guess....
                (swap-vals! rewrite-collection# (fn [old#] (assoc old# functor-name# (conj (get old# functor-name# #{}) ~rewrite-func-var))))
                (let [combined-func# (~combine-rewrite-function
                                      ~(symbol "dyna.rexpr-constructors" (str (case run-at
                                                                                :standard "simplify-"
                                                                                :construction "simplify-construct-"
                                                                                :inference "simplify-inference-"
                                                                                :jit-compiler "simplify-jit-compilation-step-")
                                                                              functor-name))
                                      ~rewrite-func-var)]
                  (intern 'dyna.rexpr-constructors '~(symbol (str (case run-at
                                                                    :standard "simplify-"
                                                                    :construction "simplify-construct-"
                                                                    :inference "simplify-inference-"
                                                                    :jit-compiler "simplify-jit-compilation-step-")
                                                                  functor-name))
                          combined-func#)))))
       ~rewrite-func-var)))

(defmacro def-rewrite-direct [functor-name runs-at function]
  (let [rewrite-func-var (gensym 'rewrite-func)]
    `(let [~rewrite-func-var ~function]
       (locking dyna.rexpr-constructors/modification-lock
         ~@(for [run-at (if (seqable? runs-at) runs-at [runs-at])]
             `(.addRewrite ~(with-meta (symbol "dyna.rexpr-constructors" (str (case run-at
                                                                                :standard "simplify-"
                                                                                :construction "simplify-construct-"
                                                                                :inference "simplify-inference-"
                                                                                :jit-compiler "simplify-jit-compilation-step-")
                                                                              functor-name))
                              {:tag "dyna.SimplifyRewriteCollection"})
                           ~rewrite-func-var)))
       ~rewrite-func-var)))

(defmacro def-rewrite [& args]
  (let [kw-args (apply hash-map (if (= (mod (count args) 2) 0)
                                  args
                                  (drop-last args)))]
    (if (:match-combines kw-args)
      (let [combines (:match-combines kw-args)
            contains-or (first (filter #(= 'or (caar %)) (zipseq combines (range))))]
        (assert (not (contains? kw-args :match)))
        (if contains-or
          `(do ~@(let [[group idx] contains-or]
                   (for [cmb (rest group)]
                     `(def-rewrite
                        :match-combines ~(vec (cons cmb
                                                    (drop-nth combines idx)))
                        ~@(apply concat (dissoc kw-args :match-combines))
                        ~(last args)))))
          `(do
             ~@(for [i (range (count combines))]
                 `(def-rewrite
                    :match {:rexpr ~(get combines i)
                            :context ~(vec (drop-nth combines i))}
                    ~@(apply concat (dissoc kw-args :match-combines))
                    ~(last args))))))
      (let [rewrite (make-rewrite-func-body kw-args (last args)) ;; in the case that there is not a last argument, then this will want to match against hte value.
            matcher (:match kw-args)
            matcher-rexpr (if (map? matcher) (:rexpr matcher) matcher)
            functor-name (car matcher-rexpr)
            arity (if (= (cdar matcher-rexpr) :any) nil (- (count matcher-rexpr) 1))
            runs-at (:run-at kw-args :standard)
            rewriter-function (make-rewriter-function kw-args matcher rewrite &form)
            rewrite-func-var (gensym 'rewrite-func)
            run-in-jit (:run-in-jit kw-args true) ;; indicate that this can be run inside of the JIT compiled, code
            jit-compiler-rewrite (:jit-compiler-rewrite kw-args false)]
        (when (and (not (and (:is-debug-check-rewrite kw-args) (not system/check-rexpr-arguments)))
                   (not (and (:is-debug-rewrite kw-args) (not system/debug-statements))))
          (dyna-assert (or (not (map? matcher)) (not (contains? matcher :context)) (= :inference runs-at))) ;; context can only be used when in inference
          (let [ret
                `(let []
                   (def-rewrite-direct ~functor-name ~runs-at ~rewriter-function)
                   ~(when run-in-jit ;; then we are going to save the representation of this rule somewhere
                      `(swap! dyna.rexpr/rexpr-rewrites-source
                              (fn [x#]
                                (let [prev# (get x# ~(symbol (str functor-name "-rexpr")) [])]
                                  (assoc x# ~(symbol (str functor-name "-rexpr"))
                                         (conj prev# {:matcher (quote ~matcher)
                                                      :rewrite (quote ~rewrite)
                                                      ;; this is the source of the rewrite function
                                                      :rewrite-func (quote ~rewriter-function)
                                                      :kw-args (quote ~kw-args)
                                                      :rewrite-body (quote ~(last args))
                                                      :namespace *ns*
                                                      })))))))
                ]
            ret))))))

(defmacro def-iterator [& args]
  (let [kw-args (apply hash-map (drop-last args))
        func-body (last args)
        matcher (:match kw-args)
        matcher-rexpr (if (map? matcher) (:rexpr matcher) matcher)
        functor-name (car matcher-rexpr)
        functor-type (symbol (str functor-name "-rexpr"))
        can-jit (:can-jit kw-args true)
        iter-func `(fn ~'[rexpr]
                     (match-rexpr ~'rexpr ~matcher ~func-body))
        ret `(let [~'iter-func-var ~iter-func]
               ~(when can-jit
                  `(swap! rexpr-iterators-source update ~functor-type conj [(quote ~kw-args) (quote ~func-body) ~'*ns*]))
               (swap! rexpr-iterators-accessors update ~functor-type conj ~'iter-func-var)
               #_(swap! rexpr-iterators-accessors (fn ~'[old]
                                                  (assoc ~'old ~functor-type (conj (get ~'old ~functor-type [])
                                                                                   iter-func#))))
               ;; this needs to save the code definition for finding an iterator
               ;; `(when (:can-jit kw-args true)
               ;;    ;; this will want to take the matcher name and the func-body for the expression
               ;;    ;; the matcher will want to identify the same expression values?

               ;;    ;; though there might not be that much stuff which will have custom iterator code?  I suppose that it should
               ;;    ;; just find what is possible with this
               ;;    )
               )
        ]
    ret))

(defn get-variable-value [variable]
  (if (instance? constant-value-rexpr variable)
    (.value ^constant-value-rexpr variable)
    (ctx-get-value (context/get-context) variable)))

#_(def ^{:dynamic true} *memoization-make-guesses-handler*
  ;; this function is called before a guess is going to be made.  If this function returns true, then it will make the guess
  ;; otherwise it will not make the guess and delay
  ;;
  ;; This is important as making a bad guess could cause the system to not terminate, so we attempt to delay guessing for as long as possible
  (fn [memo-table variables variable-values]
    false))
(def-tlocal memoization-make-guesses-handler)


#_(def ^{:dynamic true} *simplify-with-inferences* false)
#_(def ^{:dynamic true} *simplify-looking-for-fast-fail-only* false) ;; meaning that a rewrite which might take a lot of time should be skipped
(def-tlocal simplify-with-inferences)
(def-tlocal simplify-looking-for-fast-fail-only)

(defn simplify-fast [^Rexpr rexpr]
  (debug-tbinding
   [current-simplify-stack (conj (tlocal *current-simplify-stack*) rexpr)
    current-simplify-running simplify]
   (assert (context/has-context))
   ;(ctx-add-rexpr! rexpr)
   ((rexpr-simplify-fast-collection rexpr) rexpr simplify-fast)
   #_(let [ret ((get @rexpr-rewrites-func (type rexpr) simplify-identity) rexpr simplify)]
     (if (or (nil? ret) (= ret rexpr))
       rexpr ;; if not changed, don't do anything
       (do
         (dyna-assert (rexpr? ret))
                                        ;(ctx-add-rexpr! (context/get-context) ret)
         ret)))))

(def simplify simplify-fast)

(swap! debug-useful-variables assoc
       'simplify (fn [] simplify)
       'simplify-fast (fn [] simplify-fast))


(defn simplify-construct [^Rexpr rexpr]
  (debug-tbinding
   [current-simplify-stack (conj (tlocal *current-simplify-stack*) rexpr)
    current-simplify-running simplify-construct]
   ((rexpr-simplify-construct-collection rexpr) rexpr simplify-construct)
   #_(let [ret ((get @rexpr-rewrites-construct-func (type rexpr) simplify-identity) rexpr simplify-construct)]
     (if (nil? ret)
       rexpr
       (do
         (dyna-assert (rexpr? ret))
         ret)))))

(defn simplify-inference [^Rexpr rexpr]
  (debug-tbinding
   [current-simplify-stack (conj (tlocal *current-simplify-stack*) rexpr)
    current-simplify-running simplify-inference]
   (let [ctx (context/get-context)
         ret ((rexpr-simplify-inference-collection rexpr) rexpr simplify-inference)]
     (if (nil? ret)
       rexpr
       (do
         (ctx-add-rexpr! ctx ret)
         ret))
     #_(let [ret ((get @rexpr-rewrites-inference-func (type rexpr) simplify-identity) rexpr simplify-inference)]
       (if (nil? ret)
         rexpr
         (do (dyna-assert (rexpr? ret))
             (ctx-add-rexpr! ctx ret)
             ret))))))

(defn simplify-fully-no-guess [rexpr]
  (loop [cri rexpr]
    (system/should-stop-processing?)
    (let [nri (loop [cr cri]
                (let [nr (debug-tbinding [current-top-level-rexpr cr]
                                        (simplify-fast cr))]
                  (if (not= cr nr)
                    (recur nr)
                    nr)))
          nrif (debug-tbinding [current-top-level-rexpr nri]
                              (tbinding [simplify-with-inferences true]
                                (simplify-inference nri)))]
      (if (not= nrif nri)
        (recur nrif)
        nrif))))

(defn simplify-fully-with-jit [rexpr]
  (loop [cr rexpr]
    (let [nr (simplify-fully-no-guess cr)
          ;; simplify-jit will create new rewrites and perform those rewrites when applicable
          jr (simplify-jit-create-rewrites nr)]
      (if (= nr jr)
        jr
        (recur jr)))))

(def simplify-fully-internal simplify-fully-with-jit
  ;; simplify-fully if needed to be used by something internal.  Should avoid
  ;; creating new guesses as that might cause the system to make a bad guess causing it to not terminate
  )

(defn simplify-fully [rexpr]
  (try
    (loop [cri rexpr]
      (let [nri (simplify-fully-with-jit cri)
            nri2 (tbinding [memoization-make-guesses-handler (fn [memo-table variable variable-values]
                                                                ;; it is possible that there are multiple *different* kinds of guesses which could be made
                                                                ;; this function could be replaced with something that is smarter and chooses between multiple different options for what to guess about
                                                                true)]
                   (simplify-fast nri))]
        (if (= nri nri2)
          nri
          (recur nri2))))
    (catch UnificationFailure _ (make-multiplicity 0))))

(defn simplify-top [rexpr]
  (let [ctx (context/make-empty-context rexpr)]
    (context/bind-context ctx (simplify-fully rexpr))))

(defn simplify-rexpr-query [query-id rexpr]
  ;; TODO: we might want to make this construct some table for the expression.
  ;; So what representation would come back from the expression

  ;; this could callback async, so we don't want something to depend on this
  ;; having finished a computation before the function returns.

  (let [[ctx res]
        (system/converge-agenda ;; this will keep rerunning this until the agenda does not have any more work to do
         (let [ctx (context/make-empty-context rexpr)
               res (context/bind-context ctx
                                         (simplify-fully rexpr))]
           [ctx res]))]
    ((tlocal system/query-output) query-id {:context ctx
                                     :context-value-map (get (ctx-get-inner-values ctx) 4)
                                     :rexpr res
                                     :rexpr-original rexpr})))


(defn find-iterators [rexpr]
  (let [typ (type rexpr)
        rrs (get @rexpr-iterators-accessors typ [])]
    (apply union (for [rs rrs] (rs rexpr)))))


;; there should be some matcher which is going to identify which expression.
;; this would have some which expressions are the expressions
;; this is going to have to have some context in which an expression

#_(defn is-ground? [var-name]
  (or (and (is-variable? var-name)
           (is-variable-set? var-name))
      (is-constant? var-name)))

#_(def is-ground? is-bound?)

(def-rewrite-matcher :str [string] (string? string))

(def-rewrite-matcher :ground [var-name]
                                        ; this should be redfined such that it will return the ground value for the variable
                                        ; though we might not want to have the matchers identifying a given expression
  (is-bound? var-name))

#_(def-rewrite-matcher :not-ground [var] ;; TODO: I think I can just use :free instead of :not-ground, through the is only used by the unification construction
  (and (is-variable? var) (not (is-bound? var))))

(def-rewrite-matcher :free [var-name]
  (and (is-variable? var-name)
       (not (is-bound? var-name))))

;; (def-rewrite-matcher :computes [var-name] ;; this can be the the same as free, but it should represent that it will compute something
;;   (and (is-variable? var-name)
;;        (not (is-variable-set? var-name))
;;        var-name))


(def-rewrite-matcher :rexpr [rexpr] (rexpr? rexpr))

(def-rewrite-matcher :rexpr-list [rexpr-list]
                     (and (seqable? rexpr-list) (every? rexpr? rexpr-list)))

(def-rewrite-matcher :empty-rexpr [rexpr] (and (rexpr? rexpr) (is-empty-rexpr? rexpr)))


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
  (every? is-bound? var-list))


(def-rewrite-matcher :any [v]
  (is-rexpr-value? v))

(def-rewrite-matcher :any-list [any-list]
  (every? is-rexpr-value? any-list))

;; just match anything
(def-rewrite-matcher :unchecked [x] true)

;; this are things which we want to iterate over the domain for
;; this should
(def-rewrite-matcher :iterate [x]
  (and (is-variable? x) (not (is-bound? x))))

#_(def-rewrite-matcher :type-known [x]
  ;; if there is meta data present for an expression in which case we can just use this
  (do (or (is-ground? x))
      (assert false)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-rewrite
  :match {:rexpr (unify (:any A) (:any B))
          :check (= A B)} ;; if the variables are equal to eachother, then it should always work out
  :run-at :construction
  (make-multiplicity 1))

(def-rewrite
  ;; the matched variable should have what value is the result of the matched expression.
  :match {:rexpr (unify (:ground A) (:ground B))
          :check (= (get-value A) (get-value B))}
  :run-at [:standard :construction :inference]
  (make-multiplicity 1))

(def-rewrite
  :match {:rexpr (unify (:ground A) (:ground B))
          :check (not= (get-value A) (get-value B))}
  :run-at [:standard :construction :inference]
  (make-multiplicity 0))

(def-rewrite
  :match (unify (:ground A) (:free B))
  :run-at [:construction :standard :inference]
  :assigns-variable B
  (get-value A))

(comment
  (def-rewrite
    :match (unify (:ground A) (:ground B))
    :run-at [:standard :construction :inference]
    :check (= (get-value A) (get-value B)))


  ;; the assigns variable rewrite expands into a make-unify, so can't use it directly....
  ;; I suppose can make the assigns varible code get included in the make-rewrite-func-body

  (def-rewrite
    :match (unify (:free A) (:ground B))
    :run-at [:standard :inference]
    :assigns-variable A
    (get-value B))

  )


; this should run at both, so there should be a :run-at :both option that can be selected
(def-rewrite
  :match (unify (:free A) (:ground B))
  :run-at [:standard :construction :inference] ; this will want to run at construction and when it encounters the value so that we can use it as early as possible
  :assigns-variable A
  (get-value B)
  #_(when (context/has-context)
    (assert (not (is-bound? A))) ;; otherwise the setting the value into the context should fail
    (set-value! A (get-value B))
    (make-multiplicity 1)))

(def-iterator
  :match (unify (:iterate A) (:ground B))
  (iterators/make-unit-iterator A (get-value B)))

;; TODO: there is a bidrectional binding iterator that could be added here.  Something like A and B are both ungrounded, and if it managed to ground either of the values, then the other will become ground.
;; This should also exist in the case of the unify-structure, where if all of the arguments are ground, then it could ground the other values, or if it can ground the initial value, then it can ground all of the output variables.
;; How will those variables figure out which


(def-rewrite
  :match (unify-structure (:free out) (:unchecked file-name) (:ground dynabase) (:unchecked name-str) (:ground-var-list arguments))
  :run-at [:construction :standard :inference]
  :assigns-variable out
  (let [dbval (get-value dynabase)
        arg-vals (vec (map get-value arguments))
        sterm (DynaTerm. name-str dbval file-name arg-vals)]
    ;; (when (is-ground? out)
    ;;     (debug-repl "uf1"))
    sterm
    #_(let [res (make-unify out (make-constant sterm))]
        res)))

(def-rewrite
  :match (unify-structure (:ground out) (:unchecked file-name) (:any dynabase) (:unchecked name-str) (:any-list arguments))
  :run-at [:construction :standard :inference]
  (let [out-val (get-value out)]
    (if (or (not (instance? DynaTerm out-val))
            (not= (.name ^DynaTerm out-val) name-str)
            (not= (.arity ^DynaTerm out-val) (count arguments)))
      (make-multiplicity 0) ;; the types do not match, so this is nothing
      (let [conj-map (into [] (map (fn [a b]
                                     (make-unify a (make-constant b)))
                                   arguments (.arguments ^DynaTerm out-val)))
            ret (make-conjunct [(make-unify dynabase (make-constant (.dynabase ^DynaTerm out-val)))
                                (make-conjunct conj-map)])]
        ;(debug-repl "rr")
        ret))))

(def-rewrite
  :match {:rexpr (unify-structure (:any out) (:unchecked file-name) (:any dynabase) (:unchecked name-str) (:any-list arguments))
          :context (unify-structure out (:unchecked file-name2) (:any dynabase2) (:unchecked name-str2) (:any-list arguments2))}
  :run-at :inference
  (if (or (not= name-str name-str2)
          (not= (count arguments) (count arguments2)))
    (make-multiplicity 0) ;; then these two failed to unify together
    (let [res  ;; this needs to unify all of the arguments together
          (make-conjunct [(make-unify dynabase dynabase2)
                          (make-conjunct (vec (map make-unify arguments arguments2)))])]
      res)))



(comment
  (def-rewrite
    :match (conjunct (:rexpr-list children))
    :run-at [:standard :inference]
    (let [res (make-conjunct (doall (map #(let [r (simplify %)]
                                            (if (is-empty-rexpr? r) (throw (UnificationFailure.))
                                                r))
                                         children)))]
      res)))

(def-rewrite
  :match (conjunct (:rexpr-list children))
  :run-at [:standard :jit-compiler] ; :inference
  (make-conjunct (vec (map simplify children))))

(def-rewrite
  :match (conjunct (:rexpr-list children))
  :run-at :inference
  (let [ctx (context/get-context)]
    (doseq [[projected-vars rr] (all-conjunctive-rexprs rexpr)]
      (when (empty? projected-vars) ;; TODO: handle when there are projected vars, as these could still be useful
        (ctx-add-rexpr! ctx rr)))
    (make-conjunct (vec (map simplify children)))))



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
    (case (long @mult)
      0 (or (first (filter is-empty-rexpr? children)) (make-multiplicity 0))
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
  (make-disjunct (vec (filter #(not (is-empty-rexpr? %)) children))))

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
      (make-disjunct (vec others)))))


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
        children-with-contexts (vec
                                 (for [[child-rexpr child-ctx] new-children]
                                   (ctx-exit-context (ctx-subtract child-ctx intersected-ctx)
                                                     child-rexpr)))]
    ;; the intersected context is what can be passed up to the parent, we are going to have to make new contexts for the children
    (ctx-add-context! outer-context intersected-ctx)
                                        ;(debug-repl "disjunct standard")
    (let [ret (make-disjunct children-with-contexts)]
      #_(when-not (= (exposed-variables ret) (exposed-variables rexpr))
        (debug-repl "disjunct exposed"))
      ret)))

(def-iterator
  :match (disjunct (:rexpr-list children))
  (let [all-iters (vec (map find-iterators children))]
    ;; this has to intersect the iterators for the same variables
    (when (every? not-empty all-iters)
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
  ;:is-check-rewrite true
  (when (not= (get-argument M 0) 0)
    (debug-repl "should not happen, proj to inf multiplicity")
    (make-multiplicity ##Inf)))

(def-rewrite
  :match (proj (:free A) (:rexpr R))
  :run-at :construction
  :is-debug-check-rewrite true
  (do
    (when-not (contains? (exposed-variables R) A)
      (debug-repl "proj var not in body")
      nil)))

;; TODO: this rewrite should be cleaned up, there is a lot of "debugging junk" contained in it
(def-rewrite
  :match (proj (:variable A) (:rexpr R))
  :run-at [:standard]

  (let [ctx (context/make-nested-context-proj rexpr [A])
        vv (volatile! nil)
        nR (context/bind-context ctx
                                 (let [zz (simplify R)]
                                   (vreset! vv zz)
                                   zz))]
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
      (do
        (dyna-debug (when-not (or (is-empty-rexpr? nR) (contains? (exposed-variables nR) A))
                      (print "failed find projected var")
                      (debug-repl "gg9")))
        ;(when (<= (count (exposed-variables nR)) 1)  (debug-repl "proj??"))
        (make-proj A nR)))))

(def-rewrite
  :match (proj (:variable A) (:rexpr R))
  :run-at :inference
  (let [ctx (context/make-nested-context-proj rexpr [A])
        nR (context/bind-context ctx (simplify R))
        new-A-rep (if (ctx-is-bound? ctx A)
                    (make-constant (ctx-get-value ctx A))
                    ;; look for a unify expression which can be used to simplify the expression by combining stuff together
                    (let [found (volatile! nil)]
                      (context/scan-through-context-by-variable
                       ctx A found-rexpr
                       (when (is-unify? found-rexpr)
                         (vreset! found found-rexpr)))
                      (when-not (nil? @found)
                        (if (= A (:a @found))
                          (:b @found) ;; select the other variable from the unify expression
                          (:a @found)))))]
    (if (nil? new-A-rep)
      (do
        (dyna-assert (or (is-empty-rexpr? nR) (contains? (exposed-variables nR) A)))
        (make-proj A nR))
      (do
        ;(debug-repl "proj33")
        (remap-variables nR {A new-A-rep})))))

(def-rewrite
  :match (proj (:ground A) (:rexpr R))
  :run-at [:standard :construction]
  (if (is-constant? A) R
      (remap-variables R {A (make-constant (get-value A))})))


(def-rewrite
  ;; lift disjuncts out of projection
  :match (proj (:variable A) (disjunct (:rexpr-list Rs)))
  (let [res (make-disjunct (vec (map #(make-proj A %) Rs)))]
    ;;(debug-repl "proj disjunct")
    res))

(def-rewrite
  ;; lift conjuncts which don't depend on the variable out of the projection
  :match (proj (:variable A) (conjunct (:rexpr-list Rs)))
  :run-at :inference
  (let [not-contain-var (transient [])
        conj-children (vec (remove nil? (map (fn [r]
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


(defn- ^{:dyna-jit-external true} projection-iterator-filter [A iters]
  (remove nil? (map (fn [i]
                      (let [b (iter-what-variables-bound i)]
                        (if (not (some #{A} b))
                          i
                          (if (>= (count b) 2)
                            (iterators/make-skip-variables-iterator i #{A})))))
                    iters)))

(def-iterator
  :match (proj (:variable A) (:rexpr R))
  (let [iters (find-iterators R)]
    ;; if the variable that is projected is contained in the iterator, then we
    ;; will just project it out of the iterator as well
    (projection-iterator-filter A iters)))

(def-rewrite
  :match (proj (:variable A) (:rexpr R))
  :run-at :inference
  (let [iters (find-iterators R)]
    (when (some #(some #{A} (iter-what-variables-bound %)) iters) ;; if there is some iterator that can bind the value of the variable
      (let [results (transient [])]
        (iterators/run-iterator
         :iterators iters
         :required [A]
         :rexpr-in R
         :rexpr-result nR
         :simplify simplify  ;; this will be the simplify methods that is being used in context
         (let [Aval (get-value A)
               zzzz (when (nil? Aval) (debug-repl))
               rr (make-conjunct [(iterator-encode-state-ignore-vars #{A})
                                  (context/bind-no-context
                                   (remap-variables-handle-hidden nR {A (make-constant Aval)}))])]
           ;; the results are just going to become disjuncts, so we will just store them

           ;; this is going to have to encode the state as an R-expr while removing some of the variables
           ;; I suppose that this will mean that it
           ;(debug-repl "in proj iterator")
           (dyna-assert (not (contains? (exposed-variables rr) A)))
           (conj! results rr)))
        ;(debug-repl "proj used iterator")
        (when (= 0 (count results))
          (debug-repl "pp"))
        (make-disjunct (persistent! results))))))

#_(def-rewrite
  :match (proj (:variable A) (:rexpr R))
  :run-at :inference
  (let [iter (find-iterators R)
        iter-self (filter #(contains? (iter-what-variables-bound %) A) iter)]
    (when-not (empty? iter-self)
      (let [proj-vals (transient #{})
            iter-selected (first iter-self)
            iter-which-binding-order (first (iter-variable-binding-order iter-selected)) ;; this should choose somehow which
            zzz (assert (.contains iter-which-binding-order A)) ;; this should be a vector
            iter-run (iter-create-iterator (first iter-self) iter-which-binding-order)] ;; the binding would need to be which variable is getting bound or something...
        (iter-run-cb iter-run #(conj! proj-vals (get % A)))

        (let [nR (make-disjunct (doall (for [val (persistent! proj-vals)]
                                         (remap-variables R {A (make-constant val)}))))]
          ;(debug-repl "ff")
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
              (get @(tlocal system/globally-defined-user-term) n))]
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
                                      :var-list arguments]
  (is-constraint? [this] true)
  (variable-functional-dependencies [this] {(into #{} (filter is-variable? arguments)) #{result}}))

(def-rewrite
  :match (simple-function-call (:unchecked function) (:any result) (:ground-var-list arguments))
  :run-at [:standard :construction]
  :assigns-variable result
  (apply function (map get-value arguments)))

#_(def-rewrite
  :match (simple-function-call (:unchecked function) (:any result) (:ground-var-list arguments))
  :run-at :jit-compiler
  :assigns-variable result
  ;; this is going to want to generate something which calls the function, but also we want the generation to go in directly instead of be indirected through
  (do
    (comment
      ;; something like this
      (jit-macro
       `(~function ~@(map (jit-evaluate-cljform )))
       ))
    (???)))

(defn make-function-call
  {:rexpr-constructor 'simple-function-call
   :rexpr-constructor-type simple-function-call-rexpr}
  [function result args]
  (assert (fn? function))
  (make-simple-function-call function result args))



(def-base-rexpr delayed-rexpr-renamed [:var-map vmap
                                       :unchecked deferred-rexpr]
  (rexpr-jit-info [this] {:jittable false})
  (primitive-rexpr [this] (remap-variables deferred-rexpr vmap)))

(def-rewrite
  :match (delayed-rexpr-renamed (:unchecked vmap) (:unchecked deferred-rexpr))
  (let [nctx (context/make-empty-context deferred-rexpr)]
    (doseq [[vdef vcur] vmap
            :let [val (get-value vcur)]
            :when (not (nil? val))]
      (set-value-in-context! vdef nctx val))
    (let [nr (context/bind-context nctx
                           (simplify deferred-rexpr))]
      (remap-variables nr vmap))))

(def-rewrite
  ;; if there is nothing in the renammping map, then we can just not exist in
  ;; the first place as there is no point
  :match (delayed-rexpr-renamed (empty? vmap) (:unchecked deferred-rexpr))
  :run-at :construction
  deferred-rexpr)
