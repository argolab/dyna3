(ns dyna-backend.rexpr
  (:require [dyna-backend.utils :refer :all])
  (:require [dyna-backend.context :as context
             ;:rename '{get-value context-get-value,
             ;          is-bound? context-is-bound?
             ;          set-value! context-set-value!}
             ])
  (:require [clojure.set :refer [union difference]])
  (:import (dyna_backend UnificationFailure)))


(declare simplify)
(declare simplify-construct)

;(defn simplify-construct [r] r)

(defprotocol Rexpr
  (primitive-rexpr [this]) ;; return a primitive r-expr for the expression
  ;;(replace-expressions [this expressions-map]) ;; replace a given nested expression
  (get-variables [this])
  (get-children [this])
  (get-argument [this n])
  (get-arguments [this])
  (as-list [this]) ; use for printing out the structure

  (exposed-variables [this]) ; return variables values that are exposed externally (so hide aggregators and proj)
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
       (deftype ~(symbol rname) ~(vec (cons 'cached-hash-code (map cdar vargroup)))
         Rexpr
         ~'(primitive-rexpr [this] this)                    ;; this is a primitive expression so we are going to just always return ourselves
         (~'get-variables ~'[this]
           (concat
             (list ~@(map cdar (filter #(= :var (car %1)) vargroup)))
             ~@(map cdar (filter #(= :var-list (car %1)) vargroup))
             ))
         (~'get-children ~'[this]
           (concat
             (list ~@(map cdar (filter #(= :rexpr (car %1)) vargroup)))
             ~@(map cdar (filter #(= :rexpr-list (car %1)) vargroup))
             ))
         (~'get-argument ~'[this n] (nth ~(vec (map cdar vargroup)) ~'n))
         (~'get-arguments ~'[this] ~(vec (map cdar vargroup)))

         (~'as-list ~'[this]
           (list (quote ~(symbol name))
                 ~@(for [v vargroup]
                     (case (car v)
                       :rexpr `(as-list ~(cdar v))
                       :rexpr-list `(map as-list ~(cdar v))
                       (cdar v)
                       ))))
         (~'exposed-variables ~'[this]
           (difference (union #{~@(keep
                                    #(if (= :var (car %)) (cdar %))
                                    vargroup)}
                              ~@(keep
                                  #(if (= :rexpr (car %))
                                     `(exposed-variables ~(cdar %)))
                                  vargroup)
                              ;; ~@(keep
                              ;;    #(if (= :rexpr-list (car %))
                              ;;       `(apply union (for [v ~(cdar %)]
                              ;;                       (exposed-variables v))))
                              ;;    vargroup)
                              )
                       #{~@(keep
                             #(if (= :hidden-var (car %)) (cdar %))
                             vargroup)}
                       ))
         Object
         (equals ~'[this other]
           (or (identical? ~'this ~'other)
               (and (instance? ~(symbol rname) ~'other)
                    (= (hash ~'this) (hash ~'other))
                    ~@(for [[var idx] (zipmap vargroup (range))]
                        `(= ~(cdar var) (get-argument ~'other ~idx))
                        )
                    ))

           )
         (hashCode [this] ~'cached-hash-code)
         (toString ~'[this] (str (as-list ~'this)))
         )


       (defn ~(symbol (str "make-" name))
         {:rexpr-constructor (quote ~name)
          :rexpr-constructor-type ~(symbol rname)}
         ~(vec (map cdar vargroup))
         (assert (and
                  ~@(map (fn [x] `(~(resolve (symbol (str "check-argument-" (symbol (car x))))) ~(cdar x)))
                        vargroup)))
         (simplify-construct (~(symbol (str rname "."))
                               (+ ~(hash rname) ~@(for [[var idx] (zipmap vargroup (range))]
                                                    `(* (hash ~(cdar var)) ~(+ 3 idx))
                                                    ))
                               ~@(map cdar vargroup))))
       (swap! rexpr-constructors assoc ~(str name) ~(symbol (str "make-" name)))
       (defmethod print-method ~(symbol rname) ~'[this ^java.io.Writer w]
         (aprint.core/aprint (as-list ~'this) ~'w))
       )))

(defn make-structure [name args]
  `(~name ~@args))

(def ^:const null-term (make-structure '$null []))


;;;;;;;;;;;;;;;;;;;;;;;;;;
;; things like variables and constants should instead be some other type rather than an R-expr
;; this could be something

(defprotocol RexprValue
  (get-value [this])
  (set-value! [this value])
  (is-bound? [this ])
  )

(defrecord variable-rexpr [varname]
  RexprValue
  (get-value [this] (context/get-value context/*context* this))
  (set-value! [this  value] (context/set-value! context/*context* this value))
  (is-bound? [this]  (context/need-context (context/is-bound? context/*context* this)))
  Object
  (toString [this] (str "(variable " varname ")"))
  )

;; there should be some version of bound/unbound variables which are designed to access slots in the expression

(defrecord constant-value-rexpr [value]
  RexprValue
  (get-value [this] value)
  (set-value! [this  v]
    (if (not= v value)
      (throw (UnificationFailure. "can not assign value to constant"))))
  (is-bound? [this] true)
  Object
  (toString [this] (str "(constant " value ")"))
  )

;; should the structured types have their own thing for how their are represented
;; though these will want to have some e
(defrecord structured-rexpr [name arguments]
  RexprValue
  (get-value [this]
    ;; this is going to have to construct the structure for this
    ;; which means that it has to get all of the values, and then flatten it to a structure
    (make-structure name (map (fn [x] (context/get-value context/*context* x)) arguments))
    )
  (set-value! [this v]
    (if (or (not= (car v) name) (not= (+ 1 (count arguments)) (count v)))
      nil;(throw (Unification
    ))
  (is-bound? [this]
    (context/need-context (every? (fn [x] (context/is-bound? context/*context* x)) arguments))))


(defn is-constant? [x] (instance? constant-value-rexpr x))
(defn is-variable? [variable]
  (instance? variable-rexpr variable))

(defn is-rexpr? [rexpr]
  (and (instance? Rexpr rexpr)
       (not (or (is-variable? rexpr) (is-constant? rexpr)))))

(defn check-argument-mult [x] (int? x))
(defn check-argument-rexpr [x] (is-rexpr? x))
(defn check-argument-rexpr-list [x] (every? is-rexpr? x))
(defn check-argument-var [x] (or (is-variable? x) (is-constant? x)))
(defn check-argument-var-list [x] (every? is-variable? x))
(defn check-argument-hidden-var [x] (check-argument-var x))
(defn check-argument-str [x] (string? x))


(def-base-rexpr multiplicity [:mult m])

(def-base-rexpr conjunct [:rexpr-list args])

(def make-* make-conjunct)

(def-base-rexpr disjunct [:rexpr-list args])

(def make-+ make-disjunct)

(defn make-variable [varname]
  (variable-rexpr. varname))

(defmethod print-method variable-rexpr [this ^java.io.Writer w]
  (.write w (str "(variable " (.varname this) ")")))

(defn make-constant [val]
  (constant-value-rexpr. val))

(defmethod print-method constant-value-rexpr [this ^java.io.Writer w]
  (.write w (str "(constant " (.value this) ")")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-base-rexpr unify [:var a
                       :var b])

(def-base-rexpr proj [:hidden-var v
                      :rexpr body])

(def-base-rexpr aggregator [:str operator
                            :var result
                            :hidden-var incoming
                            :rexpr body])

(def-base-rexpr if [:rexpr cond
                    :rexpr true-branch
                    :rexpr false-branch])


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

(def-base-rexpr +-op [:var-list disjunction-variables
                      :rexpr base-expr
                      :rexpr-list bodies])


;(load "context")
(load "rewrites")
(load "rexpr_builtins")
