(ns dyna-backend.rexpr
    (:require [dyna-backend.utils :refer :all]))


(defprotocol Rexpr
  (primitive-rexpr [this]) ;; return a primitive r-expr for the expression
  ;;(replace-expressions [this expressions-map]) ;; replace a given nested expression
  (get-variables [this])
  (get-children [this])
  )

(defmacro def-base-rexpr [name args]
  (let [vargroup (partition 2 args)
        rname (str name "-rexpr")]
    `(do
       (deftype ~(symbol rname) ~(vec (map cdar vargroup))
       Rexpr
       ~'(primitive-rexpr [this] this) ;; this is a primitive expression so we are going to just always return ourselves
       (~'get-variables ~'[this] (list ~@(map cdar (filter #(= :var (car %1)) vargroup))))
       (~'get-children ~'[this] (list ~@(map cdar (filter #(= :rexpr (car %1)) vargroup))))
       )
       (defn ~(symbol (str "make-" name)) ~(vec (map cdar vargroup))
         (~(symbol (str rname ".")) ~@(map cdar vargroup)))
       )))

(defn make-structure [name args]
  `(~name ~@args))

(def ^:const null-term (make-structure '$null []))


(def-base-rexpr multiplicity [:mult m])

(deftype *-rexpr [args]
  Rexpr
  (primitive-rexpr [this] this)
  (get-variables [this] ())
  (get-children [this] args))

(defn make-*
  ([] (make-multiplicity 1))
  ([x] x)
  ([x y & args] (*-rexpr. (concat (list x y) args))))

(def make-conjunct make-*)

(deftype +-rexpr [args]
  Rexpr
  (primitive-rexpr [this] this)
  (get-variables [this] ())
  (get-children [this] args))

(defn make-+
  ([] (make-multiplicity 0))
  ([x] x)
  ([x y & args] (+-rexpr. (concat (list x y) args))))

(def make-disjunct make-+)

(deftype variable-rexpr [varname]
  Rexpr
  (primitive-rexpr [this] this)
  (get-variables [this] (list this))
  (get-children [this] ()))

(defn make-variable [varname]
  (variable-rexpr. varname))

(defn is-variable? [x] (instance? variable-rexpr x))

(deftype constant-value-rexpr [value]
  Rexpr
  (primitive-rexpr [this] this)
  (get-variables [this] (list this))
  (get-children [this] ()))

(defn make-constant [val]
  (constant-value-rexpr. val))

(defn is-constant? [x] (instance? constant-value-rexpr x))

(def-base-rexpr unify [:var a
                       :var b])

(def-base-rexpr proj [:var v
                      :rexpr body])

(def-base-rexpr aggregator [:str operator
                            :var result
                            :var incoming
                            :rexpr body])

(def-base-rexpr if [:rexpr cond
                    :rexpr true-branch
                    :rexpr false-branch])


(load "rewrites")
(load "rexpr_builtins")
