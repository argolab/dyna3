(ns dyna-backend.rexpr
    (:require [dyna-backend.utils :refer :all]))


(defprotocol Rexpr
  (primitive-rexpr [this]) ;; return a primitive r-expr for the expression
  ;;(replace-expressions [this expressions-map]) ;; replace a given nested expression
  (get-variables [this])
  (get-children [this])
  (as-list [this])
  )

;; the annotation on a variable can be one of
;;; :var, :rexpr, :var-list, :rexpr-list
;;; other annotations are ignored for the time being

(def rexpr-containers (atom #{}))

(defmacro def-base-rexpr [name args & optional]
  (let [vargroup (partition 2 args)
        rname (str name "-rexpr")
        opt (if (not (nil? optional)) (vec optional) [])]
    `(do
       (deftype ~(symbol rname) ~(vec (map cdar vargroup))
       Rexpr
       ~'(primitive-rexpr [this] this) ;; this is a primitive expression so we are going to just always return ourselves
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
       (~'as-list ~'[this]
        (list 'test ;(quote ~(symbol name))
              ;; ~@(for [v vargroup]
              ;;     (case (car v)
              ;;       ;; :rexpr `(as-list ~(cdar v))
              ;;       ;; :rexpr-list `(map as-list ~(cdar v))
              ;;       "test"
              ;;       ;(cdar v)
              ;;       ))))
              ))
       )
       (defn ~(symbol (str "make-" name)) ~(vec (map cdar vargroup))
         (let [ret (~(symbol (str rname ".")) ~@(map cdar vargroup))]
           (simplify-construct ret)
           ))
       (defmethod print-method ~(symbol rname) ~'[this ^java.io.Writer w]
         (aprint.core/aprint (as-list ~'this) ~'w))
       ;(swap! rexpr-containers conj ~(symbol name))
       )))

(defn make-structure [name args]
  `(~name ~@args))

(def ^:const null-term (make-structure '$null []))


(def-base-rexpr multiplicity [:mult m])

(def-base-rexpr conjunct [:rexpr-list args])

;; (deftype *-rexpr [args]
;;   Rexpr
;;   (primitive-rexpr [this] this)
;;   (get-variables [this] ())
;;   (get-children [this] args))

;; (defn make-*
;;   ([] (make-multiplicity 1))
;;   ([x] x)
;;   ([x y & args] (*-rexpr. (concat (list x y) args))))


(def make-* make-conjunct)

(def-base-rexpr disjunct [:rexpr-list args])

;; (deftype +-rexpr [args]
;;   Rexpr
;;   (primitive-rexpr [this] this)
;;   (get-variables [this] ())
;;   (get-children [this] args))

;; (defn make-+
;;   ([] (make-multiplicity 0))
;;   ([x] x)
;;   ([x y & args] (+-rexpr. (concat (list x y) args))))

(def make-+ make-disjunct)

;;;;;;;;;;;;;;;;;;;;;;;;;;
;; things like variables and constants should instead be some other type rather than an R-expr
;; this could be something

(defprotocol RexprValue
  (get-value [this context])
  (set-value! [this context value])
  (is-bound? [this context])
  )

(deftype variable-rexpr [varname]
    RexprValue
    ;; using (.get-value ...) is calling a method on the class
    (get-value [this context] (.get-value context this))
    (set-value! [this context value] ())
    (is-bound? [this context] (.is-bound? context this))
  )

;; there should be some version of bound/unbound variables which are designed to access slots in the expression

(deftype cosntant-variable-rexpr [value]
  RexprValue
  (get-value [this context] value)
  (set-value! [this context value] (throw (RuntimeException. "attempting to set the value of a constant")))
  (is-bound? [this context] true)
  )

;; should the structured types have their own thing for how their are represented
;; though these will want to have some e
(deftype structured-rexpr [name arguments]
  RexprValue
  (get-value [this context] (???))
  (set-value! [this context value] (???))
  (is-bound? [this context] (???)))



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

;;;;;;;;;;;;;;;;;;;;;;;;

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
