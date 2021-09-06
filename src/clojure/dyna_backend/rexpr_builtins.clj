;; this file contains base cases R-expressions.  For example the add operator which
;; requires using some builtin method to perform the addition between two numbers

(ns dyna-backend.rexpr-builtins
  (:require [dyna-backend.utils :refer :all])
  (:require [dyna-backend.rexpr :refer :all])
  ;(:require [dyna-backend.rewrites :refer [def-rewrite]])
  (:require [clojure.set :refer [union]])
  (:require [dyna-backend.user-defined-terms :refer [def-user-term]])
  )

;(in-ns 'dyna-backend.rexpr)

(defn  get-variables-in-expression [expression]
  (if (symbol? expression)
    (if (re-matches #"v[0-9]+" (str expression))
      #{ expression }
      #{ }) ; this does not match a variable expression
    (if (seq? expression)
      (reduce union (map get-variables-in-expression (cdr expression)))
      #{ })))

(defn construct-rewrite-for-expression [name nargs body]
  (let [all-vars (map #(symbol (str "v" %)) (range nargs))
        all-ground (= (car body) :allground)
        required-ground (if all-ground
                          all-vars
                          (get-variables-in-expression (cdar body)))

        ]

        ;; there is no point to include the grounding variables, as this is just going to ground everything
        ;; we are not required to ground
        ;; grounding-variables (if all-ground
        ;;                       ()
        ;;                       (list (car body)))

    `(def-rewrite
       :match (~name ~@(for [var all-vars]
                         (if (.contains required-ground var)
                           `(:ground ~(symbol (str "g" var)))
                           `(:free ~var))))

       ;;:grounding ~all-vars
       :run-at :standard
       ;;:resulting ()  ; might be nice to know what the resulting form of this rewrite should be

     (let ~(vec (apply concat
                       (for [v required-ground]
                         `[~v (get-value ~(symbol (str "g" v)))])))
       ~(if all-ground
          `(if ~(cdar body)
             (make-multiplicity 1)
             (make-multiplicity 0))
          `(make-unify ~(car body) (make-constant ~(cdar body))))
       ))
    ))



(defmacro def-builtin-rexpr [name nargs & rewrites]
  ;(print "hello this is here\n")
  ;; (doall (for [rr rewrites]
  ;;          (construct-rewrite-for-expression name nargs rr)))
  `(do
     (def-base-rexpr ~name ~(vec (flatten (for [i (range 0 nargs)]
                                            [:var (symbol (str "v" i))]))))
     ~@(for [rr rewrites]
         (construct-rewrite-for-expression name nargs rr)
        )
     ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; there should be some pattern which matches if there is something

(def-builtin-rexpr add 3
  ;; :allground should just be the special case
  (:allground (= v2 (+ v0 v1))) ;; return true that for this to identify that this is mul 1, false otherwise

  ;; there should only ever be 1 variable which is free, this means that this expression is rewritten for an expression
  ;; this would have some of the expression


  (v2 (+ v0 v1))  ;; assign some value to a variable using the existing variables
  (v1 (- v2 v0))
  (v0 (- v2 v1))
  )

(def-user-term "+" 2 (make-add v0 v1 v2))
(def-user-term "-" 2 (make-add v2 v1 v0))


(def-builtin-rexpr times 3
  (:allground (= v2 (* v0 v1)))
  (v2 (* v0 v1)) ;; this could just identify that these variables must be ground unless they are annotated with other expressions
  (v1 (/ v2 v0))
  (v0 (/ v2 v1)))

(def-user-term "*" 2 (make-times v0 v1 v2))
(def-user-term "/" 2 (make-times v2 v1 v0))

(def-builtin-rexpr min 3
  (:allground (= v2 (min v0 v1)))
  (v2 (min v0 v1))
  )
(def-user-term "min" 2 (make-min v0 v1 v2))

(def-builtin-rexpr max 3
  (:allground (= v2 (max v0 v1)))
  (v2 (max v0 v1))
  )
(def-user-term "max" 2 (make-max v0 v1 v2))

(def-builtin-rexpr pow 3
  (:allground (= v2 (java.lang.Math/pow v0 v1)))
  (v2 (java.lang.Math/pow v0 v1))
  (v1 (/ (java.lang.Math/log v0) (java.lang.Math/log v2)))
  (v0 (java.lang.Math/pow v2 (/ 1 v1))))

(def-user-term ["pow" "^"] 2 (make-pow v0 v1 v2))
(def-user-term "sqrt" 1 (make-pow v0 (make-constant 0.5) v1))

(def-builtin-rexpr exp 2
  (:allground (= v1 (java.lang.Math/exp v0)))
  (v1 (java.lang.Math/exp v0))
  (v0 (java.lang.Math/log v1))
  )

(def-user-term "exp" 1 (make-exp v0 v1))
(def-user-term "log" 1 (make-exp v1 v0))

;; (def-base-rexpr log [:var v0 :var v1])  ;; have some log which just gets inverted into exp.  though this is not something that would represent a given expression
;; (def-rewrite
;;   :match (log (:any v0) (:any v1))
;;   :run-at :construction
;;   (make-exp v1 v0))

(def-builtin-rexpr lessthan 3
  (:allground (= v2 (< v0 v1)))
  (v2 (< v0 v1))) ;; there should be a return true / false place for this expression

(def-user-term ["lesshthan" "<"] 2 (make-lessthan v0 v1 v2))
(def-user-term ["greaterthan" ">"] 2 (make-lessthan v1 v0 v2))

(def-builtin-rexpr lessthan-eq 3
  (:allground (= v2 (<= v0 v1)))
  (v2 (<= v0 v1)))

(def-user-term ["lessthaneq" "<="] 2 (make-lessthan-eq v0 v1 v2))
(def-user-term ["greaterthaneq" ">="] 2 (make-lessthan-eq v1 v0 v2))

(comment
  (def-rewrite
    :match (lessthan (:var A) (:var B) (is-true? x))
    :run-at :inference
    :context (lessthan (:var C) (:var A) (is-true? y))
    :infers (lessthan C B (make-constant true))
    ;; then this will need to make a new conjucntive constraint
    nil
    )
  )

;; (def-base-rexpr greaterthan [:var v0 :var v1 :var v2])
;; (def-rewrite
;;   :match (greaterthan (:any v0) (:any v1) (:any v2))
;;   :run-at :construction
;;   (make-lessthan v1 v0 v2))

;; (def-base-rexpr greaterthan-eq [:var v0 :var v1 :var v2])
;; (def-rewrite
;;   :match (greaterthan-eq (:any v0) (:any v1) (:any v2))
;;   :run-at :construction
;;   (make-lessthan-eq v1 v0 v2))

(def-builtin-rexpr equals 3
  (:allground (= v2 (= v0 v1)))
  (v2 (= v0 v1)))

;; this should maybe just be unification rather than having something different for equals checking?
(def-user-term ["equals" "=="] 2 (make-equals v0 v1 v2))

(def-builtin-rexpr not-equals 3
  (:allground (= v2 (not= v0 v1)))
  (v2 (not= v0 v1)))

(def-user-term ["notequals" "!="] 2 (make-not-equals v0 v1 v2))

(def-builtin-rexpr land 3
  (:allground (= (boolean v2) (boolean (and v0 v1))))
  (v2 (boolean (and v0 v1))))
(def-user-term ["land" "&"] 2 (make-land v0 v1 v2))

(def-builtin-rexpr lor 3
  (:allground (= (boolean v2) (boolean (or v0 v1))))
  (v2 (boolean (or v0 v1))))
(def-user-term ["lor" "|"] 2 (make-lor v0 v1 v2))


(def-builtin-rexpr not 2
  (:allground (= (v1 (not v0))))
  (v1 (not v0)))
(def-user-term ["not" "!"] 1 (make-not v0 v1))



(def-builtin-rexpr sin 2
  (:allground (= v1 (java.lang.Math/sin v0)))
  (v1 (java.lang.Math/sin v0))
  (v0 (java.lang.Math/asin v1)))
(def-user-term "sin" 1 (make-sin v0 v1))
(def-user-term "asin" 1 (make-sin v1 v0))

(def-builtin-rexpr cos 2
  (:allground (= v1 (java.lang.Math/cos v0)))
  (v1 (java.lang.Math/cos v0))
  (v0 (java.lang.Math/acos v1)))
(def-user-term "cos" 1 (make-cos v0 v1))
(def-user-term "acos" 1 (make-cos v1 v0))

(def-builtin-rexpr tan 2
  (:allground (= v1 (java.lang.Math/tan v0)))
  (v1 (java.lang.Math/tan v0))
  (v0 (java.lang.Math/atan v1)))
(def-user-term "tan" 1 (make-tan v0 v1))
(def-user-term "atan" 1 (make-tan v1 v0))

;; java does not appear to have the inverse asinh included????
;; will have to include some other math library for this I suppose.... sigh
(def-builtin-rexpr sinh 2
  (:allground (= v1 (java.lang.Math/sinh v0)))
  (v1 (java.lang.Math/sinh v0)))
(def-user-term "sinh" 1 (make-sinh v0 v1))
(def-user-term "asinh" 1 (make-sinh v1 v0))

(def-builtin-rexpr cosh 2
  (:allground (= v1 (java.lang.Math/cosh v0)))
  (v1 (java.lang.Math/cosh v0)))
(def-user-term "cosh" 1 (make-cosh v0 v1))
(def-user-term "acosh" 1 (make-cosh v1 v0))

(def-builtin-rexpr tanh 2
  (:allground (= v1 (java.lang.Math/tanh v0)))
  (v1 (java.lang.Math/tanh v0)))
(def-user-term "tanh" 1 (make-tanh v0 v1))
(def-user-term "atanh" 1 (make-tanh v1 v0))

;; (def-builtin-rexpr abs 2
;;                   :allground (= v1 (if (>= v0 0) v0 (- v0)))
;;                   (v1 (if (>= v0 0) v0 (- v0))))



;; this needs to have some way of defining the sequence things

(def-base-rexpr range [:var Low
                       :var High
                       :var Step
                       :var Out
                       :var Contained])
;; the contained variable should just be true.  In which case it will ensure that the value is contained inside of the range
(def-user-term "range" 4 (make-range v0 v1 v2 v3 v4))
(def-user-term "range" 3 (make-range v0 v1 (make-constant 1) v2 v3))

(def-rewrite
  :match (range (:ground Low) (:ground High) (:ground Step) (:ground Out) (:any Contained))
  :run-at :standard
  ;; this should just do the check directly, rather than having to deal with the any expression
  ;; as the any expression should only be used in the case that it needs to split the expression with the disjunction
  ;; if there is some expression in which it could possible have that it would
  (let [LowV (get-value Low)
        HighV (get-value High)
        StepV (get-value Step)
        OutV (get-value Out)]
    (make-unify Contained
                (make-constant-bool
                 (and (int? OutV)
                      (>= LowV OutV)
                      (< OutV HighV)
                      (= (mod (- OutV LowV) StepV) 0))))))

;; there should be notation that this is going to introduce a disjunct
;; such that it knows that this would have some loop or something
(def-rewrite
  :match (range (:ground Low) (:ground High) (:ground Step) (:any Out) (:ground Contained))
  :run-at :standard ;; there should be some version of run-at where it would be able to indicate that it would introduce a disjunct, so that this could be some "optional" rewrite or something that it might want to defer until later.  This would be trying to find if
  (do (assert (get-value Contained)) ;; in the case that this is false, there is no way for us to rewrite this expression
      (let [LowV (get-value Low)
            HighV (get-value High)
            StepV (get-value Step)]
        (if (is-bound? Out)
          (let [OutV (get-value Out)]
            (make-multiplicity
             (and (int? OutV)
                  (>= LowV OutV)
                  (< OutV HighV)
                  (= (mod (- OutV LowV) StepV) 0))))
          (if (>= LowV HighV) (make-multiplicity 0)
              (make-disjunct [(make-no-simp-unify Out (make-constant LowV)) ; this make-unify will have to avoid running the constructors, otherwise it will assign the value directly.  So no-simp should allow for this to avoid those at construction rewrites
                              (make-range (make-constant (+ LowV StepV))
                                          High
                                          Step
                                          Out)]))))))

(comment
  (def-iterator
    :match (range (:ground Low) (:ground High) (:ground Step) (:iterate Out) (:ground Contained))
    (make-iterator Out (range (get-value Low) (get-value High) (get-value Step))))
  )

;; there is no way to define a range with 3 arguments, as it would use the same name here
;; that would have to be represented with whatever is some named mapped from a symbol to what is being created


(defn generate-random [x]
  ;; this should map to a uniform float between 0-1.  Which will mean that this finds
  (.hashCode ^Object x))

(def-builtin-rexpr random 2
  (:allground (= v1 (generate-random v0)))
  (v1 (generate-random v0)))

(def-user-term "random" 1 (make-random v0 v1))



(def-base-rexpr unify-with-return [:var A :var B :var Return])

(def-rewrite
  :match (unify-with-return (:ground A) (:ground B) (:free Return))
  :run-at :construction
  (make-unify Return (= (get-value A) (get-value B))))

(def-rewrite
  :match (unify-with-return (:any A) (:any B) (#(= true %) Return))
  :run-at :construction
  (make-unify A B))

(def-user-term "$unify" 2 (make-unify-with-return v0 v1 v2))


(def-user-term "$make_with_key" 2 (make-multiplicity 1))  ;; TODO: should construct some structured term

(def-user-term "$value" 1 (make-multiplicity 1)) ;; TODO: should return the value for some pair which might have the withkey construct
(def-user-term "$arg" 1 (make-multiplicity 1)) ;; TODO: should return the argument which is associated with the withkey construct


;; operators for handling an array.  An array in Dyna is just a linked list of cells with the name ".".  This is akin to prolog

(def-user-term "$nil" 1 (make-unify v0 (make-structured-rexpr "$nil" [])))
(def-user-term "$cons" 2 (make-unify v2 (make-structured-rexpr "." [v0 v1])))

;; operators for handing a map of elements.  The map is a wrapped clojure map which is associate
(defrecord DynaMap [map-elements])

(def-base-rexpr map-element-access [:var Key
                                    :var Value
                                    :var previous_map
                                    :var resulting_map])

(def-user-term "$map_empty" 0 (make-unify v0 (make-constant (DynaMap. {})))) ;; return an empty map value
(def-user-term "$map_element" 3 (make-map-element-access v0 v1 v2 v3))
;(def-user-term "$map_merge" 2) ;; take two maps and combine them together

(def-rewrite
  :match (map-element-access (:ground Key) (:any Value) (:any previous_map) (:ground resulting_map))
  ;; read a value out of the map
  (let [pm (get-value resulting_map)]
    (if (not (instance? DynaMap pm))
      (make-multiplicity 0)
      (let [m (.map-elements ^DynaMap pm)
            k (get-value Key)
            r (get m k)]
        (if (nil? r)
          (make-multiplicity 0)
          (make-conjunct [(make-unify Value (make-constant r))
                          ;; remove the key from the map
                          (make-unify previous_map (make-constant (DynaMap. (dissoc m k))))])))
      )))

(def-rewrite
  :match (map-element-access (:ground Key) (:ground Value) (:ground previous_map) (:any resulting_map))
  ;; put a value into the map
  (let [pm (get-value previous_map)]
    (if (not (instance? DynaMap pm))
      (make-multiplicity 0)
      (let [m (.map-elements ^DynaMap pm)
            k (get-value Key)
            v (get-value Value)
            r (assoc m k v)]
        (make-unify resulting_map (make-constant (DynaMap. r)))))))


(def-user-term "$unary_-" 1 (make-add v0 v1 (make-constant 0)))
