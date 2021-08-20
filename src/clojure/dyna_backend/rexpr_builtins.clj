;; this file contains base cases R-expressions.  For example the add operator which
;; requires using some builtin method to perform the addition between two numbers

(ns dyna-backend.rexpr-builtins
  (:require [dyna-backend.utils :refer :all])
  (:require [dyna-backend.rexpr :refer :all])
  ;(:require [dyna-backend.rewrites :refer [def-rewrite]])
  (:require [clojure.set :refer [union]])
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




(def-builtin-rexpr times 3
  (:allground (= v2 (* v0 v1)))
  (v2 (* v0 v1)) ;; this could just identify that these variables must be ground unless they are annotated with other expressions
  (v1 (/ v2 v0))
  (v0 (/ v2 v1))
  )
(def-builtin-rexpr min 3
  (:allground (= v2 (min v0 v1)))
  (v2 (min v0 v1))
  )
(def-builtin-rexpr max 3
  (:allground (= v2 (max v0 v1)))
  (v2 (max v0 v1))
  )
(def-builtin-rexpr pow 3
  (:allground (= v2 (java.lang.Math/pow v0 v1)))
  (v2 (java.lang.Math/pow v0 v1))
  (v0 (java.lang.Math/pow v2 (/ 1 v1)))
  )

(def-builtin-rexpr exp 2
  (:allground (= v1 (java.lang.Math/exp v0)))
  (v1 (java.lang.Math/exp v0))
  (v0 (java.lang.Math/log v1))
  )

(def-base-rexpr log [:var v0 :var v1])  ;; have some log which just gets inverted into exp.  though this is not something that would represent a given expression
(def-rewrite
  :match (log (:any v0) (:any v1))
  :run-at :construction
  (make-exp v1 v0))

(def-builtin-rexpr lessthan 3
  (:allground (= v2 (< v0 v1)))
  (v2 (< v0 v1))
  ) ;; there should be a return true / false place for this expression
(def-builtin-rexpr lessthan-eq 3
  (:allground (= v2 (<= v0 v1)))
  (v2 (<= v0 v1))
  )

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

(def-base-rexpr greaterthan [:var v0 :var v1 :var v2])
(def-rewrite
  :match (greaterthan (:any v0) (:any v1) (:any v2))
  :run-at :construction
  (make-lessthan v1 v0 v2))

(def-base-rexpr greaterthan-eq [:var v0 :var v1 :var v2])
(def-rewrite
  :match (greaterthan-eq (:any v0) (:any v1) (:any v2))
  :run-at :construction
  (make-lessthan-eq v1 v0 v2))
;
(def-builtin-rexpr equals 3
                   (:allground (= v2 (= v0 v1)))
                   (v2 (= v0 v1)))

(def-builtin-rexpr not-equals 3
                   (:allground (= v2 (not= v0 v1)))
                   (v2 (not= v0 v1)))

(def-builtin-rexpr land 3
  (:allground (= (boolean v2) (boolean (and v0 v1))))
  (v2 (boolean (and v0 v1)))
  )
(def-builtin-rexpr lor 3
  (:allground (= (boolean v2) (boolean (or v0 v1))))
  (v2 (boolean (or v0 v1)))
  )


(def-builtin-rexpr not 2
  (:allground (= (v1 (not v0))))
  (v1 (not v0)))


(def-builtin-rexpr sin 2
                   (:allground (= v1 (java.lang.Math/sin v0)))
                   (v1 (java.lang.Math/sin v0))
                   (v0 (java.lang.Math/asin v1))
                   )

(def-builtin-rexpr cos 2
                   (:allground (= v1 (java.lang.Math/cos v0)))
                   (v1 (java.lang.Math/cos v0))
                   (v0 (java.lang.Math/acos v1)))

(def-builtin-rexpr tan 2
                   (:allground (= v1 (java.lang.Math/tan v0)))
                   (v1 (java.lang.Math/tan v0))
                   (v0 (java.lang.Math/atan v1)))

;; java does not appear to have the inverse asinh included????
;; will have to include some other math library for this I suppose.... sigh
(def-builtin-rexpr sinh 2
                   (:allground (= v1 (java.lang.Math/sinh v0)))
                   (v1 (java.lang.Math/sinh v0)))

(def-builtin-rexpr cosh 2
                   (:allground (= v1 (java.lang.Math/cosh v0)))
                   (v1 (java.lang.Math/cosh v0)))

(def-builtin-rexpr tanh 2
                   (:allground (= v1 (java.lang.Math/tanh v0)))
                   (v1 (java.lang.Math/tanh v0)))




;; (def-builtin-rexpr abs 2
;;                   :allground (= v1 (if (>= v0 0) v0 (- v0)))
;;                   (v1 (if (>= v0 0) v0 (- v0))))



;; this needs to have some way of defining the sequence things


(def-base-rexpr range [:var Low
                       :var High
                       :var Step
                       :var Out])

;; there should be notation that this is going to introduce a disjunct
;; such that it knows that this would have some loop or something
(def-rewrite
  :match (range (:ground Low) (:ground High) (:ground Step) (:any Out))
  :run-at :standard ;; there should be some version of run-at where it would be able to indicate that it would introduce a disjunct, so that this could be some "optional" rewrite or something that it might want to defer until later.  This would be trying to find if
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
                                      Out)])))))

(comment
  (def-iterator
    :match (range (:ground Low) (:ground High) (:ground Step) (:iterate Out))
    (make-iterator Out (range (get-value Low) (get-value High) (get-value Step))))
  )

;; there is no way to define a range with 3 arguments, as it would use the same name here
;; that would have to be represented with whatever is some named mapped from a symbol to what is being created


(defn generate-random [x]
  (.hashCode ^Object x))

(def-builtin-rexpr random 2
  (:allground (= v1 (generate-random v0)))
  (v1 (generate-random v0)))
