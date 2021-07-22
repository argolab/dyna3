;; this file contains base cases R-expressions.  For example the add operator which
;; requires using some builtin method to perform the addition between two numbers

(ns dyna-backend.rexpr
  (:require [dyna-backend.utils :refer :all])
  (:require [dyna-backend.rexpr :refer :all])
  ;(:require [dyna-backend.rewrites :refer [def-rewrite]])
  (:require [clojure.set :refer [union]])
  )

(in-ns 'dyna-backend.rexpr)

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
                         `[~v (.get-value ~(symbol (str "g" v)))])))
       ~(if all-ground
          `(if ~(cdar body)
             (make-multiplicity 1)
             (make-multiplicity 0))
          `(make-unify ~(car body) (make-constant ~(cdar body))))
       ))
    ))



(defmacro def-builtin-rexpr [name nargs & rewrites]
  ;(print "hello this is here\n")
  (doall (for [rr rewrites]
           (construct-rewrite-for-expression name nargs rr)))

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
(def-builtin-rexpr land 3
  (:allground (= (boolean v2) (boolean (and v0 v1))))
  (v2 (boolean (and v0 v1)))
  )
(def-builtin-rexpr lor 3
  (:allground (= (boolean v2) (boolean (or v0 v1))))
  (v2 (boolean (or v0 v1)))
  )
