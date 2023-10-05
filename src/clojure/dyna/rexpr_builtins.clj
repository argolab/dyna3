;; this file contains base cases R-expressions.  For example the add operator which
;; requires using some builtin method to perform the addition between two numbers

(ns dyna.rexpr-builtins
  (:require [dyna.utils :refer :all])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.rexpr :refer :all])
  (:require [clojure.set :refer [union]])
  (:require [dyna.user-defined-terms :refer [def-user-term]])
  (:require [dyna.context :as context])
  (:require [dyna.rexpr-pretty-printer :refer [rexpr-printer]])
  (:import [dyna.rexpr unify-structure-rexpr])
  (:import [dyna DynaTerm DIterable DIterator DIteratorInstance UnificationFailure DynaMap IteratorBadBindingOrder]))

;(in-ns 'dyna.rexpr)

(defn  get-variables-in-expression [expression]
  (cond
    (symbol? expression)
    (if (re-matches #"v[0-9]+" (str expression))
      #{ expression }
      #{ }) ; this does not match a variable expression

    (seq? expression)
      (reduce union (map get-variables-in-expression (cdr expression)))

    (vector? expression)
    (reduce union (map get-variables-in-expression expression))

    :else
    #{}))

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
                         (if (some #{var} required-ground)
                           `(:ground ~(symbol (str "g" var)))
                           `(:free ~var))))

       ;;:grounding ~all-vars
       :run-at :standard
       ;;:resulting ()  ; might be nice to know what the resulting form of this rewrite should be
       ~@(if all-ground
           `[:is-check-rewrite true
             :check-expression ~(cdar body)]  ;; this expression should return true or false depending if the check works
           `[:is-assignment-rewrite true
             :assignment-requires-ground-vars [~@required-ground]  ;; variables which are required ground by this expression
             :assignment-computes-var ~(car body) ;; which variable is computed as the result of this expression
             :assignment-computes-expression ~(cdar body) ;; the code which is going to do the computation
             ])

       ;; because of the let-expression, it is a little hard to pull apart the map value that is going to be returned
       ;; how efficient is it going to be about destructuring the representation
       ~@(if all-ground
           [:check]
           [:assigns-variable (car body)])
       (let ~(vec (apply concat
                         (for [v required-ground]
                         `[~v (get-value ~(symbol (str "g" v)))])))
         ~(cdar body)

         ;; ~@(if all-ground
         ;;   `[:check ~(cdar body)]
         ;;   ;; `(if ~(cdar body)
         ;;   ;;   (make-multiplicity 1)
         ;;   ;;   (make-multiplicity 0))
         ;;   `[:assigns {~(car body) ~(cdar body)}]
         ;;   ;`(make-unify ~(car body) (make-constant ~(cdar body)))
         ;;   )
       ))
    ))


;; maybe the builtin R-exprs should have some approach which allows for a
;; dynabase call to be used inplace of the builtin call it would be something
;; like if one of the arguments is a dynabase, then it could replace the
;; argument with whatever is the approperate expression.
;;
;; this would require waiting until there is at least one of the arguments
;; ground.  Also, what the arguments look like for a particular expression how
;; would those arguments work with a given expression?  I suppose that the names
;; would somehow have to indcate the mode of what is getting called, as these
;; expressions have to support different modes.
;;
;; This would mean that the gradient stuff could be implemented in "pure dyna,"
;; though operations like `max` which might be implemented in the runtime would
;; have to consider which of the expression
(defmacro def-builtin-rexpr [name nargs & rewrites]
  ;(print "hello this is here\n")
  ;; (doall (for [rr rewrites]
  ;;          (construct-rewrite-for-expression name nargs rr)))
  `(do
     (def-base-rexpr ~name ~(vec (flatten (for [i (range 0 nargs)]
                                            [:var (symbol (str "v" i))])))
       (is-constraint? [this] true)
       (variable-functional-dependencies ~'[this]
                                         ~(into {} (for [rr rewrites
                                                         :when (not= :allground (car rr))]
                                                     [(into #{} (get-variables-in-expression (cdar rr))) #{(car rr)}]))))
     ~@(for [rr rewrites]
         (construct-rewrite-for-expression name nargs rr)
        )
     ))

(defmacro binary-op-printer [symb rexpr]
  `(defmethod rexpr-printer ~(symbol (str rexpr "-rexpr")) ~'[r]
     (if (= (make-constant true) (:v2 ~'r))
       (str (rexpr-printer (:v0 ~'r)) ~(str symb) (rexpr-printer (:v1 ~'r)))
       (str (rexpr-printer (:v2 ~'r)) "=" (rexpr-printer (:v0 ~'r)) ~(str symb) (rexpr-printer (:v1 ~'r))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(if (= "true" (System/getProperty "dyna.allow_bigint_type" "true"))
  (defmacro upcast-big-int [a b] a) ;; the first argument will upcast to a big int using +'
  (defmacro upcast-big-int [a b] b))

;; don't print the big int with the 1N suffix
(defmethod print-method clojure.lang.BigInt [^clojure.lang.BigInt o ^java.io.Writer w]
  (.write w (.toString o)))

(if (= "true" (System/getProperty "dyna.allow_ratio_type" "true"))
  (defmacro maybe-cast-to-float [a] a)
  (defmacro maybe-cast-to-float [a] `(double ~a)))

; there should be some pattern which matches if there is something

(def-builtin-rexpr add 3
  ;; :allground should just be the special case
  (:allground (= v2 ((upcast-big-int +' +) v0 v1))) ;; return true that for this to identify that this is mul 1, false otherwise

  ;; there should only ever be 1 variable which is free, this means that this expression is rewritten for an expression
  ;; this would have some of the expression


  (v2 ((upcast-big-int +' +) v0 v1))  ;; assign some value to a variable using the existing variables
  (v1 ((upcast-big-int -' -) v2 v0))
  (v0 ((upcast-big-int -' -) v2 v1)))

(def-user-term "+" 2 (make-add v0 v1 v2))
(def-user-term "-" 2 (make-add v2 v1 v0))
(binary-op-printer "+" add)


(defn- is-equal? [val] (fn [x] (= x (make-constant val))))

(def-rewrite
  :match (add ((is-equal? 0) _) (:any B) (:any C))
  (make-unify B C))

(def-rewrite
  :match (add (:any A) ((is-equal? 0) _) (:any C))
  (make-unify A C))

(def-rewrite
  :match {:rexpr (add (:variable A) (:any B) (:variable C))
          :check (= A C)}
  :assigns-variable B
  0)

(def-rewrite
  :match {:rexpr (add (:any A) (:variable B) (:variable C))
          :check (= B C)}
  :assigns-variable A
  0)



#_(def-rewrite
  :match (add (:ground A) (:any B) (:any C))
  (let [av (get-value A)]
    (cond (= av 0) (make-unify B C) ;; the value is zero, so can unify the variables together
          (and (= B C) (not= av 0)) (make-multiplicity 0) ;; the two variables equal will never work
          :else nil)))

#_(def-rewrite
  :match (add (:any A) (:ground B) (:any C))
  (let [bv (get-value B)]
    (cond (= bv 0) (make-unify A C)  ;; the value is zero, so can unify the variables together
          (and (= A C) (not= bv 0)) (make-multiplicity 0)         ;; the two variables equal will never work as non-zero added between them
          :else nil)))

(def-builtin-rexpr times 3
  (:allground (= v2 ((upcast-big-int *' *) v0 v1)))
  (v2 ((upcast-big-int *' *) v0 v1)) ;; this could just identify that these variables must be ground unless they are annotated with other expressions
  (v1 (/ v2 (maybe-cast-to-float v0)))
  (v0 (/ v2 (maybe-cast-to-float v1))))

(def-user-term "*" 2 (make-times v0 v1 v2))
(def-user-term "/" 2 (make-times v2 v1 v0))
(binary-op-printer "*" times)

(def-rewrite
  :match (times ((is-equal? 1) _) (:any B) (:any C))
  (make-unify B C))

(def-rewrite
  :match (times (:any A) ((is-equal? 1) _) (:any C))
  (make-unify A C))

(def-rewrite
  :match {:rexpr (times (:any A) (:variable B) (:variable C))
          :check (= B C)}
  :assigns-variable A
  1)

(def-rewrite ;; A * B = A
  :match {:rexpr (times (:variable A) (:any B) (:variable C))
          :check (= A C)}
  :assigns-variable B
  1)


#_(def-rewrite
  :match (times (:ground A) (:any B) (:any C))
  (let [av (get-value A)]
    (cond (= av 1) (make-unify B C)
          (and (= B C) (not= av 1)) (make-multiplicity 0)
          :else nil)))

#_(def-rewrite
  :match (times (:any A) (:ground B) (:any C))
  (let [bv (get-value B)]
    (cond (= bv 1) (make-unify A C)
          (and (= A C) (not= bv 1)) (make-multiplicity 0)
          :else nil)))


(def-builtin-rexpr min 3
  (:allground (= v2 (min v0 v1)))
  (v2 (min v0 v1)))
(def-user-term "min" 2 (make-min v0 v1 v2))


;; if the output of the min is already known, then at least one of the arguments must
(def-rewrite
  :match (min (:ground A) (:any B) (:ground C))
  (let [av (get-value A)
        cv (get-value C)]
    (cond (> av cv) (make-unify B C)  ;; then the B variable must take on the value which is the min
          (< av cv) (make-multiplicity 0) ;; then the min result already has something smaller than the output so this is not possible
          :else nil)))

(def-rewrite
  :match (min (:any B) (:ground A) (:ground C))
  (let [av (get-value A)
        cv (get-value C)]
    (cond (> av cv) (make-unify B C)  ;; then the B variable must take on the value which is the min
          (< av cv) (make-multiplicity 0) ;; then the min result already has something smaller than the output so this is not possible
          :else nil)))

(def-builtin-rexpr max 3
  (:allground (= v2 (max v0 v1)))
  (v2 (max v0 v1)))
(def-user-term "max" 2 (make-max v0 v1 v2))

(def-rewrite
  :match (max (:ground A) (:any B) (:ground C))
  (let [av (get-value A)
        cv (get-value C)]
    (cond (< av cv) (make-unify B C)
          (> av cv) (make-multiplicity 0)
          :else nil)))

(def-rewrite
  :match (max (:any B) (:ground A) (:ground C))
  (let [av (get-value A)
        cv (get-value C)]
    (cond (< av cv) (make-unify B C)
          (> av cv) (make-multiplicity 0)
          :else nil)))

(def-builtin-rexpr pow 3
  (:allground (= v2 (java.lang.Math/pow v0 v1)))
  (v2 (java.lang.Math/pow v0 v1))
  (v1 (/ (java.lang.Math/log v0) (java.lang.Math/log v2)))
  (v0 (java.lang.Math/pow v2 (/ 1 v1))))

(def-user-term ["pow" "**"] 2 (make-pow v0 v1 v2))
(def-user-term "sqrt" 1 (make-pow v0 (make-constant 0.5) v1))
(binary-op-printer "**" pow)

(def-builtin-rexpr exp 2
  (:allground (= v1 (java.lang.Math/exp v0)))
  (v1 (java.lang.Math/exp v0))
  (v0 (java.lang.Math/log v1)))

(def-user-term "exp" 1 (make-exp v0 v1))
(def-user-term "log" 1 (make-exp v1 v0))

(def-builtin-rexpr lessthan 3
  (:allground (= v2 (< v0 v1)))
  (v2 (< v0 v1))) ;; there should be a return true / false place for this expression

(def-user-term ["lessthan" "<"] 2 (make-lessthan v0 v1 v2))
(def-user-term ["greaterthan" ">"] 2 (make-lessthan v1 v0 v2))
(binary-op-printer "<" lessthan)

(def-builtin-rexpr lessthan-eq 3
  (:allground (= v2 (<= v0 v1)))
  (v2 (<= v0 v1)))

(def-user-term ["lessthaneq" "<="] 2 (make-lessthan-eq v0 v1 v2))
(def-user-term ["greaterthaneq" ">="] 2 (make-lessthan-eq v1 v0 v2))
(binary-op-printer "<=" lessthan-eq)

(defn is-true? [x] (= (make-constant true) x))

(def-rewrite
  :match {:rexpr (lessthan (:free A) (:any B) (is-true? _))
          :context (lessthan (:any C) A (is-true? _))}
  :run-at :inference
  :infers (make-lessthan C B (make-constant true)))

(def-rewrite
  :match {:rexpr (lessthan (:any A) (:free B) (is-true? _))
          :context (lessthan B (:any C) (is-true? _))}
  :run-at :inference
  :infers (make-lessthan A C (make-constant true)))

(def-rewrite
  :match {:rexpr (lessthan (:any A) (:any B) (:any C))
          :check (= A B)}
  :run-at :construction
  (make-unify C (make-constant false)))


(def-rewrite
  :match {:rexpr (lessthan-eq (:free A) (:any B) (is-true? _))
          :context (lessthan-eq (:any C) A (is-true? _))}
  :run-at :inference
  :infers (make-lessthan-eq C B (make-constant true)))

(def-rewrite
  :match {:rexpr (lessthan-eq (:any A) (:free B) (is-true? _))
          :context (lessthan-eq B (:any C) (is-true? _))}
  :run-at :inference
  :infers (make-lessthan-eq A C (make-constant true)))

(def-rewrite
  :match (lessthan (:any A) (:any B) (#(= % (make-constant false)) _))
  :run-at :construction
  (make-lessthan-eq B A (make-constant true)))

(def-rewrite
  :match (lessthan-eq (:any A) (:any B) (#(= % (make-constant false)) _))
  :run-at :construction
  (make-lessthan B A (make-constant true)))

(def-rewrite
  :match {:rexpr (lessthan (:any A) (:free B) (is-true? _))
          :context (lessthan-eq B (:any C) (is-true? _))}
  :run-at :inference
  :infers (make-lessthan-eq A C (make-constant true)))

(def-rewrite
  :match {:rexpr (lessthan (:free A) (:any B) (is-true? _))
          :context (lessthan-eq (:any C) A (is-true? _))}
  :run-at :inference
  :infers (make-lessthan-eq C B (make-constant true)))

(def-rewrite
  :match {:rexpr (lessthan-eq (:any A) (:free B) (is-true? _))
          :context (lessthan B (:any C) (is-true? _))}
  :run-at :inference
  :infers (make-lessthan-eq A C (make-constant true)))

(def-rewrite
  :match {:rexpr (lessthan-eq (:free A) (:any B) (is-true? _))
          :context (lessthan (:any C) A (is-true? _))}
  :run-at :inference
  :infers (make-lessthan-eq C B (make-constant true)))

(def-builtin-rexpr equals 3
  (:allground (= v2 (= v0 v1)))
  (v2 (= v0 v1)))


;; unify-with-return is just called equals.  In the case that we know that two
;; of the values have to be equal, as the return from the expression is going to
;; be true, then it can replace the expression with an equals value
(def-rewrite
  :match (equals (:any A) (:any B) (is-true? _))
  :run-at [:construction :standard]
  (make-unify A B))

(def-rewrite
  :match {:rexpr (equals (:any A) (:any B) C)
          :check (= A B)}
  :run-at :construction
  (make-unify C (make-constant true)))

(def-rewrite
  :match {:rexpr (equals (:free A) (:any B) (is-true? _))
          :context (equals A (:any C) (is-true? _))}
  :run-at :inference
  :infers (make-equals B C (make-constant true)))

(def-rewrite
  :match {:rexpr (equals (:free A) (:any B) (is-true? _))
          :context (equals (:any C) A (is-true? _))}
  :run-at :inference
  :infers (make-equals B C (make-constant true)))


(def-rewrite
  :match {:rexpr (equals (:any A) (:free B) (is-true? _))
          :context (equals B (:any C) (is-true? _))}
  :run-at :inference
  :infers (make-equals B C (make-constant true)))

(def-rewrite
  :match {:rexpr (equals (:any A) (:free B) (is-true? _))
          :context (equals (:any C) B (is-true? _))}
  :run-at :inference
  :infers (make-equals B C (make-constant true)))


(def-user-term ["equals" "=="] 2 (make-equals v0 v1 v2))
(binary-op-printer "==" equals)

(def-builtin-rexpr not-equals 3
  (:allground (= v2 (not= v0 v1)))
  (v2 (not= v0 v1)))

(def-rewrite
  :match (not-equals (:any A) (:any B) (#(= % (make-constant false)) _))
  :run-at [:construction :standard]
  (make-unify A B))

(def-rewrite
  :match {:rexpr (not-equals (:any A) (:any B) C)
          :check (= A B)}
  :run-at :construction
  (make-unify C (make-constant false)))

(def-user-term ["notequals" "!="] 2 (make-not-equals v0 v1 v2))
(binary-op-printer "!=" not-equals)

(def-builtin-rexpr land 3
  (:allground (= (boolean v2) (boolean (and v0 v1))))
  (v2 (boolean (and v0 v1))))
(def-user-term ["land" "&&"] 2 (make-land v0 v1 v2))
(binary-op-printer "&&" land)

(def-builtin-rexpr lor 3
  (:allground (= (boolean v2) (boolean (or v0 v1))))
  (v2 (boolean (or v0 v1))))
(def-user-term ["lor" "||"] 2 (make-lor v0 v1 v2))  ;; the pipe might be something which is or between methods so that we can use this to define types
(binary-op-printer "||" lor)


(def-builtin-rexpr not 2
  (:allground (= (v1 (not v0))))
  (v1 (not v0)))
(def-user-term ["not" "!"] 1 (make-not v0 v1))

(defmethod rexpr-printer not-rexpr [r]
  (str (rexpr-printer (:v1 r)) "= !" (rexpr-printer (:v0 r))))


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


(def-base-rexpr range [:var Low
                       :var High
                       :var Step
                       :var Out
                       :var Contained])
;; the contained variable should just be true.  In which case it will ensure that the value is contained inside of the range
(def-user-term "range" 4 (make-range v0 v1 v2 v3 v4))
(def-user-term "range" 3 (make-range v0 v1 (make-constant 1) v2 v3))
(def-user-term "range" 2 (make-range (make-constant 0) v0 (make-constant 1) v1 v2))

(defmethod rexpr-printer range-rexpr [r]
  (if (and (= 1 (get-value (:Step r))) (= true (get-value (:Contained r))))
    (str "range(" (rexpr-printer (:Low r)) "," (rexpr-printer (:High r)) "," (rexpr-printer (:Out r)) ")")
    (str (rexpr-printer (:Contained r)) "=range(" (rexpr-printer (:Low r)) "," (rexpr-printer (:High r)) "," (rexpr-printer (:Step r)) "," (rexpr-printer (:Out r)) ")")))

(def-rewrite
  :match (range (:ground Low) (:ground High) (:ground Step) (:ground Out) (:any Contained))
  :run-at :standard
  ;; this should just do the check directly, rather than having to deal with the any expression
  ;; as the any expression should only be used in the case that it needs to split the expression with the disjunction
  ;; if there is some expression in which it could possible have that it would
  (let [LowV (get-value Low)
        HighV (get-value High)
        StepV (get-value Step)
        OutV (get-value Out)
        successful (and (int? OutV)
                        (>= OutV LowV)
                        (< OutV HighV)
                        (= (mod (- OutV LowV) StepV) 0))]
    (make-unify Contained
                (make-constant-bool successful))))

(def-rewrite
  :match {:rexpr (range (:ground Low) (:ground High) Step Out (:any Contained))
          :check (>= (get-value Low) (get-value High))}
  :assigns-variable Contained
  false)

(defn- ^{:dyna-jit-external true} range-iterator [Out low-v high-v step-v]
  (let [r (range low-v high-v step-v)]
    #{(reify DIterable
        (iter-what-variables-bound [this] #{Out})
        (iter-variable-binding-order [this] [[Out]])
        (iter-create-iterator [this which-binding]
          (when (not= which-binding [Out])
            (throw (IteratorBadBindingOrder.)))
          (reify DIterator
            (iter-run-cb [this cb-fn] (doseq [v (iter-run-iterable this)] (cb-fn v)))
            (iter-run-iterable [this]
              (for [v r]
                (reify DIteratorInstance
                  (iter-variable-value [this] v)
                  (iter-continuation [this] nil))))
            (iter-run-iterable-unconsolidated [this] (iter-run-iterable this))
            (iter-bind-value [this value]
              (if (and (int? value) (< (mod (- value low-v) step-v) high-v))
                iterator-empty-instance
                nil))
            (iter-estimate-cardinality [this]
              (quot (- high-v low-v) step-v)
                                        ;(count r) ;; this is not optimized, as it will scan through the entire list when doing this count
              ))))}))

(def-iterator
  :match (range (:ground Low) (:ground High) (:ground Step) (:free Out) (is-true? Contained))
  (let [low-v (get-value Low)
        high-v (get-value High)
        step-v (get-value Step)]
    (when (and (int? low-v) (int? high-v) (int? step-v))
      (range-iterator Out low-v high-v step-v))))


;; there should be notation that this is going to introduce a disjunct
;; such that it knows that this would have some loop or something
#_(def-rewrite
  :match (range (:ground Low) (:ground High) (:ground Step) (:free Out) (is-true? Contained))
  :run-at :inference ;; there should be some version of run-at where it would be able to indicate that it would introduce a disjunct, so that this could be some "optional" rewrite or something that it might want to defer until later.  This would be trying to find if
  (do ;(assert (get-value Contained)) ;; in the case that this is false, there is no way for us to rewrite this expression
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
                                          Out
                                          Contained)]))))))


;; there is no way to define a range with 3 arguments, as it would use the same name here
;; that would have to be represented with whatever is some named mapped from a symbol to what is being created

(def random-seed (Integer/valueOf (System/getProperty "dyna.random_seed" (str (rand-int (bit-shift-left 1 31))))))

(defn generate-random [x]
  ;; this will generate a random int32 value
  ;; not sure if the random seed should be improved in how it gets included
  (let [h (.hashCode ^Object x)]
    (unchecked-add-int
     (unchecked-multiply-int h random-seed)
     (bit-xor h random-seed))))

(def-builtin-rexpr random 2
  (:allground (= v1 (generate-random v0)))
  (v1 (generate-random v0)))

(def-user-term "builtin_random_int32" 1 (make-random v0 v1))



;; this will cast to a string as well as concat strings together.
;; I suppose that if all but one of the arguments are ground, then it could still run.
;; this would be finding which of the expressions would correspond with
(def-base-rexpr cast-to-string [:var Out
                                :var-list Args]
  (is-constraint? [this] true))

(def-rewrite
  :match (cast-to-string (:any Out) (:ground-var-list Args))
  (make-unify Out (make-constant (apply str (map get-value Args)))))

;; this is going to cast the value into a string as well as concat multiple strings together
(doseq [i (range 1 50)]
  (let [vars (map #(symbol (str "v" %)) (range 0 (+ 1 i)))]
    (eval `(def-user-term "str" ~i (make-cast-to-string ~(last vars) ~(vec (drop-last vars)))))))

(def-user-term "str" 0 (make-unify v0 (make-constant ""))) ;; with zero arguments, it should just return the empty stringx

;; check that the argument is a string
(def-builtin-rexpr is-string 2
  (:allground (= v1 (string? v0)))
  (v1 (string? v0)))

(def-user-term "string" 1 (make-is-string v0 v1))

(comment
  ;; the unify-with-return is basically the same as ==.  Which returns a boolean
  ;; value if two expressions can unify together if the unify-with-return was
  ;; the last expression in a term, then it might end up not checking the
  ;; unification properly so we actually want to /always/ unify when using
  ;; $unify, and then have that == can be the conditional version which
  ;; sometimes returns false

  (def-base-rexpr unify-with-return [:var A :var B :var Return]
    (is-constraint? [this] true))

  (def-rewrite
    :match (unify-with-return (:ground A) (:ground B) (:free Return))
    :run-at [:standard :construction]
    (make-unify Return (make-constant (= (get-value A) (get-value B)))))

  (def-rewrite
    :match (unify-with-return (:any A) (:any B) (is-true? Return))
    :run-at :construction
    (make-unify A B))

  (def-rewrite
    :match (unify-with-return (:any A) (:any B) (:ground Return))
    :run-at [:standard :construction]
    (when (= (get-value Return) true)
      (make-unify A B))))

;; this should check if the arguments are the same variable, in which case this
;; can just unify the result with true?  but if there is an expression like
;; `X=X` is that suppose to be considered "inf" instead of just 1, as there are
;; infinite number of values for which that expression is true for assuming that
;; there isn't multiple places in which the variable X appears.  I suppose that
;; this will just get rewritten as proj(X, 1) which will have the right semantic
;; meaning, as it will construct the proj statement when it converts from the
;; parser, and then when it converts the unify statement, it will eventially
;; identify the return value as true so it will not identify which of the
;; expressions

;(def-user-term "$unify" 2 (make-unify-with-return v0 v1 v2))

(def-user-term "$unify" 2 (make-conjunct [(make-unify v0 v1)
                                          (make-unify v2 (make-constant true))]))


;; (def-user-term "$make_with_key" 2 (make-multiplicity 1))  ;; TODO: should construct some structured term

;; (def-user-term "$value" 1 (make-multiplicity 1)) ;; TODO: should return the value for some pair which might have the withkey construct
;; (def-user-term "$arg" 1 (make-multiplicity 1)) ;; TODO: should return the argument which is associated with the withkey construct


;; operators for handling an array.  An array in Dyna is just a linked list of cells with the name ".".  This is akin to prolog

;; (def-user-term "$nil" 1 (make-unify v0 (make-structured-rexpr "$nil" [])))
;; (def-user-term "$cons" 2 (make-unify v2 (make-structured-rexpr "." [v0 v1])))

(def-user-term "$nil" 0 (make-unify v0 (make-constant DynaTerm/null_term)))  ;; this is $nil
(def-user-term "$cons" 2 (make-unify-structure v2 nil (make-constant DynaTerm/null_term) "." [v0 v1]))

;; operators for handing a map of elements.  The map is a wrapped clojure map which is associate
;(defrecord DynaMap [map-elements])

(defmethod print-method DynaMap [^DynaMap this ^java.io.Writer w]
  (.write w (str (.map-elements this))))

(def-base-rexpr map-element-access [:var Key
                                    :var Value
                                    :var previous-map
                                    :var resulting-map]
  (is-constraint? [this] true))

(def-base-rexpr map-list-keys [:var Map
                               :var KeyList])

(def-builtin-rexpr is-map 2
  (:allground (= v1 (instance? DynaMap v0)))
  (v1 (instance? DynaMap v0)))

(def-user-term "$map_empty" 0 (make-unify v0 (make-constant (DynaMap. {})))) ;; return an empty map value
(def-user-term "$map_element" 3 (make-map-element-access v0 v1 v2 v3))
(def-user-term "$map_keys" 1 (make-map-list-keys v0 v1))
(def-user-term "map" 1 (make-is-map v0 v1))
;(def-user-term "$map_merge" 2) ;; take two maps and combine them together

;; there should be some way to insert a value into a map overriding, but this will have that
;(def-user-term "$map_insert" )

(def-rewrite
  :match (map-element-access (:ground Key) (:any Value) (:any previous-map) (:ground resulting-map))
  ;; read a value out of the map
  (let [pm (get-value resulting-map)]
    (if (not (instance? DynaMap pm))
      (make-multiplicity 0)
      (let [m (.map-elements ^DynaMap pm)
            k (get-value Key)
            r (get m k)]
        (if (nil? r)
          (make-multiplicity 0)
          (make-conjunct [(make-unify Value (make-constant r))
                          ;; remove the key from the map
                          (make-unify previous-map (make-constant (DynaMap. (dissoc m k))))]))))))

(def-rewrite
  :match (map-element-access (:ground Key) (:ground Value) (:ground previous-map) (:any resulting-map))
  ;; put a value into the map
  ;; if the value already exists in the map, it will have to be mult 0, otherwise it would not be consistent with multiple modes
  (let [pm (get-value previous-map)]
    (if (not (instance? DynaMap pm))
      (make-multiplicity 0)
      (let [m (.map-elements ^DynaMap pm)
            k (get-value Key)
            v (get-value Value)]
        (if (contains? m k)
          (make-multiplicity 0) ;; we can not override an existing key, otherwise this is going to break the out of order procesinsg of this expression...
          (make-unify resulting-map (make-constant (DynaMap. (assoc m k v)))))))))

(def-rewrite
  :match (map-list-keys (:ground Map) (:free KeyList))
  :assigns-variable KeyList
  (let [pm (get-value Map)]
    (when-not (instance? DynaMap pm)
      (throw (UnificationFailure. "not a map")))
    (DynaTerm/make_list (keys (.map-elements ^DynaMap pm)))))

;; this is more permissive than the other function which will return the keys in a particular order
(def-rewrite
  :match (map-list-keys (:ground Map) (:ground KeyList))
  :check true ;; this checks that the sets (represented as a list) are equal
  (let [pm (get-value Map)
        kl (get-value KeyList)]
    (if-not (and (instance? DynaMap pm)
                 (instance? DynaTerm kl))
      false
      (let [l (.list_to_vec ^DynaTerm kl)]
        (if (nil? l) false
            (= (into #{} l) (into #{} (keys (.map-elements ^DynaMap pm)))))))))

(comment
  (def-rewrite
    :match (map-element-access (:ground Key) (:any Value) (:any previous-map) (:any resulting-map))
    :run-at :inference
    (let [ctx (context/get-context)
          did-consider (transient #{previous-map})  ;; the key should not be contained in the previous map, so there is no point
          can-consider-vars (transient #{resulting-map})]
      ;; this will need to look through all of the resulting variables to see if there is any other variable
      ;; which matches ground key.  This will generate new unify rexprs which should allow values to "flow" through the map access

      )))

;; TODO: there should be some operator which is able to do a many element access
;; on the map.  This would allow for it to find that there are

;; (def-rewrite
;;   :match {:rexpr (map-element-access (:ground Key) (:any Value) (:any previous-map) (:ground resulting_map))
;;           :context }
;;   )

;; there should not be any reason to make this into something custom, I suppose that there could be some additional rules defined for
;; the different expressions in the case that an identity element has been identified.  Then it would allow for it to rewrite a rule as just a unification
;; or something.  Though that might allow for strange behavior where there is something like &foo+0=&foo.  So I suppose that this should just keep the values
;; defined using the existing operators
(def-user-term "$unary_-" 1 (make-add v0 v1 (make-constant 0)))

(def-user-term "," 2 (make-conjunct [(make-unify (make-constant true) v0) (make-unify v1 v2)]))


(def-base-rexpr regex-matcher [:var InputString
                               :var Regex
                               :var matched-string
                               :var-list Args])

(def-rewrite
  :match (regex-matcher (:ground InputString) (:ground Regex) (:any MatchedResult) (:variable-list Args))
  (let [inp (get-value InputString)
        re (get-value Regex)]
    (if-not (and (string? inp) (string? re))
      (make-multiplicity 0)
      (let [pattern (re-pattern re)
            matched (re-seq pattern inp)]
        ;; this needs to unify all of the expressions together
        (make-disjunct (doall (for [match matched]
                                (if (< (count match) (+ 1 (count Args)))
                                  (do
                                    (dyna-warning (str "The regular expression " Regex " does not have enough groups for " (count Args) " variables"))
                                    (make-multiplicity 0))
                                  (make-conjunct [(make-no-simp-unify MatchedResult (make-constant (car match)))
                                                  (make-conjunct (doall (map #(make-no-simp-unify %1 (make-constant %2))
                                                                             Args (cdr match))))])))))))))
;; (doseq [i (range 0 50)]
;;   (let [vars (map #(symbol (str "v" %)) (range 3 (+ i 4)))]
;;     (eval `(def-user-term "$regex_match" ~(+ i 3)
;;              (make-conjunct (make-unify ~(last vars) (make-constant true))
;;                             (make-regex-matcher v0 v1 v2 ~(vec (drop-last vars))))))))

(def-builtin-rexpr is-int 2
  (:allground (= v1 (integer? v0)))
  (v1 (integer? v0)))

(def-builtin-rexpr is-float 2
  (:allground (= v1 (float? v0)))
  (v1 (float? v0)))

(def-builtin-rexpr is-number 2
  (:allground (= v1 (number? v0)))
  (v1 (number? v0)))

(def-user-term "int" 1 (make-is-int v0 v1))
(def-user-term "float" 1 (make-is-float v0 v1))
(def-user-term "number" 1 (make-is-number v0 v1))

(defn- round-down [v]
  (cond (integer? v) v
        (float? v) (int (Math/floor v))
        :else (???)))

(defn- round-up [v]
  (cond (integer? v) v
        (float? v) (int (Math/ceil v))
        :else (???)))

(def-rewrite
  :match-combines [(is-int (:free Var) (is-true? _))
                   (lessthan (:free Var) (:ground Upper) (is-true? _))
                   (or (lessthan (:ground Lower) (:free Var) (is-true? _))
                       (lessthan-eq (:ground Lower) (:free Var) (is-true? _)))]
  :run-at :inference
  :infers
  (make-range (make-constant (round-down (get-value Lower)))
              (make-constant (round-up (get-value Upper)))
              (make-constant 1)
              Var
              (make-constant true)))

(def-rewrite
  :match-combines [(is-int (:free Var) (is-true? _))
                   (lessthan-eq (:free Var) (:ground Upper) (is-true? _))
                   (or (lessthan (:ground Lower) (:free Var) (is-true? _))
                       (lessthan-eq (:ground Lower) (:free Var) (is-true? _)))]
  :run-at :inference
  :infers
  (make-range (make-constant (round-down (get-value Lower)))
              (make-constant (round-up (+ 1 (get-value Upper)))) ;; the upper bound is non-inclusive, so we need to +1 in the case of <= for upper
              (make-constant 1)
              Var
              (make-constant true)))



(defmacro incompatible-types [type1 type2]
  `(do
     (def-rewrite
       :match {:rexpr (~type1 ~'(:free Var) ~'(:any Result))
               :context (~type2 ~'Var (is-true? ~'_))}
       :run-at :inference
       :assigns-variable ~'Result
       false ;; the value getting assigned to the result
       )
     (def-rewrite
       :match {:rexpr (~type2 ~'(:free Var) ~'(:any Result))
               :context (~type1 ~'Var (is-true? ~'_))}
       :run-at :inference
       :assigns-variable ~'Result
       false)))

(incompatible-types is-int is-string)
(incompatible-types is-int is-float)
(incompatible-types is-float is-string)
(incompatible-types is-number is-string)

(defmacro not-structure-type [type]
  `(do
     (def-rewrite
       :match {:rexpr (~type ~'(:free Var) ~'(:any Result))
               :context ~'(unify-structure Var _ _ _ _)}
       :run-at :inference
       :assigns-variable ~'Result
       false)
     (def-rewrite
       :match {:rexpr ~'(unify-structure (:free Var) _ _ _ _)
               :context (~type ~'Var (is-true? ~'_))}
       :run-at :inference
       (make-multiplicity 0))))

(not-structure-type is-int)
(not-structure-type is-float)
(not-structure-type is-number)
(not-structure-type is-string)

(comment
  (def-builtin-rexpr int-division 3
    (:allground (= v2 (quot v0 v1)))
    (v2 (quot v0 v1)))
  (def-user-term ["int_division" "//"] 2 (make-int-division v0 v1 v2))

  (def-rewrite
    :match-combines [(int-division (:free Num) (:ground Denom) (:any Result))h.D., Mathematics, University of Texas at Austin, 2003.


                     (or (lessthan (:free Num) (:ground Upper) (is-true? _))
                         (lessthan-eq (:free Num) (:ground Upper) (is-true? _)))
                     (or (lessthan (:ground Lower) (:free Num) (is-true? _))
                         (lessthan-eq (:ground Lower) (:free Num) (is-true? _)))]
    :run-at :inference
    :infers
    (make-range (make-constant (round-down (get-value Lower)))
                (make-constant (round-up (get-value Upper)))
                Demon
                Num
                (make-constant true))))


(def-builtin-rexpr int-cast 2
  (:allground (= v1 (bigint v0)))
  (v1 (bigint v0)))

(defn- cast-to-float [x]
  (if (instance? String x)
    (Double/parseDouble ^String x)
    (. ^Number (num x) doubleVaue)))

(def-builtin-rexpr float-cast 2
  (:allground (= v1 (cast-to-float v0)))
  (v1 (cast-to-float v0)))

(def-user-term "cast_int" 1 (make-int-cast v0 v1))
(def-user-term "cast_float" 1 (make-float-cast v0 v1))


(def-base-rexpr meta-is-ground [:var input
                                :var result])
(def-user-term "$ground" 1 (make-meta-is-ground v0 v1))

(def-rewrite
  :match (meta-is-ground (:ground input) (:any result))
  :assigns-variable result
  true)

(def-base-rexpr meta-is-free [:var input
                              :var result])
(def-user-term "$free" 1 (make-meta-is-free v0 v1))

;; if this value is used, then $free will return true.  This should make it easier to run this against
;; though it would only match against $free rather than having it actually match against an unbound value
;; this might be better if is changed to some dummy type rather than having this represented as a DynaTerm, so it is forced to be checked by $free
;(def ^:dynamic *dollar-free-matches-ground-values* false)
(def-tlocal dollar-free-matches-ground-values)

(defrecord meta-free-dummy-value []
  Object
  (toString [this]
    "$FREE_VARIABLE"))
(def meta-free-dummy-free-value (meta-free-dummy-value.)
                                        ;(DynaTerm. "$free_meta_representing_unbound_value" [])
  )

(defmethod rexpr-printer meta-free-dummy-value [x]
  "$FREE_VARIABLE")

(def-rewrite
  :match (meta-is-free (:ground input) (:any result))
  :assigns-variable result
  ;; this can only match the dummy placeholder value for free, otherwise then it would clearly be bound to something else
  (or (= meta-free-dummy-free-value (get-value input))
      (tlocal *dollar-free-matches-ground-values*)))
(def-rewrite
  :match {:rexpr (meta-is-free _ (:any result))
          :check (tlocal *dollar-free-matches-ground-values*)}
  :assigns-variable result
  true)
(def-rewrite
  :match (meta-is-free (:free input) (:any result))
  :run-at :inference ;; this is indended to delay this a bit such that it has time to check if this is truly a free variable
  :assigns-variable result
  true)


(def-builtin-rexpr colon-line-tracking 3
  (:allground (= v2 (DynaTerm. "$colon_line_tracking" [v0 v1])))
  (v2 (DynaTerm. "$colon_line_tracking" [v0 v1])))

(def-user-term "$colon_line_tracking" 2 (make-colon-line-tracking v0 v1 v2))

(def-builtin-rexpr colon-line-tracking-min 2
  (:allground (and (= "$colon_line_tracking" (:name v1))
                   (> (get v1 0) v0))))

(def-rewrite
  :match {:rexpr (colon-line-tracking-min (:ground idx) (:free res))
          :context (colon-line-tracking (:ground idx2) _ res)}
  :run-at :inference
  :check (>= (get-value idx2) (get-value idx)))

(def-rewrite
  :match {:rexpr (colon-line-tracking-min (:ground idx) (:free res))
          :context (colon-line-tracking-min (:ground idx2) res)
          :check (>= (get-value idx2) (get-value idx))}
  :run-at :inference
  (make-multiplicity 1))
