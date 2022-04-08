;; this file contains base cases R-expressions.  For example the add operator which
;; requires using some builtin method to perform the addition between two numbers

(ns dyna.rexpr-builtins
  (:require [dyna.utils :refer :all])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.rexpr :refer :all])
  ;(:require [dyna.rewrites :refer [def-rewrite]])
  (:require [clojure.set :refer [union]])
  (:require [dyna.user-defined-terms :refer [def-user-term]])
  (:import [dyna DynaTerm])
  )

;(in-ns 'dyna.rexpr)

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
       ~@(if all-ground
           `[:is-check-rewrite true
             :check-expression (quote ~(cdar body))]  ;; this expression should return true or false depending if the check works
           `[:is-assignment-rewrite true
             :assignment-requires-ground-vars [~@required-ground]  ;; variables which are required ground by this expression
             :assignment-computes-var ~(car body) ;; which variable is computed as the result of this expression
             :assignment-computes-expression (quote ~(cdar body)) ;; the code which is going to do the computation
             ])



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

(def-rewrite
  :match (add (:ground A) (:any B) (:any C))
  (let [av (get-value A)]
    (cond (= av 0) (make-unify B C) ;; the value is zero, so can unify the variables together
          (and (= B C) (not= av 0)) (make-multiplicity 0) ;; the two variables equal will never work
          :else nil)))

(def-rewrite
  :match (add (:any A) (:ground B) (:any C))
  (let [bv (get-value B)]
    (cond (= bv 0) (make-unify A C)  ;; the value is zero, so can unify the variables together
          (and (= A C) (not= bv 0)) (make-multiplicity 0)         ;; the two variables equal will never work as non-zero added between them
          :else nil)))

(def-builtin-rexpr times 3
  (:allground (= v2 (* v0 v1)))
  (v2 (* v0 v1)) ;; this could just identify that these variables must be ground unless they are annotated with other expressions
  (v1 (/ v2 v0))
  (v0 (/ v2 v1)))

(def-user-term "*" 2 (make-times v0 v1 v2))
(def-user-term "/" 2 (make-times v2 v1 v0))


(def-rewrite
  :match (times (:ground A) (:any B) (:any C))
  (let [av (get-value A)]
    (cond (= av 1) (make-unify B C)
          (and (= B C) (not= av 1)) (make-multiplicity 0)
          :else nil)))

(def-rewrite
  :match (times (:any A) (:ground B) (:any C))
  (let [bv (get-value B)]
    (cond (= bv 1) (make-unify A C)
          (and (= A C) (not= bv 1)) (make-multiplicity 0)
          :else nil)))


(def-builtin-rexpr min 3
  (:allground (= v2 (min v0 v1)))
  (v2 (min v0 v1)))
(def-user-term "min" 2 (make-min v0 v1 v2))

(def-builtin-rexpr max 3
  (:allground (= v2 (max v0 v1)))
  (v2 (max v0 v1)))
(def-user-term "max" 2 (make-max v0 v1 v2))

(def-builtin-rexpr pow 3
  (:allground (= v2 (java.lang.Math/pow v0 v1)))
  (v2 (java.lang.Math/pow v0 v1))
  (v1 (/ (java.lang.Math/log v0) (java.lang.Math/log v2)))
  (v0 (java.lang.Math/pow v2 (/ 1 v1))))

(def-user-term ["pow" "**"] 2 (make-pow v0 v1 v2))
(def-user-term "sqrt" 1 (make-pow v0 (make-constant 0.5) v1))

(def-builtin-rexpr exp 2
  (:allground (= v1 (java.lang.Math/exp v0)))
  (v1 (java.lang.Math/exp v0))
  (v0 (java.lang.Math/log v1)))

(def-user-term "exp" 1 (make-exp v0 v1))
(def-user-term "log" 1 (make-exp v1 v0))

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

(defn is-true? [x] (= (make-constant true) x))

(def-rewrite
  :match {:rexpr (lessthan (:any A) (:any B) (is-true? _))
          :context (lessthan (:any C) A (is-true? _))}
  :run-at :inference
  :infers (make-lessthan C B (make-constant true)))

(def-rewrite
  :match {:rexpr (lessthan (:any A) (:any B) (is-true? _))
          :context (lessthan B (:any C) (is-true? _))}
  :run-at :inference
  :infers (make-lessthan A C (make-constant true)))

(def-rewrite
  :match {:rexpr (lessthan (:any A) (:any B) (:any C))
          :check (= A B)}
  :run-at :construction
  (make-unify C (make-constant false)))

;; (def-rewrite
;;   :match {:rexpr (lessthan (:any A) (:any B) (is-true? _))
;;           :context (lessthan (:any C) (:any D) (is-true? _))}
;;   :run-at :inference
;;   (do
;;     ;(debug-repl "match lessthan")
;;     nil))


(def-rewrite
  :match {:rexpr (lessthan-eq (:any A) (:any B) (is-true? _))
          :context (lessthan-eq (:any C) A (is-true? _))}
  :run-at :inference
  :infers (make-lessthan-eq C B (make-constant true)))

(def-rewrite
  :match (lessthan (:any A) (:any B) (#(= % (make-constant false)) _))
  :run-at :construction
  (make-lessthan-eq B A (make-constant true)))

(def-rewrite
  :match (lessthan-eq (:any A) (:any B) (#(= % (make-constant false)) _))
  :run-at :construction
  (make-lessthan B A (make-constant true)))

(def-rewrite
  :match {:rexpr (lessthan (:any A) (:any B) (is-true? _))
          :context (lessthan-eq B (:any C) (is-true? _))}
  :run-at :inference
  :infers (make-lessthan-eq A C (make-constant true)))


(def-rewrite
  :match {:rexpr (lessthan (:any A) (:any B) (is-true? _))
          :context (lessthan-eq (:any C) A (is-true? _))}
  :run-at :inference
  :infers (make-lessthan-eq C B (make-constant true)))

(def-rewrite
  :match {:rexpr (lessthan-eq (:any A) (:any B) (is-true? _))
          :context (lessthan B (:any C) (is-true? _))}
  :run-at :inference
  :infers (make-lessthan-eq A C (make-constant true)))

(def-rewrite
  :match {:rexpr (lessthan-eq (:any A) (:any B) (is-true? _))
          :context (lessthan (:any C) A (is-true? _))}
  :run-at :inference
  :infers (make-lessthan-eq C B (make-constant true)))

(def-builtin-rexpr equals 3
  (:allground (= v2 (= v0 v1)))
  (v2 (= v0 v1)))


;; XXX: should this rewrite exist??? this makes it basically the same as unify-with-return
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
  :match {:rexpr (equals (:any A) (:any B) (is-true? _))
          :context (equals A (:any C) (is-true? _))}
  :run-at :inference
  :infers (make-equals B C (make-constant true)))

(def-rewrite
  :match {:rexpr (equals (:any A) (:any B) (is-true? _))
          :context (equals (:any C) A (is-true? _))}
  :run-at :inference
  :infers (make-equals B C (make-constant true)))


(def-rewrite
  :match {:rexpr (equals (:any A) (:any B) (is-true? _))
          :context (equals B (:any C) (is-true? _))}
  :run-at :inference
  :infers (make-equals B C (make-constant true)))

(def-rewrite
  :match {:rexpr (equals (:any A) (:any B) (is-true? _))
          :context (equals (:any C) B (is-true? _))}
  :run-at :inference
  :infers (make-equals B C (make-constant true)))


;; this should maybe just be unification rather than having something different for equals checking?
(def-user-term ["equals" "=="] 2 (make-equals v0 v1 v2))

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

(def-builtin-rexpr land 3
  (:allground (= (boolean v2) (boolean (and v0 v1))))
  (v2 (boolean (and v0 v1))))
(def-user-term ["land" "&"] 2 (make-land v0 v1 v2))

(def-builtin-rexpr lor 3
  (:allground (= (boolean v2) (boolean (or v0 v1))))
  (v2 (boolean (or v0 v1))))
(def-user-term ["lor" "|"] 2 (make-lor v0 v1 v2))  ;; the pipe might be something which is or between methods so that we can use this to define types


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


;; this will cast to a string as well as concat strings together.
;; I suppose that if all but one of the arguments are ground, then it could still run.
;; this would be finding which of the expressions would correspond with
(def-base-rexpr cast-to-string [:var Out
                                :var-list Args])

(def-rewrite
  :match (cast-to-string (:any Out) (:ground-var-list Args))
  (make-unify Out (make-constant (apply str (map get-value Args)))))

;; this is going to cast the value to some expression
(doseq [i (range 1 50)]
  (let [vars (map #(symbol (str "v" %)) (range 0 (+ 1 i)))]
    (eval `(def-user-term "str" ~i (make-cast-to-string ~(last vars) ~(vec (drop-last vars)))))))

(def-user-term "str" 0 (make-unify v0 (make-constant ""))) ;; with zero arguments, it should just return the empty stringx

;; check that the argument is a string
(def-builtin-rexpr is-string 2
  (:allground (= v1 (string? v0)))
  (v1 (string? v0)))

(def-user-term "string" 1 (make-is-string v0 v1))

(def-base-rexpr unify-with-return [:var A :var B :var Return])

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
    (make-unify A B)))

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

(def-user-term "$unify" 2 (make-unify-with-return v0 v1 v2))


;; (def-user-term "$make_with_key" 2 (make-multiplicity 1))  ;; TODO: should construct some structured term

(def-user-term "$value" 1 (make-multiplicity 1)) ;; TODO: should return the value for some pair which might have the withkey construct
(def-user-term "$arg" 1 (make-multiplicity 1)) ;; TODO: should return the argument which is associated with the withkey construct


;; operators for handling an array.  An array in Dyna is just a linked list of cells with the name ".".  This is akin to prolog

;; (def-user-term "$nil" 1 (make-unify v0 (make-structured-rexpr "$nil" [])))
;; (def-user-term "$cons" 2 (make-unify v2 (make-structured-rexpr "." [v0 v1])))

(def-user-term "$nil" 0 (make-unify v0 (make-constant DynaTerm/null_term)))  ;; this is $nil
(def-user-term "$cons" 2 (make-unify-structure v2 nil (make-constant DynaTerm/null_term) "." [v0 v1]))

;; operators for handing a map of elements.  The map is a wrapped clojure map which is associate
(defrecord DynaMap [map-elements])

(defmethod print-method DynaMap [^DynaMap this ^java.io.Writer w]
  (.write w (str (.map-elements this))))

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
                          (make-unify previous_map (make-constant (DynaMap. (dissoc m k))))]))))))

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

;; TODO: there should be some operator which is able to do a many element access
;; on the map.  This would allow for it to find that there are

;; (def-rewrite
;;   :match {:rexpr (map-element-access (:ground Key) (:any Value) (:any previous_map) (:ground resulting_map))
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
