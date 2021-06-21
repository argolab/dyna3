(ns dyna-backend.rexpr
  (:require [dyna-backend.rexpr :refer :all])
  (:require [dyna-backend.context :refer :all])
  )

(in-ns 'dyna-backend.rexpr)


(def special-arg-functions
  #{
    'is-variable?
    'is-variable-set?
    'get-variable-value
    'is-constant?
    'simplify
    })

(def rexpr-matchers (atom {}))

(def rexpr-rewrites (atom {}))

(defmacro def-rewrite-matcher [name var body]
  (let [b (add-function-argument special-arg-functions '&context body)]
    `(swap! rexpr-matchers assoc (quote ~name)
            (with-meta
              (fn ~(vec (cons '&context var)) ~b)
              {:matcher-name (quote ~name)
               :matcher-args (quote ~var)
               :matcher-body (quote ~b)})
            )))


(defn- save-defined-rewrite
  [functor-name matcher rewriter]
  ;; insert something into the set
  (if (not (contains? @rexpr-rewrites functor-name))
    (swap! rexpr-rewrites assoc functor-name #{}))
  )

(defn- replace-with-matcher-functions [expr]
  (map (fn [x] (if (contains? @rexpr-matchers x)
                 (get @rexpr-matchers x)
                 (if (list? x) (replace-with-matcher-functions x)
                     x))) expr))

(defn- make-matcher-function [matcher]
  ;; this needs to go through and define something where the different functions
  ;; are invoked on the relvant parts of the expression.  Because the
  ;; expressions have different field values, and are not positional, this means
  ;; that those matchers will have to extract the right values (or something
  (let [m (add-function-argument special-arg-functions '&context
                                 (replace-with-matcher-functions matcher))

        ]

    `(fn ~'[&context rexpr]
       nil
       )
    ))


(defmacro def-rewrite [& args]
  (let [kw-args (apply hash-map (drop-last args))
        rewrite (last args)
        functor-name (car (:match kw-args))
        arity (if (= (cdar (:match kw-args)) :any) nil (- (count (:match kw-args)) 1))
        matcher (:match kw-args)
        matcher-function (make-matcher-function matcher)
        ]
    ;; this is going to have to identify which expressions are going to do the matching, then it will find which expressions


    `(save-defined-rewrite
      (quote ~functor-name)
      ~matcher-function
      (fn ~'[x] 123)
      )
    ))

;; this should mask out the variable and introduce a new context variable which is for the nested context
(defmacro rewrite-context [rexpr & args]
  `(let [~'&context (~'make-nested-context ~'&context ~rexpr)]
     ~@args))

(defn is-variable? [&context variable]
  (instance? variable-rexpr))

(defn is-variable-set? [&context variable]
  (or (instance? constant-value-rexpr variable)
      (.is-bound? &context variable)))

(defn is-constant? [&context variable]
  (instance? constant-value-rexpr variable))

(defn get-variable-value [&context variable]
  (if (instance? constant-value-rexpr variable)
    (.value variable)
    (.get-value &context variable)))


;; (defn simplify
;;   ([rexpr] (let [context (make-empty-context rexpr)]
;;              (simplify context rexpr))
;;    ([context rexpr]
;;    ;; this needs to find some rewrite and apply it to the rexpr


;;    (print "taking multiple arguments")
;;    (???))))

(defn simplify
  [rexpr]

  rexpr)
  ;; ([rexpr]  (let [ctx (make-empty-context rexpr)]
  ;;             (bind-context ctx
  ;;                           (simplify ctx rexpr))))
  ;; ([context rexpr]

  ;;  ;; the rewrite that it will want to match for a given expression

  ;;  ;; there should be different modes which are some of the expressions which might
  ;;  (???)))


;; simplification which takes place a construction time
(defn simplify-construct [rexpr]
  rexpr)

(defn simplify-top [rexpr]
  (let [ctx (make-empty-context rexpr)]
    (bind-context ctx
                  (simplify rexpr))))

;; there should be some matcher which is going to identify which expression.
;; this would have some which expressions are the expressions
;; this is going to have to have some context in which an expression

(def-rewrite-matcher :ground [var-name]
  ;; is-variable-set? is going to have to take
  (if (and (is-variable? var-name) (is-variable-set? var-name))
    (get-variable-value var-name)
    (if (is-constant? var-name)
      (.value var-name))
    ))

(def-rewrite-matcher :free [var-name]
  (and (is-variable? var-name) (not (is-variable-set? var-name)) var-name))

(defn is-rexpr? [rexpr]
  (not (or (is-variable? rexpr) (is-constant? rexpr))))

(def-rewrite-matcher :rexpr [rexpr] (is-rexpr? rexpr))

(def-rewrite-matcher :rexpr-list [rexpr-list]
  (and (list? rexpr-list) (every? is-rexpr? rexpr-list)))


;; something that has a name first followed by a number of different unified expressions
(def-rewrite-matcher :structured [rexpr]

  (and (not (is-variable? rexpr))
       (not (instance? Rexpr rexpr))
       (or (list? rexpr) (vector? rexpr))))
;; this could have that there is some meta-data that is contained in the context
;; then this will have to look at those values

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-rewrite
  :match (unify (:structured A) (:structured B))
  ;; that this should run early, when invoked by the make method call.
  ;; there should be some methods like
  :run-at :construction
  (if (or (not= (count A) (count B)) (not= (car A) (car B)))
    (multiplicity 0) ;; meaning that the names on these expressions does not match.
    ;; return the original rexpr
    rexpr))

(def-rewrite
  ;; the matched variable should have what value is the result of the matched expression.
  :match (unify (:ground A) (:ground B))
  :run-at :standard
  (if (= A B)
    (multiplicity 1)
    (multiplicity 0)))

(def-rewrite
  :match (conjunct (:rexpr-list children))  ;; the conjuncts and the disjuncts are going to have to have some expression wihch
  (make-conjunct (for [child children]
                   (simplify child))))

;; (def-rewrite
;;   :match (conjunct (:rexpr-list children))
;;   :run-at :construnction
;;   ;; which expressions are we going to allow with the given expression
;;   (case (count children)
;;     0 (make-multiplicity 1)
;;     1 (car children)
;;     :else original-rexpr))

(def-rewrite
  :match (conjunct ((fn [x] (= (count x) 1)) children))
  :run-at :construnction
  (car children))

(def-rewrite
  :match (conjunct ((fn [x] (= (count x) 0)) children))
  :run-at :construction
  (make-multiplicity 1))

(def-rewrite
  :match (disjunct (:rexpr-list children))
  (make-disjunct (for [child children]
                   (simplify child))))

(def-rewrite
  :match (disjunct (:rexpr-list children))
  (case (count children)
    0 (make-multiplicity 0)
    1 (car children)
    :else original-rexpr))


;; this should either return nil which means that there is no match
;; or this should match which expression has some

(def-rewrite
  :match (if (:rexpr A) (:rexpr B) (:rexpr C)) ;; with the (:match pattern being something that allows it to select the correct matcher for a given expression
  (let [rr (rewrite-context A
            (simplify A))]
    ;; this is going to need to have some rewrite context which masks out the current value
    nil

    ))





;; ;; this is something that can be automatically generated in the case that
;; (def-rewrite
;;   :match (add (:ground A) (:ground B) (:non-ground C))
;;   (make-unify C `(+ ~A ~B)))
