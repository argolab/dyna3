(ns dyna-backend.rexpr
  (:require [dyna-backend.rexpr :refer :all])
  (:require [dyna-backend.context :refer :all])
  (:require [clojure.zip :refer [seq-zip]])
  (:require [aprint.core :refer [aprint]])
  (:require [dyna-backend.utils :refer :all])
  )

(in-ns 'dyna-backend.rexpr)


;; (def special-arg-functions
;;   #{
;;     'is-variable?
;;     'is-variable-set?
;;     'get-variable-value
;;     'is-constant?
;;     'simplify
;;     })

(def rexpr-matchers (atom {}))

(def rexpr-rewrites (atom {}))

;; we are going to have to have different collections depending on when the rewrite is run at

(def rewrite-run-at
  { :construction {}
    :standard {}
    :complete {}  })

(defmacro def-rewrite-matcher [name var body]
  `(swap! rexpr-matchers assoc (quote ~name)
          ;(with-meta
          (fn ~var ~body)
          ;; for some reason, with the macro expansion, the meta-data causes it to fail
  ;;           {:matcher-name (quote ~name)
  ;;            :matcher-args (quote ~var)
  ;;            :matcher-body (quote ~body)})
  ;; )
))


(defn save-defined-rewrite
  [functor-name rewriter]
  (swap-vals! rexpr-rewrites
              (fn [old] (assoc old functor-name
                               (conj (get old functor-name #{}) rewriter))))
  )


;; (defn- replace-with-matcher-functions [expr]
;;   (map (fn [x] (if (contains? @rexpr-matchers x)
;;                  (get @rexpr-matchers x)
;;                  (if (list? x) (replace-with-matcher-functions x)
;;                      x))) expr))

(defn make-rewriter-function [matcher body]
  ;; this needs to go through and define something where the different functions
  ;; are invoked on the relvant parts of the expression.  Because the
  ;; expressions have different field values, and are not positional, this means
  ;; that those matchers will have to extract the right values (or something
  (let [n-args (- (count matcher) 1)
        ;args (for [_ (range n-args)] (gensym))
        named-args (for [v (cdr matcher)]
                     (if (list? v)
                       (cdar v)
                       v))
        ]
    `(fn ~'[rexpr]
       (let [~(vec named-args) (.get-arguments ~'rexpr)] ; unsure if using the global function vs the .func is better?
         (if (and ~@(map (fn [arg mat]
                           `(~(get @rexpr-matchers mat mat)
                             ~arg)) named-args (for [m (cdr matcher)]
                                                 (if (list? m) (car m) m))))
           (do ~body)
           ~'rexpr ; if there is no matched rewrite, then this can return either the rexpr back again, or nil?
           )
         )
       )
    )
  )


(defmacro def-rewrite [& args]
  (let [kw-args (apply hash-map (drop-last args))
        rewrite (last args)
        functor-name (car (:match kw-args))
        arity (if (= (cdar (:match kw-args)) :any) nil (- (count (:match kw-args)) 1))
        matcher (:match kw-args)
        rewriter-function (make-rewriter-function matcher rewrite)
        ]


    ;; this is going to have to identify which expressions are going to do the matching, then it will find which expressions

    (if (= (:run-at kw-args :standard) :standard)
      `(save-defined-rewrite
        ~(symbol (str functor-name "-rexpr"))
        ~rewriter-function
        ))

    ;; `(save-defined-rewrite
    ;;   ~(symbol (str functor-name "-rexpr"))  ;; this should be the type
    ;;   (fn ~'[x] nil)
    ;;   (fn ~'[x] 123)
    ;;   )


    ))

;; this should mask out the variable and introduce a new context variable which is for the nested context
;; (defmacro rewrite-context [rexpr & args]
;;   `(let [~'&context (~'make-nested-context ~'&context ~rexpr)]
;;      ~@args))

(defn is-variable? [variable]
  (instance? variable-rexpr))

(defn is-variable-set? [variable]
  (or (instance? constant-value-rexpr variable)
      (.is-bound? *context* variable)))

(defn is-constant? [variable]
  (instance? constant-value-rexpr variable))

(defn get-variable-value [variable]
  (if (instance? constant-value-rexpr variable)
    (.value variable)
    (.get-value *context* variable)))


;; (defn simplify
;;   ([rexpr] (let [context (make-empty-context rexpr)]
;;              (simplify context rexpr))
;;    ([context rexpr]
;;    ;; this needs to find some rewrite and apply it to the rexpr


;;    (print "taking multiple arguments")
;;    (???))))

(defn simplify
  [rexpr]
  ;; this should just match the given type and identify if there are rewrites defined for this

  (let [typ (type rexpr)
        rrs (.get @rexpr-rewrites typ)]
    (if (nil? rrs)
      rexpr ;; there is nothing here so we are just going to return the r-expr unmodified
      (or (first (filter (complement nil?))
                 (for [rw rrs]
                   (let [res (rw rexpr)]
                     (if (not= res rexpr) res)))) rexpr))))

;; simplification which takes place a construction time
;; (defn simplify-construct [rexpr]
;;   rexpr)

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
  (and (instance? Rexpr rexpr)
       (not (or (is-variable? rexpr) (is-constant? rexpr)))))

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
    (make-multiplicity 0) ;; meaning that the names on these expressions does not match.
    ;; return the original rexpr
    nil))

(def-rewrite
  ;; the matched variable should have what value is the result of the matched expression.
  :match (unify (:ground A) (:ground B))
  :run-at :standard ; this should run at construction
  (if (= A B)
    (make-multiplicity 1)
    (make-multiplicity 0)))

(def-rewrite
  :match (unify (:ground A) (:free B))
  :run-at :construction
  (make-unify B A))

(def-rewrite
  :match (unify (:free A) (:ground B))
  :run-at :both ; this will want to run at construction and when it encounters the value
  (do
    ; record that a value has been assigned with the context
    (set-value! *context* A B)
    nil))



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
  ; in the case that there is only 1 argument, this
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

;; this needs to have some additional combining of the rules.  In the case that there is some

(def-rewrite
  :match (disjunct (:rexpr-list children))
  (case (count children)
    0 (make-multiplicity 0)
    1 (car children)
    :else rexpr))


;; this should either return nil which means that there is no match
;; or this should match which expression has some

;; (def-rewrite
;;   :match (if (:rexpr A) (:rexpr B) (:rexpr C)) ;; with the (:match pattern being something that allows it to select the correct matcher for a given expression
;;   (let [rr (bind-context (make-nested-context A)
;;             (simplify A))]
;;     ;; this is going to need to have some rewrite context which masks out the current value
;;     nil

;;     ))





;; ;; this is something that can be automatically generated in the case that
;; (def-rewrite
;;   :match (add (:ground A) (:ground B) (:non-ground C))
;;   (make-unify C `(+ ~A ~B)))
