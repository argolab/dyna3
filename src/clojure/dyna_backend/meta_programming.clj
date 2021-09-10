(ns dyna-backend.meta-programming
  (:require [dyna-backend.utils :refer :all])
  (:require [dyna-backend.rexpr :refer :all])
  (:require [dyna-backend.user-defined-terms :refer [def-user-term]]))


;; there should be some meta-programming operations


(def-base-rexpr indirect-user-call [:var indirect-user-var
                                    :var-list argument-vars
                                    :var result])

(doseq [i (range 1 10)]
  (let [vars (map #(symbol (str "v" %)) (range 1 (+ 1 i)))]
    (eval `(def-user-term "$call" ~i (make-indirect-user-call ~'v0 ~(vec (drop-last vars)) ~(last vars))))))


(def-base-rexpr reflect-structure [:var out
                                   :var dynabase
                                   :var name
                                   :var arity ;; once the name and arity is known, then this can be replaced as a bunch of unify expressions
                                   :var arguments])


(let [junk-var (make-variable (gensym))]
  (def-user-term "$reflect" 3 (make-conjunct [(make-unify v3 (make-constant true))
                                              (make-proj junk-var (make-reflect-structure v0 self v1 junk-var v2))])))

(def-user-term "$reflect" 4 (make-reflect-structure v0 self v1 v2 v3))

(def-base-rexpr reflect-structure-vlist [:var out
                                         :var dynabase
                                         :var name ;; the name just needs to be known, and then we can just replace the expression
                                         :var-list arguments])

(doseq [i (range 1 10)]
  (let [vars (map #(symbol (str "v" %)) (range 1 (+ 1 i)))]
    `(eval (def-user-term "$structure" i ~(last vars) ~'self ~'v0 ~(vec (rest (drop-last vars)))))))


;; there can be something like this structure would resemble which of the
;; expressions would correspond with the variables for a given expression.  this
;; will then have to figure out which variables are contextually present in the
;; expression, as the names of variables might change at a later point in time.
;; So there would probably have to be special handing around this expression.  I
;; suppose that this would also have to

(def-base-rexpr eval-user-form [:var Out
                                :var structure])

(def-user-term "$eval" 1 (eval-user-form vv1 v0))
