(ns dyna.rexpr-dynabase
  (:require [dyna.utils :refer :all])
  (:require [dyna.base-protocols :refer :all])
  (:import  [dyna.base_protocols Dynabase])
  (:require [dyna.rexpr :refer :all])
  (:require [dyna.user-defined-terms :refer [def-user-term]])
  (:require [dyna.assumptions :refer [make-assumption]])
  (:require [dyna.system :as system]))

;; R-exprs which represent construction of dynabases
;; dynabases are a prototype styled inheritiance system for dyna


;; list of dynabases names which do not inherit from anything.  When these names
;; appear, it can allow for some additional rewrites to take place as we know
;; there will be only at most 1 instance of the dynabase in the inheritance for
;; a given class.
;(def dynabase-metainfo (atom {}))


;; for when a dynabase does not have any parent objects, this is going to be the root dynabase
;; this will likely be associated with top level files which import everything
(def-base-rexpr dynabase-constructor [:str name
                                      :var-list arguments
                                      :var parent-dynabase  ;; either constant nil, or a variable which references what dynabase this is constructed from
                                      :var dynabase])

; this should be used for accessing a field or function on a dynabase.  It will
; read any variables which were captured in the closure of the dynabase and
; check the type matches for the function that we are evaluating
(def-base-rexpr dynabase-access [:str name
                                 :var dynabase
                                 :var-list arguments])


(def-rewrite
  :match (dynabase-constructor (:str name) (:ground-var-list arguments) (:ground parent-dynabase) (:any dynabase))
  (let [parent-val (get-value parent-dynabase)
        args (vec (map get-value arguments))
        metadata (get @system/dynabase-metadata name)
        ret (cond (dnil? parent-val) (let [db (Dynabase. {name (list args)})]
                                       (make-unify dynabase (make-constant db)))
                  (instance? Dynabase parent-val) (let [parent-obj (.access-map ^Dynabase parent-val)
                                                        dbm (assoc parent-obj name (conj (get parent-obj name ()) args))
                                                        db (Dynabase. dbm)]
                                                    ;; this needs to track which kinds of dynabases this is going to inherit from
                                                    (make-unify dynabase (make-constant db)))
                  :else (do ;; this means the user did something like `new (5) {foo = 123. }` which is ill-formed
                          (dyna-debug
                           (debug-repl "unexpected dynabase parent type")
                           (assert false))
                          (make-multiplicity 0)))]
    ret))

(def-rewrite
  :match (dynabase-access (:str name) (:ground dynabase) (:variable-list args))
  (let [pv (get-value dynabase)]
    (if (not (instance? Dynabase pv))
      (make-multiplicity 0)
      (let [m (.access-map ^Dynabase pv)
            arr (get m name)]
        (if (nil? arr)
          (make-multiplicity 0)
          (if (= 1 (count arr))
            ;; then we can just make a unification of all of the values directly
            ;; this will likely set the values into the context info
            (make-conjunct (doall (map (fn [var val]
                                         (make-unify var (make-constant val)))
                                       args (first arr))))
            ;; this needs to have some disjunct over all of the different values that this can take on.  In this case, this would
            (make-disjunct
             (vec (map (fn [ae]
                         (make-conjunct (vec (map
                                              (fn [var val] (make-no-simp-unify var (make-constant val)))
                                              args ae))))
                       arr)))))))))

(comment
  (def-rewrite
    :match {:rexpr (dynabase-access (:str name) (:any dynabase) (:variable-list args))
            :context (dynabase-constructor (:str name) (:variable-list arguments) (:ground parent-dynabase) dynabase)}
    :run-at :inference
    (do
      (debug-repl "dynabase constructor inference")
      ;; if the constructor is from some dynabase which has different values
      (???)
      )
    ))

(comment
  (def-rewrite
    :match {:rexpr (dynabase-access (:str name) (:any dynabase) (:variable-list args))
            :context (dynabase-access (:str name) dynabase (:variable-list args2))}
    :run-at :inference
    (do
      (debug-repl "dynabase two access combine")
      ;; this should check if the types are compiable, and then also replace the
      ;; expression with the variables which are present at the higher scope.
      (???))))

(comment
  (def-iterator
    :match (dynabase-access (:str name) (:ground dynabase) (:variable-list args))
    ;; this should be able to iterate over the domains of the variables.  I suppose that in this case it must be when there are more than one values
    ;; otherwise this would have already been rewritten

    ;; if there was some "efficient" disjunction structure, then it could just
    ;; perform some mapping to that structure.  This would not have to track the
    ;; representation through many different values
    ))



;; this should
;; (def-base-rexpr load-file [:var filename
;;                            :var calling-from-dynabase
;;                            :var resulting-dynabase])

;; (def-user-term "$load" 1 (make-load-file v0 self v1))



(defn make-new-dynabase-identifier [has-super
                                    referenced-variables]
  ;; if we are going to somehow seralize and then relaod new items, then we are going to make these unique
  ;; we might consider using UUID as the identifier for a dynabase name.  Then we could just assume that those would be unique between different seralization
  (let [name (str (gensym 'dynabase_))]
    (swap! system/dynabase-metadata assoc name
           {:has-super has-super ;; true or false to indicate if this is a
                                   ;; "root" dynabase, as that indicates that we
                                   ;; are not going to see more than one
                                   ;; instance of it, which unlocks some
                                   ;; rewrites to avoid having to process the
                                   ;; dynabase more than once
            :referenced-variables (vec referenced-variables)
            :does-not-self-inerhit-assumption (make-assumption)  ;; there should be some assumption about the
                                           ;; dynabase not inheriting from itself.  This willx
                             ;; enable us to have more "efficient" code where an
                             ;; expression can again make the same assumptions
                             ;; as the there not being any parents
            })
    name))



;; if some variable is an instance of a dynabase.  This would be that the
;; dynabases are equal to each other, or the instance is a superset of the first
;; map
;(def-user-term "instance" 2 (make-multiplicity 1))
