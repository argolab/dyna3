(ns dyna.rexpr-dynabase
  (:require [dyna.utils :refer :all])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.rexpr :refer :all])
  (:require [dyna.user-defined-terms :refer [def-user-term]]))

;; R-exprs which represent construction of dynabases
;; dynabases are a prototype styled inheritiance system for dyna

(defrecord Dynabase [access-map])

;; list of dynabases names which do not inherit from anything.  When these names
;; appear, it can allow for some additional rewrites to take place as we know
;; there will be only at most 1 instance of the dynabase in the inheritance for
;; a given class.
(def dynabase-metainfo (atom {}))


;; for when a dynabase does not have any parent objects, this is going to be the root dynabase
;; this will likely be associated with top level files which import everything
(def-base-rexpr dynabase-constructor [:opaque-constant name
                                      :var-list arguments
                                      :var dynabase])

;; this will create a new named dynabase which inherits from another dynabase
;; the dynabase that we are inheriting from will not be known at compile time necessarily
;; as such there could be some expression like `f(X) = new (X) { stuff(Z) = 123*Z. }.`
;; I suppose that something like `{}` or `new { . }` could use the constructor version above rather than having this construct some inheritance
(def-base-rexpr dynabase-inherit [:opaque-constant name
                                  :var parent-dynabase
                                  :var-list arguments
                                  :var dynabase])

; this should be used for accessing a field or function on a dynabase.  This is a check where we are going to perform
(def-base-rexpr dynabase-access [:opaque-constant name
                                 :var dynabase
                                 :var-list arguments])


;; (def-rewrite
;;   :match (dynabase-constructor (:str name) (:any arguments) (:any dynabase))
;;   :run-at :construction
;;   (do
;;     (swap! dyna-base-roots-names conj name) ;; add the name that this is constructed from something that is a root element?
;;     nil ; don't change the value
;;     ))

(def-rewrite
  :match (dynabase-constructor (:str name) (:ground-var-list arguments) (:any dynabase))
  (let [db (Dynabase. {name [(doall (map get-value arguments))]})]
    (make-unify dynabase (make-constant db))))

(def-rewrite
  :match (dynabase-inherit (:str name) (:ground parent-dynabase) (:ground-var-list arguments) (:any dynabase))
  (let [pv (get-value parent-dynabase)]
    (if (not (instance? Dynabase pv))
      (make-multiplicity 0)
      (let [m (.access-map ^Dynabase pv)
            args (doall (map get-value arguments))
            arr (conj (get m name []) args)
            nm (assoc m name arr)]
        (make-unify dynabase (make-constant (Dynabase. nm)))))))

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
                                       args (get arr 0))))
            ;; this needs to have some disjunct over all of the different values that this can take on.  In this case, this would
            (make-disjunct
             (doall (map (fn [ae]
                           (make-conjunct (doall (map (fn [var val] (make-no-simp-unify var (make-constant val))))))
                           ) arr)))
            ;; (do
            ;;   ;; (make-disjunct
            ;;   ;;  (doall (map (fn )))
            ;;   ;;  )
            ;;   (assert false) ;; this is going to have to make some disjunct for the different expressions
            ;;   ;; this is going to be a disjunct over the different cojuncts, so we might want to have a more efficient representation for this
            ;;   ;; in the case that
            ;;   )
            )
          )))))

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
(def-base-rexpr load-file [:var filename
                           :var calling-from-dynabase
                           :var resulting-dynabase])

(def-user-term "$load" 1 (make-load-file v0 self v1))



(defn make-new-dynabase-identifier [has-parent
                                    referenced-variables]
  ;; if we are going to somehow seralize and then relaod new items, then we are going to make these unique
  ;; we might consider using UUID as the identifier for a dynabase name.  Then we could just assume that those would be unique between different seralization
  (let [name (gensym)]
    (swap! dynabase-metainfo assoc name
           {:has-parent has-parent ;; true or false to indicate if this is a
                                   ;; "root" dynabase, as that indicates that we
                                   ;; are not going to see more than one
                                   ;; instance of it, which unlocks some
                                   ;; rewrites to avoid having to process the
                                   ;; dynabase more than once
            :referenced-variables (vec referenced-variables)
            :assumption nil  ;; there should be some assumption about the
                             ;; dynabase not inheriting from itself.  This will
                             ;; enable us to have more "efficient" code where an
                             ;; expression can again make the same assumptions
                             ;; as the there not being any parents
            })))



;; if some variable is an instance of a dynabase.  This would be that the
;; dynabases are equal to each other, or the instance is a superset of the first
;; map
(def-user-term "instance" 2 (make-multiplicity 1))
