(ns dyna.rexpr-dynabase
  (:require [dyna.utils :refer :all])
  (:require [dyna.base-protocols :refer :all])
  ;(:import  [dyna.base_protocols Dynabase])
  (:require [dyna.rexpr :refer :all])
  (:require [dyna.user-defined-terms :refer [def-user-term]])
  (:require [dyna.assumptions :refer [make-assumption is-valid? depend-on-assumption invalidate!]])
  (:require [dyna.system :as system])
  (:require [dyna.rexpr-builtins :refer [def-builtin-rexpr]])
  (:require [clojure.set :refer [subset?]])
  (:import [dyna DynaTerm Dynabase]))

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
                                      :var dynabase]
  (is-constraint? [this] (let [metadata (get @(tlocal system/dynabase-metadata) name)
                               assump (:does-not-self-inerhit-assumption metadata)]
                           (if (is-valid? assump)
                             (do
                               (depend-on-assumption assump)
                               true)
                             false))))

                                        ; this should be used for accessing a field or function on a dynabase.  It will
                                        ; read any variables which were captured in the closure of the dynabase and
                                        ; check the type matches for the function that we are evaluating

(def-base-rexpr dynabase-access [:str name
                                 :var dynabase
                                 :var-list arguments]
  (is-constraint? [this] (let [metadata (get @(tlocal system/dynabase-metadata) name)
                               assump (:does-not-self-inerhit-assumption metadata)]
                           (if (is-valid? assump)
                             (do
                               (depend-on-assumption assump)
                               true)
                             false))))


(def-rewrite
  :match (dynabase-constructor (:str name) (:ground-var-list arguments) (:ground parent-dynabase) (:any dynabase))
  (let [parent-val (get-value parent-dynabase)
        args (vec (map get-value arguments))
        metadata (get @(tlocal system/dynabase-metadata) name)
        ret (cond (dnil? parent-val) (let [db (Dynabase. {name (list args)})]
                                       (make-unify dynabase (make-constant db)))
                  (instance? Dynabase parent-val) (let [parent-obj (.access_map ^Dynabase parent-val)
                                                        dbm (assoc parent-obj name (conj (get parent-obj name ()) args))
                                                        db (Dynabase. dbm)]
                                                    (when (contains? parent-obj name) ;; meaning that the same class appears more than once
                                                      (invalidate! (:does-not-self-inerhit-assumption metadata)))
                                                    ;; this needs to track which kinds of dynabases this is going to inherit from
                                                    (make-unify dynabase (make-constant db)))
                  :else (do ;; this means the user did something like `new (5) {foo = 123. }` which is ill-formed
                          (dyna-debug
                           (debug-repl "unexpected dynabase parent type")
                           (assert false))
                          (make-multiplicity 0)))]
    ret))

(def-rewrite
  :match (dynabase-constructor (:str name) (:variable-list args) (:any parent-dynabase) (:ground dynabase))
  ;; then this is something that we can attempt to figure out what the arguments
  ;; to the dynabase were the order in which something inherited from another
  ;; dynabase should be tracked somehow?  This could end up in some case where
  ;; it pulls arguments out which don't make much since?
  (let [^Dynabase dbase (get-value dynabase)]
    (if-not (and (instance? Dynabase dbase)
                 (contains? (.access_map dbase) name))
      (make-multiplicity 0)
      (let [selfs (get (.access_map dbase) name)
            self-val (first selfs)
            new-map (if (> 1 (count selfs))
                      (assoc (.access_map dbase) name
                             (cdr selfs))
                      (dissoc (.access_map dbase) name))]
        (make-conjunct [(make-unify parent-dynabase (make-constant (if (empty? new-map)
                                                                     DynaTerm/null_term
                                                                     (Dynabase. new-map))))
                        (make-conjunct (vec (map (fn [a b] (make-unify a (make-constant b)))
                                                 args self-val)))])))))

(def-rewrite
  :match (dynabase-access (:str name) (:ground dynabase) (:variable-list args))
  (let [pv (get-value dynabase)]
    (if (not (instance? Dynabase pv))
      (make-multiplicity 0)
      (let [m (.access_map ^Dynabase pv)
            arr (get m name)]
        (if (nil? arr)
          (make-multiplicity 0)
          (if (= 1 (count arr))
            ;; then we can just make a unification of all of the values directly
            ;; this will likely set the values into the context info
            (make-conjunct (vec (map (fn [var val]
                                         (make-unify var (make-constant val)))
                                       args (first arr))))
            ;; this needs to have some disjunct over all of the different values that this can take on.  In this case, this would
            (let [ret (make-disjunct
                       (vec (map (fn [ae]
                                   (make-conjunct (vec (map
                                                        (fn [var val] (make-no-simp-unify var (make-constant val)))
                                                        args ae))))
                                 arr)))]
              ;(debug-repl "db")
              ret)))))))


;; TODO: this depends on the assumption that there are no children dynabases.  As a given rule has to match in multiple places
#_(def-rewrite
  :match {:rexpr (dynabase-access (:str name) (:free dynabase) (:variable-list args))
          :check (empty? args)}
  :run-at :construction
  ;; if there are no args in the dynabase, then the dynabase does not require
  ;; this delayed expression to match against.
  (let [metadata (get @system/dynabase-metadata name)]
    (when-not (:has-super metadata)
      (debug-repl)
      (make-unify dynabase (make-constant (Dynabase. {name (list ())}))))))

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
    (swap! (tlocal system/dynabase-metadata) assoc name
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


            ;; this should track which dynabases are seen as parent and children
            ;; dynabases during the construction phase.  This should allow for
            ;; additional optimizations when it is doing inference with having
            ;; multiple dynabases access operations.  Also there will need to be
            ;; assumptions that these values haven't changed
            ;:seen-super-dynabases #{}
            ;:seen-child-dynabases #{}
            })
    name))

(def-builtin-rexpr is-dynabase 2
  (:allground (= v1 (instance? Dynabase v0)))
  (v1 (instance? Dynabase v0)))

(def-user-term "dynabase" 1 (make-is-dynabase v0 v1))

(defn is-dynabase-subset [^Dynabase A ^Dynabase B]
  ;; check that A is a subset of B
  (let [am (.access_map A)
        bm (.access_map B)]
    (and (subset? (keys am) (keys bm))
         (every? (fn [[k v]]
                   (subset? v (get bm k)))
                 am))))

(def-builtin-rexpr is-dynabase-instance 3
  (:allground (= v2 (and (instance? Dynabase v0)
                         (instance? Dynabase v1)
                         (is-dynabase-subset v0 v1))))
  (v2 (and (instance? Dynabase v0)
           (instance? Dynabase v1)
           (is-dynabase-subset v0 v1))))

(def-user-term "instance" 2 (make-is-dynabase-instance v0 v1 v2))

;; if some variable is an instance of a dynabase.  This would be that the
;; dynabases are equal to each other, or the instance is a superset of the first
;; map
;(def-user-term "instance" 2 (make-multiplicity 1))




;; NOTE: might have something like the set of keys which are known about on a
;; given dynabase.  then it could pass those through explicitly.  this would
;; allow for memoization of the parent dynabases while still having overrides
;; for the expressions that would get blocked.  this would require that there is
;; something like the "top level" dynabase which could get used.  though this
;; would have to ensure that there is no self inherit, otherwise that would be
;; come too complex for it to figure out which expression might have been the
;; previous parent expression
;;
;; though I suppose that becauise we are going allow memos to go anywhere, it
;; could happen after the dynabsae has already been dispatched, in which case
;; the child dynabase could also allow for it to use the same memo without
;; having to get combined together.
;;
;; I suppose we could also split aggregators up more such that different
;; dynabases are groupped together.  then the dynabase access operator could
;; appear before the aggregation.  This would require some more complex rewrites
;; which are going to know about dynabases inside of aggregators such that it
;; can figure out the best way to arrange the R-expr.



;; There should be a lot more optimizations that can be done with dynabases once
;; we have assumptions working fully.  The diea being that if something would
;; inhert from a given dynabase, then it would know which expression would
;; result in it creating something.  I suppose that we could also track all of
;; the subclasses which inherit from a given dynabase


(defmethod print-method Dynabase [^Dynabase this ^java.io.Writer w]
  (.write w (.toString this)))
