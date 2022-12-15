(ns dyna.memoization-v2
  (:require [dyna.utils :refer :all])
  (:require [dyna.rexpr :refer :all])
  (:require [dyna.rexpr-constructors :refer [is-meta-is-free? is-meta-is-ground?]])
  (:require [dyna.system :as system])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.user-defined-terms :refer [update-user-term! user-rexpr-combined-no-memo get-user-term]])
  (:require [dyna.assumptions :refer :all])
  (:require [dyna.context :as context])
  (:require [dyna.user-defined-terms :refer [add-to-user-term user-rexpr-combined-no-memo]])
  (:require [clojure.set :refer [union]])
  (:import [dyna DynaUserError IDynaAgendaWork]))

(defsimpleinterface IMemoContainer
  (refresh-memo-table [])
  (compute-value-for-key [key])
  (get-value-for-key [key])
  )

(deftype AgendaReprocessWork [^IMemoContainer memo-container term ^double priority]
  IDynaAgendaWork
  (run [this]
    (refresh-value-for-key memo-container term))
  (priority [this]
    priority)
  Object
  (hashCode [this]
    (bit-xor (hash memo-container) (hash term)))
  (equals [this other]
    (if-not (instance? AgendaReprocessWork other)
      false
      (and (identical? memo-container (.memo-container ^AgendaReprocessWork other))
           (= term (.term ^AgendaReprocessWork other))))))

;; this memo container only will be a value that is a single R-expr.  This is
;; the "naive" implementation which will "support everything" because it makes
;; no assumptions about the internal representation of what is getting memoized
(deftype MemoContainerRexpr []
  )

;; this is the efficient implementation of a memo table which uses an
;; associative map from keys to rexpr-values.  The map will be of a subset of
;; the keys which are contained.  If something comes in with an invalidation message, then
(deftype MemoContainerTrie [])

(deftype MemoContainer [memo-config
                        Rmemo ;; atom which contains the
                        ]
  Watcher
  (notify-invalidated! [this watching])
  (notify-message! [this watching message])

  IMemoContainer
  (refresh-memo-table [this]
    (compute-value-for-key this nil))
  (compute-value-for-key [this key]
    (???))
  (get-value-for-key [this key]
    (???)))

(def-base-rexpr memoization-placeholder [:unchecked name ;; this should match
                                                         ;; the term name which
                                                         ;; we are going to look
                                                         ;; up the memoization
                                                         ;; container and
                                                         ;; configuration on
                                         :var-map args-map])

(def ^{:private true :dynamic true} *expand-memoization-placeholder* true)
(def-rewrite
  :match {:rexpr (memoization-placeholder (:unchecked name) (:unchecked args-map))
          :check *expand-memoization-placeholder*}
  (let [term (get-user-term name)]
    ))

(def-base-rexpr memoized-rexpr-v2 [:unchecked memoization-container
                                   :var-map variable-name-mapping])

(def-rewrite
  :match (memoized-rexpr-v2 (:unchecked memoization-container) (:unchecked variable-name-mapping))
  (let [memo-config (.memo-config memoization-container)]

    ))

(defn- rebuild-memo-table-for-term [term-name]
  (let [[old new] (update-user-term! term-name
                                     (fn [dat]
                                       (let [[orig-rexpr-assumpt orig-rexpr] (compute-with-assumption
                                                                              (user-rexpr-combined-no-memo dat))
                                             required-vars ()
                                             ]
                                         (debug-repl "rebuild 1")
                                         (???))))])
  (debug-repl "rebuild memo")

  )

(defn- identify-term-name [rexpr]
  (only (for [[projected-vars rr] (all-conjunctive-rexprs rexpr)
               :when (and (is-unify-structure? rr) (= (:out rr) (make-variable "$0")))]
           rr)))

(defn handle-dollar-memo-rexpr [rexpr source-file dynabase]
  (when-not (dnil? dynabase)
    (throw (DynaUserError. "$memo does not support dynabases (yet)")))
  (let [term-structure (identify-term-name rexpr)]
    (when (nil? term-structure)
      (throw (DynaUserError. "$memo does not support wildcard matchin, it should have a term name matched for its first argument.  E.g. `$memo(foo[X]) = \"null\".`")))
    (when-not (dnil? (get-value (:dynabase term-structure)))
      (throw (DynaUserError. "$memo does not support dynabases (yet)")))
    (let [term-name (:name term-structure)
          args (:arguments term-structure)
          ;; the name of the term that we are going to enable memoization on
          call-name {:name term-name
                     :arity (count args)
                     :source-file source-file}
          [memo-mode memo-mode-rexpr] (when (is-aggregator? rexpr)
                                        (let [incoming (:incoming rexpr)]
                                          (if (is-constant? incoming)
                                            [(keyword (get-value incoming)) nil]
                                            (or (only (for [[projected-vars rr] (all-conjunctive-rexprs rexpr)
                                                            :when (and (is-unify? rr) (= (:a rr) incoming))]
                                                        [(keyword (get-value (:b rr))) rr]))
                                                [nil nil]))))
          argument-signatures (into [] (for [arg args] ;; identify constraints on the arguments variables. such as $free or $ground
                                         (filter #(let [r (get % 1)]
                                                    (and (not (is-conjunct? r))
                                                         (not (is-proj? r))
                                                         (not (= term-structure r))
                                                         ;(not (and (is-unify-structure? r) (= (:out r) (make-variable "$0"))))
                                                         (contains? (exposed-variables r) arg)))
                                                 (all-conjunctive-rexprs rexpr))))
          argument-modes (into [] (for [s argument-signatures]
                                    (case (count s) ;; if there is more than 1 constraint, then this might be something else?
                                      0 :ground  ;; if there are no constraints on the variables, then we are going to default to ground?  This will mean that it must be present for
                                      1 (let [r (cadar s)]
                                          (cond (and (is-meta-is-ground? r) (= true (get-value (:result r)))) :ground
                                                (and (is-meta-is-free? r) (= true (get-value (:result r)))) :free))
                                      nil)))
          all-used-conjuncts (union #{rexpr memo-mode-rexpr term-structure}
                                    (apply union (for [s argument-signatures]
                                                   (into #{} (map second s)))))
          ;; if there is a non-trival constraint, then this means there needs to be some code run at the memoization time to determine what it should do
          has-non-trivial-constraint (or (not (every? (fn [s] (every? #(or (is-meta-is-free? %)
                                                                           (is-meta-is-ground? %))
                                                                      (map second s)))
                                                      argument-signatures))
                                         (not (every? #(let [r (second %)]
                                                         (or (is-proj? r)
                                                             (is-conjunct? r)
                                                             (contains? all-used-conjuncts r)))
                                                      (all-conjunctive-rexprs rexpr))))
          ]
      (when-not (#{:null :unk :none} memo-mode)
        ;; the memoization mode values should be a constant value.
        ;; if the memoized value comes from
        (throw (DynaUserError. "$memo mode unrecogninzed, should be a string of: \"null\", \"unk\" or \"none\".")))

      (when (= "$memo" term-name)
        (throw (DynaUserError. "Can not set $memo on $memo.")))

      ;; TODO: this can only "add" to the memoization, modes.  Not sure if there
      ;; should be some way to remove a memoization mode.  It would have to
      ;; reconstruct the not-memoized value.  maybe there could be another
      ;; method which is for "clearning" out the memoization settings on a given
      ;; function, though it would likely be some meta / compiler_expression
      ;; rule rather than checking if the expression is an override.  The
      ;; override will still potentially have that there is something which
      ;; needs to get checked
      (let [[old new] (update-user-term! call-name
                                         (fn [dat]
                                           (let [dat1 (if-not (:memoization-tracker-method-name dat)
                                                        (assoc dat :memoization-tracker-method-name (str (gensym '$memo_controller_)))
                                                        dat)
                                                 modes (conj (:memoization-modes dat1 #{}) memo-mode)
                                                 dat2 (assoc dat1
                                                             :memoization-modes modes
                                                             :memoization-argument-modes (conj (:memoization-argument-modes dat1 #{}) argument-modes)
                                                             :memoization-decl-settings (inc (:memoization-decl-settings dat1 0)))
                                                 mode (if (and (= (count modes) 1) (<= (:memoization-decl-settings dat2) 1))
                                                        (first (:memoization-modes dat2))
                                                        :complex)
                                                 dat3 (assoc dat2
                                                             :memoization-mode mode
                                                             :is-memoized-unk (if (and (:unk modes) (not (is-valid? (:is-memoized-unk dat2))))
                                                                                (make-assumption)
                                                                                (:is-memoized-unk dat2))
                                                             :is-memoized-null (if (and (:null modes) (not (is-valid? (:is-memoized-null dat2))))
                                                                                (make-assumption)
                                                                                (:is-memoized-null dat2))
                                                             :memoized-rexpr (if (or (:null modes) (:unk modes))
                                                                               (make-multiplicity 0)
                                                                               ;; if this is only :none, then there is no memoized R-expr
                                                                               nil))]
                                             dat3)))]
        ;(debug-repl "$memo")

        ;; save the method definition for the $memo value
        (add-to-user-term source-file dynabase (:memoization-tracker-method-name new) 1 rexpr)

        ;; invalid assumptions that have been replaced
        (doseq [k (keys new)]
          (let [ov (get old k)
                nv (get new k)]
            (when (and (not (identical? ov nv))
                       (satisfies? Assumption ov))
              (when (nil? ov) (debug-repl))
              (invalidate! ov))))

        ;; this is going to have to invalidate some assumptions based off what modes are contained
        (when (:null (:memoization-modes new))
          (invalidate! (:is-not-memoized-null new)))

        ;; push that we are going to construct the memo tables for this
        (system/push-agenda-work #(rebuild-memo-table-for-term call-name))))))

(defn handle-dollar-priority-rexpr [rexpr source-file dynabase]
  (when-not (dnil? dynabase)
    (throw (DynaUserError. "$priority does not support dynabases (yet)")))
  (let [term-structure (identify-term-name rexpr)]
    (when-not (dnil? (get-value (:dynabase term-structure)))
      (throw (DynaUserError. "$priority does not support dynabases (yet)")))
    (let [call-name {:name (:name term-structure)
                     :arity (count (:arguments term-structure))
                     :source-file source-file}
          [old new] (update-user-term! call-name (fn [dat]
                                                   (if-not (:memoization-priorty-method dat)
                                                     (assoc dat :memoization-priorty-method (str (gensym '$priority_controller_)))
                                                     dat)))]
      (add-to-user-term source-file dynabase (:memoization-priorty-method new) 1 rexpr))))
