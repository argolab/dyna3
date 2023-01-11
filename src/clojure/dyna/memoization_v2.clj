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
  (:require [dyna.rexpr-builtins :refer [meta-free-dummy-free-value]])
  (:require [clojure.set :refer [union]])
  (:import [dyna DynaUserError IDynaAgendaWork DynaTerm]))

(defsimpleinterface IMemoContainer
  (refresh-memo-table [])
  (compute-value-for-key [key])
  (get-value-for-key [key])
  (refresh-value-for-key [term])

  ;; calls which are made by the R-expr when it is trying to access the expression
  (memo-rewrite-access [variables variable-values])
  (memo-get-iterator [variables variable-values])
  (memo-get-assumption []))

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
;; (deftype MemoContainerRexpr []
;;   )

;; this is the efficient implementation of a memo table which uses an
;; associative map from keys to rexpr-values.  The map will be of a subset of
;; the keys which are contained.  If something comes in with an invalidation message, then
;; (deftype MemoContainerTrie [])

#_(deftype MemoContainer [memo-config
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
    (???))
  (memo-get-assumption [this]
    (???)))

(deftype MemoContainerGenericRexpr []
  ;; this is a generic version of the memo table.  It uses R-exprs to control
  ;; when it will access some value, as well as for the internal representation.
  ;; The internal representations are treated as "opaque" which means that they
  ;; can be "more general", though because performing checks against the
  ;; internal representation can require comparing equality between R-exprs
  ;; (something which essentially doesn't really work in general), this is going to be a lot slower and .
  Watcher
  (notify-invalidated! [this watching] (???))
  (notify-message! [this watching message] (???))

  IMemoContainer
  (refresh-memo-table [this])
  (compute-value-for-key [this key])
  (get-value-for-key [this key])
  (refresh-value-for-key [this key])
  (memo-get-assumption [this]
    (???)))

(defn- is-key-contained [])

(deftype MemoContainerTrieStorage [memo-modes ;; either a keyword (:unk or :null) or a set of keywords
                                   memo-controller ;; a function which will identify when the memo is supported
                                   memo-controller-term-name  ;; the DynaTerm name that is used when calling memo controller
                                   number-of-variables  ;; the number of variables which are used for any key
                                   assumption
                                   data ;; (atom [map-of-what-keys-are-contained (PrefixTrie.)])
                                   ;; the map will bve
                                   ]
  Watcher
  (notify-invalidated! [this watching] (???))
  (notify-message! [this watching message] (???))

  IMemoContainer
  (refresh-memo-table [this])
  (compute-value-for-key [this key])
  (get-value-for-key [this key])
  (refresh-value-for-key [this key])

  ;; calls which are made by the R-expr when it is trying to access the expression
  (memo-rewrite-access [this variables variable-values]
    (???))
  (memo-get-iterator [this variables variable-values]
    (???))
  (memo-get-assumption [this]
    assumption))

;; the placeholder will lookup the memoization container associated with a given
;; name.  This is an extra step of indirection which we can "defer."  This will
;; have that the placeholder will be able to get rewritten as needed
(def-base-rexpr memoization-placeholder [:unchecked name
                                         :var-list args-map])
;; if this should expand the memoization-placeholder or just leave it as is.
(def ^{:private true :dynamic true} *expand-memoization-placeholder* true)

(def-base-rexpr memoized-access [:unchecked memoization-container
                                 :var-list variable-mapping])
(def ^{:private true :dynamic true} *lookup-memoized-values* true)


(def-rewrite
  :match {:rexpr (memoization-placeholder (:unchecked name) (:unchecked args-map))
          :check *expand-memoization-placeholder*}
  (let [term (get-user-term name)]
    ;;(make-memoized-rexpr-v2 nil args-map)
    (debug-repl "memoization placeholder r-expr rewrite")
    (make-memoized-access nil args-map)))

#_(def-rewrite
  :match {:rexpr (memoized-rexpr-v2 (:unchecked memoization-container) (:unchecked variable-name-mapping))
          :check *lookup-memoized-values*}
  (let [memo-config (.memo-config memoization-container)]
    (debug-repl "memoized rexpr v2 rewrite")
    (???)))

(def-rewrite
  :match {:rexpr (memoized-access (:unchecked ^IMemoContainer container) (:unchecked variable-map))
          :check *lookup-memoized-values*}
  ;; inside of the JIT, the last argument could be something which will be generated using the local variables
  ;; this will prevent us from having to indirect through the *context* to access the values of variables
  (memo-rewrite-access container variable-map (map get-value variable-map)))

(def-iterator
  :match {:rexpr (memoized-access (:unchecked ^IMemoContainer container) (:unchecked variable-map))
          :check *lookup-memoized-values*}
  (memo-get-iterator container variable-map (map get-value variable-map)))


(defn- get-all-children [rexpr]
  (let [c (ensure-set (get-children rexpr))]
    (union c
           (apply union (map get-all-children c)))))

(defn- make-memoization-controller-function-rexpr-backed [info]
  (let [memo-controller-rexpr (make-user-call {:name (:memoization-tracker-method-name info)
                                               :arity 1
                                               :source-file (:source-file (:term-name info))}
                                              {(make-variable "$0") (make-variable 'Input)
                                               (make-variable "$1") (make-variable 'Result)}
                                              0 {})]
    (fn [^DynaTerm signature]
      (let [ctx (context/make-empty-context memo-controller-rexpr)
            res (context/bind-context-raw ctx
                                          (set-value! (make-variable 'Input) signature)
                                          (simplify-top memo-controller-rexpr))]
        (when (= (make-multiplicity 1) res)
          (keyword (ctx-get-value ctx (make-variable 'Result))))))))

(defn- make-memoization-controller-function [info]
  ;; this will return a function which represents $memo.  If the representation of the function is "sufficently simple"
  (cond (and (= 1 (count (:memoization-modes info)))
             (= 1 (count (:memoization-argument-modes info)))
             (not (:memoization-has-non-trivial-constraint info)))
        (let [f `(do
                   (ns dyna.memoization-v2)
                   (fn [^DynaTerm signature#]
                       (let [~'args (.arguments signature#)]
                         (when (and ~@(for [[i mode] (zipseq (range) (first (:memoization-argument-modes info)))
                                            :when (= :ground mode)]
                                        ;; for the free variables, we are not going to care about those
                                        `(not= (get ~'args ~i) meta-free-dummy-free-value)
                                        ))
                           ~(first (:memoization-modes info))))))
              r (eval f)
              ]
          r)
        ;; TODO: this should handle slightly more complex functions in the case
        ;; that all of the constraints are trivial, though if there is
        ;; overrides, the order might be different atm?  I supose that the
        ;; representation will have to use something other than sets to control
        ;; what the order is for overriding expressions

        :else
        (make-memoization-controller-function-rexpr-backed info)))

(defn- rebuild-memos-for-term [term-name]
  ;;
  )

(defn- refresh-memo-table [^IMemoContainer memo-container]
  ;; refreshing the memo table will be that it should
  (debug-repl "refresh memo table")
  (when (is-valid? (memo-get-assumption memo-container))
    ;; this is going to have to identify which keys in the table are defined as null, and then

    ))

(defn- rebuild-memo-table-for-term [term-name]
  ;; this will create a new memo container for the term.  The container will
  ;; just be the thing which holds the memos and the references to the R-expr
  ;; which represents the computation for the term.  In the case that the R-expr changes, then we should probably just
  (let [dep-memos (volatile! nil)
        [old new] (update-user-term! term-name
                                     (fn [dat]
                                       (let [[orig-rexpr-assumpt orig-rexpr] (binding [*expand-memoization-placeholder* false
                                                                                       *lookup-memoized-values* false]
                                                                               (compute-with-assumption
                                                                                (simplify-top (user-rexpr-combined-no-memo dat))))
                                             required-vars ()
                                             rexpr-children (get-all-children orig-rexpr)
                                             dependant-memos (vec (filter #(or (is-memoization-placeholder? %) (is-memoized-access? %)) rexpr-children))  ;; this should also identify memoization access expressions
                                             controller-function (make-memoization-controller-function dat)
                                             memo-container (MemoContainerTrieStorage.
                                                             (if (= 1 (count (:memoization-modes dat)))
                                                               (first (:memoization-modes dat))
                                                               (:memoization-modes dat))
                                                             controller-function
                                                             (:name (:term-name dat)) ;; the name used for creating the term
                                                             ;; the last argument which is the result is not included, so there needs to be some
                                                             ;; map from the variables which are used and which variables are included in the mapping
                                                             (+ 1 (:arity (:term-name dat) 0)) ;;
                                                             (make-assumption)
                                                             (atom [{} {}])
                                                             )
                                             ret (assoc dat
                                                        :memoization-container memo-container
                                                        :memoization-subscribed-upstream (into #{} (map :name (filter is-memoization-placeholder? dependant-memos)))  ;; things that we are following
                                                        )
                                             ]
                                         (vreset! dep-memos dependant-memos)
                                         (debug-repl "rebuild 1")

                                         ret)))]
    (when (:memoization-container old)
      ;; any old container is going to have to get deleted.
      (invalidate! (memo-get-assumption (:memoization-container old))))
    (let [container (:memoization-container new)
          old-subscribed (:memoization-subscribed-upstream old)
          new-subscribed (:memoization-subscribed-upstream new)]
      (doseq [n new-subscribed]
        (update-user-term! n (fn [dat]
                               (let [c (:memoization-container dat)]
                                 (when (and c (is-valid? (memo-get-assumption c)))
                                   (add-watcher! (memo-get-assumption c) container)))
                               (update dat :memoization-subscribed-downstream conj term-name))))
      (doseq [n old-subscribed
              :when (not (contains? new-subscribed n))]
        (update-user-term! (fn [dat]
                             ;; this should remove the assumption from the term container.  This will mean that
                             (update dat :memoization-subscribed-downstream disj term-name))))
      (doseq [n new-subscribed]
        (let [sub (get @system/user-defined-terms n)
              dc (:memoization-container sub)]
          (when (and dc (is-valid? (memo-get-assumption dc)))
            (add-watcher! (memo-get-assumption container) dc))))
      (doseq [v @dep-memos]
        (when (is-memoized-access? v)
          ;; this is a table directly without a term name, which means that we need to just notify it directly
          (???)
          ))

      #_(doseq [v @dep-memos]
        (debug-repl "need to subscribe to the table")
        (if (is-memoization-placeholder? v)
          (update-user-term! (:name v) (fn [dat]

                                         ))
          (let [table (:memoization-container v)]
            (???))
          )
        ;; if the table already exists, then this can just subscribe to the table, otherwise this will have that it might need
        (???))

      )
    ;; if there is something else that is downstream which needs to get subscribed to this item, then we are going to have to handle that as well

    (when (:null (:memoization-modes new))
      (system/push-agenda-work #(refresh-memo-table (:memoization-container new))))

    (debug-repl "rebuild memo"))

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
                                                             :memoization-decl-settings (inc (:memoization-decl-settings dat1 0))
                                                             :memoization-has-non-trivial-constraint (or has-non-trivial-constraint (:memoization-has-non-trivial-constraint dat1 false)))
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
                                                                               (make-memoization-placeholder call-name
                                                                                                             (into [] (for [i (range (+ 1 (count args)))]
                                                                                                                        (make-variable (str "$" i))))
                                                                                                             #_(into {} (for [i (range (+ 1 (count args)))
                                                                                                                            :let [v (make-variable (str "$" i))]]
                                                                                                                        [v v])))
                                                                               ;(make-multiplicity 0)
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
