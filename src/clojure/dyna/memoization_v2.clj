(ns dyna.memoization-v2
  (:require [dyna.utils :refer :all])
  (:require [dyna.rexpr :refer :all])
  (:require [dyna.rexpr-constructors :refer [is-meta-is-free? is-meta-is-ground? make-disjunct-op
                                             is-aggregator-op-outer? is-aggregator-op-inner?
                                             make-aggregator-op-outer make-aggregator-op-inner]])
  (:require [dyna.system :as system])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.user-defined-terms :refer [update-user-term! user-rexpr-combined-no-memo get-user-term]])
  (:require [dyna.assumptions :refer :all])
  (:require [dyna.context :as context])
  (:require [dyna.user-defined-terms :refer [add-to-user-term user-rexpr-combined-no-memo]])
  (:require [dyna.rexpr-builtins :refer [meta-free-dummy-free-value]])
  (:require [dyna.prefix-trie :refer :all])
  (:require [dyna.rexpr-aggregators-optimized :refer [*aggregator-op-contribute-value*]])
  (:require [clojure.set :refer [union difference]])
  (:import [dyna DynaUserError IDynaAgendaWork DynaTerm InvalidAssumption])
  (:import [dyna.assumptions Watcher Assumption])
  (:import [dyna.prefix_trie PrefixTrie])
  (:import [clojure.lang IFn]))


(defn- get-all-children [rexpr]
  (let [c (ensure-set (get-children rexpr))]
    (union c
           (apply union (map get-all-children c)))))
(declare get-tables-from-rexpr)

(defsimpleinterface IMemoContainer
  ;; this interface represent the "public" methods for each of the memo
  ;; containers to access the underlying memo containers
  (memo-get-assumption [])
  (memo-rewrite-access [variables variable-values])
  (memo-get-iterator [variables variable-values])

  ;; setup assumptions about what this depends on
  (memo-setup-new-table [])

  ;;
  (memo-refresh-value-for-key [key]))

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



(deftype AgendaReprocessWork [^IMemoContainer memo-container term ^double priority]
  IDynaAgendaWork
  (run [this]
    (memo-refresh-value-for-key memo-container term))
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
  ;; (refresh-memo-table [this])
  ;; (compute-value-for-key [this key])
  ;; (get-value-for-key [this key])
  ;; (refresh-value-for-key [this key])
  ;; (memo-get-assumption [this]
  ;;   (???))
  )

(defn- is-key-contained? [keys-contained-map check-for]
  (if (and (empty? check-for) (not (nil? keys-contained-map)))
    true
    (if (nil? keys-contained-map)
      false
      (let [k (first check-for)
            r (rest check-for)]
        (or (is-key-contained? (get keys-contained-map k) r)
            (and (not (nil? k)) ;; do not check for nil twice if that is already the value of K
                 (is-key-contained? (get keys-contained-map nil) r)))))))

(deftype MemoContainerTrieStorageAggregatorContributions [^IFn memo-controller ;; these set the policies of what should happen depending on the arguments
                                                          ^IFn memo-priority-function
                                                          aggregator-op
                                                          orig-rexpr
                                                          argument-variables
                                                          ;result-variable
                                                          ^Assumption assumption
                                                          data ;; (atom [valid has-computed (PrefixTrie memoized-values)])
                                                          ]
  Watcher
  (notify-invalidated! [this watching]
    (swap! data (fn [[a b c]] [false b c]))
    (invalidate! assumption))
  (notify-message! [this watching message]
    (debug-repl "notify message")
    ;; TODO: this is going to have to identify which keys need to get recomputed
    ;; and then do the recomputation.  In the case that some of the values will have that it might
    (???)
    )

  IMemoContainer
  (memo-get-assumption [this] assumption)
  (memo-rewrite-access [this variables variable-values]
    (let [control-arg (conj (vec (map #(if (nil? %) meta-free-dummy-free-value %) variable-values)) nil)
          control-setting (memo-controller control-arg)]
      (cond (= control-setting :fallthrough)
            (let [vm (zipmap argument-variables variables)]
              (remap-variables orig-rexpr vm))

            (= control-setting :defer)
            nil ;; returning nil in this case will mean that it does not perform a rewrite, hence it will be defered

            (= (first control-setting) :lookup)
            (let [[valid has-computed memoized-values] @data]
              (when-not valid
                (throw (InvalidAssumption. "memo table no longer valid")))
              (let [lookup-key (drop-last (second control-setting))
                    has-key (is-key-contained? has-computed lookup-key)]
                (when-not has-key
                  (let [prio (memo-priority-function variable-values)  ;; the priority of this compute operation.  though this is different
                        [old-dat new-dat] (swap-vals! data (fn [[a b c]]
                                                        (if-not a
                                                          [a b c]
                                                          [a (assoc-in b lookup-key true) c] ;; record that this value is going to get computed
                                                          )))
                        ]
                    (when (or (identical? (second old-dat) has-computed) (not (is-key-contained? (second old-dat) lookup-key)))
                      (system/push-agenda-work (AgendaReprocessWork. this lookup-key prio)))
                    ;(debug-repl "need to compute for key")
                    ))

                ;; this should return the result for this expression
                (when has-key
                  ;; TODO: this needs to return the right values for this.  In which case, it will need to be represented as a memo table
                  (???))
                (let [
                      ;rr (make-disjunct-op argument-variables memoized-values)
                      ]

                  )
                (make-multiplicity 0)
                ))

            :else (???) ;; this should not happen, means that it returned something that was unexpected
            )))
  (memo-get-iterator [this variables variable-values]
    (let [control-arg (conj (vec (map #(if (nil? %) meta-free-dummy-free-value %) variable-values)) nil)
          control-setting (memo-controller control-arg)]
      (cond (= control-setting :fallthrough) #{} ;; in the fallthrough case this
                                                 ;; should just rewrite as the
                                                 ;; orig-rexpr, so just let that
                                                 ;; happen rather than having to
                                                 ;; deal with the "iterator
                                                 ;; remapping mess"
            (= control-setting :defer) #{}

            (= (first control-setting) :lookup)
            (let []
              (debug-repl "memo get iterator lookup")
              (???)))))

  (memo-setup-new-table [this]
    (let [deps (flatten (map get-tables-from-rexpr (filter #(or (is-memoization-placeholder? %) (is-memoized-access? %))
                                                           (get-all-children orig-rexpr))))]
      (doseq [d deps]
        (add-watcher! (memo-get-assumption d) this))))

  (memo-refresh-value-for-key [this key]
    (let [cctx (context/make-empty-context orig-rexpr)]
      (doseq [[var val] (zipseq argument-variables key)
              :when (not (nil? val))]
        (ctx-set-value! cctx var val))
      (let [rr (binding [*aggregator-op-contribute-value* (fn [value mult]
                                                            (debug-repl "agg contrib")
                                                            (make-aggregator-op-inner (make-constant value)
                                                                                      []
                                                                                      (make-multiplicity mult)))]
                 (context/bind-context cctx
                                       (debug-repl "simp top")
                                       (simplify-top orig-rexpr)))]
        (debug-repl "refresh for key")
        (???)))

    ))



(def-rewrite
  :match {:rexpr (memoization-placeholder (:unchecked name) (:unchecked args-map))
          :check *expand-memoization-placeholder*}
  (let [term (get-user-term name)]
    (depend-on-assumption (:memoized-rexpr-assumption term))
    (remap-variables (:memoized-rexpr term) args-map)))

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


;; The memo controller function should return one of 3 values:
;;  :lookup      -- means that it should be looked up in the memo table.  If it is not already computed in the table, then some update should be enqueued (null)
;;  :defer       -- this should not do anything, there is not enough information here yet.  This could be an unk or an R-expr which is not yet resolved
;;  :fallthrough -- fall through the computation of the underlying R-expr.  Do NOT memoize the result

;; if is only using these three values, then how will it know what the
;; conditional expression depends on.  This needs to return some "key" in the
;; case of :lookup, which indicates what the

(defn- make-memoization-controller-function-rexpr-backed [info]
  (let [memo-controller-rexpr (make-user-call {:name (:memoization-tracker-method-name info)
                                               :arity 1
                                               :source-file (:source-file (:term-name info))}
                                              {(make-variable "$0") (make-variable 'Input)

                                               (make-variable "$1") (make-variable 'Result)}
                                              0 {})
        term-name (:name (:term-name info))]
    (fn [signature] ;; the signature should be an array of argument bindings.  The last value will be the result of
      (let [ctx (context/make-empty-context memo-controller-rexpr)
            res (context/bind-context-raw ctx
                                          (set-value! (make-variable 'Input) (DynaTerm. term-name (drop-last signature)))
                                          (simplify-top memo-controller-rexpr))]
        (if (= (make-multiplicity 1) res)
          (let [v (ctx-get-value ctx (make-variable 'Result))]
            (if (= "none" v)
              :fallthrough
              (if (= "null" v)
                [:lookup (conj (vec (drop-last signature)) nil)]
                (if (= "unk" v)
                  ;; if all of the variables are ground, then it can return :lookup, otherwise
                  (if (every? #(not= meta-free-dummy-free-value %) (drop-last signature))
                    [:lookup (conj (vec (drop-last signature)) nil)]
                    :defer)
                  (throw (DynaUserError. "$memo returned something other than none, null or unk"))
                  ))))
          (if (= (make-multiplicity 0) res)
            :fallthrough
            (do
              ;(dyna-warning "$memo defined such that it uses delayed constraints, this is _not_ recommened, as it means the memo can not be used until it is resolved")
              :defer)
            ;(throw (DynaUserError. "$memo defined incorrectly"))
            ))))))

(defn- make-memoization-controller-function [info]
  ;; this will return a function which represents $memo.  If the representation of the function is "sufficently simple"
  (cond (and (= 1 (count (:memoization-modes info)))
             (= 1 (count (:memoization-argument-modes info)))
             (not (:memoization-has-non-trivial-constraint info)))
        (let [f `(do
                   (ns dyna.memoization-v2)
                   (fn [~'args] ;; the function that is generated could be cached and reused in many cases, as there are unlikely to be lots of different kinds of functions here?
                     ~(cond
                        (= :unk (:memoization-mode info))
                        `(if (and ~@(for [i (range (count (first (:memoization-argument-modes info))))]
                                      `(not= (get ~'args ~i) meta-free-dummy-free-value)))
                           [:lookup (conj (vec (drop-last ~'args)) nil)]
                           :defer)

                        (= (:null (:memoization-mode info)))
                        `(if (and ~@(for [[i mode] (zipseq (range) (first (:memoization-argument-modes info)))
                                          :when (= :ground mode)]
                                      `(not= (get ~'args ~i) meta-free-dummy-free-value)))
                           [:lookup [~@(for [[i mode] (zipseq (range) (first (:memoization-argument-modes info)))
                                             :when (= :ground mode)]
                                         `(get ~'args ~i))
                                     nil]]
                           :defer)

                        (= :none (:memoization-mode info))
                        `:fallthrough)))
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

(defn- convert-user-term-to-have-memos [rexpr mapf]
  (debug-binding
   [*current-simplify-stack* (conj *current-simplify-stack* rexpr)]
   (if (is-aggregator-op-outer? rexpr)
     (if (= "only_one_contrib" (:name (:operator rexpr)))
       (make-aggregator-op-outer (:operator rexpr)
                                 (:result rexpr)
                                 (rewrite-rexpr-children (:bodies rexpr) ;; this is a disjunct
                                                         (fn [rr]
                                                           (assert (and (is-aggregator-op-inner? rr)
                                                                        (empty? (:projected rr))))
                                                           (let [zz (make-aggregator-op-inner (:incoming rr)
                                                                                              (:projected rr)
                                                                                              (convert-user-term-to-have-memos (:body rr) mapf))]
                                                             (when-not (= (exposed-variables rr) (exposed-variables zz))
                                                               (debug-repl "expose fail"))
                                                             zz))))
       (make-aggregator-op-outer (:operator rexpr)
                                 (:result rexpr)
                                 (mapf (:bodies rexpr) (:operator rexpr) (:result rexpr))))
     (mapf rexpr nil nil))))

(defn- get-tables-from-rexpr [r]
  (cond
    (is-memoized-access? r) [(:memoization-container r)]
    (is-memoization-placeholder? r)
    (let [t (get-user-term (:name r))
          tr (:memoized-rexpr t)]
      (depend-on-assumption (:memoized-rexpr-assumption t))
      (if (= tr r)
        (???) ;; in this case, we do not have the tables ready to be looked at yet?  So this needs to defer or something.
        (flatten (map get-tables-from-rexpr (filter #(or (is-memoized-access? %) (is-memoization-placeholder? %))
                                                    (get-all-children tr))))))
    :else nil))

(defn- rebuild-memo-table-for-term [term-name]
  ;; this will create a new memo container for the term.  The container will
  ;; just be the thing which holds the memos and the references to the R-expr
  ;; which represents the computation for the term.  In the case that the R-expr changes, then we should probably just
  (let [dep-memos (volatile! nil)
        ;new-containers (volatile! nil)
        variable-list (vec (map #(make-variable (str "$" %)) (range (+ 1 (:arity term-name)))))  ;; the variables which need to be synced across the memoization expressions (could be in any order, but it needs to be the same in all places)

        ;; first we will put in some placeholder in for this expression, such that in the case that we reference ourselves, it will not have an issue.
        [old1 new1] (update-user-term! term-name
                                       (fn [dat]
                                         (assoc dat
                                                :memoized-rexpr-assumption (make-assumption)
                                                :memoized-rexpr (make-memoization-placeholder term-name variable-list))))
        ;; second we will generate the Real memo tables (there might be multiple tables which are combined together depending on the structure of the R-expr
        [old2 new2] (update-user-term! term-name
                                       (fn [dat]
                                         (let [[orig-rexpr-assumpt orig-rexpr] (binding [*expand-memoization-placeholder* false
                                                                                         *lookup-memoized-values* false]
                                                                                 (compute-with-assumption
                                                                                  (simplify-top (user-rexpr-combined-no-memo dat))))
                                               controller-function (make-memoization-controller-function dat)
                                               priority-function (constantly 0) ;; TODO: have the priority function
                                               rexpr-with-memos (convert-user-term-to-have-memos orig-rexpr
                                                                                                 (fn [rr agg-op agg-result]

                                                                                                   (let [exposed (exposed-variables rr)
                                                                                                         container (if (contains? exposed (last variable-list))
                                                                                                                     (do
                                                                                                                       ;; this needs to just creat a normal memo table?
                                                                                                                       ;; or something which isn't optimized for aggregators
                                                                                                                       (???))
                                                                                                                     (MemoContainerTrieStorageAggregatorContributions.
                                                                                                                      controller-function
                                                                                                                      priority-function
                                                                                                                      agg-op
                                                                                                                      rr
                                                                                                                      (drop-last variable-list) ;; the argument variables
                                        ;agg-result  ;; this is the local variable which is used
                                                                                                                      #_(last variable-list) ;; result of aggregation goes here....though this might not be used by the aggregator
                                                                                                                      (make-assumption)
                                                                                                                      (atom [true nil (PrefixTrie. (- (count variable-list) 1)
                                                                                                                                                   0 {})])))]
                                                                                                     ;(debug-repl "tt")
                                                                                                     ;(vswap! new-containers conj container)
                                                                                                     ;; the variable list might not want to contain the resulting variable...
                                                                                                     (make-memoized-access container (vec (drop-last variable-list))))))
                                               ]
                                           (assoc dat
                                                  :memoized-rexpr rexpr-with-memos))))]

    (let [old-tables (ensure-set (when (:memoized-rexpr old1)
                                   (filter #(or (is-memoized-access? %) (is-memoization-placeholder? %))
                                           (get-all-children (:memoized-rexpr old1)))))
          new-tables (ensure-set (when (:memoized-rexpr new2)
                                   (filter #(or (is-memoized-access? %) (is-memoization-placeholder? %))
                                           (get-all-children (:memoized-rexpr new2)))))]

      ;; this needs make the new tables be subscribed to anything that they need
      (doseq [tr (difference new-tables old-tables)
              t (get-tables-from-rexpr tr)]
        (memo-setup-new-table t))

      ;; mark that the R-expr for the memo table has been changed
      (when (:memoized-rexpr-assumption old1)
        (invalidate! (:memoized-rexpr-assumption old1)))

      ;; then this needs to mark the old tables as invalidated.  This should kick off other work to get done
      (doseq [tr (difference old-tables new-tables)
              t (get-tables-from-rexpr tr)]
        ;; these tables are no longer used, so they should be invalidated
        (notify-invalidated! t nil))
      )))

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
                       (instance? Assumption ov))
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
