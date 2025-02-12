(ns dyna.memoization-v2
  (:require [dyna.utils :refer :all])
  (:require [dyna.rexpr :refer :all])
  (:require [dyna.rexpr-constructors :refer [is-meta-is-free? is-meta-is-ground? make-disjunct-op make-no-simp-disjunct-op
                                             is-aggregator-op-outer? is-aggregator-op-inner?
                                             make-aggregator-op-outer make-aggregator-op-inner
                                             is-disjunct-op?]])
  (:require [dyna.system :as system])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.user-defined-terms :refer [update-user-term! add-to-user-term! user-rexpr-combined-no-memo get-user-term]])
  (:require [dyna.assumptions :refer :all])
  (:require [dyna.context :as context])
  (:require [dyna.rexpr-builtins :refer [meta-free-dummy-free-value]])
  (:require [dyna.prefix-trie :refer :all])
  (:require [dyna.rexpr-aggregators-optimized])
  (:require [dyna.rexpr-disjunction :refer [trie-diterator-instance]])
  (:require [clojure.set :refer [union difference]])
  (:import [dyna DynaUserError IDynaAgendaWork DynaTerm InvalidAssumption UnificationFailure DIterable DynaAgenda ClojureUnorderedVector ClojureHashMap IteratorBadBindingOrder])
  (:import [dyna.assumptions Watcher Assumption])
  (:import [dyna.prefix_trie PrefixTrie])
  (:import [clojure.lang IFn]))

;; the priority for system work that should be done immeditly is 1e16
;; for user work that does not have anything set, we will give that a low priority by default.  Which will be -1e16 in this case
(def unset-priority-default-work -1e16)

(defn- get-all-children [rexpr]
  (let [c (set (get-children rexpr))]
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
  (memo-refresh-value-for-key [key])
  (memo-push-recompute-key [key]))

;; the placeholder will lookup the memoization container associated with a given
;; name.  This is an extra step of indirection which we can "defer."  This will
;; have that the placeholder will be able to get rewritten as needed
(def-base-rexpr memoization-placeholder [:unchecked name
                                         :var-map args-map]
  (rexpr-jit-info [this] {:jittable false}))
;; if this should expand the memoization-placeholder or just leave it as is.
;(def ^{:private true :dynamic true} *expand-memoization-placeholder* true)
(def-tlocal expand-memoization-placeholder)

(def-base-rexpr memoized-access [:unchecked memoization-container
                                 :var-list variable-mapping]
  (rexpr-jit-info [this] {:jittable false}))
#_(def ^{:private true :dynamic true} *lookup-memoized-values* true)
(def-tlocal lookup-memoized-values)

#_(def ^{:private true :dynamic true} *memoization-forward-placeholder-bindings* nil)
(def-tlocal memoization-forward-placeholder-bindings)
(def-base-rexpr memoization-filled-in-values-placeholder [:var-list variable-mapping]
  (rexpr-jit-info [this]
                  (debug-print "TODO: make the fill in values placeholder able to be jitted, this should be reading values from the context or something")
                  {:jittable false}))

(def-rewrite
  :match {:rexpr (memoization-filled-in-values-placeholder (:unchecked var-mapping))
          :check (not (nil? (tlocal *memoization-forward-placeholder-bindings*)))}
  ;; this might not be the most efficient way to go about this?  Suppose it should go into the context?
  (make-conjunct (vec (for [[var val] (zipseq var-mapping (tlocal *memoization-forward-placeholder-bindings*))
                            :when (not (nil? val))]
                        (make-unify var (make-constant val))))))


(deftype AgendaReprocessWork [^IMemoContainer memo-container term ^double priority]
  IDynaAgendaWork
  (run [this]
    (when DynaAgenda/print_agenda_work
      (println "running agenda work" term)) ;; this should get controlled by some flag, so a user can see if they screwed up their priority functions/memoization
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



#_(deftype MemoContainerGenericRexpr []
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

(declare ^{:private true} make-update-handler-function)

(deftype MemoContainerTrieStorageAggregatorContributions [^IFn memo-controller ;; these set the policies of what should happen depending on the arguments
                                                          ^IFn memo-priority-function
                                                          aggregator-op
                                                          orig-rexpr
                                                          argument-variables
                                                          ;result-variable
                                                          ^Assumption assumption
                                                          data ;; (atom [valid has-computed (PrefixTrie memoized-values)])
                                                          updating-data ;; an (atom {}) which is used to hold metadata for processing updates
                                                          ]
  Watcher
  (notify-invalidated! [this watching]
    (swap! data (fn [[a b c]] [false b c]))
    (invalidate! assumption))
  (notify-message! [this watching message]
    ;; there can be many things that we depend on.  These will each have their one assumption.  In the case that
    (let [[handler-assumpt update-handler] (or (get @updating-data watching)
                                               (get (swap! updating-data assoc watching (compute-with-assumption (make-update-handler-function this watching))) watching))]
      (if-not (is-valid? handler-assumpt)
        (do
          (swap! updating-data dissoc watching) ;; delete from the map the old handler as the assumption for it is no longer valid
          (recur watching message)) ;; reprocesses this and create a new handler
        (update-handler this watching message))))

  IMemoContainer
  (memo-get-assumption [this] assumption)
  (memo-push-recompute-key [this key]
    (let [kk (doall key)]
      (when (is-key-contained? (second @data) kk) ;; if we don't have the key already in the table, then we can't "recompute" it
        (let [prio (memo-priority-function kk)]
          (system/push-agenda-work (AgendaReprocessWork. this kk prio))))))
  (memo-rewrite-access [this variables variable-values]
    (let [control-arg (conj (vec variable-values) nil)
          control-setting (try (memo-controller control-arg)
                               (catch Exception err :defer))]
      (cond (= control-setting :fallthrough)
            (let [vm (into {} (for [[a v] (zipseq argument-variables variables)
                                    :when (not= a v)]
                                [a v]))]
              (remap-variables orig-rexpr vm))

            (= control-setting :defer)
            nil ;; returning nil in this case will mean that it does not perform a rewrite, hence it will be defered

            (= (first control-setting) :lookup)
            (let [[valid has-computed memoized-values] @data]
              (when-not valid
                (throw (InvalidAssumption. "memo table no longer valid")))
              (let [lookup-key (drop-last (second control-setting))
                    has-key (is-key-contained? has-computed lookup-key)]
                (if-not has-key
                  (if ((tlocal *memoization-make-guesses-handler*) this variables variable-values) ;; return true if this should make the guess
                    (let [[old-dat new-dat] (swap-vals! data (fn [[a b c]]
                                                               (if-not a
                                                                 [a b c] ;; not valid, do not change
                                                                 [a (assoc-in b lookup-key true) c])))]
                      (when (or (identical? (second old-dat) has-computed) ;; this first check is just an optimization, we really care about if the we were the ones to add the new lookup key, which means it wasn't in old
                                (not (is-key-contained? (second old-dat) lookup-key)))
                        (assert (not (some #{meta-free-dummy-free-value} lookup-key)))
                        (memo-push-recompute-key this lookup-key))
                      (do
                        (throw (UnificationFailure. "empty memo (making guess)")) ;; we could be more efficient about stopping the evaluation by throwing unification failure
                        (make-multiplicity 0)) ;; return 0, as this is the current "guess" for this value and there is currently nothing there
                      )
                    nil ;; we are not making a guess, so we return nil which does not do the rewrite
                    )

                  ;; has-key is true, so we are going to return the matched values from the data trie
                  (let [;has-nil (some nil? variable-values)
                        lrexpr (make-no-simp-disjunct-op argument-variables memoized-values nil) ;; build a disjunct opt which holds the current memoized values
                        lcontext (context/make-empty-context lrexpr)
                        variables-map (zipmap variables argument-variables)]
                    (doseq [[var val] (zipseq argument-variables variable-values)
                            :when (not (nil? val))]
                      ;; set all of the incoming variables to their respected value
                      (ctx-set-value! lcontext var val))
                    ;(debug-repl "pre return")
                    (let [res (context/bind-context lcontext
                                                    (tbinding [memoization-make-guesses-handler (fn [memo-table variable variable-values] false) ;; do not make guesses
                                                               aggregator-op-get-variable-value (fn [variable]
                                                                                                  (get-value (get variables-map variable variable)))]
                                                              (simplify-fully-no-guess lrexpr)))]
                      (when-not (is-empty-rexpr? res)
                        (debug-repl "memo access res"))
                      res)))))

            :else
            (do ;(debug-repl "should not happen")
                (???)) ;; this should not happen, means that it returned something that was unexpected
            )))
  (memo-get-iterator [this variables variable-values]
    (let [control-arg (conj (vec variable-values) nil)
          control-setting (try (memo-controller control-arg)
                               (catch Exception err :defer))]
      #_(when-not (= :defer control-setting)
        (debug-repl "get iter"))
      (cond (= control-setting :fallthrough) #{} ;; in the fallthrough case this
            ;; should just rewrite as the
            ;; orig-rexpr, so just let that
            ;; happen rather than having to
            ;; deal with the "iterator
            ;; remapping mess"
            (= control-setting :defer) #{}  ;; in defer, there is nothing that we are going to do

            (= (first control-setting) :lookup)
            (let [lookup-key (drop-last (second control-setting))
                  [valid has-computed memoized-values] @data
                  has-key (is-key-contained? has-computed lookup-key)]
              (if has-key
                (let [contains-wildcard (.contains-wildcard ^PrefixTrie memoized-values)]
                  (when (not= contains-wildcard (- (bit-shift-left 1 (count variables)) 1)) ;; when there is something which is not wildcard
                    #{(reify DIterable
                        (iter-what-variables-bound [this]
                          (into #{} (for [[idx var] (zipseq (range) variables)
                                          :when (and (= 0 (bit-and contains-wildcard (bit-shift-left 1 idx)))
                                                     (is-variable? var))]
                                      var)))
                        (iter-variable-binding-order [this]
                          [variables])
                        (iter-create-iterator [this which-binding]
                          ;(assert (.contains (iter-variable-binding-order this) which-binding))
                          ;; this is using the same code as the optimized disjunct to create an iterator, as they are both just looping through
                          ;; the values of the prefix trie
                          ;(debug-repl "create memo iterator")
                          (when (not= variables which-binding)
                            (throw (IteratorBadBindingOrder.)))
                          (trie-diterator-instance (count variables) (.root ^PrefixTrie memoized-values) variables)))}))
                (do
                  ;; then we have not computed this key yet.
                  ;; this should enqueue the work for this to perform the computation.
                  #{}))))))

  (memo-setup-new-table [this]
    (let [deps (flatten (map get-tables-from-rexpr (filter #(or (is-memoization-placeholder? %) (is-memoized-access? %))
                                                           (get-all-children orig-rexpr))))]
      (doseq [d deps]
        (add-watcher! (memo-get-assumption d) this))))

  (memo-refresh-value-for-key [this key]
    (loop []
      (let [[valid _ current-memoized-values] @data
            [compute-assumpt [cctx ret-rexpr accumulated-agg-values]]
            (compute-with-assumption
             (let [cctx (context/make-empty-context orig-rexpr)]
               (doseq [[var val] (zipseq argument-variables key)
                       :when (not (nil? val))]
                 (ctx-set-value! cctx var val))
               ;(debug-repl "do refresh")
               (let [accumulator (volatile! nil) ;; this is a "flat" map from tuples to values (not a trie)
                     rr (tbinding [aggregator-op-contribute-value (fn [value mult]
                                                                     (let [kvals (vec (map get-value argument-variables))]
                                                                       (when (some nil? kvals)
                                                                         (debug-repl "accum nil"))
                                                                       (vswap! accumulator update kvals
                                                                               (fn [old]
                                                                                 (if (nil? old)
                                                                                   ((:many-items aggregator-op) value mult)
                                                                                   ((:combine-mult aggregator-op) old value mult)))))
                                                                     (make-multiplicity 0))
                                  aggregator-op-additional-constraints
                                  (if (:add-to-in-rexpr aggregator-op)
                                    (let [ati (:add-to-in-rexpr aggregator-op)]
                                      (fn [incoming-variable]
                                        (if-not (tlocal *simplify-with-inferences*)
                                          (make-multiplicity 1)
                                          (let [kvals (vec (map get-value argument-variables))
                                                cur-val (get @accumulator kvals)]
                                            #_(when (some nil? kvals)
                                              (debug-repl "accum nil"))
                                            (if-not (nil? cur-val)
                                              (let [rr (ati cur-val incoming-variable)]
                                                (simplify-inference rr))
                                              (make-multiplicity 1))))))
                                    (fn [incoming-variable]
                                      (make-multiplicity 1)))
                                  aggregator-op-saturated (if (:saturate aggregator-op)
                                                              (let [sf (:saturate aggregator-op)]
                                                                (fn []
                                                                  (let [kvals (vec (map get-value argument-variables))
                                                                        cur-val (get @accumulator kvals)]
                                                                    #_(when (some nil? kvals)
                                                                      (debug-repl "accum nil"))
                                                                    (when-not (nil? cur-val)
                                                                      (sf cur-val)))))
                                                              (fn [] false))
                                  aggregator-op-should-eager-run-iterators true  ;; maybe this should only run it eagerly if it can fully ground all of the variables
                                  ]
                          (context/bind-context cctx
                                                (try (simplify-fully orig-rexpr)
                                                     (catch UnificationFailure e (make-multiplicity 0)))))]
                 [cctx rr @accumulator]))
             )
            ;; this is a new trie which will contain all of the new R-expr values which are represented
            ;; how this will encode the different values will mean that
            accum-vals-wrapped (update-vals accumulated-agg-values (fn [x]
                                                                     ;; TODO: this needs to know which operator is used?
                                                                     ;; this will mean that memoization will need to track
                                                                     ;; this information from when it is constructed?
                                                                     ;; or it will have to look at the origional R-expr and figure it out from there
                                                                     (debug-print "TODO: memoization needs to know which operator to add to the aggregator")
                                                                     (ClojureUnorderedVector/create
                                                                      [(make-aggregator-op-inner nil (make-constant x) [] (make-multiplicity 1))])))
            new-values (if (is-empty-rexpr? ret-rexpr)
                         accum-vals-wrapped
                         (update accum-vals-wrapped key (fn [x] (ClojureUnorderedVector/concat [x [ret-rexpr]]))))
            new-values-freq (frequencies new-values)
            ]

        (let [need-to-redo (volatile! false)
              messages-to-send (volatile! nil)]
          (swap! data (fn [[valid has-computed mv]]
                        (if-not valid
                          [valid has-computed mv] ;; then just don't do anything as this is already invalidated, so we are not going to update
                          (if-not (identical? mv current-memoized-values)
                            ;; we only care about the current-memoized-values
                            ;; chainging.  The has-computed could change while
                            ;; we are performing a computation and that is fine.
                            ;; As such do not directly use swap! on the atom
                            ;; when performing this update.

                            (do (vreset! need-to-redo true)
                                [valid has-computed mv])
                            (let [existing-values (frequencies (trie-get-values-collection mv key))]
                              (if (= existing-values new-values-freq)
                                (do ;; then this is the same, so we do not have to do anything here
                                  (vreset! messages-to-send nil)
                                  [valid has-computed mv])
                                (do ;; there are new values to insert
                                        ;(debug-repl "memo insert")
                                  #_(dyna-debug
                                   (when (some #(some nil? %) (map first (keys new-values-freq)))
                                     (debug-repl "insert free")))
                                  (vreset! messages-to-send nil)
                                  (let [with-deleted
                                        #_(reduce-kv (fn [[kk _]]))
                                          ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
                                        ;; TODO: change these to use reduce-kv instead of seq the map, as it seems that running seq on the map is causing
                                        ;; it to have some kind of slow iterator in this

                                        (loop [cmv mv
                                               kks (keys existing-values)]
                                          (if (empty? kks) cmv
                                              (let [[kk _] (first kks)]
                                                (if (contains? new-values kk)
                                                  (recur cmv (next kks))
                                                  (do
                                                    (vswap! messages-to-send conj kk)
                                                    (recur (trie-delete-matched cmv kk) (next kks)))))))
                                        with-added (loop [cmv with-deleted
                                                          kvs (seq new-values)]
                                                     (if (empty? kvs)
                                                       cmv
                                                       (let [[kk re] (first kvs)]
                                                         #_(when-not (= mult 1)
                                                             (debug-repl "mult?"))
                                                         ;; TODO: this needs to check that
                                                         (vswap! messages-to-send conj kk)
                                                         (recur (trie-update-collection cmv kk (fn [c]

                                                                                                 ;; (when-not (nil? c)
                                                                                                 ;;   ;; TODO: this "replace" c instead of adding it to the
                                                                                                 ;;   ;; collection.  This means that it also does not have
                                                                                                 ;;   ;; to
                                                                                                 ;;   (debug-repl)
                                                                                                 ;;   (???))
                                                                                                 ;; (vec (concat (or c []) re))
                                                                                                 (vec re)
                                                                                                 ))
                                                                (next kvs)))))]
                                    [valid has-computed with-added]))))))))
          (if @need-to-redo
            (recur)
            (doseq [msg @messages-to-send]
              (send-message! assumption {:kind :value-changed
                                         :from-memo-table this
                                         :key msg}))))))))

(defn- replace-memo-reads-with-placeholder [rexpr assumption]
  (cond (is-memoized-access? rexpr) (let [cc (:memoization-container rexpr)]
                                      (when (= assumption (memo-get-assumption cc))
                                        ;; then this rexpr matches the assumption that we are looking for
                                        [(make-memoization-filled-in-values-placeholder (:variable-mapping rexpr))]))
        (is-memoization-placeholder? rexpr) (let [t (get-user-term (:name rexpr))]
                                              (depend-on-assumption (:memoized-rexpr-assumption t))
                                              (let [r (:memoized-rexpr t)]
                                                (assert (not= r rexpr))
                                                (for [rr (replace-memo-reads-with-placeholder r assumption)]
                                                  (remap-variables rr (:args-map rexpr)))))

        (is-disjunct? rexpr) (remove empty? (map #(replace-memo-reads-with-placeholder % assumption) (get-children rexpr)))
        (is-disjunct-op? rexpr) (let [djvars (:disjunction-variables rexpr)]
                                  (doall (for [[vassign rexpr] (trie-get-values (:rexprs rexpr) nil)
                                               :let [ra (replace-memo-reads-with-placeholder rexpr assumption)]
                                               :when (not (empty? ra))
                                               rr ra]
                                           (let [res (make-conjunct (conj (for [[val var] (zipseq vassign djvars)
                                                                                :when (not (nil? val))]
                                                                            (make-unify var (make-constant val)))
                                                                          rr))]
                                             res
                                             #_(do (debug-repl "disjunct found something")
                                                 (???))))))

        :else
        ;; this version should use the index of the rexpr in the expression
        ;; being rewritten.  This will ensure that if something is duplicated,
        ;; that it will get processed twice
        (let [children (transient [])]
          (rewrite-rexpr-children rexpr (fn [r] (conj! children r) r))
          (for [[idx child] (zipseq (range) (persistent! children))
                rr (replace-memo-reads-with-placeholder child assumption)
                :let [idc (volatile! -1)]]
            (rewrite-rexpr-children rexpr (fn [r]
                                            (vswap! idc inc)
                                            (if (= @idc idx)
                                              rr
                                              r)))))))

(defn ^{:private true} make-update-handler-function [^MemoContainerTrieStorageAggregatorContributions container ^Assumption triggering-assumption]
  ;; this should look at the orig-rexpr and do some preprocessing against the expression so that this can be a bit more efficient when it comes
  ;; to handling the message.  This could also have state using its own atoms/voliates!
  (let [orig-rexpr (.orig-rexpr container)
        aggregator-op (.aggregator-op container)
        placeholder-rexprs (vec (replace-memo-reads-with-placeholder orig-rexpr triggering-assumption))]
    ;(debug-repl "make update handler function")
    (fn [^MemoContainerTrieStorageAggregatorContributions container ^Assumption triggering-assumption message]
      ;; this needs to identify all of the values on the R-expr which need to get recomputed, and do that

      ;; TODO: message needs more structure, as there could be different types
      ;; of messages that are sent.  If there is just a notification message,
      ;; then it is bindings for which variables have changed?  Or is this going
      ;; to be that some of the values might
      (assert (= (:kind message) :value-changed))
      (let [data (.data container)
            arg-vars (.argument-variables container)
            values-to-recompute (volatile! {})
            [valid has-computed memoized-values] @data]
        ;; Step 1: Identify all of the values in our memo table that need to get recomputed
        (doseq [pr placeholder-rexprs]
          (tbinding [memoization-forward-placeholder-bindings (:key message)]
            (let [ctx (context/make-empty-context pr)
                  result (context/bind-context ctx (try (simplify-fully-no-guess pr)
                                                        (catch UnificationFailure e (make-multiplicity 0))))
                  ;; for now going to do a simpler version where it only handles a single value of the variables.  This will need to handle
                  ;; the case where it needs to get an iterator over the R-expr which is returned.  Such that it will get all of the bindings
                  var-bindings (doall (map #(get-value-in-context % ctx) arg-vars))]
              (vswap! values-to-recompute assoc-in var-bindings true))))


        ;; Step 2: deduplicate the list of values which need to be recomputed.  If there is a wild card then it will back off the values to just the wildcard value
        (let [to-compute-set (volatile! #{})
              new-values (volatile! {})]
          ((fn rec [so-far m]
             (if (= true m)
               (vswap! to-compute-set conj (reverse so-far))
               (if (contains? m nil) ;; then there is a wild card in the binding of this variable
                 (if (= (get m nil) true)
                   (rec (cons nil so-far) true)
                   (rec (cons nil so-far) (apply merge (vals m))))
                 (doseq [[k v] m]
                   (rec (cons k so-far) v))))
             ) () @values-to-recompute)

          (doseq [to-compute @to-compute-set]
            ;; this is going to push to the agenda work which will recompute the relevant keys
            (memo-push-recompute-key container to-compute))

          #_(when false

            ;; Step 3: Do the actual computation for the new values
            (doseq [to-compute @to-compute-set]
              (let [ctx (context/make-empty-context orig-rexpr)]
                (doseq [[var val] (zipseq arg-vars to-compute)
                        :when (not (nil? val))]
                  (ctx-set-value! ctx var val))
                (let [result (context/bind-context-raw ctx (try (simplify-fully orig-rexpr)
                                                                (catch UnificationFailure e (make-multiplicity 0))))]
                  (vswap! new-values assoc to-compute result))))

            ;; Step 4: Update the values in the memo table.  If something else has already changed the value, then we might have to requeue some refresh of this new value
                                        ;(debug-repl "do table update")
            (let [[[_ _ old-memoized-values] [valid _ new-memoized-values]]
                  (swap-vals! data (fn [[valid has-computed c-memoized-values]]
                                     (if-not valid
                                       [valid has-computed memoized-values] ;; if not valid, do not change anything
                                       (do
                                         (assert (identical? memoized-values c-memoized-values)) ;; otherwise something else has concurrently modified this, we need to handle that case
                                         [valid has-computed (loop [mv (loop [mv c-memoized-values
                                                                              dels (seq @to-compute-set)]
                                                                         (let [[f & r] dels
                                                                               d (trie-delete-matched mv f)]
                                                                           (if (empty? r)
                                                                             d
                                                                             (recur d r))))
                                                                    adding (seq @new-values)]
                                                               (let [[[key val] & r] adding]
                                                                 (let [n (trie-insert-val mv key val)]
                                                                   (if (empty? r)
                                                                     n
                                                                     (recur n r)))))]))))
                  sending-message-assumption (.assumption container)]
                                        ;(debug-repl "after update")
              (when valid ;; if the table is not valid, then we are not going to lok for anything to up

                ;; Step 5: send update messages for the keys that have changed in the table
                (doseq [[key vals-old vals-new] (tries-differences old-memoized-values new-memoized-values)]
                  (assert (= (count key) (.arity ^PrefixTrie new-memoized-values))) ;; TODO: fix tries-differences, or figure out what is oging to happen in the case that we do not have all of the keys
                  (let [message-to-send {:kind :value-changed
                                         :from-memo-table container
                                         :key key}]
                    (send-message! sending-message-assumption message-to-send)))
                (println "after sending messages")
                ))))))))

(def-rewrite
  :match {:rexpr (memoization-placeholder (:unchecked name) (:unchecked args-map))
          :check (tlocal *expand-memoization-placeholder*)}
  (let [term (get-user-term name)]
    (depend-on-assumption (:memoized-rexpr-assumption term))
    (remap-variables (:memoized-rexpr term) args-map)))

(def-rewrite
  :match {:rexpr (memoized-access (:unchecked ^IMemoContainer container) (:unchecked variable-map))
          :check (tlocal *lookup-memoized-values*)}
  ;; inside of the JIT, the last argument could be something which will be generated using the local variables
  ;; this will prevent us from having to indirect through the *context* to access the values of variables
  (memo-rewrite-access container variable-map (map get-value variable-map)))

(def-iterator
  :match {:rexpr (memoized-access (:unchecked ^IMemoContainer container) (:unchecked variable-map))
          :check (tlocal *lookup-memoized-values*)}
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
            res (tbinding [dollar-free-matches-ground-values true] ;; this essentially tunrs $free into a no-op, which allows for foo(1,2,3) and foo(FREE,FREE,FREE) to both be matched by $free.  The reason
                  (context/bind-context-raw ctx
                                            (set-value! (make-variable 'Input) (DynaTerm. term-name (vec (map #(if (nil? %) meta-free-dummy-free-value %)
                                                                                                              (drop-last signature)))))
                                            (simplify-fully-no-guess memo-controller-rexpr)))]
        (if (= (make-multiplicity 1) res)
          (let [v (ctx-get-value ctx (make-variable 'Result))]
            (if (= "none" v)
              :fallthrough
              (if (= "null" v)
                [:lookup (conj (vec (drop-last signature)) nil)]
                (if (= "unk" v)
                  ;; if all of the variables are ground, then it can return :lookup, otherwise
                  (if (every? #(not (nil? %)) (drop-last signature))
                    [:lookup (conj (vec (drop-last signature)) nil)]
                    :defer)
                  (throw (DynaUserError. "$memo returned something other than none, null or unk"))))))
          (if (= (make-multiplicity 0) res)
            :fallthrough
            (do
              ;(dyna-warning "$memo defined such that it uses delayed constraints, this is _not_ recommened, as it means the memo can not be used until it is resolved")
              :defer)
            ;(throw (DynaUserError. "$memo defined incorrectly"))
            ))))))


(defn- make-memoization-controller-function [info]
  ;; this will return a function which represents $memo.  If the representation of the function is "sufficently simple"
  ;(debug-repl "make controller")
  (make-memoization-controller-function-rexpr-backed info)
  #_(cond (and (= 1 (count (:memoization-modes info)))
             (= 1 (count (:memoization-argument-modes info)))
             (not (:memoization-has-non-trivial-constraint info)))
        (let [f `(do
                   (in-ns 'dyna.memoization-v2)
                   ;; TODO: the last value pass as the argument represents the result of aggregation.  This value is always null.  We should instead just remove that from the array

                   (fn [~'args] ;; the function that is generated could be cached and reused in many cases, as there are unlikely to be lots of different kinds of functions here?
                     ~(cond
                        (= :unk (:memoization-mode info))
                        `(if (and ~@(for [i (range (count (first (:memoization-argument-modes info))))]
                                      `(not (nil? (get ~'args ~i)))))
                           [:lookup (conj (vec (drop-last ~'args)) nil)]
                           :defer)

                        (= (:null (:memoization-mode info)))
                        `(if (and ~@(for [[i mode] (zipseq (range) (first (:memoization-argument-modes info)))
                                          :when (= :ground mode)]
                                      `(not (nil?  (get ~'args ~i)))))
                           [:lookup [~@(for [[i mode] (zipseq (range) (first (:memoization-argument-modes info)))]
                                         (if (= :ground mode)
                                           `(get ~'args ~i)
                                           nil))
                                     nil]]
                           :defer)

                        (= :none (:memoization-mode info))
                        `:fallthrough)))
              r (binding [*ns* dummy-namespace] ;; work around *ns* binding issues
                  (eval f))
              ]
          r)
        ;; TODO: this should handle slightly more complex functions in the case
        ;; that all of the constraints are trivial, though if there is
        ;; overrides, the order might be different atm?  I supose that the
        ;; representation will have to use something other than sets to control
        ;; what the order is for overriding expressions

        :else
        (make-memoization-controller-function-rexpr-backed info)))

#_(defn- rebuild-memos-for-term [term-name]
  ;;
  )

#_(defn- refresh-memo-table [^IMemoContainer memo-container]
  ;; refreshing the memo table will be that it should
  (debug-repl "refresh memo table")
  (when (is-valid? (memo-get-assumption memo-container))
    ;; this is going to have to identify which keys in the table are defined as null, and then

    ))


(defn- make-priority-controller-function [call-name priority-function-name]
  (let [rexpr (make-user-call {:name priority-function-name
                               :arity 1
                               :source-file (:source-file call-name)}
                              {(make-variable "$0") (make-variable 'Input)
                               (make-variable "$1") (make-variable 'Result)}
                              0 {})]
    (fn [signature]
      (try
        (let [ctx (context/make-empty-context rexpr)
              res (context/bind-context-raw ctx
                                            (set-value! (make-variable 'Input) (DynaTerm. (:name call-name)
                                                                                          (vec (map #(if (nil? %) meta-free-dummy-free-value %) signature))))
                                            (simplify-fully-no-guess rexpr))
              val (get-value-in-context (make-variable 'Result) ctx)]
          (if-not (and (= (make-multiplicity 1) res) (number? val))
            (do
              (dyna-warning (str "$priority did not return a numerical priority for " (:name call-name) "/" (:arity call-name)))
              unset-priority-default-work)
            val))
        (catch Exception err
          (do
            (dyna-warning (str "$priority did not return a numerical priority for " (:name call-name) "/" (:arity call-name)))
            unset-priority-default-work))))))

(defn- convert-user-term-to-have-memos [rexpr mapf]
  ;; this takes an R-expr and adds one or more memo tables to the R-expr such that it will support memoization
  ;; I suppose that it will
  (debug-tbinding
   [current-simplify-stack (conj (tlocal *current-simplify-stack*) rexpr)]
   (if (is-aggregator-op-outer? rexpr)
     (if (= "only_one_contrib" (:name (:operator rexpr)))
       (make-aggregator-op-outer (:operator rexpr)
                                 (:result rexpr)
                                 (rewrite-rexpr-children (:bodies rexpr) ;; this is a disjunct
                                                         (fn [rr]
                                                           (assert (and (is-aggregator-op-inner? rr)
                                                                        (empty? (:projected rr))))
                                                           (let [zz (make-aggregator-op-inner (:operator rr)
                                                                                              (:incoming rr)
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

(declare ^{:private true} rebuild-memo-table-for-term)

(defrecord rebuild-memo-table-for-term-agenda-work [term-name]
  IDynaAgendaWork
  (run [this] (rebuild-memo-table-for-term term-name))
  (priority [this] 1e16))

(defn- rebuild-memo-table-for-term [term-name]
  ;; this will create a new memo container for the term.  The container will
  ;; just be the thing which holds the memos and the references to the R-expr
  ;; which represents the computation for the term.  In the case that the R-expr changes, then we should probably just
  (let [variable-list (vec (map #(make-variable (str "$" %)) (range (+ 1 (:arity term-name)))))  ;; the variables which need to be synced across the memoization expressions (could be in any order, but it needs to be the same in all places)

        ;; first we will put in some placeholder in for this expression, such that in the case that we reference ourselves, it will not have an issue.
        [old1 new1] (update-user-term! term-name
                                       (fn [dat]
                                         (assoc dat
                                                :memoized-rexpr-assumption (make-assumption)
                                                :memoized-rexpr (make-memoization-placeholder term-name (zipmap (map #(make-variable (str "$" %)) (range))
                                                                                                                variable-list)))))
        ;; second we will generate the Real memo tables (there might be multiple tables which are combined together depending on the structure of the R-expr
        orig-rexpr-assumpt-v (volatile! nil)
        [old2 new2] (update-user-term! term-name
                                       (fn [dat]
                                         (let [[orig-rexpr-assumpt orig-rexpr] (tbinding [expand-memoization-placeholder false
                                                                                          lookup-memoized-values false]
                                                                                 (compute-with-assumption
                                                                                  (simplify-top (user-rexpr-combined-no-memo dat))))
                                               controller-function (make-memoization-controller-function dat)
                                               priority-function (if (:memoization-priorty-method dat)
                                                                   (make-priority-controller-function term-name (:memoization-priorty-method dat))
                                                                   (constantly unset-priority-default-work))
                                               rexpr-with-memos (convert-user-term-to-have-memos orig-rexpr
                                                                                                 (fn [rr agg-op agg-result]
                                                                                                   (if (nil? agg-op)
                                                                                                     (let []
                                                                                                       rr ;; just return without adding a memo table as this should have already finished its computation
                                                                                                       ;(debug-repl "nil agg op")
                                                                                                       ;(???)
                                                                                                       )
                                                                                                     (let [exposed (exposed-variables rr)
                                                                                                           container (if (contains? exposed (last variable-list))
                                                                                                                       (do
                                                                                                                         ;; this needs to just create a normal memo table?
                                                                                                                         ;; or something which isn't optimized for aggregators

                                                                                                                         ;; this could happen if the memo got fully computed already
                                                                                                                         ;; in which case there is nothing to "memoize"
                                                                                                                         (???))
                                                                                                                       (MemoContainerTrieStorageAggregatorContributions.
                                                                                                                        controller-function
                                                                                                                        priority-function
                                                                                                                        agg-op
                                                                                                                        rr
                                                                                                                        (vec (drop-last variable-list)) ;; the argument variables
                                                                                                                        (make-assumption)
                                                                                                                        (atom [true nil (make-PrefixTrie (- (count variable-list) 1)
                                                                                                                                                         0 nil)])
                                                                                                                        (atom nil)))
                                                                                                           nr (make-memoized-access container (vec (drop-last variable-list)))]
                                                                                                       ;; the variable list might not want to contain the resulting variable...
                                                                                                       #_(when-not (= (exposed-variables nr) (exposed-variables rr))
                                                                                                           (debug-repl "exposed failed"))
                                                                                                       nr))))
                                               ]
                                           (vreset! orig-rexpr-assumpt-v orig-rexpr-assumpt)
                                           (assoc dat
                                                  :memoized-rexpr rexpr-with-memos))))]
    (tbinding [fast-fail-on-invalid-assumption false]              ;binding [*fast-fail-on-invalid-assumption* false]
      (let [watcher (reify Watcher
                      (notify-message! [this watching message] nil)
                      (notify-invalidated! [this watching]
                        ;; then it needs to rebuild the memo tables for this term
                        (system/push-agenda-work (->rebuild-memo-table-for-term-agenda-work term-name))))]
        (add-watcher! @orig-rexpr-assumpt-v watcher)
        ;; TODO: this should refresh the updated key instead of rebuilding the entire table
        (add-watcher! (:def-assumption new2) watcher)))
    (let [old-tables (set (when (:memoized-rexpr old1)
                                   (filter #(or (is-memoized-access? %) (is-memoization-placeholder? %))
                                           (get-all-children (:memoized-rexpr old1)))))
          new-tables (set (when (:memoized-rexpr new2)
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
        (notify-invalidated! t nil)))))

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
    (when-not (and (is-aggregator? rexpr) (= "=" (:operator rexpr)))
      ;; this might work ok with := in some cases, but there are some bugs which need to get worked out
      ;; easier to just disable non `=` aggregators
      (throw (DynaUserError. "$memo can only be defined using the `=` aggregator")))
    (let [term-name (:name term-structure)
          args (:arguments term-structure)
          ;; the name of the term that we are going to enable memoization on
          call-name {:name term-name
                     :arity (count args)
                     :source-file source-file}
          [memo-mode memo-mode-rexpr] (when (is-aggregator? rexpr) ;; this is just going to fail if this is not an aggregator, so it might as well just assert this?
                                        ;; I suppose that this could attempt to simplify the body of the expression first, bu then it will potentially have that this picks up assumptions etc
                                        ;; if we don't allow for := in the first place with $memo, then it could have that it would simplify the unk vs null stuff as it would only work with
                                        (let [incoming (:incoming rexpr)
                                              get-value-const (fn [x]
                                                                (let [v (get-value x)]
                                                                  ;; TODO: := is broken on $memo currently
                                                                  (if (and (instance? DynaTerm v) (= (.name ^DynaTerm v) "$colon_line_tracking"))
                                                                    (get v 1)
                                                                    v)))]
                                          (if (is-constant? incoming)
                                            [(keyword (get-value-const incoming)) nil]
                                            (or (only (for [[projected-vars rr] (all-conjunctive-rexprs rexpr)
                                                            :when (and (is-unify? rr) (= (:a rr) incoming))]
                                                        [(keyword (get-value-const (:b rr))) rr]))
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
                                      0 (do
                                          ;; if there are no constraints on the variables, then we are going to default to ground?  This will mean that it must be present for
                                          (dyna-warning "$memo variables should be annotated with $free or $ground (e.g. X:$free)")
                                          :ground)
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
        (debug-repl "memo mode")
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
                                                             :memoization-modes mode
                                                             :is-memoized-unk (if (and (:unk modes) (not (is-valid? (:is-memoized-unk dat2))))
                                                                                (make-assumption)
                                                                                (:is-memoized-unk dat2))
                                                             :is-memoized-null (if (and (:null modes) (not (is-valid? (:is-memoized-null dat2))))
                                                                                (make-assumption)
                                                                                (:is-memoized-null dat2))
                                                             :memoized-rexpr (if (or (:null modes) (:unk modes))
                                                                               (make-memoization-placeholder call-name
                                                                                                             #_(into [] (for [i (range (+ 1 (count args)))]
                                                                                                                        (make-variable (str "$" i))))
                                                                                                             (into {} (for [i (range (+ 1 (count args)))
                                                                                                                              :let [v (make-variable (str "$" i))]]
                                                                                                                          [v v])))
                                                                               ;(make-multiplicity 0)
                                                                               ;; if this is only :none, then there is no memoized R-expr
                                                                               nil))]
                                             dat3)))]
        ;(debug-repl "$memo")

        ;; save the method definition for the $memo value
        (add-to-user-term! source-file dynabase (:memoization-tracker-method-name new) 1 rexpr)

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
        (system/push-agenda-work (->rebuild-memo-table-for-term-agenda-work call-name))))))

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
      (add-to-user-term! source-file dynabase (:memoization-priorty-method new) 1 rexpr)
      (if (not= (:memoization-priorty-method new) (:memoization-priorty-method old))
        (system/push-agenda-work (->rebuild-memo-table-for-term-agenda-work call-name))))))


(swap! debug-useful-variables assoc
       'work-agenda (fn [] (tlocal system/work-agenda)))

(defn print-memo-table [call-name]
  (let [term (get-user-term call-name)]
    (println (:memoized-rexpr term))
    (debug-repl)))
