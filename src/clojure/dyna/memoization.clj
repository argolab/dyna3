(ns dyna.memoization
  (:require [dyna.utils :refer :all])
  (:require [dyna.rexpr :refer :all])
  (:require [dyna.system :as system])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.user-defined-terms :refer [update-user-term! user-rexpr-combined-no-memo get-user-term]])
  (:require [dyna.assumptions :refer :all])
  (:require [dyna.context :as context])
  ;(:import  [dyna.base_protocols MemoizationContainer])
  )

(defsimpleinterface IMemoContainer
  (get-value-for-key [key])
  (compute-value-for-key [key])
  (refresh-memo-table []))

;; this container can be modified
(deftype MemoContainer [Rconditional+Rmemo  ;; is an atom that will get updated
                        Rorig+assumption-upstream ;; an atom which gets updated when this
                        ;; Rorig
                        ;; ^:unsynchronized-mutable assumption-upstream ;; the upstream is the same.  This should be modifable, such that we can reset it later
                        assumption-self ;; the for when this changes.  This should not become "invalid" rather it just sends notifications of changes
                        memo-config ;; there needs to be some way to know what variables are "required" for the unk memo kind
                        ]
  Watcher
  (notify-invalidated! [this watching]
    (let [Rorig+assumpt-val @Rorig+assumption-upstream
          [Rorig upstream] Rorig+assumpt-val]
      (if (identical? upstream watching)
        ;; then this needs to do a refresh of the memo table
        ;; and this needs to reconstruct the origional values
        (let [term-name (:memo-for-term memo-config)]
          (if (nil? term-name)
            (invalidate! assumption-self) ;; unsure how to update this memo table, so we are just going to mark it as invalid, and let that propagate
            (let [[orig-rexpr-assumpt orig-rexpr] (compute-with-assumption
                                                   (user-rexpr-combined-no-memo (get-user-term term-name)))
                  cas-result (compare-and-set! Rorig+assumption-upstream
                                               Rorig+assumpt-val
                                               [orig-rexpr orig-rexpr-assumpt])]
              (assert cas-result)
              (add-watcher! orig-rexpr-assumpt this)
              (system/push-agenda-work #(refresh-memo-table this))
              ;(debug-repl "got invalidated notified")
              )))
        (do
          (debug-repl "unknown assumption invalidated")
          (???)))))
  (notify-message! [this watching message]
    ;; just refresh the memo table here
    (system/push-agenda-work #(refresh-memo-table this))
    ;(debug-repl "got message notified")
    ;(???)
    )

  IMemoContainer
  (get-value-for-key [^MemoContainer this key]
    (context/bind-no-context
     (let [cond-memo Rconditional+Rmemo
           cond-memo-val @cond-memo
           [cond memo] cond-memo-val
           check-ctx (context/make-nested-context-memo-conditional cond)
           check-conditional (context/bind-context check-ctx
                                                   (simplify (make-conjunct [key cond])))]
       (if (is-non-empty-rexpr? check-conditional)
         (do
           (depend-on-assumption assumption-self)
           memo) ;; then the memo table contains this value, so it needs to just apply the values of the key to get the right output
         (if (is-empty-rexpr? check-conditional)
           (compute-value-for-key this key)
           ;; nil indicating that the memo could not be computed, so this is going to have to delay
           nil)))))
  (compute-value-for-key [^MemoContainer this key]
    (assert (= :unk (:memo-mode memo-config)))
    (let [[Rorig upstream-assumpt] @Rorig+assumption-upstream
          memo-addition (simplify-top (make-conjunct [key Rorig]))
          cond-memo Rconditional+Rmemo
          new-cond-memo-val @cond-memo
          [new-cond new-memo] new-cond-memo-val
          recheck-condition (context/bind-context (context/make-nested-context-memo-conditional new-cond)
                                                  (simplify (make-conjunct [key new-cond])))]
      (if (is-empty-rexpr? recheck-condition)
        ;; then we can add the new memo back into the memo table
        (let [cas-result (compare-and-set! cond-memo
                                           new-cond-memo-val
                                           [(make-disjunct [new-cond key])
                                            (make-disjunct [new-memo memo-addition])])]
          (assert cas-result) ;; this is going to have to recompute or something, as the memoized expression has changed
          ;(debug-repl "nm")
          memo-addition)
        (do
          (debug-repl "failed to save result into the memo table")
          ;; then this must mean that hte result is already contained in the memo table
          ;; in which case
          (???)))))
  (refresh-memo-table [this]
    (assert (is-valid? assumption-self))
    (let [memo-value @Rconditional+Rmemo
          [cond memo] memo-value
          [Rorig assumption-upstream] @Rorig+assumption-upstream]
      (assert (is-valid? assumption-upstream)) ;; if this is not valid, then we  should rebuild the origional expression
      (let [[orig-result-assumpt orig-result] (context/bind-no-context
                                              (compute-with-assumption
                                               (simplify-top (make-conjunct [cond Rorig]))))]
        (when (not= orig-result memo)
          ;; then we need to save the memo in to the table, and signal that an event happened
          (add-watcher! orig-result-assumpt this)
          (if (compare-and-set! Rconditional+Rmemo memo-value [cond orig-result])
            (do ;; the update was successful
              (send-message! assumption-self
                             {:kind :refresh-table
                              :table this
                              :old-memo memo
                              :new-memo orig-result}))
            (do ;; the update was not successful
              (system/push-agenda-work #(refresh-memo-table this))
              (debug-repl "failed to save refresh of memo table")
              (???))))))))

(defmethod print-method MemoContainer [^MemoContainer this ^java.io.Writer w]
  (.write w (str @(.Rconditional+Rmemo this) "\n" @(.Rorig+assumption-upstream this))))

(def-base-rexpr memoized-rexpr [:unchecked memoization-container
                                :var-map variable-name-mapping])

(def-rewrite
  :match (memoized-rexpr (:unchecked ^dyna.memoization.MemoContainer memoization-container) (:unchecked variable-name-mapping))
  (let [memo-config (.memo-config memoization-container)]
    (when (or (= :null (:memo-mode memo-config))
              (every? is-ground? (map variable-name-mapping (:required-ground-variables memo-config))))
      (let [key (case (:memo-mode memo-config)
                  :unk (make-conjunct (doall (map #(make-no-simp-unify % (get variable-name-mapping %))
                                             (:required-ground-variables memo-config))))
                  :null (make-multiplicity 1))
            memo-rexpr (get-value-for-key memoization-container key)
            res (simplify (remap-variables memo-rexpr variable-name-mapping))]
        res))))


#_(def-rewrite
  :match (memoized-rexpr (:unchecked ^dyna.memoization.MemoContainer memoization-container) (:unchecked variable-name-mapping))
  (let [memo-config (.memo-config memoization-container)]
    ;; this should check if the mode is unk or if this is the value which is represented
    (when (or (= :null (:memo-mode memo-config))
              (every? is-ground? (map variable-name-mapping (:required-ground-variables memo-config))))
      (let [cond-memo (.Rconditional+Rmemo memoization-container)
            cond-memo-val @cond-memo
            [cond memo] cond-memo-val
            check-ctx (context/make-nested-context-memo-conditional cond) ;; this can read from the current context for the variable names
            check-conditional (context/bind-context check-ctx
                                                    (simplify (remap-variables cond variable-name-mapping)))]
        (if (is-non-empty-rexpr? check-conditional)
          ;; this is contained in the memo table, so we can just return the table which will get the relevant entries
          (simplify (remap-variables memo variable-name-mapping))
          (when (is-empty-rexpr? check-conditional) ;; if it is nither empty or non-empty, then we can't determine if it should return or not, need
            (assert (= :unk (:memo-mode memo-config)))
            (let [memo-keys (make-conjunct (doall (map #(make-no-simp-unify % (get variable-name-mapping %))
                                                       (:required-ground-variables memo-config))))
                  memo-addition (simplify-top (make-conjunct [memo-keys (.Rorig memoization-container)]))
                  new-cond-memo-val @cond-memo]
              (if (identical? new-cond-memo-val cond-memo-val)
                (let [cas-result (compare-and-set! cond-memo
                                               cond-memo-val
                                               [(make-disjunct [cond memo-keys])
                                                (make-disjunct [memo memo-addition])])]
                  (assert cas-result)
                  (simplify (remap-variables memo-addition variable-name-mapping)))
                ;; if it is different, then that means that there might be a new expression which was added
                (let [[cond2 memo2] new-cond-memo-val
                      check-ctx2 (context/make-nested-context-memo-conditional cond2)
                      check-conditional2 (context/bind-context check-ctx2 (simplify (remap-variables cond2 variable-name-mapping)))]
                  (if (is-empty-rexpr? check-conditional2)
                    ;; then the expression is still not memoized, so we can still add it to the expression
                    (let [cas-result (compare-and-set! cond-memo
                                                       new-cond-memo-val
                                                       [(make-disjunct [cond2 memo-keys])
                                                        (make-disjunct [memo2 memo-addition])])
                          ret (simplify (remap-variables memo-addition variable-name-mapping))]
                      (assert cas-result)
                      ;(debug-repl "d2")
                      ret)
                    ;; then there is a new expression which is contained in the memo table that represents this
                    ;; so we should instead return what is in the memo table instead of our previously computed value
                    ;; so that that it will stay consistent
                    (let [ret (simplify (remap-variables memo2 variable-name-mapping))]
                      ;(debug-repl "d1")
                      ret)))))))))))

#_(comment
 (defn refresh-memo-table [^MemoContainer memo-table]
   (assert (is-valid? (.assumption-self memo-table))) ;; otherwise this is already invalidated.  in which case we should stop I suppose??
   (let [memo-value @(.Rconditional+Rmemo memo-table)
         [conditional memo] memo-value
         orig (.Rorig memo-table)
         orig-result (simplify-top (make-conjunct [conditional orig]))]
                                        ;(debug-repl "refresh")
     (when (not= memo orig-result)
       ;; then this needs to set the memo-table to the new value
       (if (compare-and-set! (.Rconditional+Rmemo memo-table) memo-value [conditional orig-result])
         (do ;; meaning that this updated the memo table successfully
           (send-message! (.assumption-self memo-table)
                          {:kind :refresh-table
                           :table memo-table
                           :old-memo memo
                           :new-memo orig-result}))
         (do ;; meaning that somehting else changed the memo table before we
           ;; could refresh this.  If this is something that only partially
           ;; refreshed the values, then that might needs that it trys again.  Though thi smight find itself with
           (system/push-agenda-work #(refresh-memo-table memo-table))
           (debug-repl)
           (???))))
                                        ;(debug-repl "refresh result")
     ;; this needs to upate the R-expr and refresh the assumption
     ;; in the case
                                        ;(???)
     )))


(defn rebuild-memo-table-for-term [term-name]
  (let [[old new] (update-user-term! term-name
                                    (fn [dat]
                                      (assert (contains? #{:null :unk} (:memoization-mode dat)))
                                      (let [[orig-rexpr-assumpt orig-rexpr] (compute-with-assumption
                                                                             ;; this could call simplify on this term
                                                                             (user-rexpr-combined-no-memo dat))
                                            orig-vars (exposed-variables orig-rexpr)
                                            unk-required-vars (into #{} (filter #(not= (make-variable (str "$" (:arity term-name))) %) orig-vars))
                                            mem-container (MemoContainer. (atom [(case (:memoization-mode dat)
                                                                                   :unk (make-multiplicity 0)
                                                                                   :null (make-multiplicity 1))
                                                                                 (make-multiplicity 0)]) ;; the container should always start empty, and then we have to recheck this memo
                                                                          (atom [orig-rexpr orig-rexpr-assumpt])
                                                                          ;(make-invalid-assumption) ;; this is _not_ consistent with the upstream
                                                                          (make-assumption)
                                                                          {:memo-mode (:memoization-mode dat)
                                                                           ;; in the case of unk memos, some of the variables _must_ be ground before we attempt the lookup, otherwise we dont know if we should store something or wait for more of the
                                                                           :required-ground-variables (if (= :unk (:memoization-mode dat))
                                                                                                        unk-required-vars
                                                                                                        nil)
                                                                           :memo-for-term term-name})]
                                        (add-watcher! orig-rexpr-assumpt mem-container)
                                        (assoc dat
                                               :memoized-rexpr (make-memoized-rexpr mem-container
                                                                                    (into {} (for [k (exposed-variables orig-rexpr)]
                                                                                               [k k])))))))
        new-memos (:memoized-rexpr new)
        old-memos (:memoized-rexpr old)]
    (when (is-memoized-rexpr? new-memos)
      (system/push-agenda-work #(refresh-memo-table (:memoization-container new-memos))))
    (when (is-memoized-rexpr? old-memos)  ;; signal to the old container that it is junked
      (invalidate! (.assumption (:memoization-container old-memos))))
    ;(debug-repl "rebuild")
    ))

;; there should be something that is more "flexible" for setting something as memoized
;; but this is going
(defn set-user-term-as-memoized [term-name mode]
  (assert (contains? #{:unk :null :none} mode))
  (let [[old new] (update-user-term! term-name
                                    (fn [dat]
                                      ;; this is going to need create the memo table and set up the assumptions that this is the result
                                      ;; if there is something that is memoized, then this should
                                      (let [d1 (assoc dat
                                                      :memoization-mode mode
                                                      :memoized-rexpr (make-multiplicity 0))
                                            d2 (case mode
                                                 :unk (assoc d1
                                                             :is-memoized-unk (make-assumption)
                                                             :is-memoized-null (make-invalid-assumption)
                                                             :is-not-memoized-null (make-assumption))
                                                 :null (assoc d1
                                                             :is-memoized-unk (make-invalid-assumption)
                                                             :is-memoized-null (make-assumption)
                                                             :is-not-memoized-null (make-invalid-assumption))
                                                 :none (assoc d1
                                                             :is-memoized-unk (make-invalid-assumption)
                                                             :is-memoized-null (make-invalid-assumption)
                                                             :is-not-memoized-null (make-assumption)
                                                             :memoized-rexpr nil))]
                                        d2)))]
    (doseq [k (keys new)]
      (let [ov (get old k)
            nv (get new k)]
        (when (and (not (identical? ov nv))
                   (satisfies? Assumption ov))
          (when (nil? ov) (debug-repl))
          (invalidate! ov))))
    (when (contains? #{:null :unk} mode)
      (system/push-agenda-work #(rebuild-memo-table-for-term term-name)))))


(defn print-memo-table [term-name]
  (let [term (get-user-term term-name)]
    (if (nil? term)
      (println "term " term-name " not found")
      (do
        (println "~~~~~~~~~~~~~~Memo table~~~~~~~~~~~~~~~~")
        (println term-name)
        (println "mode: " (:memoization-mode term))
        (println "table: " (:memoized-rexpr term))
        (println "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")))))
