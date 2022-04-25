(ns dyna.memoization
  (:require [dyna.utils :refer :all])
  (:require [dyna.rexpr :refer :all])
  (:require [dyna.system :as system])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.user-defined-terms :refer [update-user-term user-rexpr-combined-no-memo]])
  (:require [dyna.assumptions :refer :all])
  (:require [dyna.context :as context])
  ;(:import  [dyna.base_protocols MemoizationContainer])
  )

;; this is going to have to have some way in which the expression can be updated
;; in the case that the assumption is updated, then it would have that there are
;; some expressions which are represented with
;; (comment
;;   (def-base-rexpr memoized-rexpr [:rexpr Rmemo ;; the R-expr which contains the memoized
;;                                   :rexpr Rorig
;;                                   :unchecked assumption])


;;   (def-rewrite
;;     :match memoized-rexpr (:rexpr Rmemo) (:rexpr Rorig))

;;   )

(definterface IMemoContainer
  (get_memo [this]))

;; the values in the container should have that this
;; the conditional and memo will need to be updateable together.  I suppose that means that
(deftype MemoContainer [Rconditional+Rmemo
                        Rorig
                        assumption
                        memo-config ;; there needs to be some way to know what variables are "required" for the unk memo kind
                        ]

  Watcher
  (notify-invalidated! [this watching]
    (debug-repl "got invalidated notified")
    (???))
  (notify-message! [this watching message]
    (debug-repl "got message notified")
    (???)))

;; (defmethod print-method MemoContainer [^MemoContainer this ^java.io.Writer w]
;;   (.write w ))

;; (def-base-rexpr memoized-rexpr [
;;                                 ])

(defn make-memoized-container [rexpr assumptions]
  ;; (MemoContainer.
  ;;  (atom [(make-multiplicity 0) (make-multiplicity 0)])
  ;;  rexpr
  ;;  (make-assumption))
  ;; this is going to have make the memo table dependent on the assumptions which are listed
  ;; for the assumptions which
  )

;; there are no R-expr "children" of this expression as it has to direct through
;; the other expression
;; maybe there should be some cache which would be for the conditional if-statement part of this?
;; but this is going to have to determine if there is something which
(def-base-rexpr memoized-rexpr [:unchecked memoization-container
                                :unchecked variable-name-mapping]
  (get-variables [this] (into #{} (filter is-variable? (vals variable-name-mapping))))
  (remap-variables [this variable-map]
                   (make-memoized-rexpr memoization-container
                                        (into {} (for [[k v] variable-name-mapping]
                                                   [k (get variable-map v v)]))))
  (remap-variables-handle-hidden [this variable-map]
                                 (remap-variables this variable-map)))

(def-rewrite
  :match (memoized-rexpr (:unchecked ^dyna.memoization.MemoContainer memoization-container) (:unchecked variable-name-mapping))
  (let [memo-config (.memo-config memoization-container)]
    ;; this should check if the mode is unk or if this is the value which is represented
    (when (or (= :null (:memo-mode memo-config))
              (every? is-ground? (map variable-name-mapping (:required-ground-variables memo-config))))
      (let [cond-memo (.Rconditional+Rmemo memoization-container)
            cond-memo-val @cond-memo
            [cond memo] cond-memo-val
            check-ctx (context/make-nested-context-memo-conditional cond)
            check-conditional (context/bind-context check-ctx
                                                    (simplify cond))]
        (if (is-non-empty-rexpr? check-conditional)
          ;; this is contained in the memo table, so we can just return the table which will get the relevant entries
          (simplify (remap-variables memo variable-name-mapping))
          (do
            (assert (= :unk (:memo-mode memo-config)))
            (let [memo-keys (make-conjunct (doall (map #(make-no-simp-unify % (get variable-name-mapping %))
                                                       (:required-ground-variables memo-config))))
                  memo-addition (simplify-top (make-conjunct [memo-keys (.Rorig memoization-container)]))
                  cas-result (compare-and-set! cond-memo
                                               cond-memo-val
                                               [(make-disjunct [cond memo-keys])
                                                (make-disjunct [memo memo-addition])])]
              ;(debug-repl "matching against a memoized expression")
              (assert cas-result)
              (simplify (remap-variables memo-addition variable-name-mapping))
              ;; if the result is not contained in the table, then we need to compute if there is something
              )))
        ;; this is going to have to check if the conditional matches against the
        ;; expression in the case that the conditional does not match, then it would
        ;; have to fall through to the origional expression
        ))))

(defn refresh-memo-table [^MemoContainer memo-table]
  (assert (is-valid? (.assumption memo-table))) ;; otherwise this is already invalidated.  in which case we should stop I suppose??
  (let [memo-value @(.Rconditional+Rmemo memo-table)
        [conditional memo] memo-value
        orig (.Rorig memo-table)
        orig-result (simplify-top (make-conjunct [conditional orig]))]
    ;(debug-repl "refresh")
    (when (not= memo orig-result)
      ;; then this needs to set the memo-table to the new value
      (if (compare-and-set! (.Rconditional+Rmemo memo-table) memo-value [conditional orig-result])
        (do ;; meaning that this updated the memo table successfully
          (send-message! (.assumption memo-table)
                         {:kind :refresh-table
                          :table memo-table
                          :old-memo memo
                          :new-memo orig-result}))
        (do ;; meaning that somehting else changed the memo table before we
            ;; could refresh this.  If this is something that only partially
            ;; refreshed the values, then that might needs that it trys again.  Though thi smight find itself with
          (system/push-agenda-work #(refresh-memo-table memo-table))
          (???))))
    ;(debug-repl "refresh result")
    ;; this needs to upate the R-expr and refresh the assumption
    ;; in the case
    ;(???)
    ))


(defn rebuild-memo-table-for-term [term-name]
  (let [[old new] (update-user-term term-name
                                    (fn [dat]
                                      (assert (contains? #{:null :unk} (:memoization-mode dat)))
                                      (let [orig-rexpr (user-rexpr-combined-no-memo dat)
                                            orig-vars (exposed-variables orig-rexpr)
                                            unk-required-vars (into #{} (filter #(not= (make-variable (str "$" (:arity term-name))) %) orig-vars))
                                            mem-container (MemoContainer. (atom [(case (:memoization-mode dat)
                                                                                   :unk (make-multiplicity 0)
                                                                                   :null (make-multiplicity 1))
                                                                                 (make-multiplicity 0)]) ;; the container should always start empty, and then we have to recheck this memo
                                                                          orig-rexpr
                                                                          (make-assumption)
                                                                          {:memo-mode (:memoization-mode dat)
                                                                           ;; in the case of unk memos, some of the variables _must_ be ground before we attempt the lookup, otherwise we dont know if we should store something or wait for more of the
                                                                           :required-ground-variables (if (= :unk (:memoization-mode dat))
                                                                                                        unk-required-vars
                                                                                                        nil)})]
                                        (add-watcher! (:def-assumption dat) (.assumption mem-container))
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
  (let [[old new] (update-user-term term-name
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
