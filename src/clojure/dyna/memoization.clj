(ns dyna.memoization
  (:require [dyna.utils :refer :all])
  (:require [dyna.rexpr :refer :all])
  (:require [dyna.system :as system])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.user-defined-terms :refer [update-user-term user-rexpr-combined-no-memo]])
  (:require [dyna.assumptions :refer :all])
  (:import  [dyna.base_protocols MemoizationContainer]))

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
                        assumption]

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
  (MemoContainer.
   (atom [(make-multiplicity 0) (make-multiplicity 0)])
   rexpr
   (make-assumption))
  ;; this is going to have make the memo table dependent on the assumptions which are listed
  ;; for the assumptions which
  )

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
  :match (memoized-rexpr (:unchecked memoization-container) (:unchecked variable-name-mapping))
  (do
    (debug-repl "matching against a memoized expression")))

(defn refresh-memo-table [^MemoContainer memo-table]
  (assert (is-valid? (.assumption memo-table))) ;; otherwise this is already invalidated.  in which case we should stop I suppose??
  (let [memo-value @(.Rconditional+Rmemo memo-table)
        [conditional memo] memo-value
        orig (.Rorig memo-table)
        orig-result (simplify-top (make-conjunct [conditional orig]))]
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
                                            mem-container (MemoContainer. (atom [(case (:memoization-mode dat)
                                                                                   :unk (make-multiplicity 0)
                                                                                   :null (make-multiplicity 1))
                                                                                 (make-multiplicity 0)]) ;; the container should always start empty, and then we have to recheck this memo
                                                                          orig-rexpr
                                                                          (make-assumption))]
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
    (debug-repl "rebuild")))

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
