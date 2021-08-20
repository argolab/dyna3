(ns dyna-backend.assumptions)


(defprotocol Watcher
  (notify-invalidated! [this])
  )

(defprotocol Assumption
  (invalidate! [this])
  (is-valid? [this])
  (add-watcher! [this watcher]))

(deftype assumption
  [watchers
   valid]
  Assumption
  (invalidate! [this]
    (if @valid
      (do
        (swap! valid false)
        (doall (for [w @watchers]
                 (notify-invalidated! w)))
        )))
  (is-valid? [this] @valid)
  (add-watcher! [this watcher]
    (swap! watcher conj watcher))

  Watcher
  (notify-invalidated! [this] (invalidate! this))
  )

;(defmulti print-method assumption [this ^java.io.Writer w]
;          (.write w (str "(assumption " (is-valid? this) ")")))

(defn make-assumption []
  (assumption. (atom #{})                                   ; downstream dependents
               (atom true)                                  ; is still valid, maybe could be atomic boolean?
               ))


;; there should be some original R-expr which is the thing that the assumption
;; can rederive itself from in the case that the assumption is invalidated.
;; That would allow it relook up which expressions it came from.  That
;; assumption would then gather which of the expressions might need to change


;; also would mean that there is some kind of "changable" R-expr which is built
;; into the assumption system.

;; the call expression would allow for it to somehow depend on something



;; this would have that there are some expressions
(def-base-rexpr assumption-wrapper
  [:assumption assumption
   :rexpr expression])
