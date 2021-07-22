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

(defmulti print-method assumption [this ^java.io.Writer w]
          (.write w (str "(assumption " (is-valid? this) ")")))

(defn make-assumption []
  (assumption. (atom #{}) (atom true)))
