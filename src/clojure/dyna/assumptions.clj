(ns dyna.assumptions
  (:require [dyna.system :as system])
  (:require [dyna.utils :refer :all])
  (:import [java.util WeakHashMap]))

;; any assumption which the current expression depends
(def ^:dynamic *current-watcher*)

(defprotocol Watcher
  (notify-invalidated! [this watching])
  (notify-message! [this watching message]))

(defprotocol Assumption
  (invalidate! [this])
  (is-valid? [this])
  (add-watcher! [this watcher])
  (send-message! [this message]))

(deftype assumption
  [^WeakHashMap watchers
   valid]
  Assumption
  (invalidate! [this]
    (let [[old new] (swap-vals! valid (constantly false))]
      (when (= false old)
        (locking watchers (doseq [w (.keySet watchers)]
                            (notify-invalidated! w this))))))
  (is-valid? [this] @valid)
  (add-watcher! [this watcher]
    (locking watchers
      (if (is-valid? this)
        (.put watchers watcher nil)
        (notify-invalidated! watcher this))))

  (send-message! [this message]
    (locking watchers (doseq [w (.keySet watchers)]
                        (notify-message! w this message))))

  Watcher
  (notify-invalidated! [this from-watcher] (invalidate! this))
  (notify-message! [this from-watcher message] (???))

  Object
  (toString [this] (str "[Assumption isvalid=" (is-valid? this) " watchers=" (locking (str (.keySet watchers))) "]")))


(deftype reactive-value
  [assumption
   value])


(defmethod print-method assumption [^assumption this ^java.io.Writer w]
  (.write w (.toString this)))

(defn make-assumption []
  (assumption. (WeakHashMap.)                               ; downstream dependents
               (atom true)                                  ; if this is still valid, this is atomic
               ))

(defn make-reactive-value [initial-value]
  (reactive-value. (make-assumption)
                   (atom initial-value)))

(defn depend-on-assumption [assumption & {:keys [hard] :or {hard true}}]
  ;; in this case, we are stating that the current computation would need to get
  ;; redone if the current assumption becomes invalid
  (when (bound? #'*current-watcher*)
    (add-watcher! assumption *current-watcher*)
    ;; check the assumption after adding it might get invalidated inbetween
    (when (not (is-valid? assumption))
      ;; there should be some exception to restart the computation or something
      ;; it would allow for the runtime to check which of the expressions
      (throw (RuntimeException. "attempting to use invalid assumption")))))
