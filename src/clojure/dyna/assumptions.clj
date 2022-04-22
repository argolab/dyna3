(ns dyna.assumptions
  (:require [dyna.system :as system])
  (:require [dyna.utils :refer :all])
  (:import [java.util WeakHashMap])
  (:import [dyna InvalidAssumption IDynaAgendaWork]))

;; any assumption which the current expression depends
(def ^:dynamic *current-watcher*)
(def ^:dynamic *fast-fail-on-invalid-assumption* false)

(declare depend-on-assumption
         make-assumption)

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
      (when (= true old) ;; meaning that this was valid before
        (locking watchers (doseq [w (.keySet watchers)]
                            (notify-invalidated! w this))))))
  (is-valid? [this] @valid)
  (add-watcher! [this watcher]
    (locking watchers
      (if (is-valid? this)
        (.put watchers watcher nil)
        (do (notify-invalidated! watcher this)
            (when *fast-fail-on-invalid-assumption*
              (throw (InvalidAssumption. "invlaid assumption")))))))

  (send-message! [this message]
    (locking watchers (doseq [w (.keySet watchers)]
                        (notify-message! w this message))))

  Watcher
  (notify-invalidated! [this from-watcher] (invalidate! this))
  (notify-message! [this from-watcher message] (???))

  Object
  (toString [this] (str "[Assumption isvalid=" (is-valid? this) " watchers=" (let [w watchers]
                                                                               (if-not (nil? w)
                                                                                 (locking w (str (.keySet w))))) "]")))

(defn add-watcher-function! [assumption func]
  (add-watch assumption (reify Watcher
                          (notify-message! [this assumpt message] (func message))
                          (notify-invalidated! [this assumpt] (func nil)))))

;; this can be done via atoms or agents and then there can be a watcher which is
;; added in the case that the value changes
(comment
  (defprotocol Modifable-value
    (set-value! [this value])
    (set-recompute-function! [this func]))

  (deftype reactive-value
      [value
       ^:unsynchronized-mutable recompute-function]
    clojure.lang.IDeref
    (deref [this] (let [[assumption v] @value]
                    (depend-on-assumption assumption)
                    v))

    Modifable-value
    (set-value! [this v]
      (let [[[old-assumpt _] _] (swap-vals! value (fn [old] [(make-assumption)
                                                             v]))]
        (invalidate! old-assumpt)))
    (set-recompute-function! [this function]
      (set! recompute-function function)
      (???))

    Watcher
    (notify-invalidated! [this watching]
      (let [rcf recompute-function]
        (if (nil? rcf)
          ;; then there is no way to recompute
          (set-value! this nil)
          (system/push-agenda-work (fn []
                                     (???)))
          )))
    (notify-message! [this watching message]
      ;; just invalidate and force a clean recompute for now.
      (notify-invalidated! this watching))))


(defmethod print-method assumption [^assumption this ^java.io.Writer w]
  (.write w (.toString this)))

(defn make-assumption []
  (assumption. (WeakHashMap.)                               ; downstream dependents
               (atom true)                                  ; if this is still valid, this is atomic
               ))

(defn make-invalid-assumption []
  (assumption. nil (atom false)))


(comment
  (defn make-reactive-value [initial-value]
    (reactive-value. (atom [(make-assumption)
                            initial-value])
                            (fn [] nil))))

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
