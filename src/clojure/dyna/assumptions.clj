(ns dyna.assumptions
  (:require [dyna.system :as system])
  (:require [dyna.utils :refer :all])
  (:import [java.util WeakHashMap])
  (:import [dyna InvalidAssumption IDynaAgendaWork]))

;; any assumption which the current expression depends
(def-tlocal current-watcher)
(def-tlocal fast-fail-on-invalid-assumption)

(declare depend-on-assumption
         make-assumption)


(defsimpleinterface Watcher
  (notify-invalidated! [watching])
  (notify-message! [watching message]))

(defsimpleinterface Assumption
  (invalidate! [])
  (is-valid? [])
  (add-watcher! [^dyna.assumptions.Watcher watcher])
  (send-message! [message]))


(deftype assumption-no-message-cls
    [^WeakHashMap watchers
     ^Assumption upstream]
  Assumption
  (invalidate! [this] (invalidate! upstream))
  (is-valid? [this] (is-valid? upstream))
  (add-watcher! [this watcher]
    (assert (instance? Watcher watcher))
    (locking watchers
      (.put watchers watcher nil)
      (when-not (is-valid? this)
        (notify-invalidated! watcher this)
        (when (tlocal fast-fail-on-invalid-assumption);*fast-fail-on-invalid-assumption*
          (throw (InvalidAssumption. "invalid assumption"))))))
  (send-message! [this message]
    (???))

  Watcher
  (notify-invalidated! [this from-watcher]
            (locking watchers
              (doseq [w (.keySet watchers)]
                (notify-invalidated! w this))))
  (notify-message! [this from-watcher message]
    ;; NOP
    )
  Object
  (toString [this] (str "[Assumption-no-message isvalid=" (is-valid? this)
                        " watchers=" (let [w watchers]
                                       (if-not (nil? w)
                                         (locking w) (str (.keySet w))))
                        " id=" (.hashCode this)
                        "])"))
  (hashCode [this] (System/identityHashCode this))
  (equals [this other] (identical? this other)))

(deftype assumption
  [^WeakHashMap watchers
   valid]
  Assumption
  (invalidate! [this]
    (let [[old new] (swap-vals! valid (constantly false))]
      (when (= true old) ;; meaning that this was valid before
        (locking watchers
          (doseq [w (.keySet watchers)]
            (notify-invalidated! w this))
          (.clear watchers)))))
  (is-valid? [this] @valid)
  (add-watcher! [this watcher]
    (locking watchers
      (if (is-valid? this)
        (.put watchers watcher nil)
        (do (notify-invalidated! watcher this)
            (when (tlocal fast-fail-on-invalid-assumption);*fast-fail-on-invalid-assumption*
              (throw (InvalidAssumption. "invalid assumption")))))))

  (send-message! [this message]
    (locking watchers
      (doseq [w (.keySet watchers)]
        (notify-message! w this message))))

  Watcher
  (notify-invalidated! [this from-watcher] (invalidate! this))
  (notify-message! [this from-watcher message] (send-message! this (assoc message
                                                                          :from-upstream (conj (:from-upstream message ())
                                                                                               from-watcher))))

  Object
  (toString [this] (str "[Assumption isvalid=" (is-valid? this)
                        " watchers=" (let [w watchers]
                                       (if-not (nil? w)
                                         (locking w (str (.keySet w)))))
                        " id=" (.hashCode this)
                        "]"))
  (hashCode [this] (System/identityHashCode this))
  (equals [this other] (identical? this other)))

(defn assumption-no-messages [^Assumption x]
  (assert (instance? Assumption x))
  (if (instance? assumption-no-message-cls x)
    x
    (let [r nil;(assumption-no-messages-cls. (WeakHashMap.) x)
          ]
      (add-watcher! x r)
      r)))

(defn add-watcher-function! [^Assumption ass func]  ;; if the variable name matches the class name, bad stuff happens...OMFG what in the world
  (let [f (reify Watcher
            (notify-message! [this assumpt message] (func message))
            (notify-invalidated! [this assumpt] (func nil)))]
    (add-watcher! ass ^Watcher f)))

(defmethod print-method assumption [^assumption this ^java.io.Writer w]
  (.write w (.toString this)))

(defmethod print-dup assumption [^assumption this ^java.io.Writer w]
  ;; in the case that this is duplicated, this is going to have to start as
  ;; invalid, as we are going to have to recheck everything if it was to get reloaded
  (.write w "#=(dyna.assumptions/make-invalid-assumption)"))

(defn make-assumption []
  (assumption. (WeakHashMap.)                               ; downstream dependents
               (atom true)                                  ; if this is still valid, this is atomic and we will only ever set it to false (no false->true)
               ))

(defn make-invalid-assumption []
  (assumption. nil (atom false)))


;; (comment
;;   (defn make-reactive-value [initial-value]
;;     (reactive-value. (atom [(make-assumption)
;;                             initial-value])
;;                             (fn [] nil))))

(defn depend-on-assumption [^Assumption ass ;& {:keys [hard] :or {hard true}}
                            ]
  ;; in this case, we are stating that the current computation would need to get
  ;; redone if the current assumption becomes invalid
  (let [w (tlocal current-watcher)]
    (when-not (nil? w)
      (add-watcher! ass w)
      ;; check the assumption after adding it might get invalidated inbetween
      (when (not (is-valid? ass))
        ;; there should be some exception to restart the computation or something
        ;; it would allow for the runtime to check which of the expressions
        (throw (InvalidAssumption. "attempting to use invalid assumption"))))))

(defmacro bind-assumption [assumpt & body]
  `(tbinding
   [current-watcher ~assumpt]
   ~@body))

(defmacro compute-with-assumption [& body]
  `(loop [assumpt# (make-assumption)]
     (let [[ok# res#]
           (tbinding
            [current-watcher assumpt#
             fast-fail-on-invalid-assumption true]
            #_(binding [;*current-watcher* assumpt#
                      *fast-fail-on-invalid-assumption* true])
            (try
              [true (do ~@body)]
              (catch ~InvalidAssumption err#
                [false false])))]
       (if ok#
         [assumpt# res#]
         (recur (make-assumption))))))
