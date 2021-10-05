(ns dyna.assumptions
  (:require [dyna.system :as system]))

;; any assumption which the current expression depends
(def ^:dynamic *current-watcher*)

(defprotocol Watcher
  (notify-invalidated! [this watching]))

(defprotocol Assumption
  (invalidate! [this])
  (is-valid? [this])
  (add-watcher! [this watcher]))

(deftype assumption
  [watchers
   valid]
  Assumption
  (invalidate! [this]
    (let [[old new] (swap-vals! valid (constantly false))]
      (when (= false old)
        (doseq [w @watchers]
          (notify-invalidated! w this)))))
  (is-valid? [this] @valid)
  (add-watcher! [this watcher]
    (swap! watcher conj watcher))

  Watcher
  (notify-invalidated! [this from-watcher] (invalidate! this))

  Object
  (toString [this] (str "[Assumption isvalid=" (is-valid? this) " watchers=" @watchers "]")))

(defmethod print-method assumption [^assumption this ^java.io.Writer w]
  (.write w (.toString this)))


;(defmulti print-method assumption [this ^java.io.Writer w]
;          (.write w (str "(assumption " (is-valid? this) ")")))

(defn make-assumption []
  (assumption. (atom #{})                                   ; downstream dependents
               (atom true)                                  ; is still valid, maybe could be atomic boolean?
               ))

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


;; there should be some original R-expr which is the thing that the assumption
;; can rederive itself from in the case that the assumption is invalidated.
;; That would allow it relook up which expressions it came from.  That
;; assumption would then gather which of the expressions might need to change


;; also would mean that there is some kind of "changable" R-expr which is built
;; into the assumption system.

;; the call expression would allow for it to somehow depend on something



;; this would have that there are some expressions
;; (def-base-rexpr assumption-wrapper
;;   [:assumption assumption
;;    :rexpr expression])

;; (def-rewrite
;;   :match (asusmption-wrapper assumption (:rexpr R))
;;   :run-at :standard
;;   (if (is-valid? assumption)
;;     (make-assumption-wrapper assumption (simplify R))
;;     ;; this is going to have to somehow identify what the new expression is.  If there is something tha t
;;     (assert false) ; this is going to need to somehow handle that there are expressions which
;;     )
;;   )

(defn make-assumption-wrapper [x] (assert false))
