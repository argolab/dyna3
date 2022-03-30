;; (ns dyna.agenda
;;   (:require [dyna.system :as system])
;;   (:import (java.util.concurrent Executor)))

;; (defprotocol AgendaItem
;;   (priority [this])
;;   (run [this]))


;; ;; (defn push-agenda [agenda item weight]
;; ;;   (locking (:lock agenda)
;; ;;     (when-not (contains? (:set agenda) item)
;; ;;       (.put (:agenda agenda))
;; ;;       )))

;; ;; (defn run-agenda [agenda]
;; ;;   (let [^java.util.Queue queue (:queue agenda)]
;; ;;     (loop [item (.pop queue)]
;; ;;       (if (nil? item)
;; ;;         nil
;; ;;         (do
;; ;;           ;; this should do the work of running the item that is on the agenda.  This will have some priority

;; ;;           (recur (.pop queue)))
;; ;;         )
;; ;;       ))
;; ;;     )
;; ;;   )

;; (defn run-workers [nthreads]
;;   )
