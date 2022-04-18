(ns dyna.memoization
  (:require [dyna.utils :refer :all])
  (:require [dyna.rexpr :refer :all])
  (:require [dyna.base-protocols :refer :all])
  (:import  [dyna.base_protocols MemoizationContainer])
  (:require [dyna.user-defined-terms :refer [update-user-term]]))

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

;; (deftype memo-container [Rconditional
;;                          Rmemo
;;                          Rorig
;;                          assumption])


;; (def-base-rexpr memoized-rexpr [
;;                                 ])

(defn make-memoized-container [rexpr assumptions]
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



;; there should be something that is more "flexible" for setting something as memoized
;; but this is going
(defn set-user-term-as-memoized [term-name mode]
  (assert (contains? #{:unk :null :none} mode))
  (update-user-term term-name
                    (fn [dat]
                      ;; this is going to need create the memo table and set up the assumptions that this is the result
                      ;; if there is something that is memoized, then this should
                      (debug-repl)
                      )))
