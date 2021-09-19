(ns dyna-backend.user-defined-terms
  (:require [dyna-backend.utils :refer :all])
  (:require [dyna-backend.rexpr :refer [make-variable]])
  (:require [dyna-backend.system :as system])
  (:require [dyna-backend.assumptions :refer [invalidate! make-assumption]]))


;; these are user defs which are always present
;; (def base-user-defs (atom {}))

(defmacro def-user-term [name arity rexpr]
  ;; define a user level term from internal
  (if (not (string? name))
    `(do ~@(for [x name]
             `(def-user-term ~x ~arity ~rexpr)))
    `(swap! system/system-defined-user-term assoc ~[name arity]
            (let [~'self (make-variable "$self")] ;; the self variable can be the current dynabase which is calling this expression, most builtin don't care
              (let ~(vec
                     (mapcat #(list (symbol (str "v" %))
                                    `(make-variable ~(str "$" %)))
                             (range (+ 1 arity))))
                ~rexpr)))))

(defn user-add-to-user-expression [source-file dynabase name arity rexpr]
  (let [object-name (merge {:name name
                            :arity arity}
                           (when (nil? dynabase) ;; when there is a dynabase, then this requires having to merge across different values
                             {:source-file source-file}))
        value {:source-file source-file
               :dynabase dynabase
               :rexpr rexpr}]
    ;; add the object to the user-defined-terms
    (swap! system/user-defined-terms (fn [old]
                                       (let [v (get old object-name)]
                                         (assoc old object-name (conj v value)))))
    ;; invalidate the assumption that this values has not changed
    ;; we do the invalidation /after/ we have already made the change, a the reader has to first get the assumption
    ;; whereas the writer has to first write the object
    (swap! system/user-defined-assumptions (fn [old]
                                      (let [v (get old object-name)]
                                        (if v (invalidate! v))
                                        (assoc old object-name (make-assumption)))))
    )
  (debug-repl)
  (assert false)

  ;; if there is a dynabase, then this needs to be "global", otherwise we can get away with just dispatching on the source file info
  ;; if there are

  ;; define to the user level term from the external program
  )

;; (defn lookup-user-def [name arity]
;;   (get base-user-defs [name arity]))
