(ns dyna-backend.user-defined-terms
  (:require [dyna-backend.rexpr :refer [make-variable]])
  (:require [dyna-backend.system :refer [base-user-expressions]]))


;; these are user defs which are always present
;; (def base-user-defs (atom {}))

(defmacro def-user-term [name arity rexpr]
  (if (not (string? name))
    `(do ~@(for [x name]
             `(def-user-term ~x ~arity ~rexpr)))
    `(swap! base-user-expressions assoc ~[name arity]
            (let [~'self (make-variable "$self")] ;; the self variable can be the current dynabase which is calling this expression, most builtin don't care
              (let ~(vec
                     (mapcat #(list (symbol (str "v" %))
                                    `(make-variable ~(str "$" %)))
                             (range (+ 1 arity))))
                ~rexpr)))))

;; (defn lookup-user-def [name arity]
;;   (get base-user-defs [name arity]))
