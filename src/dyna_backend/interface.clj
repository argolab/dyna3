(ns dyna-backend.interface)

(gen-class
  :name "org.dyna.backend_interop"
  :prefix "interop-"
  :state "instance"
  :init "init"
  :main false

  :methods [[make [String "[Lclojure.lang.Obj;"] clojure.lang.Obj]

            ]
  )


;; (defn interop-make-variable [this varname]
;;   `(variable ~varname))

;; (defn interop-make-unify [this a b]
;;   `(unify ~a ~b))

;; (defn interop-make-structure [this name structure]
;;   (concat `(~name) structure))

(defn interop-init []
  ())

(defn interop-make [this name body]
  (concat `(~name) body))

(defn interop-make-variable [this name]
  `(variable ~name))

(defn interop-make-unify [this a b]
  `(= ~a ~b))
