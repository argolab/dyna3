(ns dyna-backend.core
  (:require [aprint.core :refer [aprint]])
  (:require [clojure.tools.namespace.repl :refer [refresh]])

  (:require [dyna-backend.utils :refer :all])
  (:require [dyna-backend.rexpr :refer :all])

  )


;; (require '[])
;;(use 'aprint.core)



(def ^:dynamic *current-rewrites* nil)  ;; dynamic means that this can be set using (binding ...), and this will be local to the current thread
(def ^:dynamic *current-context* nil)
