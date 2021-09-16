(ns dyna-backend.core
  (:require [aprint.core :refer [aprint]])
  (:require [clojure.tools.namespace.repl :refer [refresh]])
  (:require [clj-java-decompiler.core :refer [decompile]])

  (:require [dyna-backend.utils :refer :all])
  (:require [dyna-backend.rexpr :refer :all])
  (:require [dyna-backend.rexpr-builtins :refer :all])
  (:require [dyna-backend.context :as context])
  (:require [dyna-backend.rexpr-dynabase])
                                        ;(:require [dyna-backend.parser_interface :refer [parse-string]])
  (:require [dyna-backend.ast-to-rexpr :refer [parse-string parse-file]])
  )

;; (defn parse-string [str]
;;   (require 'dyna-backend.parser_interface)
;;   ((resolve 'dyna-backend.parser_interface 'parse-string) str))


;; (defn parse-string [str]
;;   (require 'dyna-backend.parser_interface)
;;   (dyna-backend.parser_interface/parse-string str))


;; (require '[])
;;(use 'aprint.core)



;(def ^:dynamic *current-rewrites* nil)  ;; dynamic means that this can be set using (binding ...), and this will be local to the current thread
;(def ^:dynamic *current-context* nil)


(defn main [args]
  (println "this is the main function for dyna"))
