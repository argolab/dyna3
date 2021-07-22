(ns dyna-backend.system)

;; expressions which are defined by the user
(def ^:dynamic user-defined-expressions (atom {}))

;; expressions after they have been rewritten or optimized to some degree
(def ^:dynamic optimized-user-defined-expressions (atom {}))

;; memo tables for the current state
(def ^:dynamic memoized-expressions (atom {}))

;; the agenda of pending work.  When an assumption is invalidated, this will want to push the work onto this object
;; this should probably be a queue type rather than just a set, also some priority function will want to be constructed
;; for this also
(def ^:dynamic work-agenda (atom #{}))

(defn make-new-system-state []
  {
   :user-expressions (atom {})
   :optimized-expressions (atom {})
   :memoized (atom {})

   })

(defmacro run-under-state [state & args]
  `(binding [user-defined-expressions (:user-expressions ~state)
             optimized-user-defined-expressions (:optimized-expressions ~state)
             memoized-expressions (:memoized ~state)]
     ~@args
     ))