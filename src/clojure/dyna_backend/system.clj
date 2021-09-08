(ns dyna-backend.system)

(def base-user-expressions (atom {}))

;; expressions which are defined by the user
(def ^:dynamic user-defined-expressions (atom {}))

;; expressions after they have been rewritten or optimized to some degree
(def ^:dynamic optimized-user-defined-expressions (atom {}))

;; memo tables for the current state
(def ^:dynamic memoized-expressions (atom {}))

;; the agenda of pending work.  When an assumption is invalidated, this will want to push the work onto this object
;; this should probably be a queue type rather than just a set, also some priority function will want to be constructed
;; for this also
(def ^:dynamic work-agenda (atom #{})) ;; this should really be a priority queue instead of just a set


(declare get-priority)
(def work-agenda2 {:contains-set (java.util.HashSet.)
                   :contains-queue (java.util.PriorityQueue.
                                    100
                                    (reify java.util.Comparator
                                      (compare ^int [this a b]
                                        (let [pa (get-priority a)
                                              pb (get-priority b)]
                                          (cond (< pa pb) 1
                                                (> pa pb) -1
                                                :else 0)))))
                   :lock (Object.)})

;; how many times a user-defined function can be expanded before we stop expanding
(def ^:dynamic user-recursion-limit (atom 20))

(defn make-new-system-state []
  {:user-expressions (atom {})
   :memoized-expressions (atom {})
   :optimized-expressions (atom {})
   :work-agenda (atom #{})
   })

(defmacro run-under-state [state & args]
  `(binding [user-defined-expressions (:user-expressions ~state)
             optimized-user-defined-expressions (:optimized-expressions ~state)
             memoized-expressions (:memoized-expressions ~state)]
     ~@args
     ))


;; the memozied expressions should be somehow embedded into the

;; this should first have that this is going to find which of the defined expression will be used for something
(defn lookup-named-expression
  ([name] (lookup-named-expression name :all))
  ([name what]
   (or (get memoized-expressions name)
       (get optimized-user-defined-expressions name)
       (get user-defined-expressions name)
       (get base-user-expressions name)))
  )


(defn add-user-atom [name arity rexpr]
  ;; this is going to need to combine the aggregators together.  Which means that this is going to have to figure out where in the expression this should be combined into it
  )


;; (defn set-user-expression [name rexpr]
;;   (swap! user-defined-expressions
;;          (fn [prev]
;;            (let [pv (get prev name)]
;;              (if ()))
;;            (assoc prev name rexpr)
;;            )))
