(ns dyna.system
  (:require [dyna.utils :refer [def-tlocal tlocal tbinding]])
  (:import [dyna DynaAgenda IDynaAgendaWork ThreadVar]))

;; variables which control how the system runs

(def check-rexpr-arguments
  false;  (Boolean/parseBoolean (System/getProperty "dyna.check_rexprs_args" "false"))
  )

(def print-rewrites-performed
  (Boolean/parseBoolean (System/getProperty "dyna.print_rewrites_performed" "false")))

(def track-where-rexpr-constructed
  false;  (Boolean/parseBoolean (System/getProperty "dyna.trace_rexpr_construction" "false"))
  )

(def debug-statements
  (Boolean/parseBoolean (System/getProperty "dyna.debug" "true")))

(def status-counters
  dyna.StatusCounters/run_counters
  #_(= "true" (System/getProperty "dyna.status_counters" "true")))

#_(def default-recursion-limit
    ;; now in ThreadVar.java
    (Integer/valueOf (System/getProperty "dyna.recursion_limit" "20")))


#_(def ^:dynamic *auto-run-agenda-before-query*
  (Boolean/parseBoolean (System/getProperty "dyna.auto_run_agenda" "true")))
(def-tlocal auto-run-agenda-before-query)

(def ^{:redef true} use-optimized-rexprs
  (Boolean/parseBoolean (System/getProperty "dyna.optimized_rexprs" "true")))
(def-tlocal use-optimized-disjunct)
;(def-tlocal use-optimized-rexprs)

#_(def ^:dynamic *generate-new-jit-rewrites* false)
(def-tlocal generate-new-jit-rewrites)
(def-tlocal generate-new-jit-states)

;; terms which are included by the system.  These will get automattically
;; replaced once the objects are created in the first place these should not be
;; recursive statements or anything
(def system-defined-user-term (atom {}))

;; terms which are also like the system defined user terms, but these are
;; defined by the user using `:-make_system_term a/1.` These are assocated with
;; the current running dyna system, so it is marked as dynamic
#_(def ^:dynamic globally-defined-user-term (atom {}))
(def-tlocal globally-defined-user-term)

;; anytime that a user definition changes, there should be a corresponding
;; assumption which changes, there is going to need to be some atomic function
;; which is going to change
;(def ^:dynamic user-defined-assumptions (atom {}))

;; expressions which are defined by the user
#_(def ^:dynamic user-defined-terms (atom {}))
(def-tlocal user-defined-terms)

;; a map of which terms are exported from a file
#_(def ^:dynamic user-exported-terms (atom {}))
(def-tlocal user-exported-terms)

;; a set of java.net.URL objects of which files have been imported into the runnint system
#_(def ^:dynamic imported-files (atom #{}))
(def-tlocal imported-files)

;; the agenda is a priority queue of the work as well as a hash set which tracks what is already pushed.
;; Parallel processing could work by just processing work from the agenda in parallel.  If there is multiple
#_(def ^:dynamic work-agenda (DynaAgenda.))
(def-tlocal work-agenda)

;; how many times a user-defined function can be expanded before we stop expanding
#_(def ^:dynamic user-recursion-limit (atom default-recursion-limit))  ;; this does not need to really be an atom?  it can just hold the value directly
(def-tlocal user-recursion-limit)

;; if a query is made, where it should get printed to
#_(def ^:dynamic query-output println)
(def-tlocal query-output)

;; in the parser expressions like `$0`, `$1`, .... can be replaced with an R-expr.  This is done via this handler
;; this is used in the case of using the system like a database
#_(def ^:dynamic parser-external-value (fn [index]
                                       (throw (RuntimeException. "External value handler not set"))))
(def-tlocal parser-external-value)


;; metadata associated with all of the different types of dynabases
#_(def ^:dynamic dynabase-metadata (atom {}))
(def-tlocal dynabase-metadata)

;; this should ensure that there are system-defined-user-terms also.  could have some flag which is "system is inited" and that it would parse
;; the prelude in the case that it wasn't already inited or something?  It would want for
(defn make-new-dyna-system []
  {:globally-defined-user-term (atom {})
   :user-defined-terms (atom {})
   :user-exported-terms (atom {})
   :imported-files (atom #{})
   :work-agenda (DynaAgenda.)
   :user-recursion-limit (atom ThreadVar/default_recursion_limit)
   :query-output println
   :system-is-inited (atom false)})

#_(defn copy-dyna-system [system]
  ;; this should check that the agenda is empty? Or will have that we need to copy the agenda
  (merge (into {} (for [[k v] system]
                    (if (instance? clojure.lang.Atom v)
                      [k (atom @v)]
                      [k v])))
         {:work-agenda (DynaAgenda. ^DynaAgenda (:work-agenda system))}))

#_(def ^:dynamic *dyna-active-system* nil)
(def-tlocal dyna-active-system)

(defmacro run-under-system [system & args]
  `(let [state# ~system]
     (tbinding [dyna-active-system state#
               user-defined-terms (:user-defined-terms state#)
               user-exported-terms (:user-exported-terms state#)
               imported-files (:imported-files state#)
               work-agenda (:work-agenda state#)
               user-recursion-limit (:user-recursion-limit state#)
               query-output (:query-output state#)
               globally-defined-user-term (:globally-defined-user-term state#)]
       (when-not @(:system-is-inited state#)
         ((find-var 'dyna.core/init-system))
         (reset! (:system-is-inited state#) true))
       ~@args)))

(defn push-agenda-work [work]
  (if (instance? IDynaAgendaWork work)
    #_(if (= (.priority ^IDynaAgendaWork work) ##Inf)
      (.run ^IDynaAgendaWork work))
    (.push_work ^DynaAgenda (tlocal work-agenda) work) ;; if something is inf, it should just get popped first, there is no need to run it during the pushing stage, which might end up in weird orderings of the tasks
    (.push_work ^DynaAgenda (tlocal work-agenda) (reify IDynaAgendaWork
                                            (run [this] (work))
                                            ;; there should be some fixed priority configured for which
                                            ;; internal tasks run at.  Then some stuff could run before it
                                            ;; when it wants, but the internal stuff should probably be
                                            ;; let to run first?
                                            (priority [this] 1e16)))))

(defn run-agenda []
  (.process_agenda ^DynaAgenda (tlocal work-agenda)))

(defn maybe-run-agenda []
  (when (tlocal *auto-run-agenda-before-query*)
    (run-agenda)))

(defmacro converge-agenda [& body]
  ;; rerun the query in the case that there is work on the agenda
  ;; this can invoke the expression multiple times until it is fully done
  `(let [f# (fn [] ~@body)]
     (loop []
       (run-agenda)
       (let [r# (f#)]
         (if (.is_done ^DynaAgenda (tlocal work-agenda))
           r#
           (do
             (println "DEBUGGING Rerunning because agenda work")
             (recur)))))))

(defn is-agenda-converged? []
  (.is_done ^DynaAgenda (tlocal work-agenda)))

(defn should-stop-processing? []
  (when (Thread/interrupted)
    (throw (InterruptedException.))))
