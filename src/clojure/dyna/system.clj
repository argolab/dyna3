(ns dyna.system
  (:import [dyna DynaAgenda IDynaAgendaWork]))

;; variables which control how the system runs

(def check-rexpr-arguments
  (= "true" (System/getProperty "dyna.check_rexprs_args" "true")))

(def print-rewrites-performed
  (= "true" (System/getProperty "dyna.print_rewrites_performed" "false")))

(def track-where-rexpr-constructed
  (= "true" (System/getProperty "dyna.trace_rexpr_construction" "true")))

(def debug-statements
  (= "true" (System/getProperty "dyna.debug" "true")))

(def default-recursion-limit
  (Integer/valueOf (System/getProperty "dyna.recursion_limit" "20")))


;; terms which are included by the system.  These will get automattically
;; replaced once the objects are created in the first place these should not be
;; recursive statements or anything
(def system-defined-user-term (atom {}))

;; terms which are also like the system defined user terms, but these are
;; defined by the user using `:-make_system_term a/1.` These are assocated with
;; the current running dyna system, so it is marked as dynamic
(def ^:dynamic globally-defined-user-term (atom {}))

;; anytime that a user definition changes, there should be a corresponding
;; assumption which changes, there is going to need to be some atomic function
;; which is going to change
;(def ^:dynamic user-defined-assumptions (atom {}))

;; expressions which are defined by the user
(def ^:dynamic user-defined-terms (atom {}))

;; a map of which terms are exported from a
(def ^:dynamic user-exported-terms (atom {}))

(def ^:dynamic imported-files (atom #{}))

;; the agenda of pending work.  When an assumption is invalidated, this will want to push the work onto this object
;; this should probably be a queue type rather than just a set, also some priority function will want to be constructed
;; for this also
(def ^:dynamic work-agenda (DynaAgenda.)) ;; this should really be a priority quieue instead of just a set

;; how many times a user-defined function can be expanded before we stop expanding
(def ^:dynamic user-recursion-limit (atom default-recursion-limit))  ;; this does not need to really be an atom?  it can just hold the value directly

;; if a query is made, where it should get printed to
(def ^:dynamic query-output println)

(def ^:dynamic debug-on-assert-fail true)

;; metadata associated with all of the different types of dynabases
(def ^:dynamic dynabase-metadata (atom {}))

;; this should ensure that there are system-defined-user-terms also.  could have some flag which is "system is inited" and that it would parse
;; the prelude in the case that it wasn't already inited or something?  It would want for
(defn make-new-dyna-system []
  {:globally-defined-user-term (atom {})
   :user-defined-terms (atom {})
   :user-exported-terms (atom {})
   :imported-files (atom #{})
   :work-agenda (DynaAgenda.)
   :user-recursion-limit (atom default-recursion-limit)
   :query-output println
   :system-is-inited (atom false)
   })


(defmacro run-under-system [system & args]
  `(let [state# ~system]
     (binding [user-defined-terms (:user-defined-terms state#)
               user-exported-terms (:user-exported-terms state#)
               imported-files (:imported-files state#)
               work-agenda (:work-agenda state#)
               user-recursion-limit (:user-recursion-limit state#)
               query-output (:query-output state#)
               globally-defined-user-term (:globally-defined-user-term state#)]
       (when-not @(:system-is-inited state#)
         ((var-get #'dyna.core/init-system))
         (reset! (:system-is-inited state#) true))
       ~@args)))

(defn push-agenda-work [work]
  (.push_work ^DynaAgenda work-agenda
              (if (instance? IDynaAgendaWork work)
                work
                (reify IDynaAgendaWork
                  (run [this] (work))
                  ;; there should be some fixed priority configured for which
                  ;; internal tasks run at.  Then some stuff could run before it
                  ;; when it wants, but the internal stuff should probably be
                  ;; let to run first?
                  (priority [this] 1e16)))))
