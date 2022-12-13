(ns dyna.memoization-v2
  (:require [dyna.utils :refer :all])
  (:require [dyna.rexpr :refer :all])
  (:require [dyna.system :as system])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.user-defined-terms :refer [update-user-term! user-rexpr-combined-no-memo get-user-term]])
  (:require [dyna.assumptions :refer :all])
  (:require [dyna.context :as context]))

(defsimpleinterface IMemoContainer
  (refresh-memo-table [])
  (compute-value-for-key [key])
  (get-value-for-key [key])
  )

;; this memo container only will be a value that is a single R-expr.  This is
;; the "naive" implementation which will "support everything" because it makes
;; no assumptions about the internal representation of what is getting memoized
(deftype MemoContainerRexpr []
  )

;; this is the efficient implementation of a memo table which uses an
;; associative map from keys to rexpr-values.  The map will be of a subset of
;; the keys which are contained.  If something comes in with an invalidation message, then
(deftype MemoContainerTrie [])

(deftype MemoContainer [memo-config
                        Rmemo ;; atom which contains the
                        ]
  Watcher
  (notify-invalidated! [this watching])
  (notify-message! [this watching message])

  IMemoContainer
  (refresh-memo-table [this]
    (compute-value-for-key this nil))
  (compute-value-for-key [this key]
    (???))
  (get-value-for-key [this key]
    (???)))

(defn- rebuild-memo-table-for-term [term-name]
  )
