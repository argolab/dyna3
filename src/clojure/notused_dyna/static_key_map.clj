(ns dyna.static-key-map
  (:require [dyna.utils :refer :all]))

;; A map which will hold all of the

(defn build-map-class [name arguments]
  (let [clsname (gensym 'mapcls)
        argmap (into {} (for [k arguments]
                          [k (gensym (str k))]))
        argvars (vec (vals argmap))
        c `(do
             (ns dyna.static-key-map)
             (deftype ~clsname ~(vec (map #(with-meta % {:unsynchronized-mutable true}) argvars))
               clojure.lang.ITransientAssociative
               (assoc ~'[this key val]
                 (case ~'key
                   ~@(apply concat (for [k v]
                                     [k `(do (set! ~v ~'val)
                                             ~'val)]))
                   (throw (java.util.NoSuchElementException.))))
               (without ~'[this key] (???))
               (persistent ~'[this] ~'this)
               (count ~'[this] ~(count arguments))
               (conj ~'[this [key val]] ~'(assoc this key val))
               (valAt ~'[this key]
                 (case ~'key
                   ~@(apply concat (for [[k v] argmap]
                                     [k v]))
                   (throw (java.util.NoSuchElementException.))))
               (valAt ~'[this key notfound]
                 (case ~'key
                   ~@(apply concat (for [[k v] argmap]
                                     [k v]))
                   notfound))
               Object
               (hashCode [this]
                 (???))
               (equals [this other]
                 (???))
               (toString [this]
                 "TODO: string for static map"))
             {:class ~clsname
              :make-empty (fn [] (~(symbol (str clsname ".")) ~@(for [x argvars] nil)))
              :make (fn [args]
                      (~(symbol (str clsname "."))
                       ~@(for [[k v] argmap]
                           ~(get ~'args ~k))))}
             )]
    (eval c)))

(defn build-map [& args]
  (let [m (apply hash-map args)]
    )
  )
