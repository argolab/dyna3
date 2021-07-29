(defproject dyna_backend "0.1.0-SNAPSHOT"
  :description "Backend runtime for Dyna built on R-exprs"
  :url "https://github.com/matthewfl/dyna-R"
  :license {:name "LGPL-3.0-or-later WITH Classpath-exception"}
  :dependencies [[org.clojure/clojure "1.10.3"]
                 [org.clojure/tools.namespace "1.1.0"]
                 [aprint "0.1.3"]
                 ;[clj-python/libpython-clj "2.00-beta-22"]
                 [com.clojure-goes-fast/clj-java-decompiler "0.3.0"]]
  :repl-options {:init-ns dyna-backend.core}
  :aot [dyna-backend.interface]
  :source-paths ["src/clojure"]
  :java-source-paths ["src/java"]
  :test-paths ["test"])

