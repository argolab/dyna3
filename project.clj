(defproject dyna "0.1.0-SNAPSHOT"
  :description "Dyna built on R-exprs"
  :url "https://github.com/matthewfl/dyna-R"
  :license {:name "LGPL-3.0-or-later WITH Classpath-exception"}
  :dependencies [[org.clojure/clojure "1.10.3"]
                 [org.clojure/tools.namespace "1.1.0"]
                 [aprint "0.1.3"]
                 ;[clj-python/libpython-clj "2.00-beta-22"]
                 [com.clojure-goes-fast/clj-java-decompiler "0.3.0"]
                 [org.antlr/antlr4-runtime "4.7.2"]
                 [org.jline/jline "3.20.0"]]
  :repl-options {:init-ns dyna.core}
  ;; :aot [dyna.interface
  ;;       dyna.parser_interface]
  ;;:aot :all
  ;;:aot [dyna.rexpr]
  :source-paths ["src/clojure"]
  :java-source-paths ["target/gen-src" "src/java"]
  :resource-paths ["src/resources"]
  :test-paths ["test"]
  ;;:profiles {:uberjar {:aot :all}}
  ;;:profiles {:uberjar {:aot [dyna.rexpr]}}
  :plugins [[lein-antlr-plugin "0.1.0"]]
  :antlr-src-dir "src/antlr"
  :antlr-dest-dir "target/gen-src"
  :aliases {"compile" ["do" ["antlr"] ["javac"] "compile"]
            "uberjar" ["do" ["compile"] "uberjar"]}
  :main dyna.DynaMain
  :global-vars {;*warn-on-reflection* true  ;; useful for identifying where it uses clojure's reflection which is slow...
                ;*unchecked-math* :warn-on-boxed ;; boxed math is slow9
                }
  )
