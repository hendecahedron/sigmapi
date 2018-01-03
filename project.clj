(defproject hendekagon/sigmapi "0.0.1"
  :description "SigmaPi"
  :url "http://celeriac.net/"
  :license {:name "GNU LGPLv3 "
            :url "http://www.gnu.org/copyleft/lesser.html"}
  :source-paths ["src"]
  :dependencies
    [
      [org.clojure/clojure "1.9.0-alpha14"]
      [aysylu/loom "1.0.0"]
      [net.mikera/core.matrix "0.60.3"]
     ;[uncomplicate/neanderthal "0.17.1"]
      [criterium "0.4.4"]]
  :cljsbuild
    {:builds
              [
               {
                :id           "dev"
                :source-paths ["src"]
                :compiler     {
                               :asset-path           "js"
                               :source-map           true
                               :source-map-timestamp true
                               :pretty-print         true
                               :externs              ["externs.js"]
                               :output-to            "public/js/main.js"
                               :output-dir           "public/js"
                               :optimizations        :none
                               :parallel-build       true
                               }
                }
               ]})
