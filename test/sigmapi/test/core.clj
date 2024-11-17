(ns sigmapi.test.core
  (:refer-clojure :exclude [+ - * /])
  (:require
    [clojure.test :refer [deftest testing is]]
    [clojure.stacktrace :refer [print-cause-trace]]
    [clojure.test :as test :refer [deftest testing is]]
    [clojure.walk :as w]
    [clojure.math :as maths]
    [clojure.math.combinatorics :as x]
    [clojure.string :as string]
    [clojure.core.matrix :as m]
    [sigmapi.core :as sp :refer :all]
    [sigmapi.impl.symbolic :as s]
    [sigmapi.impl.tensor :as st]
    [sigmapi.impl.core-matrix :as cmt]
    [emmy.env :as e :refer [+ - * / cos sin exp exp2 D]]
    [loom.graph :as lg]
    [loom.attr :as lat]
    [loom.alg :as la]
    [loom.io :as lio]
    [tech.v3.datatype :as dtype :refer [shape]]
    [tech.v3.tensor :as t]
    [tech.v3.datatype.argops :as taop]
    [tech.v3.datatype.functional :as f]
    [tech.v3.datatype.reductions :as tr]
    [ham-fisted.api :as hamf]
    [clj-commons.primitive-math :as pmath]
    [criterium.core :as cc :refer [quick-bench]]
    [clj-async-profiler.core :as prof]))


(defn MHP
  "
     Suppose you're on a game show,
     and you're given the choice of three doors:
     Behind one door is a car;
     behind the others, goats.
     You pick a door, say No. 1,
     and the host, who knows what's behind the doors,
     opens another door, say No. 3, which has a goat.
     He then says to you,
     'Do you want to pick door No. 2?'
     Is it to your advantage to switch your choice ?
  "
  ([] (MHP {}))
  ([{door-number :correct-door choose-door-number :choose-door impl :impl dp :dp cp :cp
    :or {door-number 1 choose-door-number 0 impl :dtype-next/tensor}}]
   (let
     [model
      {:fg (fgtree
             (:host's-choice
               [:your-1st-choice|host's-choice
                [
                 [0 1/2 1/2]
                 [1/2 0 1/2]
                 [1/2 1/2 0]
                 ]
                (:your-1st-choice
                  [:prize|your-1st-choice&door
                   [
                    [[0 1] [1 0] [1 0]]
                    [[1 0] [0 1] [1 0]]
                    [[1 0] [1 0] [0 1]]
                    ]
                   (:door-0 [:p-door-0 [1/3 1/3 1/3]])
                   (:prize-0)]
                  [:p-your-1st-choice [1/3 1/3 1/3]])]
               [:door|host's-choice
                [
                 [0 1/2 1/2]
                 [1/2 0 1/2]
                 [1/2 1/2 0]
                 ]
                (:door [:p-door [1/3 1/3 1/3]])]
               [:your-2nd-choice|host's-choice
                [
                 [0 1/2 1/2]
                 [1/2 0 1/2]
                 [1/2 1/2 0]
                 ]
                (:your-2nd-choice
                  [:your-2nd-choice|your-1st-choice
                   [
                    [0 1/2 1/2]
                    [1/2 0 1/2]
                    [1/2 1/2 0]
                    ]
                   (:your-1st-choice-0 [:p-your-1st-choice-0 [1/3 1/3 1/3]])]
                  [:prize|your-2nd-choice&door
                   [
                    [[0 1] [1 0] [1 0]]
                    [[1 0] [0 1] [1 0]]
                    [[1 0] [1 0] [0 1]]
                    ]
                   (:door-1 [:p-door-1 [1/3 1/3 1/3]])
                   (:prize-1)])]))
       :impl impl
       }
      door (or dp (assoc [0 0 0] door-number 1))
      choice (or cp (assoc [0 0 0] choose-door-number 1))
      fg (exp->fg :sp/sp impl (:fg model))
      {m1 :marginals l :updated :as em0}
      (-> model
        (assoc :updated fg)
        (assoc :data [{:p-door door :p-door-0 door :p-door-1 door :p-your-1st-choice choice :p-your-1st-choice-0 choice}])
        updates last)
      m2 (-> l (sp/with-alg :sp/MAP) propagate MAP-config)
      ]
     {:result (if (== 1 (:prize-1 m2)) '🚗 '🐐)
      :model l
      :marginals m1
      :explanation
      (string/join \newline
        [
         \newline
         (apply str " car           " (assoc '[🚪 🚪 🚪] (:door m2) '🚗))
         (apply str " you chose     " (assoc '[🚪 🚪 🚪] (:your-1st-choice m2) '🀆))
         (apply str " host opened   " (assoc '[🚪 🚪 🚪] (:host's-choice m2) '🐐))
         (apply str " you chose     " (assoc '[🚪 🚪 🚪] (:your-2nd-choice m2) '🀆 (:host's-choice m2) '🐐))
         (apply str "               " (assoc '[🐐 🐐 🐐] (:your-2nd-choice m2) '🀆 (:door m2) '🚗))
         \newline
         (if (== 1 (:prize-1 m2)) " you won!" " you lost.")
         \newline])})))

(defn e= [e x y] (< (abs (- x y)) e))

(defn test-Bayesian-updating
  "
    An example from:
    https://ocw.mit.edu/courses/mathematics/18-05-introduction-to-probability-and-statistics-spring-2014/readings/MIT18_05S14_Reading11.pdf
    part 4 Updating again and again
  "
  [{:keys [impl]}]
  (let
    [model
       {:fg
        (sp/fgtree
          (:d [:pd [0.5 0.5]]
            [:h|d
              [[0.5 0.4 0.1]
               [0.5 0.6 0.9]]
             (:h [:ph [0.4 0.4 0.2]])])
          )
        }
     experiment
     (assoc model
       :impl impl
       :data
       [
        {:pd [0 1]}
        {:pd [0 1]}
        ])
       {{h :h} :marginals} (last (updates experiment))
       expected [0.2463 0.3547 0.3990]
       result (map (fn [hv ev]  [hv ev (e= 10e-5 hv ev)]) h expected)
     ]
    {:expected expected
     :result (if (= impl :dtype-next/tensor) (t/->jvm h) h)
     :test-result (if (and (seq result) (every? true? (map peek result))) :pass :fail)
     :experiment experiment
     }))

(defn mhp-compare []
  (reduce =
    (map
       (fn [[correct-door first-door-choice]]
         (= (:result (MHP {:correct-door correct-door :choose-door first-door-choice :impl :core.matrix/tensor}))
            (:result (MHP {:correct-door correct-door :choose-door first-door-choice :impl :dtype-next/tensor}))))
       (x/cartesian-product (range 3) (range 3)))))

















(comment

  (print-cause-trace *e)

  (mhp-compare)



  (quick-bench (test-Bayesian-updating {:impl :dtype-next/tensor}))



(let [;impl :dtype-next/tensor
      impl :core.matrix/tensor
      f (fn [] (MHP {:correct-door (rand-int 3) :choose-door (rand-int 3) :impl impl}))
        ]
    (prof/profile (do (dotimes [_ 10000] (f)) :ok)))


(prof/serve-ui 8080)



(let [
      impl :dtype-next/tensor
      ;impl :core.matrix/tensor
      ]
  (quick-bench (MHP {:correct-door (rand-int 3) :choose-door (rand-int 3) :impl impl})))




  (->> (fn [] (:result (MHP {:correct-door (rand-int 3) :choose-door (rand-int 3) :impl :dtype-next/tensor})))
    (repeatedly 100)
    frequencies
    (into (sorted-map)))

(->> (fn [] (:result (MHP {:correct-door (rand-int 3) :choose-door (rand-int 3) :impl :core.matrix/tensor})))
    (repeatedly 100)
    frequencies
    (into (sorted-map)))





)
