(ns sigmapi.test.core
  (:require
    [clojure.test :refer [deftest testing is]]
    [sigmapi.core :as sp :refer [fgtree make-node  propagate print-msgs msg-diff
        marginals exp->fg msgs-from-leaves <><> ln- P
        normalize random-matrix MAP-config combine can-message?
        update-factors]]
    [clojure.core.matrix :as m]
    [loom.graph :as lg]
    [loom.alg :as la]))


(defn
  fg-test-graph-f7
  "Figure 7 in Frey2001 Factor graphs and the sum product algorithm"
  ([] (fg-test-graph-f7 :sp/sp))
  ([alg] (fg-test-graph-f7 alg (lg/graph ['fa 'x1] ['fb 'x2] ['x1 'fc] ['x2 'fc] ['fc 'x3] ['x3 'fd] ['x3 'fe] ['fd 'x4] ['fe 'x5])))
  ([alg g]
   (fg-test-graph-f7 alg g {'x5 #{0 1} 'x2 #{0 1 2} 'x3 #{0 1 2 3} 'x4 #{0 1} 'x1 #{0 1}}))
  ([alg g states-map]
   {
    :states   states-map
    :messages {}
    :graph    g
    :nodes    {
               'x1 (make-node {:alg alg :type :sp/variable :id 'x1})
               'x2 (make-node {:alg alg :type :sp/variable :id 'x2})
               'x3 (make-node {:alg alg :type :sp/variable :id 'x3})
               'x4 (make-node {:alg alg :type :sp/variable :id 'x4})
               'x5 (make-node {:alg alg :type :sp/variable :id 'x5})
               'fa (make-node {:alg alg :type :sp/factor :graph g :id 'fa :cpm (m/matrix [0.25 0.75]) :dfn {'x1 0}})
               'fb (make-node {:alg alg :type :sp/factor :graph g :id 'fb :cpm (m/matrix [0.19 0.9 0.452]) :dfn {'x2 0}})
               'fc (make-node {:alg alg :type :sp/factor :graph g :id 'fc :cpm (random-matrix [2 3 4]) :dfn {'x1 0 'x2 1 'x3 2}})
               'fd (make-node {:alg alg :type :sp/factor :graph g :id 'fd :cpm (random-matrix [4 2]) :dfn {'x3 0 'x4 1}})
               'fe (make-node {:alg alg :type :sp/factor :graph g :id 'fe :cpm (random-matrix [4 2]) :dfn {'x3 0 'x5 1}})
               }}))

(defn figure7
  "Figure 7 in Frey2001 Factor graphs and the sum product algorithm"
  ([]
   {
    :fg
    (fgtree
      [:fc
       [
        [[0.3 0.3 0.3 0.1] [0.3 0.3 0.3 0.1] [0.3 0.3 0.3 0.1]]
        [[0.3 0.3 0.3 0.1] [0.3 0.3 0.3 0.1] [0.3 0.3 0.3 0.1]]
        ]
       (:x1 [:fa [0.1 0.9]])
       (:x2 [:fb [0.2 0.7 0.1]])
       (:x3
         [:fd
          [
           [0.4 0.6]
           [0.6 0.4]
           [0.4 0.6]
           [0.6 0.4]
           ]
          (:x4)]
         [:fe
          [
           [0.5 0.5]
           [0.5 0.5]
           [0.5 0.5]
           [0.5 0.5]
           ]
          (:x5)])])

      :priors {:x1 :fa :x2 :fb}
      }))

(defn test-cbt []
  (let
    [
     s [2 3 4 5]
     f (m/new-array s)
     g (fn ([mat v] (m/add mat v)) ([mat] mat))
     vs (map (fn [d] (m/matrix (repeat d d))) s)
     dfn (into {} (map vector s (range (count s))))
     to 2
     msgs (map (fn [v i] {:value v :id i}) vs s)
     ; do them out-of-order in as messages may not come in dimension order
     reordered-msgs (mapcat (fn [[a b]] [b a]) (partition-all 2 msgs))
     sum (combine f g reordered-msgs to dfn)
     ]
    sum))

; combine-by-tranz [f g messages to dim-for-node]
(deftest test-combine-by-tranz
  (testing "That adding a sequence of vectors containing the value of their length
  to a matrix of the same shape as the sequence of vectors results in a matrix having
  every value equal to the sum of its dimensions"
    (is (m/equals (test-cbt) (m/fill (m/new-array [2 3 4 5]) (reduce + [2 3 4 5]))))))

(deftest test-max-configuration
  (testing "That a simple graph (a branch, x2->x1<-x3) returns max config"
    (->>
      (fgtree
        (:x1
          [:x1x2
           [
            [0.1 0.2 0.7]
            [0.6 0.2 0.2]
            ]
           (:x2 [0.2 0.8])]
          [:x1x3
           [
            [0.5 0.1 0.4]
            [0.8 0.1 0.1]
            ]
           (:x3 [0.3 0.6 0.1])]))
      exp->fg :sp/mxp
      propagate
      MAP-config)))

(defn t1 []
  (->>
      (fgtree
        (:x1
          [:x1x2
           [
            [0.1 0.2 0.7]
            [0.6 0.2 0.2]
            ]
           (:x2 [0.2 0.8])]
          [:x1x3
           [
            [0.5 0.1 0.4]
            [0.8 0.1 0.1]
            ]
           (:x3 [0.3 0.6 0.1])]))
       (exp->fg :sp/mxp)
       propagate
       MAP-config))
