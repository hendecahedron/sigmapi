(ns sigmapi.test.core
  (:require
    [clojure.test :refer [deftest testing is]]
    [sigmapi.core :as sp :refer [e> make-node propagate print-msgs msg-diff
                                 marginals exp->fg msgs-from-leaves <><> ln- P ln
                                 normalize random-matrix MAP-config combine can-message?
                                 update-factors]]
    [clojure.core.matrix :as m]
    [loom.graph :as lg]
    [loom.alg :as la]))

(defn figure7
  "Figure 7 in Frey2001 Factor graphs and the sum product algorithm"
  ([]
   '[:fc
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
        (:x5)])]))

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
      '(:x1
         [:x1x2
          [
           [0.1 0.2 0.7]
           [0.6 0.2 0.2]
           ]
          (:x2 [:px1 [0.2 0.8]])]
         [:x1x3
          [
           [0.5 0.1 0.4]
           [0.8 0.1 0.1]
           ]
          (:x3 [:px3 [0.3 0.6 0.1]])])
      (exp->fg :sp/mxp)
      propagate
      MAP-config)))

; ["dog" "park" "car" "walk"]
(defn fit [px]
  (e>
    [:x|c0c1
     [
      [[0 0 0 0] [0 0 0 0.7] [0 0 0 0] [0 1 0 0]]
      [[0 0 0 0.7] [0 0 0 0] [0 0 0.3 0] [0 0 0 0.7]]
      [[0.1 0.3 0 0] [0 0 0 0.7] [0 0.1 0 0] [0 0.7 0 0]]
      [[0.9 0.1 0 0] [0.3 0 0 0] [0.1 0.5 0 0] [0 0 0 0]]
     ]
     (:x [:px px])
     (:c0)
     (:c1)]))

(defn el [x] (ln (if (== 0.0 x) e x)))

(defn fi [g]
  (reduce m/add
    (map (fn [[a b]]
      (m/mul (m/emap (fn [x] (pow x 2.0)) (m/sub (m/emap el a) (m/emap el b))) b))
      (partition 2 1 g))))