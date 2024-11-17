(ns sigmapi.impl.core-matrix
  "core.matrix tensor implementations of factor and variable nodes"
  (:require
    [clojure.core.matrix :as m]
    [clojure.set :as set]
    [clojure.math :as maths :refer [log pow E]]
    [sigmapi.core :refer
      [exp->fg make-node update-factors unnormalized-marginals propagate message op]]))


(def log- (comp (partial * -1) log))

(defn -exp [x] (pow E (* -1 x)))

(defn p-normalize
  ([p]
    (p-normalize p (/ 1 (reduce + p))))
  ([p s1]
   (if (zero? s1)
    p
     (mapv (partial * s1) p))))

(defn normalize-log
  ([l] (p-normalize (map -exp l))))

(defmethod op [:exp- :core.matrix/tensor]
  [_ _ t] (m/emap -exp t))

(defmethod op [:normalize-log :core.matrix/tensor]
  [_ _ t] (normalize-log t))

(defn indexed-best
  "
    Returns list of the best (according to the given function f)
    items in the given matrix, and their indices.
  "
  [f]
  (fn ibf [mat]
    (let [best (f mat)]
      [best (first (filter (fn [v] (== best (apply m/mget mat v))) (m/index-seq mat)))])))

(def indexed-min (indexed-best m/emin))

(def indexed-max (indexed-best m/emax))

(defn rotate-vec
  [v i f]
  (if (= f last)
    (into (subvec v (inc i) (count v)) (subvec v 0 (inc i)))
    (into (subvec v i (count v)) (subvec v 0 i))))

(defn transpose-such-that
  ([mat i f]
    (transpose-such-that mat (vec (range (m/dimensionality mat))) i f))
  ([mat v i f]
   (let [rv (rotate-vec v i f)
         tm (m/transpose mat rv)
         ]
    [tm rv
      (rotate-vec v
        (mod (- (dec (m/dimensionality mat)) i) (m/dimensionality mat))
        (if (= last f) first last))])))

(defn product-of
  [mat g messages to dim-for-node]
  (let
    [
     dimz (vec (range (m/dimensionality mat)))
     [p pv ddd]
       (reduce
         (fn [[r pv pnd] {id :id v :value}]
           (let [
                 d (get pnd (dim-for-node id))
                 [tm rv nd] (transpose-such-that r dimz d last)
                 tm (if (vector? tm) (m/matrix tm) tm)
                 q (g tm v)]
             [q rv (mapv pnd nd)]))
         [mat dimz dimz] messages)
       d (get ddd (dim-for-node to))
       [tm rv nd] (transpose-such-that p dimz d first)
     ]
    tm))

(defmethod make-node [:sp/MAP :sp/factor :core.matrix/tensor]
  ([{:keys [f clm cpm value] :as node}]
   (-> node (assoc :f (or f clm (m/emap log- (or cpm value))) :kind :sp/factor) (update :features conj :passes))))

(defmethod message [:>< :sp/MAP :sp/factor :core.matrix/tensor]
  [_ {:keys [f id dim-for-node] :as this} messages to]
  (let [product (product-of f m/add messages to dim-for-node)
        mm (map m/emin product)]
    {:dim-for-node dim-for-node
     :value mm
     :min (indexed-min mm)
     :sum product
     :im (mapv (fn [[s c]] [s (zipmap (keys (dissoc dim-for-node to)) c)]) (map indexed-min product))
     }))

(defmethod message [:<> :sp/MAP :sp/factor :core.matrix/tensor]
  [_ {:keys [f id dim-for-node] :as this} messages to to-msg parent-msg]
  (let [conf (get-in parent-msg [:configuration id])
        mind (zipmap (map :id messages) (range (count messages)))
        to-conf (get conf to)]
    {:dim-for-node dim-for-node
     :value 0
     :mind mind
     :conf conf
     :configuration (assoc (:configuration parent-msg) to to-conf)}))

(defmethod message [:i :sp/MAP :sp/factor :core.matrix/tensor]
  [_ {:keys [f id dim-for-node] :as this}]
  {:value f :repr id :dim-for-node dim-for-node})

(defmethod message [:updated :sp/MAP :sp/factor :core.matrix/tensor]
  [_ this {:keys [cpm clm value]}]
  (assoc this :f (or clm (m/emap log- (or cpm value)))))

(defmethod make-node [:sp/MAP :sp/variable :core.matrix/tensor]
  ([{:keys [id] :as node}] (assoc node :kind :sp/variable)))

(defmethod message [:>< :sp/MAP :sp/variable :core.matrix/tensor]
  [_ this messages to]
  (let [sum (reduce m/add (map :value messages))]
    {:value sum}))

(defmethod message [:<> :sp/MAP :sp/variable :core.matrix/tensor]
  [_ {:keys [id] :as this} messages to to-msg parent-msg]
  (let
    [sum (reduce m/add (map :value (cons to-msg messages)))
     min (indexed-min sum)
     conf (if parent-msg (get-in parent-msg [:configuration id]) (get-in min [1 0]))
     configuration (if parent-msg (:configuration parent-msg) {id conf})
     mto (get-in to-msg [:im conf 1])]
    {:value sum
     :min min
     :configuration (assoc configuration to mto)
     }))

(defmethod message [:i :sp/MAP :sp/variable :core.matrix/tensor]
  [_ this] {:value 0})

(defmethod make-node [:sp/sp :sp/factor :core.matrix/tensor]
  ([{:keys [f clm cpm value] :as node}]
   (-> node
     (assoc :f (or f clm (m/emap log- (or cpm value))) :kind :sp/factor)
     (update :features conj :passes))))

(defmethod message [:>< :sp/sp :sp/factor :core.matrix/tensor]
  [_ {:keys [f id dim-for-node] :as this} messages to]
  (let [product (product-of f m/add messages to dim-for-node)
        sum (m/emap log- (map m/esum (m/emap -exp product)))]
    {:value sum}))

(defmethod message [:<> :sp/sp :sp/factor :core.matrix/tensor]
  [_ this messages to to-msg parent-msg]
  (message :>< this messages to))

(defmethod message [:i :sp/sp :sp/factor :core.matrix/tensor]
  [_ {:keys [f id dim-for-node]}]
  {:value f})

(defmethod message [:updated :sp/sp :sp/factor :core.matrix/tensor]
  [_ this {:keys [clm cpm value] :as p}]
  (assoc this :f (or clm (m/emap log- (or cpm value)))))

(defmethod make-node [:sp/sp :sp/variable :core.matrix/tensor]
  ([node] (assoc node :kind :sp/variable)))

(defmethod message [:>< :sp/sp :sp/variable :core.matrix/tensor]
  [_ this messages to]
  {:value (reduce m/add (map :value messages))})

(defmethod message [:<> :sp/sp :sp/variable :core.matrix/tensor]
  [_ this messages to to-msg parent-msg]
  (message :>< this messages to))

(defmethod message [:i :sp/sp :sp/variable :core.matrix/tensor]
  [_ {id :id}] {:value 0})

