(ns sigmapi.impl.tensor
  (:require
    [clojure.math :as maths :refer [log pow E]]
    [clojure.math.combinatorics :as x]
    [clojure.core.reducers :as r]
    [tech.v3.datatype :as dtype :refer [shape]]
    [tech.v3.datatype.functional :as f]
    [tech.v3.datatype.functional :as f]
    [tech.v3.tensor :as t]
    [tech.v3.datatype.argops :as ta]
    [ham-fisted.api :as hf]
    [sigmapi.core :refer :all]))

(defn -log [x] (* (log x) -1))

(defn exp- [x] (pow E (* -1 x)))

(defn normalise
  ([p]
   (let [s (f/sum p)]
     (if (== 0 s) p (dtype/emap (fn [x] (/ x s)) :double p)))))

(def op-log (hf/double-unary-operator x (-log x)))

(def opexp- (hf/double-unary-operator x (exp- x)))

(def t-log (partial dtype/emap op-log :double))

(def texp- (partial dtype/emap opexp- :double))

(defn normalize-log
  ([p] (normalise (texp- p))))

(defmethod op [:exp- :dtype-next/tensor]
  [_ _ t] (texp- t))

(defmethod op [:normalize-log :dtype-next/tensor]
  [_ _ t] (normalize-log t))

(defn index->vec [a-shape n i]
  (->> a-shape
    (reductions
      (fn [[l r] x']
        (let [x (/ l x')
              y (int (/ r x))]
          [x (- r (* x y)) y]))
      [n i])
    rest
    (mapv peek)))

(defn indexed-best
  "
    Returns list of the best (according to the given function f)
    items in the given matrix, and their indices.
  "
  [f]
  (fn ibf [a-tensor]
    (let [i (f a-tensor)
          s (dtype/shape a-tensor)
          c (if (== 1 (count s)) [i] (index->vec s (dtype/ecount a-tensor) i))]
      [(apply t/mget a-tensor c) c])))

(def indexed-min (indexed-best ta/argmin))

(def indexed-max (indexed-best ta/argmax))

(def realize (comp t/->tensor t/->jvm))

(def pst
  (memoize
    (fn [v index-first index-last]
     (first
       (into []
         (filter (fn [p] (and (= (first p) index-first) (= (peek p) index-last))))
         (x/permutations v))))))

(def p=
  (memoize
    (fn [tp ap v]
     (first
       (into []
         (filter (fn [p] (= tp (mapv ap p))))
         (x/permutations v))))))

(defn product-of [{:keys [f dim-for-node]} messages to]
  (let [s (shape f)
        n (count s)
        to-dim (dim-for-node to)
        -to-dim (* -1 to-dim)
        dims (vec (range n))
        to-dims (t/rotate dims [-to-dim])
        f-to (t/transpose f to-dims)
        bms (mapv (fn align-tensor [{mt :value mid :id}]
                    (let [p (pst dims to-dim (dim-for-node mid))
                          r (p= to-dims p dims)
                          bs (mapv s p)]
                      (t/transpose (t/broadcast mt bs) r))) messages)
        product (reduce f/+ f-to bms)]
    product))

(defmethod make-node [:sp/sp :sp/factor :dtype-next/tensor]
  ([{:keys [graph id value dim-for-node] :as params}]
   (let [f' (t-log (t/->tensor value :datatype :double))
         s (shape f') n (count s)
         ones (repeat (dec n) 1)]
     (assoc params :f f' :s s :n n :ones ones :features #{:passes}))))

(defmethod message [:>< :sp/sp :sp/factor :dtype-next/tensor]
  ><factor [_ {:keys [f ones] :as this} messages to]
  (let [product (texp- (product-of this messages to))
        sum (t-log (reduce (fn [r i] (t/reduce-axis f/sum r i)) product ones))]
    {:value sum}))

(defmethod message [:<> :sp/sp :sp/factor :dtype-next/tensor]
  [_ this messages to to-msg parent-msg]
  (message :>< this messages to))

(defmethod message [:i :sp/sp :sp/factor :dtype-next/tensor]
  [_ {:keys [f id dim-for-node] :as this} & that]
  {:value f :dim-for-node dim-for-node})

(defmethod message [:updated :sp/sp :sp/factor :dtype-next/tensor]
  [_ this {:keys [f value] :as p}]
  (assoc this :f (t-log (or f value))))

(defmethod make-node [:sp/sp :sp/variable :dtype-next/tensor]
  ([{id :id :as node}] node))

(defmethod message [:>< :sp/sp :sp/variable :dtype-next/tensor]
  ><-sp-variable [_ this messages to]
  {:value (reduce f/+ (map :value messages))})

(defmethod message [:<> :sp/sp :sp/variable :dtype-next/tensor]
  [_ this messages to to-msg parent-msg]
  (message :>< this messages to))

(defmethod message [:i :sp/sp :sp/variable :dtype-next/tensor]
  [_ {:keys [id] :as this}]
  {:value (t/->tensor [0]) :repr id})

(defmethod make-node [:sp/MAP :sp/factor :dtype-next/tensor]
  [{:keys [value f] :as node}]
  (assoc node :f (or f (t-log (t/->tensor value :datatype :double))) :kind :sp/factor :features #{:passes}))

(defmethod message [:>< :sp/MAP :sp/factor :dtype-next/tensor]
  ><-map-tensor [_ {:keys [id f dim-for-node] :as this} messages to]
  (let [product (product-of this messages to)
        mm (t/->tensor (mapv f/reduce-min product))]
    {:dim-for-node dim-for-node
     :value mm
     :min (indexed-min mm)
     :sum product
     :im (mapv (fn [[s c]] [s (zipmap (keys (dissoc dim-for-node to)) c)]) (map indexed-min product))
     }))

(defmethod message [:<> :sp/MAP :sp/factor :dtype-next/tensor]
  <>-map-tensor [_ {:keys [id f dim-for-node] :as this} messages to to-msg parent-msg]
  (let [conf (get-in parent-msg [:configuration id])
        mind (zipmap (map :id messages) (range (count messages)))
        to-conf (get conf to)]
    {:dim-for-node dim-for-node
     :value 0
     :mind mind
     :conf conf
     :configuration (assoc (:configuration parent-msg) to to-conf)}))

(defmethod message [:i :sp/MAP :sp/factor :dtype-next/tensor]
  i-map-factor [_ {:keys [f id dim-for-node] :as this}]
  {:value f :dim-for-node dim-for-node})

(defmethod message [:updated :sp/MAP :sp/factor :dtype-next/tensor]
  update-map-factor [_ this {:keys [f value] :as p}]
  (assoc this :f (t-log (or f value))))

(defmethod make-node [:sp/MAP :sp/variable :dtype-next/tensor]
  ([{id :id :as node}] node))

(defmethod message [:>< :sp/MAP :sp/variable :dtype-next/tensor]
  ><-map-variable [_ this messages to]
  (let [sum (reduce f/+ (map :value messages))]
    {:value sum}))

(defmethod message [:<> :sp/MAP :sp/variable :dtype-next/tensor]
  <>-map-variable [_ {:keys [id] :as this} messages to to-msg parent-msg]
  (let
    [product (realize (reduce f/+ (map :value (cons to-msg messages)))) ; *** without realize here
     min (indexed-min product)
     conf (if parent-msg (get-in parent-msg [:configuration id]) (get-in min [1 0]))
     configuration (if parent-msg (:configuration parent-msg) {id conf})
     mto (get-in to-msg [:im conf 1])]
    {:value product
     :min min
     :configuration (assoc configuration to mto)}))

(defmethod message [:i :sp/MAP :sp/variable :dtype-next/tensor]
  [_ this] {:value (t/->tensor [0])})
