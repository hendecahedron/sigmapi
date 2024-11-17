(ns sigmapi.impl.symbolic
  (:refer-clojure :exclude [+ - * /])
  (:require
    [emmy.env :as e :refer [+ - * / sqrt expt exp log]]
    [sigmapi.core :as sp :refer [exp->fg make-node update-factors unnormalized-marginals propagate message]]))

(defn di [from to f] (e/definite-integral f from to))

(defn summarize
  ([f level]
    (summarize f 0.0 1.0 level))
  ([f from to level]
   (if (== level 0)
     f
     (fn pdi [x] (partial di from to (summarize (partial f x) from to (dec level)))))))

(defn ff [f] (fn [x] ((f x))))

(defn normalized
  ([f] (normalized 0.0 1.0 f))
  ([from to f]
   (let [i (e/definite-integral f from to)
         i1 (/ 1.0 i)]
     (fn [x] (* i1 (f x))))))

(defmethod make-node [:sp/sp :sp/variable :emmy/symbolic]
  ([{:keys [id f] :as node}] node))

(defmethod message [:>< :sp/sp :sp/variable :emmy/symbolic]
  [_ node messages to]
  {:value (reduce * (map :value messages))})

(defmethod message [:<> :sp/sp :sp/variable :emmy/symbolic]
  [_ node messages to]
  (message :>< node messages to))

(defmethod message [:i :sp/sp :sp/variable :emmy/symbolic]
  [_ {f :f}] {:value f})

(defmethod make-node [:sp/sp :sp/factor :emmy/symbolic]
  ([{:keys [id f dim-for-node] :as params}]
   {:f f :id id :dim-for-node dim-for-node :kind :sp/factor :features #{:passes}}))

(defmethod message [:>< :sp/sp :sp/factor :emmy/symbolic]
  [_ {:keys [f id dim-for-node d] :as node} messages to]
  (let [product (reduce * (cons f (map (fn [{f :value id :id}] (fn pf [a-vector] (f (a-vector (dim-for-node id))))) messages)))
        n (count messages)
        dims (cons (dim-for-node to) (map (comp dim-for-node :id) messages))
        pv (fn p [& args] (product (mapv (vec args) dims)))]
    {:value (ff (summarize pv n))}))

(defmethod message [:<> :sp/sp :sp/factor :emmy/symbolic]
  [_ node messages to]
  (message :>< node messages to))

(defmethod message [:i :sp/sp :sp/factor :emmy/symbolic]
  [_ {f :f}] {:value f})

(defmethod message [:updated :sp/sp :sp/factor :emmy/symbolic]
  [_ node {:keys [f value] :as p}]
  (assoc node :f (or f value)))
