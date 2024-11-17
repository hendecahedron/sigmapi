(ns ^{:doc
      " 𝝨𝝥

        Implementations of the sum-product and max-sum algorithms,
        from Factor Graphs and the Sum-Product Algorithm
        Frank R. Kschischang, Senior Member, IEEE, Brendan J. Frey, Member, IEEE, and
        Hans-Andrea Loeliger, Member, IEEE
        IEEE TRANSACTIONS ON INFORMATION THEORY, VOL. 47, NO. 2, FEBRUARY 2001
        DOI: 10.1109/18.910572
       "
      :author "Matthew Chadwick"
      :license
        "

        This library is free software; you can redistribute it and/or
        modify it under the terms of the GNU Lesser General Public
        License as published by the Free Software Foundation; either
        version 2.1 of the License, or (at your option) any later version.

        This library is distributed in the hope that it will be useful,
        but WITHOUT ANY WARRANTY; without even the implied warranty of
        MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
        Lesser General Public License for more details.

        /*
        * Copyright (C) 2016 Intermine
        *
        * This code may be freely distributed and modified under the
        * terms of the GNU Lesser General Public Licence. This should
        * be distributed with the code. See the LICENSE file for more
        * information or http://www.gnu.org/copyleft/lesser.html.
        *
        */

        "}
  sigmapi.core
  (:require
    [clojure.set :as set]
    [clojure.math :as maths :refer [log pow]]
    [clojure.walk :as walk]
    [clojure.core.reducers :as r]
    [loom.graph :as lg]
    [loom.attr :as lat]
    [loom.alg :as la])
    #?(:cljs (:require-macros [sigmapi.core :refer [fgtree]])))

#?(:clj
  (defmacro fgtree [xp]
   (walk/postwalk
     (fn [x]
       (if (and (or (vector? x) (list? x)) (not (map-entry? x)) (keyword? (first x)))
         `(~(if (vector? x) `vector `list) ~@x)
         x))
     xp)))

(defmulti op (fn [the-op impl & args] [the-op impl]))

(defmulti make-node (fn ([p] (mapv p (:make-with p)))))

(defmulti message
  (fn message-dispatch [the-message {:keys [impl alg kind] :as node} & that]
    [the-message alg kind impl]))

(defn neighbourz [edges]
  (reduce
    (fn [r [{a :id} {b :id}]]
      (-> r
        (update a (fn [n] (conj (or n []) b)))
        (update b (fn [n] (conj (or n []) a)))))
    {} edges))

(defn leaf?
  "Is the given node of the given graph a leaf node
  this depends on whether the graph is directed"
  ([g n]
   (== 1 (lg/out-degree g n))))

(defn leaves [g]
  (into #{} (filter (partial leaf? g)) (lg/nodes g)))

(defn edges->fg
  "
    Make a factor graph from these edges for this
    algorithm and implementation
  "
  ([alg impl edges]
      (let [g (reduce
                (fn [g [id p]]
                  (-> g
                    (lat/add-attr id :kind (if p :sp/factor :sp/variable))
                    (cond-> p (lat/add-attr id :cpm p))
                    (lat/add-attr id :shape (if p :box :oval))))
                (apply lg/graph (map (partial map :id) edges))
                (distinct (map (juxt :id :params) (mapcat identity edges))))
            t (lg/graph (la/bf-span g (:id (ffirst edges))))
            leafs (leaves t)
            nodes (into {} (map (juxt :id identity) (mapcat identity edges)))
            priors (into {} (filter peek (map (fn [n] [n (peek (first (filter (fn [[f to]] (== 1 (lg/out-degree t to))) (lg/out-edges t n))))]) (filter (fn [n] (= :sp/variable (lat/attr g n :kind))) (lg/nodes g)))))
            neighbours (neighbourz edges)
            ]
        {:alg        alg
         :messages   {}
         :graph      g
         :spanning-tree t
         :leaves     leafs
         :neighbours neighbours
         :priors priors
         :nodes
         (into {}
           (map
             (fn [id]
               [id
                (let [params (get-in nodes [id :params])
                      params' (if (map? params) params {:value params})]
                  (if params
                    (make-node (assoc params'
                                 :alg alg
                                 :features #{}
                                 :make-with [:alg :kind :impl]
                                 :kind :sp/factor :impl impl :graph g :id id
                                 :dim-for-node (zipmap (neighbours id) (range))
                                 :mfn (zipmap (neighbours id) (map (fn [n] (get-in nodes [n :params])) (neighbours id)))))
                    (make-node {:alg alg
                                :features #{}
                                :make-with [:alg :kind :impl]
                                :kind :sp/variable :impl impl :id id})))])
             (lg/nodes g)))})))

(defn graph->fg [alg impl {:keys [nodes edges] :as graph}]
  (let [nodes' (into {} (concat
                          (map (fn [id] [id {:id (keyword (str id))}]) (remove nodes edges))
                          (map (fn [[id params]] [id {:id (keyword (str id)) :params params}]) nodes)))
        edges' (partition 2 (map nodes' edges))
        ]
    (merge (edges->fg alg impl edges') (select-keys graph [:states :aliases]))))

(defn update-factors
  "Update the given nodes"
  ([model updates]
   (reduce
     (fn [model [id params]]
       (update-in model [:nodes id] (partial message :updated) (if (map? params) params {:value params})))
     model updates)))

(defn with-alg
  [{g :graph nodes :nodes :as model} alg]
  (reduce
    (fn [model [id node]]
      (assoc-in model [:nodes id]
        (make-node (assoc node :alg alg))))
    (assoc model :alg alg :messages {}) nodes))

; make this work with one edge
(defn as-edges
  ([exp]
    (as-edges exp []))
  ([exp edges]
    (if (and (seqable? exp) (keyword? (first exp)) (or (keyword? (first (first (rest exp)))) (keyword? (first (second (rest exp))))))
      (let [branches (if (vector? exp) (rest (rest exp)) (rest exp))]
        (reduce
          (fn [r c]
              (as-edges c
                (conj r
                  [(let [f {:id (first exp)}] (if (vector? exp) (assoc f :params (second exp)) f))
                   (if (vector? c)
                    {:id (first c) :params (second c)}
                    {:id (first c)})])))
          edges branches))
      edges)))

(defn exp->fg
  "Return a factor graph for the given expression"
  [alg impl exp]
  (edges->fg alg impl (as-edges exp)))

(defn prior-nodes [{:keys [graph nodes leaves] :as model}]
  (into {}
    (filter
      (fn [[id node]]
        (and (leaves id) (= :sp/factor (:kind node)))))
    nodes))

(defn msgs-from-leaves [{:keys [messages graph nodes leaves] :as model}]
  (reduce
    (fn [r id]
      (let [parent (first (lg/successors graph id))]
        (assoc-in r [:messages parent id]
          (assoc (message :i (get nodes id))
            :id id :flow :><))))
    model leaves))

(defn msgs-from-variables [{:keys [messages graph nodes] :as model}]
  (reduce
    (fn [r id]
      (let [parent (first (lg/successors graph id))]
        (assoc-in r [:messages parent id]
          (assoc (message :i (get nodes id))
            :id id :flow :><))))
    model
    (filter (comp (fn [n] (= :sp/variable (:kind n))) nodes)
      (lg/nodes graph))))

(defn message-passing
  "

    Synchronous message-passing on the given model given previous-model.
    This is the simplest form of message-passing. Can add other
    kinds (loopy, asynchronous core.async) later but this is easy to test

    Returns the given model with its messages updated

    A model is a map with:

    * a graph describing its structure
    * a messages map of the form {:node-to-id {:node-from-id message}}
    * a map of nodes (variable, factor)

    Messaging has two phases: in from the leaves >< and out
    from the root <>. The root is the variable node that messages
    from the leaves happen to converge on (if a factor node
    happens to get the chance to become root it passes).
    Each node combines its messages according to its local
    product and sum functions and sends the result to the node
    it's summarizing for
    (or all but one of its neighbours if it's root - see comment above).

    Frey2001Factor DOI: 10.1109/18.910572 page 502
    Pattern Recognition and Machine Learning, Christopher M. Bishop page 412

  "
  [previous-model {:keys [messages graph nodes] :as model}]
  (reduce
    (fn [{root? :root :as r} [id msgs]]
      (let [prev-msgs (get-in previous-model [:messages id])
            {:keys [features] :as node} (get nodes id)]
        (cond
          ; messages have arrived on all but one of the edges incident on v
          (and (not= msgs prev-msgs) (== (count msgs) (dec (lg/out-degree graph id))))
             (let [parent (first (set/difference (lg/successors graph id) (into #{} (keys msgs))))
                   node (get nodes id)]
               (assoc-in r [:messages parent id]
                 (assoc (message :>< node (vals (dissoc msgs parent)) parent) :flow :>< :id id)))
           ; all messages have arrived
           (and (not= msgs prev-msgs) (== (count msgs) (lg/out-degree graph id)))
              (let [[return _] (first (set/difference
                                        (into #{} (map (juxt :id :flow) (vals msgs)))
                                        (into #{} (map (juxt :id :flow) (vals prev-msgs)))))]
                (if (and (:passes features) (= :>< (get-in msgs [return :flow])))
                  (if root? r (update-in r [:messages id] dissoc return))
                  (r/reduce
                    (fn all-arrived [r parent]
                      (assoc
                        (assoc-in r [:messages parent id]
                          (assoc (message :<> node (vals (dissoc msgs parent)) parent (get msgs parent)
                                   (if root? (get msgs return) nil))
                            :flow :<> :id id))
                        :root id))
                    r (keys (if root? (dissoc msgs return) msgs)))))
              :else r)))
     model messages))

(defn messages-><
  "Propagate inflowing messages"
  [{:keys [messages graph nodes] :as model}]
  (reduce
    (fn [r [id msgs]]
      (let [recipients (lg/successors graph id)
            node (get nodes id)]
        (reduce
          (fn [r recipient]
            (assoc-in r [:messages recipient id]
             (assoc (message :>< node (vals (dissoc msgs recipient)) recipient) :flow :>< :id id)))
          r recipients)))
     model messages))

(defn messages-<>
  "Propagate outflowing messages"
  [{:keys [messages graph nodes] :as model}]
  (reduce
    (fn [r [id msgs]]
      (let [recipients (lg/successors graph id)
            node (get nodes id)]
        (reduce
          (fn [r recipient]
            (assoc-in r [:messages recipient id]
             (assoc (message :<> node (vals (dissoc msgs recipient)) recipient (get msgs recipient) nil)
               :flow :>< :id id)))
           r (keys msgs))))
     model messages))

(defn can-message?
  "The algorithm terminates once two messages have been passed
  over every edge, one in each direction.
  todo: optimise
  "
  [{:keys [messages graph nodes] :as model}]
  (or (empty? messages)
      (not= (into #{} (keys messages))
            (into #{} (mapcat keys (vals messages))))))

(defn propagations
  "Propagate messages on the given model's graph
  in both directions
  "
  ([m]
    (propagations message-passing (assoc m :messages {})))
  ([f m]
   (->> [m (msgs-from-leaves m)]
     (iterate (fn [[o n]] [n (f o n)]))
     (take-while (comp can-message? first)))))

(defn propagate
  "Propagate messages on the given model's graph
  in both directions
  todo: lazy seq - rewrite loop-recur
  "
  ([m] (propagate message-passing (assoc m :messages {})))
  ([f m]
    (loop [o m n (msgs-from-leaves m)]
      (if (can-message? o)
        (recur n (f o n))
        n))))

(defn propagate-cycles
  "Propagate messages on the given model's graph
  in both directions"
  ([n m]
    (propagate-cycles
      (comp messages-<> messages-><)
      n (assoc m :messages {})))
  ([f n m]
   (->> m
     msgs-from-leaves
     (iterate f)
     (take n))))

(defn maybe-list [x]
  (if (seqable? x) x (list x)))

(defn unnormalized-marginals
  "Returns a map of marginals for the nodes of the given model"
  [{:keys [messages graph nodes] :as model}]
  (into {}
    (comp
      (filter (comp #{:sp/variable} :kind val))
      (map
       (fn [[id node]]
         [id (:value (message :<> node (vals (get messages id)) :these :args :are-ignored))])))
    nodes))

(defn named-marginals [model marginals]
  (zipmap
    (map (:aliases model) (keys marginals))
    (map (comp (partial apply hash-map) interleave) (map (:states model) (keys marginals)) (vals marginals))))

(defn all-marginals
  "Marginals for all given models"
  [models]
  (reduce
    (fn [r m] (merge-with conj r m))
      (zipmap
        (map key
             (filter
               (comp #{:sp/variable} :kind val)
               (:nodes (first models))))
        (repeat [])) (map unnormalized-marginals models)))

(defn configuration
  "Returns the total configuration of max-sum for the given model"
  [{:keys [messages graph nodes] :as model}]
  (reduce
    (fn [r c] (merge r c))
    {} (map (comp :configuration val)
            (filter (comp (partial = :<>) :flow val)
                    (mapcat val
                      (select-keys messages (leaves graph)))))))

(defn filter-configuration [config {:keys [messages graph nodes] :as model}]
  (select-keys config
    (filter (fn [id] (= :sp/variable (:kind (get nodes id))))
      (keys config))))

(def MAP-config
  "Returns the MAP configuration of the given model"
  (comp (partial apply filter-configuration)
     (juxt configuration identity)))

(defn compute-MAP-config [impl exp]
  (MAP-config
    (propagate (exp->fg :sp/MAP impl exp))))

(defn as-states [config model]
  (into {}
    (map
      (fn [[k v]] [k (get-in model [:states k v])])
      config)))

(defn check-leaves [config sequence-by-id]
  (into {}
    (map
      (fn [[id sequence]] [id (= sequence (get config id))])
      sequence-by-id)))

(defn updates [{:keys [fg updated impl marginals data] :as model}]
  (let [{nodes :nodes priors :priors :as graph} (or updated (exp->fg :sp/sp impl fg))]
    (reductions
      (fn [{g :updated post :marginals :as model} data-priors]
        (let [g (update-factors g (merge (zipmap (vals priors) (map post (keys priors))) data-priors))]
          (assoc model :updated g :marginals (update-vals (unnormalized-marginals (propagate g)) (partial op :normalize-log impl)))))
     (assoc model :updated graph :marginals (or marginals (zipmap (keys priors) (map (comp (partial op :exp- impl) :value (partial message :i) nodes) (vals priors)))))
     data)))