(ns sigmapi.impl.normal
  "Implementations of factor and variable nodes for normal distributions"
  (:refer-clojure :exclude [+ - * /])
  (:require
    [clojure.math :as maths :refer [PI]]
    [emmy.env :as e :refer [+ - * / sqrt expt exp log]]
    [emmy.matrix :as em]
    [sigmapi.core :as sp :refer
     [exp->fg make-node update-factors unnormalized-marginals propagate message]]
    [tech.v3.tensor :as t]))

(def shape (juxt em/num-rows em/num-cols))

(defn normal [mu sd]
  (with-meta
    (fn [x]
     (*
       (/ 1 (* sd (sqrt (* 2 PI))))
       (exp (* -1/2 (expt (/ (- x mu) sd) 2)))))
    {:mu mu :sigma sd :sigma-1 (if (== 0 sd) 0 (/ 1 sd))}))

(defn multivariate-normal
  ([mu sigma]
   (let [mu (apply em/row mu)
         sigma (apply em/by-rows sigma)
         sigma-1 (em/invert sigma)]
     (multivariate-normal mu sigma sigma-1)))
  ([mu sigma sigma-1]
     (with-meta
       (fn [x]
         (let [k (count x)
               x (apply em/row x)
               x-mu (em/transpose (- x mu))
               det-sigma (em/determinant sigma)]
           (/
             (exp (get-in (* -1/2 (em/transpose x-mu) sigma-1 x-mu) [0 0]))
             (sqrt (* (expt (* 2 PI) k) det-sigma)))))
       {:mu mu :sigma sigma :sigma-1 sigma-1})))

(defn product-of-normals
  ([{:keys [f id dim-for-node messages to-dim zero-vector zero-matrix]}]
   (let
     [s1s (map (fn [{v :value id :id}] (let [j (dim-for-node id)] (assoc-in zero-matrix [j j] (:sigma-1 (meta v))))) messages)
      mus (map (fn [{v :value id :id}] (let [j (dim-for-node id)] (assoc-in zero-vector [0 j] (:mu (meta v))))) messages)
      sigma (em/invert (apply + (cons (:sigma-1 (meta f)) s1s)))
      mu (* (apply + (map * (cons (:mu (meta f)) mus) (cons (:sigma-1 (meta f)) s1s))) sigma)]
     {:mu mu :sigma sigma})))

(defn summarize
  "
    integrating over all variables except to-dim
    is the same as the marginal of to-dim (all the other variables are marginalized out)
    https://statproofbook.github.io/P/mvn-marg.html
  "
  ([mu sigma to-dim]
    (normal
      (em/get-in mu [0 to-dim])
      (em/get-in sigma [to-dim to-dim]))))

(defmethod make-node [:sp/sp :sp/variable :emmy/normal]
  ([{:keys [id] :as node}] node))

(defmethod message [:>< :sp/sp :sp/variable :emmy/normal]
  [_ this messages to]
  (let [s1s (map (comp :sigma-1 meta :value) messages)
        mus (map (comp :mu meta :value) messages)
        s1+ (apply + s1s)
        sigma (if (== 0 s1+) s1+ (/ 1 s1+))
        mu (* sigma (apply + (map * s1s mus)))]
    {:value (normal mu sigma)}))

(defmethod message [:<> :sp/sp :sp/variable :emmy/normal]
  [_ this messages to to-msg parent-msg] (message :>< this messages to))

(defmethod message [:i :sp/sp :sp/variable :emmy/normal]
  [_ this]
  {:value (with-meta (fn identiti [x] (em/by-rows [1])) {:mu 0 :sigma 1 :sigma-1 1})})

(defmethod make-node [:sp/sp :sp/factor :emmy/normal]
  ([{:keys [graph id mu sigma dim-for-node] :as params}]
   (let [f ((if (number? mu) normal multivariate-normal) mu sigma)
         s1 (:sigma-1 (meta f))
         d  (if (number? s1) 0 (em/num-cols s1))
         zv (em/make-zero 1 d)
         zm (em/make-zero d)]
      (assoc (select-keys params [:id :dim-for-node :alg :mu :sigma :kind :impl :make-with])
        :f f :features #{:passes} :zero-vector zv :zero-matrix zm :d d))))

(defmethod message [:>< :sp/sp :sp/factor :emmy/normal]
  [_ {:keys [f id dim-for-node zero-vector zero-matrix d] :as this} messages to]
  (let [to-dim (dim-for-node to)
        {:keys [mu sigma]} (product-of-normals (assoc this :to-dim to-dim :messages messages))
        ]
    {:value (summarize mu sigma to-dim)}))

(defmethod message [:<> :sp/sp :sp/factor :emmy/normal]
  [_ this messages to to-msg parent-msg] (message :>< this messages to))

(defmethod message [:i :sp/sp :sp/factor :emmy/normal]
  [_ {:keys [f id dim-for-node zero-vector zero-matrix d]}]
  {:value f})

(defmethod message [:updated :sp/sp :sp/factor :emmy/normal]
  [_ this {:keys [mu sigma] :as p}]
  (assoc this :f ((if (number? mu) normal multivariate-normal) mu sigma)))