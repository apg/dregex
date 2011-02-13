(ns dregex.core
  (:use [clojure.set :only (difference union intersection)])
  (:use [clojure.contrib.seq :only (find-first)]))

(def alphabet (into #{} (map char (range 32 127))))

;; (defn meet
;;   "Computes the set, a intersect b | a is an element of r, b is
;; an element of s"
;;   [r s]
;;   (let [cr (count r)
;;         cs (count s)
;;         m (max cr cs)
;;         nr (if (< cr m)
;;              (concat r (repeatedly (- m cr) #(identity 1)))
;;              (seq r))
;;         ns (if (< cs m)
;;              (concat s (repeatedly (- m cs) #(identity 1)))
;;              (seq s))]
;;     (into #{}
;;           (for [a r, b s :when (not (and (nil? a) (nil? b)))]
;;             (do
;;               (println "MEEEEET: " a " " b)
;;               (cond
;;                (nil? a) b
;;                (nil? b) a
;;                :else (intersection a b)))))))


(defn meet
  "Computes the set, a intersect b | a is an element of r, b is
an element of s"
  [r s]
  (into #{}
        (for [a r, b s :when (not (and (nil? a) (nil? b)))]
          (cond
           (nil? a) b
           (nil? b) a
           :else (intersection a b)))))


(defprotocol DFA
  (match [this s] "determines whether or not s is part of the language"))

(defprotocol RE
 (deriv [this a] "derivative with respect to a")
 (V [this] "nullable")
 (C [this] "compute the derivative character classes"))

(defrecord ^{:private true} Epsilon []
           Object
           (toString [_] "eps"))

(extend-type Epsilon
  RE
  (deriv [this a] nil)
  (V [this] this)
  (C [this] #{alphabet}))

(def eps (Epsilon.))

(declare notnil !! ++ && || **)

(extend-type nil RE
             (deriv [this a] nil)
             (V [_] nil)
             (C [_] (C #{})))

(extend-type Character RE
             (deriv [this a]
               (cond
                (= a eps) this
                (= this a) eps
                :else nil))
             (V [_] nil)
             (C [this]
               (let [r #{this}]
                 #{r
                   (difference alphabet r)})))

(extend-type clojure.lang.PersistentHashSet RE
             (deriv [this a]
               (if (= a eps)
                 this
                 (if (this a) eps nil)))
             (V [_] nil)
             (C [this] #{this
                         (difference alphabet this)}))

(defrecord Not [r]
  RE
  (deriv [this a]
    (if (= a eps)
      this
      (!! (deriv r a))))
  (V [_]
    (if (= (V r) eps) nil eps))
  (C [this] (C r))

  Object
  (toString [_] (str "(not " r ")")))

(def notnil (Not. nil))

(defrecord Concat [r s]
  RE
  (deriv [this a]
    (if (= a eps)
      this
      (|| (++ (deriv r a) s)
          (++ (V r) (deriv s a)))))
  (V [_]
    (and (V r) (V s)))
  (C [_]
    (if-not (V r) ;; (e.g. v(r) is not eps
      (C r)
      (meet (C r) (C s))))

  Object
  (toString [_] (str "(" r "." s ")")))

(defrecord Kleene [r]
  RE
  (deriv [this a]
    (if (= a eps)
      this
      (++ (deriv r a) (** r))))
  (V [_] eps)
  (C [_] (C r))

  Object
  (toString [_] (str "(" r ")*")))

(defrecord Or [r s]
  RE
  (deriv [this a]
    (if (= a eps)
      this
      (|| (deriv r a) (deriv s a))))
  (V [_]
    (or (V r) (V s)))
  (C [_]
    (meet (C r) (C s)))

  Object
  (toString [_] (str "(" r " + " s ")")))

(defrecord And [r s]
  RE
  (deriv [this a]
    (if (= a eps)
      this
      (&& (deriv r a) (deriv s a))))
  (V [_]
    (or (V r) (V s)))
  (C [_]
    (meet (C r) (C s)))
  
  Object
  (toString [_] (str "(" r " & " s ")")))


(defn ++
  "concat"
  [r s]
  (cond
   (or (= nil r) (= nil s)) nil
   (= eps r) s
   (= eps s) r
   :else (Concat. r s)))

(defn **
  "kleene"
  [r]
  (cond
   (= (class r) Kleene) r
   (= r eps) eps
   (= r nil) eps
   :else (Kleene. r)))



;;; || and && have other associativity optimizations that
;;; could be done. We'll deal with that later.
(defn ||
  "or"
  [r s]
  (let [hashr? (instance? clojure.lang.PersistentHashSet r)
        hashs? (instance? clojure.lang.PersistentHashSet r)]
    (cond
     (= r s) r
     (= notnil r) notnil
     (= nil r) s
     (and hashr? hashs?) (union r s)
     (and (instance? Character r) hashs?) (conj r s)
     (and (instance? Character s) hashr?) (conj s r) 
     :else (Or. r s))))

(defn &&
  "and"
  [r s]
  (cond
   (= r s) r
   (= nil r) nil
   (= notnil r) s
   :else (And. r s)))

(defn !!
  "complement"
  [r]
  (cond
   (= (class r) Not) (:r r)
   (instance? Character r) (difference alphabet #{r})
   (instance? clojure.lang.PersistentHashSet r) (difference alphabet r)
   :else (Not. r)))

(comment
  (= eps (V (deriv \a \a))) ;; matches \a
  (= eps (V (deriv (!! \a) \b))) ;; matches ^\a

  (= eps (V
          (deriv
           (deriv
            (++ (|| \a \b) (!! \b)) ;; matches (a|b)[^b]
            \b)
           \z)))

  ;; obviously we need a better way, so we'll build a DFA out of it.
  )

(defn- make-label
  [n]
  (keyword (str "q" n)))

(defn goto
  [q [Q labels d] S]
  (let [c (first S)
        qc (deriv q c)
        q-label (Q q)]
    (if-let [qc-label (Q qc)]
      (let [Dp (assoc d q-label
                      (conj (get d q-label {})
                            [S qc-label]))]
        [Q labels Dp])
      (let [qc-label (make-label (count Q))
            Qlabels (conj labels [qc-label qc])
            Qp (conj Q [qc qc-label])
            Dp (assoc d q-label
                      (conj (get d q-label {})
                            [S qc-label]))]
        (explore Qp Qlabels Dp qc)))))

(defn- explore
  [Q labels d q]
  (reduce (partial goto q) [Q labels d] (C q)))

(defn next-state
  [tests ch]
  (if (seq tests)
    (let [[s label] (first tests)]
      (if (s ch)
        label
        (recur (rest tests) ch)))
    nil))

(defn compile
  [re]
  (let [q0 (deriv re eps)
        [Q labels d] (explore {q0 :q0} {:q0 q0} {} q0)
        F (apply hash-set (map second (filter #(= (V (first %)) eps) Q)))]
    (reify DFA
      (match [this s]
        (loop [label :q0
               stream s]
          (if (and (seq stream) label)
            (recur (next-state (label d) (first stream)) (rest stream))
            (cond
             (nil? label) false
             (F label) true
             :else false)))))))
