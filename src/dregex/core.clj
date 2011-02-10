(ns dregex.core
  (:use [clojure.set :only (difference union intersection)])
  (:use [clojure.contrib.seq :only (find-first)]))

(def alphabet (into #{} (map char (range 32 127))))

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
             (C [_] #{}))

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
        qc (deriv q c)]
    (if-let [label (Q qc)]
      (let [Dq (get d label {})
            Dqp (conj Dq [S label])]
        [Q labels (assoc d label Dqp)])
      (let [new-label (make-label (count Q))
            Qp (conj Q [qc new-label])
            labelsp (conj labels [new-label qc])
            Dp (assoc d new-label {S new-label})]
        (explore Qp labelsp Dp qc)))))

(defn explore
  [Q labels d q]
  (reduce #(goto q %1 %2) [Q labels d] (C q)))

(defn make-dfa
  [re]
  (let [q0 (deriv re eps)
        [Q labels d] (explore {} {} {} q0)
        F (apply hash-set (map second (filter #(= (V (first %)) eps) Q)))]
    [q0 Q labels d F]))






;;(a + b · a) + c)

;;(|| (|| \a (++ \b \a)) \c)




;; q0: #:dregex.core.Concat{:r \a, :s \b}

;; nil :q2,
;; #:dregex.core.Or{:r \b, :s nil} :q1,
;; #:dregex.core.Concat{:r \a, :s \b} :q0
;; :q2 nil
;; :q1 #:dregex.core.Or{:r \b, :s nil}
;; :q0 #:dregex.core.Concat{:r \a, :s \b}}

;; D = :q2 [#{\space \@ \` \! \A \" \B \b \# \C \c \$ \D \d \% \E \e \& \F \f \' \G \g \( \H \h \) \I \i \* \J \j \+ \K \k \, \L \l \- \M \m \. \N \n \/ \O \o \0 \P \p \1 \Q \q \2 \R \r \3 \S \s \4 \T \t \5 \U \u \6 \V \v \7 \W \w \8 \X \x \9 \Y \y \: \Z \z \; \[ \{ \< \\ \| \= \] \} \> \^ \~ \? \_} :q2]
;;     :q1 [#{\a} :q1]}

;; F = #{}