(ns dregex.core
  "an implementation of derivative regular expressions"
  (:use [clojure.set :only (difference union intersection)])
  (:use [clojure.contrib.seq :only (find-first)]))

(def ^{:doc "The default alphabet of characters that will be used
in complements of a language."}
  *alphabet*
  (into #{} (map char (range 32 127))))

(defn meet
  "Computes the set, a intersect b for all a is an element of r, b is
   an element of s"
  [r s]
  (into #{}
        (for [a r, b s :when (not (and (nil? a) (nil? b)))]
          (cond
           (nil? a) b
           (nil? b) a
           :else (intersection a b)))))


(defprotocol Matchable
  "Provides the necessary machinery to match a string.

  A regular expression that is compiled, is turned into a DFA, which is
  essentially a state machine that consumes a stream of characters and
  checks to see if when the stream runs out it was last at a final state.
  If it was, the regular expression represented by the DFA matched that
  input stream"
  (match [this s] "determines whether or not s is part of the language"))

(defprotocol REDerivable
  "Provides the operations needed on a regular expression to convert it
   into a DFA that can be used for matching.

  Janusz Brzozowski, in 1965 defined the derivation of regular expressions,
  and the V (or 'nullable') operator. The C (or 'derivative character
  classes') operator is thanks to Owens, Reppy, Turon."
  (deriv [this a] "Derivative of this RE with respect to a.")
  (V [this] "Is this RE nullable?")
  (C [this] "Derivative of character classes represented by RE."))

(defrecord ^{:private true} Epsilon []
           Object
           (toString [_] "eps"))

(extend-type Epsilon
  REDerivable
  (deriv [this a] nil)
  (V [this] this)
  (C [this] #{*alphabet*}))

(def ^{:doc "A singleton instance of the Epsilon record type for
  uniquely representing epsilon"}
  eps
  (Epsilon.))

(declare notnil ! . + & | *)

;;; Treatment of nil is as if nil was the #{} (i.e. the empty set)
(extend-type nil REDerivable
             (deriv [this a] nil)
             (V [_] nil)
             (C [_] (C #{})))

(extend-type Character REDerivable
             (deriv [this a]
               (cond
                (= a eps) this
                (= this a) eps
                :else nil))
             (V [_] nil)
             (C [this]
               (let [r #{this}]
                 #{r
                   (difference *alphabet* r)})))

(extend-type clojure.lang.PersistentHashSet REDerivable
             (deriv [this a]
               (if (= a eps)
                 this
                 (if (this a) eps nil)))
             (V [_] nil)
             (C [this] #{this
                         (difference *alphabet* this)}))

(defrecord Not [r]
  REDerivable
  (deriv [this a]
    (if (= a eps)
      this
      (! (deriv r a))))
  (V [_]
    (if (= (V r) eps) nil eps))
  (C [this] (C r))

  Object
  (toString [_] (str "(not " r ")")))

(def notnil (Not. nil))

(defrecord Concat [r s]
  REDerivable
  (deriv [this a]
    (if (= a eps)
      this
      (| (+ (deriv r a) s)
         (+ (V r) (deriv s a)))))
  (V [_]
    (and (V r) (V s)))
  (C [_]
    (if-not (V r) ;; (e.g. v(r) is not eps
      (C r)
      (meet (C r) (C s))))

  Object
  (toString [_] (str "(" r "." s ")")))

(defrecord Kleene [r]
  REDerivable
  (deriv [this a]
    (if (= a eps)
      this
      (+ (deriv r a) (* r))))
  (V [_] eps)
  (C [_] (C r))

  Object
  (toString [_] (str "(" r ")*")))

(defrecord Or [r s]
  REDerivable
  (deriv [this a]
    (if (= a eps)
      this
      (| (deriv r a) (deriv s a))))
  (V [_]
    (or (V r) (V s)))
  (C [_]
    (meet (C r) (C s)))

  Object
  (toString [_] (str "(" r " + " s ")")))

(defrecord And [r s]
  REDerivable
  (deriv [this a]
    (if (= a eps)
      this
      (& (deriv r a) (deriv s a))))
  (V [_]
    (or (V r) (V s)))
  (C [_]
    (meet (C r) (C s)))
  
  Object
  (toString [_] (str "(" r " & " s ")")))


(defn +
  "Returns a regular expression that matches the concatenation of the
   two regular expressions `r` and `s`"
  [r s]
  (cond
   (or (= nil r) (= nil s)) nil
   (= eps r) s
   (= eps s) r
   :else (Concat. r s)))

(defn *
  "Kleene star. Matches the regular expression `r` 0 or unlimited times"
  [r]
  (cond
   (= (class r) Kleene) r
   (= r eps) eps
   (= r nil) eps
   :else (Kleene. r)))

;;; || and && have other associativity optimizations that
;;; could be done. We'll deal with that later.
(defn |
  "Logical or. Matches either `r` or `s`"
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

(defn &
  "Logical and. Matches both `r` and `s`"
  [r s]
  (cond
   (= r s) r
   (= nil r) nil
   (= notnil r) s
   :else (And. r s)))

(defn !
  "Complement. Matches the opposite of `r`"
  [r]
  (cond
   (= (class r) Not) (:r r)
   (instance? Character r) (difference *alphabet* #{r})
   (instance? clojure.lang.PersistentHashSet r) (difference *alphabet* r)
   :else (Not. r)))

(comment
  (= eps (V (deriv \a \a))) ;; matches \a
  (= eps (V (deriv (! \a) \b))) ;; matches ^\a

  (= eps (V
          (deriv
           (deriv
            (+ (| \a \b) (! \b)) ;; matches (a|b)[^b]
            \b)
           \z)))

  ;; obviously we need a better way, so we'll build a DFA out of it.
  )

(defn- make-label
  [n]
  (keyword (str "q" n)))

(defn- goto
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

(defn- next-state
  "Finds the state to go to next when given `ch`

  `tests` is a hashmap from character sets to labels.
  `ch` is a character in the alphabet"
  [tests ch]
  (if (seq tests)
    (let [[s label] (first tests)]
      (if (s ch)
        label
        (recur (rest tests) ch)))
    nil))

(defn compile
  "Compiles a regular expression into a DFA which is Matchable."
  [re]
  (let [q0 (deriv re eps)
        [Q labels d] (explore {q0 :q0} {:q0 q0} {} q0)
        F (apply hash-set (map second (filter #(= (V (first %)) eps) Q)))]
    (reify Matchable
      (match [this s]
        (loop [label :q0
               stream s]
          (if (and (seq stream) label)
            (recur (next-state (label d) (first stream)) (rest stream))
            (cond
             (nil? label) false
             (F label) true
             :else false)))))))


(comment
  (= (match
      (compile
       (+ (| \a \b) (! \b)))
      "az")
     true)

  (= (match
      (compile
       (+ (| \a \b) (! \b)))
      "ab")
     true)
  )