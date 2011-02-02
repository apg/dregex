(ns dregex.core)

(defprotocol RE
 (deriv [this a])
 (V [this]))

(defrecord ^{:private true} Epsilon []
           Object
           (toString [_] "eps"))

(extend-type Epsilon
  RE
  (deriv [this a]
    nil)
  (V [this]
    this))

(def eps (Epsilon.))

(declare notnil !! ++ && || **)


(extend-type nil RE
            (deriv [this a]
              nil)
            (V [_]
              nil))

(extend-type Character RE
            (deriv [this a]
              (if (= this a)
                eps
                nil))
            (V [_]
              nil))

(defrecord Not [r]
  RE
  (deriv [this a]
    (!! (deriv r a)))
  (V [_]
    (if (= (V r) eps)
      nil
      eps))

  Object
  (toString [_] (str "(not " r ")")))

(def notnil (Not. nil))

(defrecord Concat [r s]
  RE
  (deriv [this a]
    (|| (++ (deriv r a) s)
        (++ (V r) (deriv s a))))
  (V [_]
    (and (V r) (V s)))

  Object
  (toString [_] (str "(" r "." s ")")))

(defrecord Kleene [r]
  RE
  (deriv [this a]
    (++ (deriv r a) (** r)))
  (V [_]
    eps)

  Object
  (toString [_] (str "(" r ")*")))

(defrecord Or [r s]
  RE
  (deriv [this a]
    (|| (deriv r a) (deriv s a)))
  (V [_]
    (or (V r) (V s)))

  Object
  (toString [_] (str "(" r " + " s ")")))

(defrecord And [r s]
  RE
  (deriv [this a]
    (&& (deriv r a) (deriv s a)))
  (V [_]
    (or (V r) (V s)))

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
  (cond
   (= r s) r
   (= notnil r) notnil
   (= nil r) s
   :else (Or. r s)))

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
  (if (= (class r) Not)
    (:r r)
    (Not. r)))

(comment
  (= eps (V (deriv \a \a))) ;; matches \a
  (= eps (V (deriv (!! \a) \b))) ;; matches ^\a
  (= eps
     (V

      ))
  (= eps (V
          (deriv
           (deriv
            (++ (|| \a \b) (!! \b)) ;; matches (a|b)[^b]
            \b)
           \z)))

  ;; obviously we need a better way, so we'll build a DFA out of it.
  )