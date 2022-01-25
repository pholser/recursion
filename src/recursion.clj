(ns recursion)

(defn product [coll]
  (if (empty? coll)
    1
    (* (first coll) (product (rest coll)))))

(defn singleton? [coll]
  (and ((complement empty?) coll) (empty? (rest coll))))

(defn my-last [coll]
  (cond (empty? coll) nil
        (singleton? coll) (first coll)
        :else (my-last (rest coll))))

(defn max-element [a-seq]
  (cond (empty? a-seq) nil
        (singleton? a-seq) (first a-seq)
        :else (let [current-max (first a-seq)
                    rest-max (max-element (rest a-seq))]
                (if (> current-max rest-max) current-max rest-max))))

(defn seq-max [seq-1 seq-2]
  (max-key count seq-1 seq-2))

(defn longest-sequence [a-seq]
  (cond (empty? a-seq) nil
        (singleton? a-seq) (first a-seq)
        :else (let [current-max (first a-seq)
                    rest-max (longest-sequence (rest a-seq))]
                (seq-max current-max rest-max))))

(defn my-filter [pred? a-seq]
  (cond (nil? a-seq) '()
        (empty? a-seq) a-seq
        :else (let [fst (first a-seq)]
                (if (pred? fst)
                  (cons fst (my-filter pred? (rest a-seq)))
                  (my-filter pred? (rest a-seq))))))

(defn sequence-contains? [elem a-seq]
  (cond (nil? a-seq) false
        (empty? a-seq) false
        :else (or (= elem (first a-seq))
                  (sequence-contains? elem (rest a-seq)))))

(defn my-take-while [pred? a-seq]
  (cond (nil? a-seq) '()
        (empty? a-seq) '()
        :else (let [fst (first a-seq)]
                (if (pred? fst)
                  (cons fst (my-take-while pred? (rest a-seq)))
                  '()))))

(defn my-drop-while [pred? a-seq]
  (cond (nil? a-seq) '()
        (empty? a-seq) '()
        :else (let [fst (first a-seq)]
                (if (pred? fst)
                  (my-drop-while pred? (rest a-seq))
                  a-seq))))

(defn seq= [a-seq b-seq]
  (cond (nil? a-seq) (nil? b-seq)
        (empty? a-seq) (empty? b-seq)
        :else (and (= (first a-seq) (if (empty? b-seq) false (first b-seq)))
                   (seq= (rest a-seq) (rest b-seq)))))

(defn my-map [f seq-1 seq-2]
  (if (or (empty? seq-1) (empty? seq-2))
    '()
    (cons (f (first seq-1) (first seq-2))
          (my-map f (rest seq-1) (rest seq-2)))))

(defn power [n k]
  (cond (= 0 n) 0
        (= 1 n) 1
        (= 0 k) 1
        :else (* n (power n (dec k)))))

(defn fib [n]
  (cond (= 0 n) 0
        (= 1 n) 1
        :else (+ (fib (dec n)) (fib (- n 2)))))

(defn my-repeat [how-many-times what-to-repeat]
  (if (<= how-many-times 0)
    '()
    (cons what-to-repeat (my-repeat (dec how-many-times) what-to-repeat))))

(defn my-range [up-to]
  (if (<= up-to 0)
    '()
    (cons (dec up-to) (my-range (dec up-to)))))

(defn tails [a-seq]
  (if (empty? a-seq)
    '(())
    (cons a-seq (tails (rest a-seq)))))

(defn inits [a-seq]
  (map reverse (tails (reverse a-seq))))

(defn rotations [a-seq]
  (let [tails (tails a-seq)
        heads (inits a-seq)]
    (set (map concat tails (reverse heads)))))

(defn my-frequencies-helper [freqs a-seq]
  (if (empty? a-seq)
    freqs
    (my-frequencies-helper
      (update freqs (first a-seq) (fn [old-val] (if (nil? old-val) 1 (inc old-val))))
      (rest a-seq))))

(defn my-frequencies [a-seq]
  (my-frequencies-helper {} a-seq))

(defn un-frequencies-helper [a-map acc]
  (if (empty? a-map)
    acc
    (let [[val count] (first a-map)]
      (un-frequencies-helper
        (dissoc a-map val)
        (concat acc (repeat count val))))))

(defn un-frequencies [a-map]
  (un-frequencies-helper a-map '()))

(defn my-take [n coll]
  (cond (empty? coll) '()
        (<= n 0) '()
        :else (cons (first coll) (my-take (dec n) (rest coll)))))

(defn my-drop [n coll]
  (cond (empty? coll) '()
        (<= n 0) coll
        :else (my-drop (dec n) (rest coll))))

(defn halve [a-seq]
  (let [midpoint (int (/ (count a-seq) 2))]
    [(take midpoint a-seq) (drop midpoint a-seq)]))

(defn seq-merge [a-seq b-seq]
  (cond (empty? a-seq) b-seq
        (empty? b-seq) a-seq
        :else (let [a (first a-seq)
                    b (first b-seq)]
                (if (<= a b)
                  (cons a (seq-merge (rest a-seq) b-seq))
                  (cons b (seq-merge a-seq (rest b-seq)))))))

(defn merge-sort [a-seq]
  (cond (empty? a-seq) '()
        (singleton? a-seq) a-seq
        :else (let [[side1 side2] (halve a-seq)]
                (seq-merge (merge-sort side1) (merge-sort side2)))))

(defn accumulate-monotonic [acc last op a-seq]
  (loop [acc acc last last op op a-seq a-seq]
    (cond (empty? a-seq) (seq acc)
          ((complement op) last (first a-seq)) (seq acc)
          :else (recur (conj acc (first a-seq)) (first a-seq) op (rest a-seq)))))

(defn split-into-monotonics-helper [a-seq acc]
  (cond (empty? a-seq) acc
        (singleton? a-seq) a-seq
        :else (let [fst (first a-seq)
                    snd (second a-seq)
                    op (if (<= fst snd) <= >=)
                    first-run (accumulate-monotonic [fst snd] snd op (next (next a-seq)))]
                (split-into-monotonics-helper
                  (drop (count first-run) a-seq)
                  (conj acc first-run)))))

(defn split-into-monotonics [a-seq]
  (seq (split-into-monotonics-helper a-seq [])))

;; permutations (1 2 3 4)
;; = 1 threaded thru
;;   permutations (2 3 4)
;;   = 2 threaded thru
;;     permutations (3 4)
;;     = 3 threaded thru
;;       permutations (4)
;;       = [4]
;;      = [3 4] [4 3]
;;   = [2 3 4] [3 2 4] [3 4 2] [2 4 3] [4 2 3] [4 3 2]
;; = [1 2 3 4] [2 1 3 4] [2 3 1 4] [2 3 4 1]

(defn thread-thru [e a-seq]
  (->> (range (inc (count a-seq)))
       (map #(concat (take % a-seq) [e] (drop % a-seq)))))

(defn permutations [a-set]
  (cond (empty? a-set) '(())
        (singleton? a-set) (cons (seq a-set) '())
        :else (let [e (first a-set)
                    xs (rest a-set)]
                (mapcat (partial thread-thru e) (permutations xs)))))

(defn powerset [a-set]
  (let [s (set a-set)]
    (if (empty? s)
      #{#{}}
      (apply clojure.set/union
        #{s}
        (let [one-lessers (map (partial disj s) s)]
          (map set (map powerset one-lessers)))))))
