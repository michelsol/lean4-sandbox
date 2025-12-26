import Mathlib

/- Let $\mathbb{N}$ be the set of positive integers.
Find all functions $f: \mathbb{N} \rightarrow \mathbb{N}$ that satisfy the equation  $ f^{a b c-a}(a b c)+f^{a b c-b}(a b c)+f^{a b c-c}(a b c)=a+b+c $
for all $a, b, c \geq 2$. (Here $f^{k}$ means $f$ applied $k$ times.) -/
theorem number_theory_604926 (f : ℕ → ℕ) :
    (∀ a b c, a ≥ 2 → b ≥ 2 → c ≥ 2 →
      f^[a * b * c - a] (a * b * c) +
        f^[a * b * c - b] (a * b * c) +
        f^[a * b * c - c] (a * b * c) =
      a + b + c) ↔ ∀ n ≥ 3, f n = n - 1 := by
  constructor
  . intro h1
-- Lemma. We have $f^{t^{2}-t}\left(t^{2}\right)=t$ for all $t \ge 2$.
    have h2 (t : ℕ) (ht : t ≥ 2) : f^[t ^ 2 - t] (t ^ 2) = t := by
-- We say $1 ≤ k ≤ 8$ is good if $f^{t^{9}-t^{k}}(t^{9})=t^k$.
-- First we observe that $ f^{t^{9}-t^{3}}\left(t^{9}\right)=t^{3} \quad \text { and } \quad f^{t^{3}-t}\left(t^{3}\right)=t \Longrightarrow f^{t^{9}-t}\left(t^{9}\right)=t $ so $k=1$ and $k=3$ are good.
      have c1 (t : ℕ) (ht : t ≥ 2) : f^[t ^ 9 - t ^ 3] (t ^ 9) = t ^ 3 := by
        have e1 : t ^ 3 ≥ 2 := calc
          t ^ 3 ≥ 2 ^ 3 := by exact Nat.pow_le_pow_of_le_left ht 3
          _ ≥ 2 := by norm_num
        specialize h1 (t ^ 3) (t ^ 3) (t ^ 3) e1 e1 e1
        ring_nf at h1 ⊢
        linarith

      have c2 (t : ℕ) (ht : t ≥ 2) : f^[t ^ 9 - t] (t ^ 9) = t := by
        have d1 (t : ℕ) (ht : t ≥ 2) : f^[t ^ 3 - t] (t ^ 3) = t := by
          specialize h1 t t t ht ht ht
          ring_nf at h1 ⊢
          linarith

        specialize c1 t ht
        specialize d1 t ht
        calc
          f^[t ^ 9 - t] (t ^ 9) = f^[(t ^ 3 - t) + (t ^ 9 - t ^ 3)] (t ^ 9) := by
            congr 1
            zify
            have d1 : t ^ 9 ≥ t := Nat.le_self_pow (by norm_num) t
            have d2 : t ^ 3 ≥ t := Nat.le_self_pow (by norm_num) t
            have d3 : t ^ 9 ≥ t ^ 3 := calc
              _ = (t ^ 3) ^ 3 := by ring
              _ ≥ _ := Nat.le_self_pow (by norm_num) (t ^ 3)
            push_cast [d1, d2, d3]
            ring
          _ = f^[t ^ 3 - t] (f^[t ^ 9 - t ^ 3] (t ^ 9)) := by apply Function.iterate_add_apply
          _ = f^[t ^ 3 - t] (t ^ 3) := by rw [c1]
          _ = t := by rw [d1]

-- Then taking $(a, b, c)=\left(t, t^{4}, t^{4}\right),(a, b, c)=\left(t^{2}, t^{3}, t^{4}\right)$ gives that $k=4$ and $k=2$ are good, respectively.
      have c3 (t : ℕ) (ht : t ≥ 2) : f^[t ^ 9 - t ^ 4] (t ^ 9) = t ^ 4 := by
        have d1 : t ^ 4 ≥ 2 := calc
          t ^ 4 ≥ 2 ^ 4 := by apply Nat.pow_le_pow_of_le_left ht
          _ ≥ 2 := by norm_num
        specialize h1 t (t ^ 4) (t ^ 4) ht d1 d1
        ring_nf at h1
        rw [c2 t ht] at h1
        simpa using h1

      have c4 (t : ℕ) (ht : t ≥ 2) : f^[t ^ 9 - t ^ 2] (t ^ 9) = t ^ 2 := by
        have d1 : t ^ 2 ≥ 2 := calc
          t ^ 2 ≥ 2 ^ 2 := by apply Nat.pow_le_pow_of_le_left ht
          _ ≥ 2 := by norm_num
        have d2 : t ^ 3 ≥ 2 := calc
          t ^ 3 ≥ 2 ^ 3 := by apply Nat.pow_le_pow_of_le_left ht
          _ ≥ 2 := by norm_num
        have d3 : t ^ 4 ≥ 2 := calc
          t ^ 4 ≥ 2 ^ 4 := by apply Nat.pow_le_pow_of_le_left ht
          _ ≥ 2 := by norm_num
        specialize h1 (t ^ 2) (t ^ 3) (t ^ 4) d1 d2 d3
        ring_nf at h1
        rw [c1 t ht, c3 t ht] at h1
        simpa using h1

-- The lemma follows from k=1 and 2 being good.
      calc
        f^[t ^ 2 - t] (t ^ 2) = f^[t ^ 2 - t] (f^[t ^ 9 - t ^ 2] (t ^ 9)) := by rw [c4 t ht]
        _ = f^[(t ^ 2 - t) + (t ^ 9 - t ^ 2)] (t ^ 9) := by rw [Function.iterate_add_apply]
        _ = f^[t ^ 9 - t] (t ^ 9) := by
          congr 1
          zify
          have d1 : t ^ 9 ≥ t ^ 2 := Nat.pow_le_pow_of_le ht (by norm_num)
          have d2 : t ^ 9 ≥ t := Nat.le_self_pow (by norm_num) t
          have d3 : t ^ 2 ≥ t := Nat.le_self_pow (by norm_num) t
          push_cast [d1, d2, d3]
          ring
        _ = t := by rw [c2 t ht]

-- Now, letting $t=a b c$ we combine $ \begin{aligned} f^{t-a}(t)+f^{t-b}(t)+f^{t-c}(t) & =a+b+c \\ f^{t^{2}-a b}\left(t^{2}\right)+f^{t^{2}-t}\left(t^{2}\right)+f^{t^{2}-c}\left(t^{2}\right) & =a b+t+c \\ \Longrightarrow\left[f^{t-a}(t)-a\right]+\left[f^{t-b}(t)-b\right] & =\left[f^{t-a b}(t)-a b\right] \end{aligned} $

-- by subtracting and applying the lemma repeatedly.
    have h3 (a b c : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hc : c ≥ 2) :
        let t := a * b * c
        (f^[t - a] t - a) + (f^[t - b] t - b) = f^[t - a * b] t - a * b := by
      sorry

-- Thus if $p>q>\max\{a,b\}$ are primes then upon setting $s=a^{p} b^{q}$ and $t=s^{2}$ we get
-- $p \left[f^{t-a}(t)-a\right] + q \left[f^{t-b}(t)-b\right] = \left[f^{t-s}(t)-s\right] = 0$
-- So $q ∣ f^{t-a}(t)-a$ and $p ∣ f^{t-b}(t)-b$
-- $f^{t-a}(t) - a \ge -a > -q$ so $f^{t-a}(t) - a \ge 0$. Similarly, $f^{t-b}(t) - b \ge 0$.
-- As the weighted sum is zero, we conclude that $f^{t-a}(t)=a$ and $f^{t-b}(t)=b$.
    have h4 (a b p q : ℕ) (ha : a ≥ 2) (hb : b ≥ 2)
      (hp : p.Prime)  (hp2 : p > a) (hp3 : p > b) (hp4 : p > q)
      (hq : q.Prime) (hq2 : q > a) (hq3 : q > b) :
        let s := a ^ p * b ^ q
        let t := s ^ 2
        f^[t - a] t = a ∧ f^[t - b] t = b := by
      intro s t

      have c1 : p * (f^[t - a] t - a) + q * (f^[t - b] t - b) = f^[t - s] t - s := by
        sorry

      replace c1 : p * (f^[t - a] t - a) + q * (f^[t - b] t - b) = 0 := by
        sorry

      have c2 : (q : ℤ) ∣ f^[t - a] t - a := by
        sorry

      have c3 : (p : ℤ) ∣ f^[t - b] t - b := by
        sorry

      have c4 : f^[t - a] t = a := by
        sorry

      have c5 : f^[t - b] t = b := by
        sorry

      exact ⟨c4, c5⟩

-- In particular, if $a=n$ and $b=n+1$, then we deduce that $f(n+1)=n$ for all $n \geq 2$.
    have h5 (n : ℕ) (hn : n ≥ 2) : f (n + 1) = n := by
      let a := n
      let b := n + 1
      obtain ⟨p, q, hp, hp2, hp3, hp4, hq, hq2, hq3, _⟩ :
          ∃ (p q : ℕ) (hp : p.Prime)  (hp2 : p > a) (hp3 : p > b) (hp4 : p > q)
              (hq : q.Prime) (hq2 : q > a) (hq3 : q > b), True := by
        sorry

      specialize h4 a b p q hn (by omega) hp hp2 hp3 hp4 hq hq2 hq3
      obtain ⟨c1, c2⟩ := h4
      set t := (a ^ p * b ^ q) ^ 2
      symm
-- Details: $n = a = f^{t-a}(t) = f^{t-n}(t) = f(f^{t-(n+1)}(t)) = f(f^{t-b}(t)) = f(b) = f(n+1)$
      calc
        n = a := by rfl
        _ = f^[t - a] t := by rw [c1]
        _ = f^[t - n] t := by rfl
        _ = f^[t - (n + 1) + 1] t := by
          congr 1
          suffices t ≥ b by omega
          sorry
        _ = f (f^[t - (n + 1)] t) := by rw [Function.iterate_succ_apply']
        _ = f (f^[t - b] t) := by rfl
        _ = f b := by rw [c2]
        _ = f (n + 1) := by rfl

    intro n hn
    convert h5 (n - 1) (by omega) using 2
    omega

-- Conversely, we easily check that $f(n)=n-1$ for $n \geq 3$ with $f(1)$ and $f(2)$ arbitrary works.
  . intro h1 a b c ha hb hc
    have h2 (n k : ℕ) (c1 : k ≤ n - 2) : f^[k] n = n - k := by
      induction' k with k ih
      . simp
      . rw [Function.iterate_succ_apply', ih (by omega), h1 _ (by omega)]
        omega
    iterate 3 rw [h2]
    . zify
      have c1 : a * b * c ≥ a * b * c - a := by omega
      have c2 := calc
        a * b * c ≥ a * 2 * 2 := by
          refine Nat.mul_le_mul ?_ hc
          exact Nat.mul_le_mul_left a hb
        _ ≥ a := by omega
      have c3 : a * b * c ≥ a * b * c - b := by omega
      have c4 := calc
        a * b * c ≥ 2 * b * 2 := by
          refine Nat.mul_le_mul ?_ hc
          exact Nat.mul_le_mul_right b ha
        _ ≥ b := by omega
      have c5 : a * b * c ≥ a * b * c - c := by omega
      have c6 := calc
        a * b * c ≥ 2 * 2 * c := by
          refine Nat.mul_le_mul_right c ?_
          exact Nat.mul_le_mul ha hb
        _ ≥ c := by omega
      push_cast [c1, c2, c3, c4, c5, c6]
      ring
    . omega
    . omega
    . omega
