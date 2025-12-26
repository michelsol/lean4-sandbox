import Mathlib

/-
The sequence $a_{0}, a_{1}, a_{2}, \ldots$ of positive integers satisfies

$ a_{n+1}=\left\{\begin{array}{ll} \sqrt{a_{n}}, & \text { if } \sqrt{a_{n}} \text { is an integer } \\ a_{n}+3, & \text { otherwise } \end{array} \quad \text { for every } n \geqslant 0\right. $

Determine all values of $a_{0}>1$ for which
there is at least one number $a$ such that $a_{n}=a$ for infinitely many values of $n$.
-/

open Classical in
theorem number_theory_25005
    (a : ℕ → ℤ)
    (ha : ∀ n, 0 < a n)
    (ha0 : a 0 > 1)
    (ha1 : ∀ n, a (n + 1) = if ∃ m : ℕ, √(a n) = m then √(a n) else a n + 3)
    : (∃ n0, { k | a k = a n0 }.Infinite) ↔ 3 ∣ a 0 := by
  let EventuallyPeriodic (a : ℕ → ℤ) := ∃ n0, ∃ T > 0, ∀ n ≥ n0, a (n + T) = a n
  have h0 (a : ℕ → ℤ) n0 T (hT : T > 0) (h : ∀ n ≥ n0, a (n + T) = a n) :
      ∀ n ≥ n0, ∀ k ≥ 1, a (n + k * T) = a n := by
    intro n hn
    apply Nat.le_induction
    . convert h n hn using 2
      omega
    . intro k hk ih
      calc
        _ = a (n + k * T + T) := by congr 1; ring
        _ = a (n + k * T) := by rw [h]; omega
        _ = _ := by rw [ih]

-- Since the value of $a_{n+1}$ only depends on the value of $a_{n}$,
-- if $a_{n}=a_{m}$ for two different indices $m > n$ then the sequence is eventually periodic.
  have h1 n m (hnm : m > n) (h : a n = a m) : EventuallyPeriodic a := by
    let f (k : ℤ) := if ∃ m : ℕ, √k = m then √k else k + 3
    replace h1 n : a (n + 1) = f (a n) := ha1 n
    use n
    use m - n, by omega
    apply Nat.le_induction
    . calc
        _ = a m := by congr 1; omega
        _ = a n := h.symm
    . intro p hnp ih
      rify
      calc
        (_ : ℝ) = a (p + (m - n) + 1) := by congr 2; omega
        _ = f (a (p + (m - n))) := by rw [h1]
        _ = f (a p) := by rw [ih]
        _ = _ := by rw [h1]

-- So we look for the values of $a_{0}$ for which the sequence is eventually periodic.
  suffices EventuallyPeriodic a ↔ 3 ∣ a 0 from by
    convert this using 1
    constructor
    . intro ⟨n0, g1⟩
      have ⟨m, hm1, hm2⟩ := g1.exists_gt n0
      exact h1 n0 m hm2 (by rw [hm1])
    . intro ⟨n0, T, hT, g1⟩
      use n0
      refine Nat.frequently_atTop_iff_infinite.mp ?_
      refine Filter.frequently_atTop.mpr ?_
      intro M
      have ⟨k, hk, g2⟩ : ∃ k ≥ 1, n0 + k * T ≥ M := by
        use M + 1, by simp
        calc
          _ = n0 + M * T + T := by ring
          _ ≥ n0 + M + T := by
            gcongr
            exact Nat.le_mul_of_pos_right M hT
          _ ≥ M := by omega
      use n0 + k * T
      use g2
      exact h0 a n0 T hT g1 n0 (by omega) k hk

-- Claim 1.
-- If $a_{n} \equiv-1(\bmod 3)$, then, for all $m > n, a_{m}$ is not a perfect square.
  have h2 n (h : a n ≡ -1 [ZMOD 3]) m (hnm : m > n) : ¬IsSquare (a m) := by
-- Proof.
-- A square cannot be congruent to -1 modulo 3 ,
-- so $a_{n} \equiv-1(\bmod 3)$ implies that $a_{n}$ is not a square, therefore $a_{n+1}=a_{n}+3 > a_{n}$.
    have g1 : a (n + 1) = a n + 3 := by
      sorry
    have g2 : a (n + 1) > a n := by
      sorry
-- As a consequence, $a_{n+1} \equiv a_{n} \equiv-1(\bmod 3)$, so $a_{n+1}$ is not a square either.
    have g3 : a (n + 1) ≡ -1 [ZMOD 3] := by
      sorry
-- By repeating the argument, we prove that, from $a_{n}$ on, all terms of the sequence
-- are not perfect squares and are greater than their predecessors, which completes the proof.
    have g4 : ∀ k ≥ n, ¬IsSquare (a (k + 1)) ∧ a (k + 1) > a k := by
      apply Nat.le_induction
      . sorry
      . sorry

    specialize g4 (m - 1) (by omega)
    convert g4.left using 3
    omega

-- It follows that the sequence is eventually strictly increasing,
-- so it is not eventually periodic.
  have h3 n (h : a n ≡ -1 [ZMOD 3]) m (hnm : m > n) :
      ¬EventuallyPeriodic a := by
    sorry

-- Claim 2.
-- If $a_{n} \not \equiv-1(\bmod 3)$ and $a_{n} > 9$ then there is an index $m > n$ such that $a_{m} < a_{n}$.
  have h4 n (h : ¬a n ≡ -1 [ZMOD 3]) (h2 : a n > 9) : ∃ m > n, a m < a n := by
-- Proof.
-- Let $t^{2}$ be the largest perfect square which is less than $a_{n}$.
    have ⟨t, g1, g2⟩ : ∃ t : ℕ, t ^ 2 < a n ∧ ∀ t' : ℕ, t' ^ 2 < a n → t' ≤ t := by
      sorry
-- Since $a_{n} > 9$, $t$ is at least 3.
    have g3 : t ≥ 3 := by
      sorry
-- The first square in the sequence $a_{n}, a_{n}+3, a_{n}+6, \ldots$ will be $(t+1)^{2},(t+2)^{2}$ or $(t+3)^{2}$,
-- therefore there is an index $m > n$ such that $a_{m} \leqslant t+3 < t^{2} < a_{n}$, as claimed.
    sorry

-- Claim 3.
-- If $a_{n} \equiv 0(\bmod 3)$, then there is an index $m > n$ such that $a_{m}=3$.
  have h5 n (h : a n ≡ 0 [ZMOD 3]) : ∃ m > n, a m = 3 := by
-- Proof.
-- First we notice that, by the definition of the sequence,
-- a multiple of 3 is always followed by another multiple of 3 .
    have g1 : ∀ k ≥ n, a (k + 1) ≡ 0 [ZMOD 3] := by
      apply Nat.le_induction
      . sorry
      . sorry
-- If $a_{k} \in\{3,6,9\}$ the sequence will eventually follow  the periodic pattern $3,6,9,3,6,9, \ldots$
    have g2 k (hk : k ≥ n) (f1 : a k = 3 ∨ a k = 6 ∨ a k = 9) :
        ∃ n0 > n, ∀ l,
          a (n0 + 3 * l + 0) = 3 ∧ a (n0 + 3 * l + 1) = 6 ∧ a (n0 + 3 * l + 2) = 9 := by
      sorry
-- If $a_{n} > 9$, let $j$ be an index such that $a_{j}$ is equal to
-- the minimum value of the set $\left\{a_{n+1}, a_{n+2}, \ldots\right\}$.
    have ⟨j, g3, g3'⟩ : ∃ j > n, ∀ k > n, a j ≤ a k := by
      sorry
-- We must have $a_{j} \leqslant 9$, otherwise we could apply Claim 2 to $a_{j}$
-- and get a contradiction on the minimality hypothesis.
    have g4 : a j ≤ 9 := by
      sorry
-- It follows that $a_{j} \in\{3,6,9\}$, and the proof is complete.
    have g5 : a j = 3 ∨ a j = 6 ∨ a j = 9 := by
      sorry
    have ⟨m, g6, g7⟩ := g2 j (by omega) g5
    use m, g6
    convert (g7 0).left using 1

-- Claim 4.
-- If $a_{n} \equiv 1(\bmod 3)$, then there is an index $m > n$ such that $a_{m} \equiv-1(\bmod 3)$.
  have h6 n (h : a n ≡ 1 [ZMOD 3]) : ∃ m > n, a m ≡ -1 [ZMOD 3] := by
-- Proof.
-- In the sequence, 4 is always followed by $2 \equiv-1(\bmod 3)$, so the claim is true for $a_{n}=4$.
    have g1 : a n = 4 → ∃ m > n, a m ≡ -1 [ZMOD 3] := by
      sorry
-- If $a_{n}=7$, the next terms will be $10,13,16,4,2, \ldots$ and the claim is also true.
    have g2 : a n = 7 → ∃ m > n, a m ≡ -1 [ZMOD 3] := by
      sorry
-- For $a_{n} \geqslant 10$, we again take an index $j > n$ such that $a_{j}$ is equal
-- to the minimum value of the set $\left\{a_{n+1}, a_{n+2}, \ldots\right\}$,
    have ⟨j, g3, g3'⟩ : ∃ j > n, ∀ k > n, a j ≤ a k := by
      sorry
-- which by the definition of the sequence consists of non-multiples of 3 .
    have g4 (f1 : a n ≥ 10) : ∀ k > n, ¬a k ≡ 0 [ZMOD 3] := by
      apply Nat.le_induction
      . sorry
      . sorry
-- Suppose $a_{j} \equiv 1(\bmod 3)$.
-- Then we must have $a_{j} \leqslant 9$ by Claim 2 and the minimality of $a_{j}$.
    have g5 (f1 : a n ≥ 10) (f2 : a j ≡ 1 [ZMOD 3]) : a j ≤ 9 := by
      sorry
-- It follows that $a_{j} \in\{4,7\}$, so $a_{m}=2 < a_{j}$ for some $m > j$, contradicting the minimality of $a_{j}$.
    have g6 (f1 : a n ≥ 10) (f2 : a j ≡ 1 [ZMOD 3]) : False := by
      sorry
-- Therefore, we must have $a_{j} \equiv-1(\bmod 3)$.
    have g7 (f1 : a n ≥ 10) : a j ≡ -1 [ZMOD 3] := by
      sorry

-- By definition of the sequence, $a_n > 1$.
    have g8 : a n > 1 := by
      generalize n = n
      induction' n with n ih
      . exact ha0
      . specialize ha1 n
        rify at ih ⊢
        rw [ha1]
        split_ifs with f1
        . obtain ⟨m, f1⟩ := f1
          refine Real.lt_sqrt_of_sq_lt ?_
          linarith
        . linarith
    obtain g9 | g9 | g9 : a n = 4 ∨ a n = 7 ∨ a n ≥ 10 := by
      rw [Int.ModEq] at h
      omega
    . exact g1 g9
    . exact g2 g9
    . use j, g3
      exact g7 g9

-- It follows from the previous claims that if $a_{0}$ is a multiple of 3 the sequence will
-- eventually reach the periodic pattern $3,6,9,3,6,9, \ldots$;
  have h7 (h : a 0 ≡ 0 [ZMOD 3]) : EventuallyPeriodic a := by
    sorry

-- if $a_{0} \equiv-1(\bmod 3)$ the sequence will be strictly increasing;
  have h8 (h : a 0 ≡ -1 [ZMOD 3]) : ¬EventuallyPeriodic a := by
    sorry

-- and if $a_{0} \equiv 1(\bmod 3)$ the sequence will be eventually strictly increasing.
  have h9 (h : a 0 ≡ 1 [ZMOD 3]) : ¬EventuallyPeriodic a := by
    sorry

-- So the sequence will be eventually periodic if, and only if, $a_{0}$ is a multiple of 3 .
  have h10 : EventuallyPeriodic a ↔ 3 ∣ a 0 := by
    constructor <;> intro g1
    . by_contra g2
      obtain g3 | g3 : a 0 ≡ -1 [ZMOD 3] ∨ a 0 ≡ 1 [ZMOD 3] := by
        iterate 2 rw [Int.ModEq]
        omega
      . exact h8 g3 g1
      . exact h9 g3 g1
    . exact h7 (by rw [Int.ModEq]; omega)

  exact h10
