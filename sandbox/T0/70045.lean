import Mathlib

open Finset

/-
For all primes $p \geq 3,$ define $F(p) = \sum^{\frac{p-1}{2}}_{k=1}k^{120}$ and $f(p) = \frac{1}{2} - \left\{ \frac{F(p)}{p} \right\}$,
where $\{x\} = x - [x],$ find the value of $f(p).$
-/
theorem number_theory_70045
    (F : ℕ → ℕ) (hF : ∀ p, F p = ∑ k ∈ Icc 1 ((p - 1) / 2), k ^ 120)
    (f : ℕ → ℝ) (hf : ∀ p, f p = 1 / 2 - Int.fract (F p / p : ℝ))
    (p : ℕ) (hp1 : Nat.Prime p) (hp2 : p ≥ 3)
    : f p = if p - 1 ∣ 120 then (1 / (2 * p) : ℝ) else 1 / 2 := by

  have hp : Fact (p.Prime) := ⟨hp1⟩
  have hp2 : NeZero p := by exact NeZero.of_gt'
  have hp3 : (2 : ZMod p) ≠ 0 := by
    refine ZMod.prime_ne_zero p 2 ?_
    omega

-- We are given $ 2F(p) =\sum^{\frac{p-1}{2}}_{k=1}(k^{120}+ k^{120}) \equiv \sum^{\frac{p-1}{2}}_{k=1}(k^{120} + (p-k)^{120}) \equiv \sum_{k=1}^{p-1}k^{120} \pmod p $
  have h1 : (2 * F p : ZMod p) = (∑ k ∈ Icc 1 (p - 1), (k ^ 120 : ZMod p)) := calc
    _ = ∑ k ∈ Icc 1 ((p - 1) / 2), (k ^ 120 + k ^ 120 : ZMod p) := by
      norm_cast
      congr 1
      sorry
    _ = ∑ k ∈ Icc 1 ((p - 1) / 2), (k ^ 120 + (p - k) ^ 120 : ZMod p) := by
      apply sum_congr rfl
      intro k hk
      congr 1
      calc
        (k ^ 120 : ZMod p) = (k - p) ^ 120 := by
          sorry
        _ = (p - k) ^ 120 := by
          sorry
    _ = ∑ k ∈ Icc 1 ((p - 1) / 2), (k ^ 120 : ZMod p)
        + ∑ k ∈ Icc 1 ((p - 1) / 2), ((p - k) ^ 120 : ZMod p) := by
      apply sum_add_distrib
    _ = ∑ k ∈ Icc 1 ((p - 1) / 2), (k ^ 120 : ZMod p)
        + ∑ k ∈ Icc ((p - 1) / 2 + 1) (p - 1), (k ^ 120 : ZMod p) := by
      sorry
    _ = ∑ k ∈ Icc 1 ((p - 1) / 2) ∪ Icc ((p - 1) / 2 + 1) (p - 1), (k ^ 120 : ZMod p) := by
      rw [sum_union]
      . sorry
    _ = _ := by
      congr 1
      ext k
      simp
      omega

-- As the multiplicative group of $ ℤ/pℤ $ is cyclic of order $p-1$,
-- we can find $r$ a primitive root modulo $p$,
-- so that $r,r^2, \cdots , r^{p-1}$ is a permutation of $1,2, \cdots , p-1$ modulo $p$ .
  obtain ⟨r, h2⟩ : ∃ (r : ZMod p), Set.BijOn (λ k ↦ r ^ k) (Icc 1 (p - 1)) {k | k ≠ 0} := by
    sorry

-- Reintrepret this bijection as going from ℕ to ℕ, in order to facilitate change of variables in sums.
  replace h2 : Set.BijOn (λ k ↦ (r ^ k).val) (Icc 1 (p - 1)) (Icc 1 (p - 1)) := by
    split_ands
    . replace h2 := h2.left
      intro k hk
      specialize h2 hk
      replace h2 : ¬(r ^ k).val = 0 := by simpa using h2
      have c1 := ZMod.val_lt (r ^ k)
      simp
      omega
    . replace h2 := h2.right.left
      intro i hi j hj hij
      simp at hi hj hij
      replace hij : r ^ i = r ^ j := by exact ZMod.val_injective p hij
      exact h2 (by simpa using hi) (by simpa using hj) hij
    . replace h2 := h2.right.right
      intro k hk
      obtain ⟨hk1, hk2⟩ := by simpa using hk
      have hk' : (k : ZMod p) ≠ 0 := by sorry
      specialize h2 hk'
      obtain ⟨j, hj1, hj2⟩ := by simpa using h2
      simp only [coe_Icc, Set.mem_image, Set.mem_Icc]
      use j, hj1
      simp only [hj2, ZMod.val_natCast]
      refine Nat.mod_eq_of_lt ?_
      omega



-- Therefore $F(p) = \frac 1 2 \sum_{k=1}^{p-1}k^{120} \equiv \frac 1 2 \sum_{i=1}^{p-1}r^{120i} \equiv \frac 1 2 \sum_{i=1}^{p-1} {(r^{120})}^{i} \pmod p$
  have h3 : (F p : ZMod p) = 1 / 2 * ∑ i ∈ Icc 1 (p - 1), (((r ^ 120) ^ i) : ZMod p) := calc
      _ = 1 / 2 * ∑ k ∈ Icc 1 (p - 1), (k ^ 120 : ZMod p) := calc
        (_ : ZMod p) = 1 / 2 * (2 * F p) := by field_simp
        _ = _ := by congr 1
      _ = 1 / 2 * ∑ i ∈ Icc 1 (p - 1), ((r ^ i).val ^ 120 : ZMod p) := by
        congr 1
        symm
        rw [sum_nbij (λ k ↦ (r ^ k).val)]
        . exact h2.left
        . exact h2.right.left
        . exact h2.right.right
        . simp
      _ = 1 / 2 * ∑ i ∈ Icc 1 (p - 1), (((r ^ 120) ^ i) : ZMod p) := by
        congr 1
        apply sum_congr rfl
        intro i hi
        simp
        ring


-- If $p-1 \nmid 120$ i.e. $r^{120} \not\equiv 1 \pmod p $
-- then $F(p) = \dfrac{r^{120}({r^{120(p-1)}}-1)}{2(r^{120} - 1)} = \dfrac{r^{120}({(r^{p-1})}^{120}-1)}{2(r^{120} - 1)} = \dfrac{r^{120}(1-1)}{2(r^{120} - 1)} = 0 \pmod p $  and $f(p) = \frac 12$
  have h4 (c1 : ¬p - 1 ∣ 120) : f p = 1 / 2 := by
    have c1' : r ^ 120 ≠ 1 := by
      sorry
    have c2 : (F p : ZMod p) = 0 := calc
      _ = 1 / 2 * ∑ i ∈ Icc 1 (p - 1), (((r ^ 120) ^ i) : ZMod p) := h3
      _ = r ^ 120 * ((r ^ 120) ^ (p - 1) - 1) / (2 * (r ^ 120 - 1)) := by
        sorry
      _ = r ^ 120 * ((r ^ (p - 1)) ^ 120 - 1) / (2 * (r ^ 120 - 1)) := by
        congr 3
        ring
      _ = r ^ 120 * (1 - 1) / (2 * (r ^ 120 - 1)) := by
        congr 3
        sorry
      _ = _ := by simp
    replace c2 : p ∣ F p := by exact (ZMod.natCast_zmod_eq_zero_iff_dvd (F p) p).mp c2
    calc
      f p = 1 / 2 - Int.fract (F p / p : ℝ) := by rw [hf]
      _ = 1 / 2 - 0 := by
        congr 1
        rw [Int.fract_eq_iff]
        split_ands
        . norm_num
        . norm_num
        . use F p / p
          simp [c2]
      _ = _ := by norm_num

-- If $p-1 \mid 120$ i.e. $r^{120} \equiv 0 \pmod p$ , then
-- $F(p) = \frac 12 \sum_{k=1}^{p-1}k^{120} \equiv \frac 12\sum_{i=1}^{p-1}r^{120i} \equiv \frac {p-1}{2} \pmod p $
-- So $ f(p) =\frac{1}{2}-\left\{\frac{F(p)}{p}\right\} = \frac 12 - \frac{p-1}{2p} = \frac {1}{2p}$
  have h5 (c1 : p - 1 ∣ 120) : f p = 1 / (2 * p) := by
    have c1' : r ^ 120 = 1 := by
      sorry
    have c2 : (F p : ZMod p) = (((p - 1) / 2 : ℕ) : ZMod p) := by
      sorry
    calc
      f p = 1 / 2 - Int.fract (F p / p : ℝ) := by rw [hf]
      _ = 1 / 2 - (p - 1) / (2 * p) := by
        congr 1
        calc
          _ = Int.fract ((p - 1) / (2 * p) : ℝ) := by
            rw [Int.fract_eq_fract]
            sorry
          _ = _ := by
            rw [Int.fract_eq_self]
            split_ands
            . sorry
            . sorry
      _ = _ := by field_simp

  by_cases h6 : p - 1 ∣ 120
  . simpa [h6] using h5 h6
  . simpa [h6] using h4 h6
