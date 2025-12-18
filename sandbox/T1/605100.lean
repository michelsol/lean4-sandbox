import Mathlib

open Finset Filter Topology

/- Determine the smallest real constant $C$ with the following property:
For any five positive real numbers $a_{1}, a_{2}, a_{3}, a_{4}, a_{5}$ (not necessarily distinct),
there always exist pairwise distinct indices $i, j, k, l$ such that $\left|\frac{a_i}{a_j} - \frac{a_k}{a_l}\right| \leq C$
-/
theorem inequalities_605100
  (S : Set ℝ)
  (hS : S = {c : ℝ | ∀ (a : ℕ → ℝ) (ha : ∀ i ∈ Icc 1 5, 0 < a i),
    ∃ i j k l : ℕ, i ∈ Icc 1 5 ∧ j ∈ Icc 1 5 ∧ k ∈ Icc 1 5 ∧ l ∈ Icc 1 5 ∧
      i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧ |a i / a j - a k / a l| ≤ c})
  : IsLeast S (1 / 2) := by
-- First, we first prove that $\frac{1}{2}$ has the desired property.
  constructor
  . rw [hS]
    dsimp
    intro a ha1

-- To do this, we assume without loss of generality that $a_{1} \leq a_{2} \leq a_{3} \leq a_{4} \leq a_{5}$
    wlog h1 : MonotoneOn a (Icc 1 5)
    . specialize this S hS
      have ⟨φ, c1, c2⟩ : ∃ (φ : ℕ → ℕ) (_ : Set.BijOn φ (Icc 1 5) (Icc 1 5)),
          MonotoneOn (a ∘ φ) (Icc 1 5) := by
        sorry
      obtain ⟨i, j, k, l, hi, hj, hk, hl, hij, hik, hil, hjk, hjl, hkl, c3⟩ := this
        (a ∘ φ) (by intro i hi; exact ha1 (φ i) (c1.mapsTo hi)) c2
      use φ i, φ j, φ k, φ l
      use (c1.mapsTo hi), (c1.mapsTo hj), (c1.mapsTo hk), (c1.mapsTo hl)
      use c1.injOn.ne hi hj hij, c1.injOn.ne hi hk hik, c1.injOn.ne hi hl hil,
        c1.injOn.ne hj hk hjk, c1.injOn.ne hj hl hjl, c1.injOn.ne hk hl hkl
      exact c3

-- and consider the five fractions $\frac{a_{1}}{a_{2}}, \frac{a_{3}}{a_{4}}, \frac{a_{1}}{a_{5}}, \frac{a_{2}}{a_{3}}, \frac{a_{4}}{a_{5}}$.
-- By the pigeonhole principle, at least three of these fractions
-- lie in one of the intervals \]0, $\frac{1}{2}$ \] or $\left.] \frac{1}{2}, 1\right]$.
    let f : ℕ → ℝ := λ
      | 1 => a 1 / a 2
      | 2 => a 3 / a 4
      | 3 => a 1 / a 5
      | 4 => a 2 / a 3
      | 5 => a 4 / a 5
      | _ => 0
    let A := {i ∈ Icc 1 5 | f i ∈ Set.Ioc 0 (1 / 2)}
    let B := {i ∈ Icc 1 5 | f i ∈ Set.Ioc (1 / 2) 1}

    have h2 : #A + #B = 5 := calc
      _ = #(A ∪ B) := by
        symm
        refine card_union_of_disjoint ?_
        unfold A B
        refine disjoint_filter.mpr ?_
        intro x hx hx2 hx3
        simp at hx2 hx3
        linarith
      _ = #(Icc 1 5) := by
        congr 1
        ext i
        sorry
      _ = _ := by simp

    obtain ⟨I, hI1, hI2, hI3⟩ : ∃ (I : Finset ℕ) (_ : I ⊆ Icc 1 5) (_ : #I ≥ 3),
        ∀ i ∈ I, ∀ j ∈ I, |f i - f j| < 1 / 2 := by
      obtain c1 | c1 : #A ≥ 3 ∨ #B ≥ 3 := by omega
      . use A, by simp [A], c1
        intro i hi j hj
        simp [A] at hi hj
        refine abs_sub_lt_iff.mpr ?_
        split_ands
        . linarith
        . linarith
      . use B, by simp [B], c1
        intro i hi j hj
        simp [B] at hi hj
        refine abs_sub_lt_iff.mpr ?_
        split_ands
        . linarith
        . linarith

-- Among these, two fractions are consecutive in the list or the first and the last fraction are included.
-- In any case, the positive difference between these two fractions is less than $\frac{1}{2}$,
-- and the four involved indices are pairwise distinct.
    sorry

-- Now we show that if $C$ is such a constant, then $C \geq \frac{1}{2}$.
  . intro C hC
    rw [hS] at hC
    dsimp at hC
-- For this, consider the example 1, 2, 2, 2, $r$, where $r$ is a very large number.
    let a (r : ℝ) :=  (λ
      | 1 => 1
      | 2 => 2
      | 3 => 2
      | 4 => 2
      | 5 => r
      | _ => 0)
    have h1 (r : ℝ) (hr : r > 0) := hC (a r)
      (by
      intro i hi
      simp at hi ⊢
      obtain ⟨hi1, hi2⟩ := hi
      interval_cases i
      all_goals simp [a]
      linarith)

-- With these numbers, we can form the fractions $\frac{1}{r}, \frac{2}{r}, \frac{1}{2}, \frac{2}{2}, \frac{2}{1}, \frac{r}{2}, \frac{r}{1}$, ordered by size.
-- According to the problem statement, $\frac{1}{r}$ and $\frac{2}{r}$ cannot both be chosen.
-- Therefore, the smallest positive difference is $\frac{1}{2}-\frac{2}{r}$,
    have h2 (r : ℝ) (hr : r > 0) : |1 / 2 - 2 / r| ≤ C := by
      obtain ⟨i, j, k, l, hi, hj, hk, hl, hij, hik, hil, hjk, hjl, hkl, c1⟩ := h1 r hr
      calc
        _ ≤ _ := by
          sorry
        _ ≤ _ := c1

-- which approaches the value $\frac{1}{2}$ from below as $r \rightarrow \infty$.
    have h3 : Tendsto (λ r : ℝ ↦ |1 / 2 - 2 / r|) atTop (𝓝 (1 / 2)) := by
      convert_to Tendsto (λ r : ℝ ↦ |1 / 2 - 2 * r⁻¹|) atTop (𝓝 (|1 / 2 - 2 * 0|))
      . symm
        simp
      refine Tendsto.abs ?_
      refine Tendsto.const_sub (1 / 2) ?_
      apply Tendsto.const_mul
      exact tendsto_inv_atTop_zero

    apply le_of_tendsto h3
    . refine eventually_atTop.mpr ?_
      use 1
      intro r hr
      exact h2 r (by linarith)
