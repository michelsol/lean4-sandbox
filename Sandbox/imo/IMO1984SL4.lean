import Mathlib

open Finset

/-
Let $d$ be the sum of the lengths of all diagonals of a convex polygon of $n(n>3)$ vertices
and let $p$ be its perimeter.

Prove that  $ \frac{n-3}{2}<\frac{d}{p}<\frac{1}{2}\left(\left[\frac{n}{2}\right]\left[\frac{n+1}{2}\right]-2\right) . $
-/
theorem other_23934
    (n : ℕ)
    (hn : n > 3)
    (A : ZMod n → ℝ × ℝ)
    (hA : ∀ i ∈ Ico (0 : ℤ) n, A i ∉ convexHull ℝ {A j | j ∈ Ico (0 : ℤ) n \ {i}})
    (p : ℝ) (hp : p = ∑ i ∈ Ico (0 : ℤ) n, dist (A i) (A (i + 1)))
    (d : ℝ) (hd : d = ∑ i ∈ Ico (0 : ℤ) n, ∑ j ∈ Ico (i + 2) n, dist (A i) (A j))
    : (n - 3) / 2 < d / p ∧ d / p < (1 / 2) * (⌊(n / 2 : ℝ)⌋ * ⌊((n + 1) / 2 : ℝ)⌋ - 2) := by

-- In a convex polygon, two consecutive diagonals must intersect.
-- Therefore applying the triangle inequality twice, we obtain that
-- for any diagonal $A_{i} A_{j}$ we have $A_{i} A_{j}+A_{i+1} A_{j+1} > A_{i} A_{i+1}+A_{j} A_{j+1}$.
  have h1 (i : ℤ) (hi : i ∈ Ico (0 : ℤ) n) (j : ℤ) (hj : j ∈ Ico (i + 2) n) :
      dist (A i) (A j) + dist (A (i + 1)) (A (j + 1))
      > dist (A i) (A (i + 1)) + dist (A j) (A (j + 1)) := by
    have ⟨I, g1, g2⟩ : ∃ I : ℝ × ℝ, I ∈ segment ℝ (A i) (A j) ∧ I ∈ segment ℝ (A (i + 1)) (A (j + 1)) := by
      sorry
    have g3 : dist (A i) (A (i + 1)) < dist (A i) I + dist (A (i + 1)) I := by
      sorry
    have g4 : dist (A j) (A (j + 1)) < dist (A j) I + dist (A (j + 1)) I := by
      sorry
    have g5 : dist (A i) (A j) = dist (A i) I + dist (A j) I := by
      sorry
    have g6 : dist (A (i + 1)) (A (j + 1)) = dist (A (i + 1)) I + dist (A (j + 1)) I := by
      sorry
    rw [g5, g6]
    linarith

-- Summing all such $n(n-3) / 2$ inequalities, we obtain $2 d > (n-3) p$, proving the first inequality.
  have h2 : 2 * d > (n - 3) * p := calc
    _ = d + d := sorry
    _ = ∑ i ∈ Ico (0 : ℤ) n, ∑ j ∈ Ico (i + 2) n, dist (A i) (A j)
        + ∑ i ∈ Ico (0 : ℤ) n, ∑ j ∈ Ico (i + 2) n, dist (A (i + 1)) (A (j + 1)) := by
      congr 1
      sorry
    _ = ∑ i ∈ Ico (0 : ℤ) n, ∑ j ∈ Ico (i + 2) n, (dist (A i) (A j) + dist (A (i + 1)) (A (j + 1))) := by
      simp_rw [←sum_add_distrib]
    _ > ∑ i ∈ Ico (0 : ℤ) n, ∑ j ∈ Ico (i + 2) n, (dist (A i) (A (i + 1)) + dist (A j) (A (j + 1))) := by
      apply sum_lt_sum
      . intro i hi
        apply sum_le_sum
        intro j hj
        specialize h1 i (by simp at hi ⊢; omega) j (by simp at hj ⊢; omega)
        simp at h1
        linarith
      use 0, by simp; omega
      apply sum_lt_sum_of_nonempty
      . simp; omega
      intro j hj
      simpa using h1 0 (by simp; omega) j (by simp at hj ⊢; omega)
    _ = ∑ i ∈ Ico (0 : ℤ) n, ∑ j ∈ Ico (i + 2) n, dist (A i) (A (i + 1))
        + ∑ i ∈ Ico (0 : ℤ) n, ∑ j ∈ Ico (i + 2) n, dist (A j) (A (j + 1)) := by
      simp_rw [←sum_add_distrib]
    _ = _ := sorry

  have hp2 : p > 0 := by sorry

  have h3 : (n - 3) / 2 < d / p := by
    cancel_denoms
    apply_fun (. / p) at h2
    . field_simp at h2 ⊢
      simpa using h2
    . exact strictMono_div_right_of_pos hp2

-- Let us now prove the second inequality.
  suffices d / p < (1 / 2) * (⌊(n / 2 : ℝ)⌋ * ⌊((n + 1) / 2 : ℝ)⌋ - 2) from by simpa [h3]

-- We notice that for each diagonal $A_{i} A_{i+j}$ (we may assume that $j \leq[n / 2]$ )
-- the following relation holds: $ A_{i} A_{i+j} < A_{i} A_{i+1}+\cdots+A_{i+j-1} A_{i+j}$   (1)
  have h4 (i : ℤ) (hi : i ∈ Ico (0 : ℤ) n) (j : ℤ) (hj : j ∈ Ico (2 : ℤ) ⌊(n / 2 : ℝ)⌋) :
      dist (A i) (A (i + j)) < ∑ k ∈ Ico i (i + j), dist (A k) (A (k + 1)) := by
    replace ⟨hj, hj2⟩ : j ≥ 2 ∧ j < ⌊(n / 2 : ℝ)⌋ := by simpa using hj
    revert j
    apply Int.le_induction
    . intro hj
      have g1 : Ico i (i + 2) = {i, i + 1} := by ext j; simp; omega
      suffices dist (A i) (A (i + 2))
          < dist (A i) (A (i + 1)) + dist (A (i + 1)) (A (i + 1 + 1)) from by simpa [g1]
      sorry
    . intro j hj ih hj2
      specialize ih (by omega)
      sorry

-- We now split the proof depending on the parity of $n$.
  obtain ⟨k, h5 | h5⟩ := n.even_or_odd'
  swap
-- If $n=2 k+1$, then summing the inequalities (1) for $j=2,3, \ldots, k$ and $i=1,2, \ldots, n$
-- yields $d < (2+3+\cdots+k) p=\dfrac{([n / 2][n+1 / 2]-2)}{2} p $.
  . have h6 : d < (⌊(n / 2 : ℝ)⌋ * ⌊((n + 1) / 2 : ℝ)⌋ - 2) / 2 * p := calc
      _ < (∑ j ∈ Ico (2 : ℤ) k, j) * p := by
        sorry
      _ = (∑ j ∈ Ico (1 : ℤ) k, j - 1) * p := by
        congr 1
        norm_cast
        have g1 : {1} ⊆ Ico (1 : ℤ) k := by intro i hi; simp at hi ⊢; omega
        have g2 : Ico (1 : ℤ) k \ {1} = Ico (2 : ℤ) k := by ext i; simp; omega
        simp [←sum_sdiff g1, g2]
      _ = (k * (k + 1) / 2 - 2 / 2) * p := by
        sorry
      _ = (k * (k + 1) - 2) / 2 * p := by
        sorry
      _ = _ := by
        congr 4
        . sorry
        . sorry
-- which proves the second inequality.
    apply_fun (. / p) at h6
    swap
    . exact strictMono_div_right_of_pos hp2
    dsimp at h6
    convert h6 using 1
    field_simp
    ring
-- If $n=2 k$, then summing the inequalities (1) for $j=2,3, \ldots, k-1$, $i=1,2, \ldots, n$
-- and for $j=k, i=1,2, \ldots, k$ again yields $d < (2+3+\cdots+$ $(k-1)+k / 2) p=\frac{1}{2}([n / 2][n+1 / 2]-2) p$.
-- which proves the second inequality.
  . have h6 : d < (⌊(n / 2 : ℝ)⌋ * ⌊((n + 1) / 2 : ℝ)⌋ - 2) / 2 * p := calc
      _ < (∑ j ∈ Ico (2 : ℤ) (k - 1), j + k / 2) * p := by
        sorry
      _ < (∑ j ∈ Ico (2 : ℤ) (k - 1), j + k) * p := by
        generalize ∑ j ∈ Ico (2 : ℤ) (k - 1), j = s
        sorry
      _ < (∑ j ∈ Ico (2 : ℤ) k, j) * p := by
        sorry
      _ = (∑ j ∈ Ico (1 : ℤ) k, j - 1) * p := by
        sorry
      _ = (k * (k + 1) / 2 - 2 / 2) * p := by
        sorry
      _ = (k * (k + 1) - 2) / 2 * p := by
        sorry
      _ = _ := by
        congr 4
        . sorry
        . sorry
-- which proves the second inequality.
    apply_fun (. / p) at h6
    swap
    . exact strictMono_div_right_of_pos hp2
    dsimp at h6
    convert h6 using 1
    field_simp
    ring
