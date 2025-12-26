import Mathlib

open Finset

/-
Let $a_{1}, a_{2}, \ldots, a_{n}, k$, and $M$ be positive integers such that
$$ \frac{1}{a_{1}}+\frac{1}{a_{2}}+\cdots+\frac{1}{a_{n}}=k \quad \text { and }
\quad a_{1} a_{2} \ldots a_{n}=M $$
If $M>1$, prove that the polynomial
$$ P(x)=M(x+1)^{k}-\left(x+a_{1}\right)\left(x+a_{2}\right) \cdots\left(x+a_{n}\right) $$
has no positive roots.
-/

theorem algebra_24909
  (n : ℕ) (n_ge_1 : n ≥ 1)
  (a : ℕ → ℕ) (k M : ℕ)
  (a_gt_0 : ∀ i ∈ Icc 1 n, 0 < a i)
  (k_gt_0 : 0 < k) (M_gt_1 : 1 < M)
  (hsum : ∑ i ∈ Icc 1 n, (1 / a i : ℝ) = k) (hprod : ∏ i ∈ Icc 1 n, a i = M)
  : let P (x : ℝ) := M * (x + 1) ^ k - ∏ i ∈ Icc 1 n, (x + a i)
    ¬∃ (x : ℝ) (_ : 0 < x), P x = 0 := by
  -- AM-GM inequality with two positive weights.
  have geom_mean_le_arith_mean2_weighted' {w₁ w₂ p₁ p₂ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
      (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) : (p₁ ^ w₁ * p₂ ^ w₂) ^ (w₁ + w₂)⁻¹ ≤
        (w₁ * p₁ + w₂ * p₂) / (w₁ + w₂) :=
    sorry
  -- Equality holds in AM-GM inequality, iff all values with nonzero weights are equal.
  have geom_mean_eq_arith_mean2_weighted'_iff {w₁ w₂ p₁ p₂ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
      (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) : (p₁ ^ w₁ * p₂ ^ w₂) ^ (w₁ + w₂)⁻¹ =
        (w₁ * p₁ + w₂ * p₂) / (w₁ + w₂)
      ↔ (0 ≠ w₁ → 0 ≠ w₂ → p₁ = p₂) :=
    sorry

  intro p
  push_neg
/- Consider $x$ a positive root of $P$. -/
  intro x hx hpx
  have a_gt_0' : ∀ i ∈ Icc 1 n, a i > (0 : ℝ) := by intro i hi; specialize a_gt_0 i hi; norm_cast
  have a_ge_1' : ∀ i ∈ Icc 1 n, a i ≥ (1 : ℝ) := by intro i hi; specialize a_gt_0 i hi; norm_cast
/-
We first prove that, for $x>0$,  $$ a_{i}(x+1)^{1 / a_{i}} \leqslant x+a_{i}, $$
with equality if and only if $a_{i}=1$.
-/
  have h1 : ∀ i ∈ Icc 1 n, a i * (x + 1) ^ (1 / a i : ℝ) ≤ x + a i := by
/-
If $a_{i}>1$, the AM-GM inequality applied to a single copy of $x+1$ and
$a_{i}-1$ copies of 1 yields
$$ \frac{(x+1)+\overbrace{1+1+\cdots+1}^{a_{i}-1 \text { ones }}}{a_{i}} \geqslant
\sqrt[a_{i}]{(x+1) \cdot 1^{a_{i}-1}}
\Longrightarrow a_{i}(x+1)^{1 / a_{i}} \leqslant x+a_{i} $$
-/
    intro i hi
    specialize a_gt_0' i hi
    specialize a_ge_1' i hi
    suffices (x + 1) ^ (1 / a i : ℝ) ≤ (x + a i) / a i from by
      have a_pos : a i > (0 : ℝ) := by specialize a_gt_0 i hi; norm_cast
      exact (le_div_iff₀' a_pos).mp this
    calc
      (x + a i) / a i = (1 * (x + 1) + (a i - 1) * 1) / (1 + (a i - 1)) := by simp
      _ ≥ ((x + 1) ^ (1 : ℝ) * 1 ^ (a i - 1 : ℝ)) ^ (1 + (a i - 1) : ℝ)⁻¹ := by
        apply geom_mean_le_arith_mean2_weighted'
        . norm_num
        . linarith
        . linarith
        . norm_num
      _ = _ := by simp
/-
It is clear that equality occurs if $a_{i}=1$.
Since $x+1>1$, the inequality is strict for $a_{i}>1$.
-/
  have h1' : ∀ i ∈ Icc 1 n, a i * (x + 1) ^ (1 / a i : ℝ) = x + a i ↔ a i = 1 := by
    intro i hi
    specialize a_gt_0' i hi
    specialize a_ge_1' i hi
    calc
      _ ↔ (x + 1) ^ (1 / a i : ℝ) = (x + a i) / a i := by field_simp; ring_nf
      _ ↔ ((x + 1) ^ (1 : ℝ) * 1 ^ (a i - 1 : ℝ)) ^ (1 + (a i - 1) : ℝ)⁻¹
          = (1 * (x + 1) + (a i - 1) * 1) / (1 + (a i - 1)) := by simp
      _ ↔ ((0 : ℝ) ≠ 1 → (0 : ℝ) ≠ a i - 1 → x + 1 = 1) := by
        apply geom_mean_eq_arith_mean2_weighted'_iff
        . norm_num
        . linarith
        . linarith
        . norm_num
      _ ↔ _ := by
        constructor
        . intro h1
          by_contra h
          specialize h1 (by norm_num) (by intro _; apply h; rify; linarith)
          linarith
        . intro h; simp [h]

/-
Multiplying the inequalities (1) for $i=1,2, \ldots, n$ yields
$$ \prod_{i=1}^{n} a_{i}(x+1)^{1 / a_{i}} \leqslant \prod_{i=1}^{n}\left(x+a_{i}\right)
\Longleftrightarrow
M(x+1)^{\sum_{i=1}^{n} 1 / a_{i}}-\prod_{i=1}^{n}\left(x+a_{i}\right) \leqslant 0
\Longleftrightarrow P(x) \leqslant 0 $$
with strict inequality iff there is some i such that $a_{i}≠1$$.
We will therefore show that if $a_i ≠ 0$ for some i, then $P(x) < 0$.
-/

  have h3 : (∃ i ∈ Icc 1 n, a i ≠ 1) → ∏ i ∈ Icc 1 n, a i * (x + 1) ^ (1 / a i : ℝ) < ∏ i ∈ Icc 1 n, (x + a i) := by
    intro ⟨i₀, hi₀, ai₀⟩
    have : {i₀} ⊆ Icc 1 n := by simp at hi₀ ⊢; omega
    iterate 2 rw [←prod_sdiff this, prod_singleton]
    set A := ∏ i ∈ Icc 1 n \ {i₀}, a i * (x + 1) ^ (1 / a i : ℝ)
    set B := a i₀ * (x + 1) ^ (1 / a i₀ : ℝ)
    set A' := ∏ i ∈ Icc 1 n \ {i₀}, (x + a i)
    set B' := (x + a i₀)
    suffices A ≤ A' ∧ B < B' from sorry
    constructor
    . apply prod_le_prod
      . intro i hi; positivity
      . intro i hi; exact h1 i (by simp at hi ⊢; omega)
    . specialize h1 i₀ hi₀
      apply lt_of_le_of_ne h1
      intro h; exact ai₀ ((h1' i₀ hi₀).mp h)

  have h4 : (∏ i ∈ Icc 1 n, a i * (x + 1) ^ (1 / a i : ℝ) < ∏ i ∈ Icc 1 n, (x + a i)) ↔ p x < 0 := by
    suffices ∏ i ∈ Icc 1 n, a i * (x + 1) ^ (1 / a i : ℝ) = M * (x + 1) ^ k from calc
      _ ↔ M * (x + 1) ^ k < ∏ i ∈ Icc 1 n, (x + a i) := by rw [this]
      _ ↔ M * (x + 1) ^ k - ∏ i ∈ Icc 1 n, (x + a i) < 0 := by constructor <;> (intro _; linarith)
    rw [prod_mul_distrib]
    congr 1
    . norm_cast
    . sorry

  replace h3 : (∃ i ∈ Icc 1 n, a i ≠ 1) → p x < 0 := by
    intro h; specialize h3 h; rwa [←h4]

/- But $P(x)=0$, so all $a_i$'s must be 1 -/
  have h5 : ∀ i ∈ Icc 1 n, a i = 1 := by
    by_contra h
    push_neg at h
    specialize h3 h
    linarith

  /-
  But this implies $M=1$, which is not possible.
  Hence $P$ has no positive roots.
  -/

  have : M = 1 := calc
    M = _ := hprod.symm
    _ = ∏ i ∈ Icc 1 n, 1 := by rw [prod_congr rfl h5]
    _ = 1 := by simp

  linarith
