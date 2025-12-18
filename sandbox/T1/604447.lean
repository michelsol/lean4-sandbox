import Mathlib

open Real Polynomial Finset

/-
On a polynomial of degree three it is allowed to perform the following two operations arbitrarily many times:
(i) reverse the order of its coefficients including zeroes (for instance, from the polynomial $x^{3}-2 x^{2}-3$ we can obtain $-3 x^{3}-2 x+1$;
(ii) change polynomial $P(x)$ to the polynomial $P(x+1)$.
Is it possible to obtain the polynomial $x^{3}-3 x^{2}+3 x-3$ from the polynomial $x^{3}-2$ ?
The answer is no.
-/

theorem algebra_604447 : ¬∃ P : ℕ → ℝ[X], ∃ r ≥ 2,
        P 1 = X ^ 3 - 2
        ∧ P r = X ^ 3 - 3 * X ^ 2 + 3 * X - 3
        ∧ ∀ i ∈ Ico 1 r,
          (∀ k ∈ Icc 0 3, (P (i + 1)).coeff k = (P i).coeff (3 - k))
          ∨ (P (i + 1) = (P i).comp (X + 1))
      := by
  intro ⟨P, r, hr, h1, h2, h3⟩

-- The original polynomial $x^{3}-2$ has a unique real root.
-- The two transformations clearly preserve this property.
  have h4 i (hi : i ∈ Icc 1 r) : ∃! x, (P i).eval x = 0 := by
    revert i
    suffices ∀ i ≥ 1, i ≤ r → ∃! x, eval x (P i) = 0 from by simpa
    apply Nat.le_induction
    . intro c1
      sorry
    . intro i hi ih hir
      specialize ih (by omega)
      sorry

  let x (i : ℕ) := if hi : i ∈ Icc 1 r then (h4 i hi).choose else 0

  have h5 : x 1 = 2 ^ (1 / 3 : ℝ) := by
    set x0 : ℝ := 2 ^ (1 / 3 : ℝ)
    have c1 : 1 ∈ Icc 1 r := by simp; omega
    apply (h4 1 c1).unique
    . dsimp [x]
      split_ifs
      simpa using (h4 1 c1).choose_spec.left
    . suffices (2 ^ (3 : ℝ)⁻¹ : ℝ) ^ 3 - 2 = 0 from by simpa [h1, x0]
      rw [←rpow_mul_natCast (by norm_num)]
      simp

  have h6 : x r = 1 + 2 ^ (1 / 3 : ℝ) := by
    set x0 : ℝ := 1 + 2 ^ (1 / 3 : ℝ)
    have c1 : r ∈ Icc 1 r := by simp; omega
    apply (h4 r c1).unique
    . dsimp [x]
      split_ifs
      simpa using (h4 r c1).choose_spec.left
    . suffices -2 + (2 ^ (3 : ℝ)⁻¹ : ℝ) ^ 3 = 0 from by simp [h2, x0]; ring_nf; simpa
      rw [←rpow_mul_natCast (by norm_num)]
      simp

  have h7 i (hi : i ∈ Ico 1 r) : x (i + 1) = 1 / x i ∨ x (i + 1) = x i - 1 := by
    specialize h3 i hi
    obtain h3 | h3 := h3
-- If $\alpha$ is the only real root of $P(x)$, then the first operation produces a polynomial with root $\frac{1}{\alpha}$,
    . left
      sorry
-- and the second operation gives a polynomial with root $\alpha-1$.
    . right
      sorry

-- Since the root of the original polynomial is $\sqrt[3]{2}$, and that of the resulting polynomial is $1+\sqrt[3]{2}$,
-- the problem is reduced to the question whether it is possible to obtain the latter number from the former by operations $x \mapsto \frac{1}{x}$ and $x \mapsto x-1$.
  replace ⟨x, r, hr, h1, h2, h3⟩ : ∃ x : ℕ → ℝ, ∃ r ≥ 2,
      x 1 = 2 ^ (1 / 3 : ℝ)
      ∧ x r = 1 + 2 ^ (1 / 3 : ℝ)
      ∧ ∀ i ∈ Ico 1 r, x (i + 1) = 1 / x i ∨ x (i + 1) = x i - 1
      := by
    use x, r
  clear * - hr h1 h2 h3

-- Let us apply one more operation $x \mapsto x-1$ (so as to transform $\sqrt[3]{2}$ to itself).
  replace ⟨x, r, hr, h1, h2, h3, h4⟩ : ∃ x : ℕ → ℝ, ∃ r ≥ 2,
      x 1 = 2 ^ (1 / 3 : ℝ)
      ∧ x r = 2 ^ (1 / 3 : ℝ)
      ∧ (∀ i ∈ Ico 1 r, x (i + 1) = 1 / x i ∨ x (i + 1) = x i - 1)
      ∧ x r = x (r - 1) - 1
      := by
    use λ i ↦ if i = r + 1 then 2 ^ (1 / 3 : ℝ) else x i
    use r + 1, by omega
    split_ands
    . have c1 : 1 ≠ r + 1 := by omega
      simp [c1, h1]
    . simp
    . intro i hi
      by_cases c1 : i + 1 = r + 1
      . have c2 : i ≠ r + 1 := by omega
        have c3 : i = r := by omega
        simp [c1, c2, c3, h2]
      have c2 : i ≠ r + 1 := by simp at hi; omega
      specialize h3 i (by simp at hi ⊢; omega)
      simp [c1, c2]
      ring_nf at h3 ⊢
      simpa using h3
    . simp at h2 ⊢
      linarith

-- Now, reverse all the operations so that the number $\sqrt[3]{2}$ is transformed to itself by  operations of the form $x \mapsto \frac{1}{x}$ and $x \mapsto x+1$.
  replace ⟨x, r, hr, h1, h2, h3, h4⟩ : ∃ x : ℕ → ℝ, ∃ r ≥ 2,
      x 1 = 2 ^ (1 / 3 : ℝ)
      ∧ x r = 2 ^ (1 / 3 : ℝ)
      ∧ (∀ i ∈ Ico 1 r, x (i + 1) = 1 / x i ∨ x (i + 1) = x i + 1)
      ∧ x 2 = x 1 + 1
      := by
    use λ i ↦ x (r + 1 - i), r, hr
    split_ands
    . simpa using h2
    . simpa using h1
    . intro i hi
      obtain h3 | h3 := h3 (r - i) (by simp at hi ⊢; omega)
      . left
        have c1 : r + 1 - i = r - i + 1 := by simp at hi; omega
        simp [c1, h3]
      . right
        have c1 : r + 1 - i = r - i + 1 := by simp at hi; omega
        simp [c1]
        linarith
    . simp
      linarith

-- It is easy to see that the composition of any number of such operations
-- is a fractional-linear function $x \mapsto \frac{a x+b}{c x+d}$, where $a, b, c, d$ are non-negative integers and $a d-b c= \pm 1$.
-- Each operation does not decrease $a+b+c+d$ which remains ≥ 3, therefore $ c ≠ 0 $ or $ b ≠ 0 $ remains true.
  have h5 : ∀ i ≥ 2, i ≤ r → ∃ (a b c d : ℕ)
    (g1 : (a * d - b * c : ℤ) = 1 ∨ (a * d - b * c : ℤ) = -1)
    (g2 : a + b + c + d ≥ 3)
    (g3 : c ≠ 0 ∨ b ≠ 0)
    , x i = (a * x 1 + b) / (c * x 1 + d) := by
    apply Nat.le_induction
    . intro hr2
      use 1, 1, 0, 1
      use by omega
      use by omega
      use by omega
      simpa using h4
    . intro i hi ih hi2
      replace ⟨a, b, c, d, g1, g2, g3, ih⟩ := ih (by omega)
      specialize h3 i (by simp; omega)
      obtain h3 | h3 := h3
      . use c, d, a, b, by ring_nf at g1 ⊢; omega
        use by omega
        use by
          by_contra! g4
          have g5 : b = 1 ∧ c = 1 := by
            replace g1 : b * c = (1 : ℤ) ∨ b * c = (-1 : ℤ) := by simp [g4] at g1; omega
            sorry
          omega
        simpa [ih] using h3
      . use a + c, b + d, c, d
        use (by push_cast; ring_nf at g1 ⊢; simpa using g1)
        push_cast
        rw [ih] at h3
        use by omega
        use by omega
        sorry

-- Thus $\sqrt[3]{2}$ is transformed to itself by some such composition.
-- This means however that $x_1 = \sqrt[3]{2}$ is a root of non-zero polynomial $x(c x+d)-a x-b$
  have ⟨a, b, c, d, h6, h7, h8, h9⟩ := h5 r hr (by omega)
  have h10 : c * x 1 + d ≠ 0 := by sorry
  have h11 : x r = x 1 := by rw [h1, h2]
  have h12 : c * x 1 ^ 2 + (d - a) * x 1 - b = 0 := by
    field_simp [h11] at h9
    linarith
-- with integral coefficients and degree at most 2, as $ c ≠ 0 $ or $ b ≠ 0 $, which is impossible.
  sorry
