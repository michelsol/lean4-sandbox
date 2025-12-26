import Mathlib

/-
Given a real number $k$, consider the equation $\frac{|x|}{x+4}=k x^{2}$.
Prove that this equation has four distinct real solutions for $x$ if and only if $k > \frac{1}{4}$
-/
theorem algebra_321366
    (k : ℝ) (e : ℝ → Prop) (he : ∀ x, e x ↔  |x| / (x + 4) = k * x ^ 2)
    (sol : Set ℝ) (hsol : sol = {x ≠ -4 | e x})
    : sol.ncard = 4 ↔ k > 1 / 4 := by
-- To prove that the equation $\frac{|x|}{x+4}=k x^{2}$ has four distinct real solutions for $x$ if and only if $k > \frac{1}{4}$,
-- we will analyze the equation by considering the cases $x>0$, $x<0$, and $x=0$.
-- Keep in mind that the domain of the equation requires $x+4 \neq 0$, so $x \neq -4$.

-- ### Trivial Solution
-- For any real number $k$ we see that $x=0$ is always a solution.
-- For the equation to have four distinct solutions,
-- we need to find three other distinct non-zero solutions.
  have h1 : (sol ∩ {0}).ncard = 1 := by
    simp only [Set.ncard_eq_one]
    use 0
    simp [hsol, he]

-- ### Case 1: $x > 0$
-- When $x>0$, we have $|x| = x$. The equation becomes:
-- $\frac{x}{x+4} = kx^2$
-- Since we are looking for non-zero solutions, we can divide by $x$:
-- $\frac{1}{x+4} = kx$
-- $1 = kx(x+4)$
-- $kx^2 + 4kx - 1 = 0$
  have g1 (x : ℝ) (hx : x > 0) : e x ↔ k * x ^ 2 + 4 * k * x - 1 = 0 := calc
      _ ↔ |x| / (x + 4) = k * x ^ 2 := by rw [he x]
      _ ↔ x / (x + 4) = k * x ^ 2 := by congr! 2; exact abs_of_pos hx
      _ ↔ 1 / (x + 4) * x = k * x * x := by congr! 1 <;> ring
      _ ↔ 1 / (x + 4) = k * x := by exact mul_left_inj' (by linarith)
      _ ↔ 1 / (x + 4) * (x + 4) = k * x * (x + 4) := by exact Iff.symm (mul_left_inj' (by linarith))
      _ ↔ 1 = k * x ^ 2 + 4 * k * x := by
        congr! 1
        . exact one_div_mul_cancel (by linarith)
        . ring
      _ ↔ _ := by constructor <;> intro c1 <;> linarith

-- This is a quadratic equation in $x$. For it to have real solutions, the discriminant $\Delta$ must be non-negative.
-- $\Delta = (4k)^2 - 4(k)(-1) = 16k^2 + 4k = 4k(4k+1)$
-- For distinct real solutions, $\Delta > 0$, which means $k < -1/4$ or $k > 0$.
-- We are in the case where $x>0$. Let the roots of the quadratic be $x_1$ and $x_2$.
-- By Vieta's formulas, the product of the roots is $x_1 x_2 = \frac{-1}{k}$.

-- * If $k > 0$, the product of the roots is negative.
-- This means one root is positive and one is negative.
-- Therefore, for $k>0$, we find exactly **one positive solution**.
  have h2 (hk : k > 0) : (sol ∩ {x | x > 0}).ncard = 1 := by
    let Δ := discrim k (4 * k) (-1)
    have hΔ1 : Δ = 4 * k * (4 * k + 1) := by unfold Δ discrim; ring
    have hΔ2 : Δ > 0 := by rw [hΔ1]; positivity
    let s := √Δ
    have hΔ3 : Δ = s * s := by simp [s, hΔ2.le]
    let x1 := (-(4 * k) + s) / (2 * k)
    let x2 := (-(4 * k) - s) / (2 * k)

    have c1 x (hx : x > 0) : x ∈ sol ↔ x = x1 ∨ x = x2 := by
      convert quadratic_eq_zero_iff (by linarith) hΔ3 x using 1
      convert g1 x hx using 1
      . rw [hsol]
        suffices x ≠ -4 by simp [this]
        linarith
      . ring_nf
    replace c1 x (hx : x > 0) : x ∈ sol ↔ x = x1 := by
      convert c1 x hx using 1
      suffices x ≠ x2 by simp [this]
      suffices x2 ≤ 0 by linarith
      sorry
    replace c1 : sol ∩ {x | x > 0} = {x1} := by
      ext x
      constructor
      . intro ⟨d1, d2⟩
        simpa using (c1 x d2).mp d1
      . intro d1
        simp at d1
        subst d1
        have d2 : x1 > 0 := by
          sorry
        split_ands
        . exact (c1 x1 d2).mpr rfl
        . exact d2
    simp [c1]

-- * If $k < -1/4$, the product of the roots is positive.
-- The sum of the roots is $x_1 + x_2 = \frac{-4k}{k} = -4$, which is negative.
-- If both roots are real and their product is positive and sum is negative,
-- both roots must be negative. Thus, for $k < -1/4$, there are **no positive solutions**.
  have h3 (hk : k < -1 / 4) : sol ∩ {x | x > 0} = ∅ := by
    let Δ := discrim k (4 * k) (-1)
    have hΔ1 : Δ = 4 * k * (4 * k + 1) := by unfold Δ discrim; ring
    have hΔ2 : Δ > 0 := by
      rw [hΔ1]
      apply mul_pos_of_neg_of_neg <;> linarith
    let s := √Δ
    have hΔ3 : Δ = s * s := by simp [s, hΔ2.le]
    let x1 := (-(4 * k) + s) / (2 * k)
    let x2 := (-(4 * k) - s) / (2 * k)

    have c1 x (hx : x > 0) : x ∈ sol ↔ x = x1 ∨ x = x2 := by
      convert quadratic_eq_zero_iff (by linarith) hΔ3 x using 1
      convert g1 x hx using 1
      . rw [hsol]
        suffices x ≠ -4 by simp [this]
        linarith
      . ring_nf

    ext x
    calc
      _ ↔ x ∈ sol ∧ x > 0 := by simp
      _ ↔ (x = x1 ∨ x = x2) ∧ x > 0 := by
        suffices 0 < x → (x ∈ sol ↔ x = x1 ∨ x = x2) by simpa using this
        exact c1 x
      _ ↔ _ := by
        suffices x = x1 ∨ x = x2 → x ≤ 0 by simpa using this
        intro hx
        obtain hx | hx := hx
        all_goals subst hx
        . have c2 := calc
            x1 ≤ 0 ↔ (-(4 * k) + s) / (2 * k) ≤ 0 / (2 * k) := by simp [x1]
            _ ↔ -(4 * k) + s ≥ 0 := by
              refine div_le_div_right_of_neg ?_
              linarith
            _ ↔ s ≥ 4 * k := by constructor <;> intro d1 <;> linarith
          rw [c2]
          suffices s ≥ 0 by linarith
          exact Real.sqrt_nonneg Δ
        . sorry

-- ### Case 2: $x < 0$
-- When $x<0$, we have $|x| = -x$. The equation becomes:
-- $\frac{-x}{x+4} = kx^2$
-- Again, for non-zero solutions, we can divide by $x$:
-- $\frac{-1}{x+4} = kx$
-- $-1 = kx(x+4)$
-- $kx^2 + 4kx + 1 = 0$
  have g2 (x : ℝ) (hx : x < 0) (hx2 : x ≠ -4) : e x ↔ k * x ^ 2 + 4 * k * x + 1 = 0 := calc
      _ ↔ |x| / (x + 4) = k * x ^ 2 := by rw [he x]
      _ ↔ -x / (x + 4) = k * x ^ 2 := by congr! 2; exact abs_of_neg hx
      _ ↔ 1 / (x + 4) * -x = -k * x * -x := by congr! 1 <;> ring
      _ ↔ 1 / (x + 4) = -k * x := by exact mul_left_inj' (by linarith)
      _ ↔ 1 / (x + 4) * (x + 4) = (-k * x) * (x + 4) := by exact Iff.symm (mul_left_inj' (by sorry))
      _ ↔ 1 = -k * x ^ 2 - 4 * k * x := by
        congr! 1
        . exact one_div_mul_cancel (by sorry)
        . ring
      _ ↔ _ := by constructor <;> intro c1 <;> linarith

-- This is another quadratic equation. For it to have distinct real solutions,
-- its discriminant $\Delta'$ must be positive.
-- $\Delta' = (4k)^2 - 4(k)(1) = 16k^2 - 4k = 4k(4k-1)$
-- For two distinct real solutions, $\Delta' > 0$, which means $k < 0$ or $k > 1/4$.
-- We are in the case where $x<0$. Let the roots be $x_3$ and $x_4$.
-- The product of the roots is $x_3 x_4 = \frac{1}{k}$ and the sum is $x_3 + x_4 = -4$.

-- * If $k > 1/4$, the product of the roots is positive, and their sum is negative.
-- This implies that both roots are negative.
-- So, for $k > 1/4$, we find **two distinct negative solutions**.
-- We must also confirm these solutions are not $x=-4$.
-- Substituting $x=-4$ into $kx^2+4kx+1=0$ gives $k(-4)^2+4k(-4)+1 = 16k-16k+1=1=0$,
-- which is impossible.
  have h4 (hk : k > 1 / 4) : (sol ∩ {x | x < 0}).ncard = 2 := by
    let Δ' := discrim k (4 * k) 1
    have hΔ'1 : Δ' = 4 * k * (4 * k - 1) := by unfold Δ' discrim; ring
    have hΔ'2 : Δ' > 0 := by
      rw [hΔ'1]
      nlinarith
    let s := √Δ'
    have hΔ'3 : Δ' = s * s := by simp [s, hΔ'2.le]
    let x1 := (-(4 * k) + s) / (2 * k)
    let x2 := (-(4 * k) - s) / (2 * k)

    have c1 x (hx : x < 0) (hx2 : x ≠ -4) : x ∈ sol ↔ x = x1 ∨ x = x2 := by
      convert quadratic_eq_zero_iff (by linarith) hΔ'3 x using 1
      convert g2 x hx sorry using 1
      . rw [hsol]
        suffices x ≠ -4 by simp [this]
        simpa using hx2
      . ring_nf
    replace c1 : sol ∩ {x | x < 0} = {x1, x2} := by
      sorry
    rw [c1]
    rw [Set.ncard_insert_of_not_mem]
    . simp
    . suffices x1 ≠ x2 by simpa using this
      sorry

-- * If $k < 0$, the product of the roots is negative.
-- This means one root is positive and one is negative.
-- Since we are in the case $x<0$, we find exactly **one negative solution**.

  have h5 (hk : k < 0) : (sol ∩ {x | x < 0}).ncard = 1 := by
    sorry

  have h5' (hk : k > 0 ∧ k < 1 / 4) : (sol ∩ {x | x < 0}).ncard = 0 := by
    sorry

-- ### Synthesis of Results
-- Now, we combine the number of solutions from all cases ($x=0$, $x>0$, $x<0$).

-- * **If $k > 1/4$**:
--     * One solution at $x=0$.
--     * From Case 1 ($x>0$), since $k>1/4 > 0$, there is **one** positive solution.
--     * From Case 2 ($x<0$), since $k>1/4$, there are **two** distinct negative solutions.
--     * Total solutions: $1 + 1 + 2 = 4$.
  have h6 (hk : k > 1 / 4) : sol.ncard = 4 := by
    specialize h2 (by linarith)
    specialize h4 (by linarith)
    calc
      _ = (sol ∩ {x | x < 0} ∪ (sol ∩ {0} ∪ sol ∩ {x | x > 0})).ncard := by
        congr 1
        ext x
        constructor
        . intro c1
          have c2 : x < 0 ∨ x = 0 ∨ x > 0 := by apply lt_trichotomy
          simp [c1, c2]
        . intro c1
          obtain c1 | c1 | c1 := c1
          all_goals simp [c1.left]
      _ = (sol ∩ {x | x < 0}).ncard + (sol ∩ {0}).ncard + (sol ∩ {x | x > 0}).ncard := by
        sorry
      _ = _ := by simp [h1, h2, h4]

-- * **If $k \le 1/4$**:
--     * If $k = 1/4$: We get one solution at $x=0$, one positive solution (since $k>0$), and one negative solution (since $\Delta' = 0$). Total = 3 solutions.
  have h7 (hk : k = 1 / 4) : sol.ncard = 3 := by
    sorry

--     * If $0 < k < 1/4$: We get one solution at $x=0$, one positive solution (since $k>0$), and no negative solutions (since $\Delta' < 0$). Total = 2 solutions.
  have h8 (hk : 0 < k ∧ k < 1 / 4) : sol.ncard = 2 := by
    sorry

--     * If $k = 0$: The equation becomes $\frac{|x|}{x+4}=0$, which implies $x=0$. Total = 1 solution.
  have h9 (hk : k = 0) : sol.ncard = 1 := by
    simp only [Set.ncard_eq_one]
    use 0
    ext x
    suffices ¬x = -4 ∧ (x = 0 ∨ x + 4 = 0) ↔ x = 0 by simpa [hsol, he, hk] using this
    constructor
    . intro ⟨c1, c2⟩
      obtain c2 | c2 := c2
      . linarith
      . exfalso
        apply c1
        linarith
    . intro c1
      simp [c1]

--     * If $k < 0$: We get one solution at $x=0$, no positive solutions, and one negative solution. Total = 2 solutions.
  have h10 (hk : k < 0) : sol.ncard = 2 := by
    sorry

-- ### Conclusion
-- Therefore, the equation $\frac{|x|}{x+4}=k x^{2}$ has four distinct real solutions for $x$ if and only if $k > \frac{1}{4}$.
  constructor
  . contrapose!
    intro c1
    obtain hk | hk | hk | hk : k = 1 / 4 ∨ (0 < k ∧ k < 1 / 4) ∨ k = 0 ∨ k < 0 := by
      by_cases c2 : k = 1 / 4
      all_goals simp only [c2, true_or, false_or]
      replace c2 : k < 1 / 4 := lt_of_le_of_ne c1 c2
      by_cases c3 : 0 < k
      all_goals simp only [c3, c2, true_and, true_or, false_and, false_or]
      push_neg at c3
      exact eq_or_lt_of_le c3
    . specialize h7 hk
      omega
    . specialize h8 hk
      omega
    . specialize h9 hk
      omega
    . specialize h10 hk
      omega
  . exact h6
