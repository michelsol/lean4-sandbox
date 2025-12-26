import Mathlib

open Finset Real

/- Given that $ a,b,c, x_1, x_2, ... , x_5 $ are real positives such that  $ a+b+c=1 $ and $ x_1.x_2.x_3.x_4.x_5 = 1 $.
Prove that $(ax_1^2+bx_1+c)(ax_2^2+bx_2+c)...(ax_5^2+bx_5+c)\ge 1$
-/
theorem inequalities_59132
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 5, 0 < x i)
    (h1 : a + b + c = 1)
    (h2 : ∏ i ∈ Icc 1 5, x i = 1) :
    ∏ i ∈ Icc 1 5, (a * x i ^ 2 + b * x i + c) ≥ 1 := by

-- Let's consider a single term from the product, $ax_i^2+bx_i+c$.
-- Since we are given that $a,b,c > 0$ and $a+b+c=1$, we can treat $a, b, c$ as weights.
-- We apply the weighted AM-GM inequality with the numbers $y_1=x_i^2$, $y_2=x_i$, $y_3=1$
-- and the corresponding weights $w_1=a$, $w_2=b$, $w_3=c$.

-- For each $i \in \{1, 2, 3, 4, 5\}$, we have:
-- $ax_i^2 + bx_i + c = a(x_i^2) + b(x_i^1) + c(x_i^0) \ge (x_i^2)^a (x_i^1)^b (1)^c = x_i^{2a+b}$
  have h3 (i : ℕ) (hi : i ∈ Icc 1 5) : a * x i ^ 2 + b * x i + c ≥ x i ^ (2 * a + b) := calc
    _ ≥ (x i ^ 2) ^ a * x i ^ b * 1 ^ c := by
      let w : ℕ → ℝ := λ | 1 => a | 2 => b | 3 => c | _ => 0
      let y : ℕ → ℝ := λ | 1 => x i ^ 2 | 2 => x i | 3 => 1 | _ => 0
      calc
        _ = ∏ k ∈ {1, 2, 3}, y k ^ w k := by simp [y, w]
        _ = ∏ k ∈ Icc 1 3, y k ^ w k := by congr 1
        _ ≤ ∑ k ∈ Icc 1 3, w k * y k := by
          apply geom_mean_le_arith_mean_weighted (Icc 1 3) w y
          . intro k hk
            simp at hk
            obtain hk | hk | hk : k = 1 ∨ k = 2 ∨ k = 3 := by omega
            all_goals
              subst hk
              simp [w]
              positivity
          . calc
              _ = ∑ k ∈ {1, 2, 3}, w k := by congr 1
              _ = a + b + c := by
                simp [w]
                ring
              _ = 1 := h1
          . intro k hk
            specialize hx i hi
            simp at hk
            obtain hk | hk | hk : k = 1 ∨ k = 2 ∨ k = 3 := by omega
            all_goals
              subst hk
              simp [y]
              try positivity
        _ = ∑ k ∈ {1, 2, 3}, w k * y k := by congr 1
        _ = a * x i ^ 2 + b * x i + c := by
          simp [w, y]
          ring
    _ = (x i ^ 2) ^ a * x i ^ b := by simp
    _ = x i ^ (2 * a) * x i ^ b := by
      congr 1
      rw [←rpow_natCast_mul]
      . simp
      . specialize hx i hi
        positivity
    _ = x i ^ (2 * a + b) := by
      rw [rpow_add]
      exact hx i hi

-- Now, we can take the product of these inequalities for $i=1$ to $5$:

-- $\prod_{i=1}^{5} (ax_i^2+bx_i+c) \ge \prod_{i=1}^{5} x_i^{2a+b} = \left(\prod_{i=1}^{5} x_i\right)^{2a+b} = (1)^{2a+b} = 1$

  calc
    _ ≥ ∏ i ∈ Icc 1 5, x i ^ (2 * a + b) := by
      apply prod_le_prod
      . intro i hi
        specialize hx i hi
        positivity
      . exact h3
    _ = (∏ i ∈ Icc 1 5, x i) ^ (2 * a + b) := by
      refine finset_prod_rpow (Icc 1 5) x ?_ (2 * a + b)
      intro i hi
      specialize hx i hi
      positivity
    _ = 1 ^ (2 * a + b) := by rw [h2]
    _ = 1 := by simp
