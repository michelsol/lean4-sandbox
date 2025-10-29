import Mathlib

open Real
open Set

-- example : ∑' n, (if n ≥ 1 then 1 / n ^ 2 else 0) = π ^ 2 / 6 := by
--   sorry

-- #check z
-- #check g

noncomputable def z (s : ℝ) := ∑' n : ℕ, if n ≥ 1 then 1 / (n : ℝ) ^ s else 0

noncomputable def g (s : ℝ) := ∫ x in Ioi 0, x ^ (s - 1) * exp (-x)

example (s : ℝ) : z s * g s = ∫ x in Ioi 0, x ^ (s - 1) / (exp x - 1) := by
  unfold z g
  sorry

example := calc
  g 1 = ∫ x in Ioi 0, exp (-x) := by
    unfold g
    congr 1 with x
    simp
  _ = 1 := by exact integral_exp_neg_Ioi_zero

example := calc
  ∫ x in (0 : ℝ)..1, (3 * x + 1) / (x + 1) ^ 2
    = ∫ x in (0 : ℝ)..1, 3 / (x + 1) - 2 / (x + 1) ^ 2 := by
    congr 1 with x
    field_simp
    ring
  _ = (∫ x in (0 : ℝ)..1, 3 / (x + 1)) - ∫ x in (0 : ℝ)..1, 2 / (x + 1) ^ 2 := by
    apply intervalIntegral.integral_sub
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le]
      · sorry
      · norm_num
    · sorry
  _ = (∫ x in (0 : ℝ)..1, 3 * (1 / (x + 1))) - ∫ x in (0 : ℝ)..1, 2 * (1 / (x + 1) ^ 2) := by
    congr 2 with x
    · ring
    · ring
  _ = 3 * (∫ x in (0 : ℝ)..1, 1 / (x + 1)) - 2 * ∫ x in (0 : ℝ)..1, 1 / (x + 1) ^ 2 := by simp
  _ = 3 * log 2 - 1 := by
    congr 1
    · congr 1
      simp
      norm_num
    · calc
        _ = 2 * (∫ x in (0 : ℝ)..1, deriv (fun t => -1 / (t + 1)) x) := by
          congr 1
          apply intervalIntegral.integral_congr
          intro x hx
          obtain ⟨hx1, hx2⟩ := by simpa using hx
          symm
          calc
            deriv (fun t => -1 / (t + 1)) x = deriv ((fun t => -1) / (fun t => t + 1)) x := by
              congr 1 with t
            _ = _ := by
              rw [deriv_div]
              · simp
              · fun_prop
              · fun_prop
              · linarith
        _ = 2 * (1 / 2 : ℝ) := by
          congr 1
          rw [intervalIntegral.integral_deriv_eq_sub]
          · norm_num
          · intro x hx
            obtain ⟨hx1, hx2⟩ := by simpa using hx
            apply DifferentiableAt.fun_div
            · fun_prop
            · fun_prop
            · linarith
          · sorry
        _ = 1 := by norm_num
