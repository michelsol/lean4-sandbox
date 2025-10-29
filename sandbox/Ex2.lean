import Mathlib


/-- The `n`-th digit of `x` in base `b`. -/
def nth_digit (b x n : ℕ) := x / b ^ n % b

/-
How many ordered pairs of integers $(m, n)$ satisfy $\sqrt{n^2 - 49} = m$?
-/
open Real

example :
  let S := { (m, n) : ℤ × ℤ | n ^ 2 - 49 ≥ 0 ∧ √(n ^ 2 - 49) = m }
  S = {(24, 25), (0, 7), (0, -7), (24, -25)} := by
  intro S
  subst S
  ext ⟨m, n⟩
  calc
    _ ↔ n ^ 2 - 49 ≥ 0 ∧ √(n ^ 2 - 49) = m := by rfl
    _ ↔ m ≥ 0 ∧ n ^ 2 - 49 = m ^ 2 := by
      constructor
      · intro ⟨h1, h2⟩
        split_ands
        · rify
          rw [←h2]
          apply Real.sqrt_nonneg
        · rify at h1 ⊢
          refine (sqrt_eq_iff_eq_sq h1 ?_).mp h2
          · rw [←h2]
            apply Real.sqrt_nonneg
      · intro ⟨h1, h2⟩
        split_ands
        · rw [h2]
          apply sq_nonneg
        · rify at h1 h2
          rw [h2]
          exact sqrt_sq h1
    _ ↔ m ≥ 0 ∧ (n + m) * (n - m) = 49 := by
      constructor
      all_goals
        intro ⟨h1, h2⟩
        split_ands
        exact h1
        linarith
    _ ↔ _ := by
      constructor
      · intro ⟨h1, h2⟩
        sorry
      · intro h1
        obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ := h1
        all_goals norm_num

example (a b : ℤ) (h1 : a * b = 49) : (a, b) = (7, 7) ∨ (a, b) = (49, 1) ∨ (a, b) = (1, 49) ∨
    (a, b) = (-7, -7) ∨ (a, b) = (-49, -1) ∨ (a, b) = (-1, -49) := by
  suffices a = 7 ∨ a = 49 ∨ a = 1 ∨ a = -7 ∨ a = -49 ∨ a = -1 by
    rcases this with h2 | h2 | h2 | h2 | h2 | h2
    all_goals
      subst h2
      norm_num
      linarith
  suffices a.natAbs ∈ ({1, 7, 49} : Finset ℕ) by
    obtain h2 | h2 | h2 := by simpa using this
    all_goals
      rw [Int.natAbs_eq_iff] at h2
      tauto
  convert_to a.natAbs ∈ Nat.divisors 49 using 1
  refine Nat.mem_divisors.mpr ⟨?_, by norm_num⟩
  refine Int.dvd_natCast.mp ?_
  use b
  simpa using h1.symm
