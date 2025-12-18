import Mathlib

/-
What is the last digit of $2023^{2024^{2025^{2026^{2027}}}}$ ?
-/
theorem number_theory_128507 : 2023 ^ 2024 ^ 2025 ^ 2026 ^ 2027 % 10 = 1 := by
  -- First simplify the base : 2023 ^ p is congruent to 3 ^ p mod 10
  have h1 (p : ℕ) : 2023 ^ p % 10 =
      3 ^ p % 10 := by
    rw [Nat.pow_mod]

  rw [h1]

  -- Then we can reduce the exponent modulo 4, since 3^n mod 10 is periodic with period 4
  have h2 (n : ℕ) : 3 ^ (4 * n) % 10 = 1 := by
    rw [Nat.pow_mul]
    induction' n with n ih <;> omega

  -- Finally, we reduce the exponent modulo 4
  have h3 (p : ℕ) (h1a : p > 0) : 3 ^ 2024 ^ p % 10 =
      3 ^ (4 * (2024 ^ p / 4)) % 10 := by
    congr 2
    refine Eq.symm (Nat.mul_div_cancel' ?_)
    refine Nat.dvd_of_mod_eq_zero ?_
    simp [Nat.pow_mod, h1a]

  rw [h3 _ (by positivity)]
  rw [h2]
