import Mathlib

/-
Determine the smallest integer multiple of $9997$, other than $9997$ itself,
that consists exclusively of odd digits.
-/

theorem number_theory_619295 :
    let hasIthDigit (m : ℕ) (i : ℕ) := m / 10 ^ i ≠ 0
    let ithDigit (m : ℕ) (i : ℕ) := (m / 10 ^ i) % 10
    IsLeast {m : ℕ | m % 9997 = 0 ∧ m ≠ 9997 ∧ m ≠ 0 ∧
      ∀ (i : ℕ) (_ : hasIthDigit m i), ithDigit m i % 2 = 1} 33339995 := by

  intro hasIthDigit ithDigit
-- The solution requires finding the smallest integer multiple of $9997$,
-- other than $9997$ itself, that consists exclusively of odd digits.
  constructor
  swap
  . intro m ⟨h1, h2, h3, h4⟩

-- The multiple must be an odd multiple, so it can be expressed as $9997(2a + 1)$,
-- where $a  >  0$.
    have h5 : m % 2 = 1 := by
      specialize h4 0 (by omega)
      convert_to m % 10 % 2 = 1 using 1 at h4
      . simp [ithDigit]
      convert_to m % 2 = 1 using 1 at h4
      . apply Nat.mod_mod_of_dvd
        omega
      exact h4
    have ⟨a, h6⟩ : ∃ a : ℕ, m = 9997 * (2 * a + 1) := by
      have ⟨k, c1⟩ : 9997 ∣ m := by omega
      have c2 : k % 2 = 1 := by simpa [c1, Nat.mul_mod] using h5
      have ⟨a, c3⟩ : ∃ a : ℕ, k = 2 * a + 1 := by
        refine Odd.exists_bit1 ?_
        exact Nat.odd_iff.mpr c2
      use a
      convert c1 using 2
      rw [c3]

-- Rewrite the expression using the distributive property:
-- $9997(2a + 1) = (10000 - 3)(2a + 1) = 10000(2a + 1) - 6a - 3$.
    have h7 : (m : ℤ) = 10000 * (2 * a + 1) - 6 * a - 3 := by linarith

-- Simplify the expression:
-- $10000(2a + 1) - 6a - 3 = 10000(2a) + 10000 - 6a - 3 = 10000(2a) + 9997 - 6a$.
    have h8 : (m : ℤ) = 10000 * (2 * a) + (9997 - 6 * a) := by linarith

-- If $a \le 1666$, the number will be formed by concatenating the number $2a$ with the
-- four-digit number $9997 - 6a$ (with leading zeroes if necessary to make it four digits).
-- the fifth digit from the right will always be even,
-- which does not satisfy the condition of having only odd digits.
-- Therefore, $a$ must be greater than $1666$, so $a \ge 1667$.
    have h9 : a ≥ 1667 := by
      by_contra! h9
      have c1 : 9997 ≥ 6 * a := by linarith
      convert_to m = 10000 * (2 * a) + (9997 - 6 * a) using 1 at h8
      . zify [c1]
      have c2 : ithDigit m 4 % 2 = 0 := calc
        _ = m / 10000 % 10 % 2 := rfl
        _ = m / 10000 % 2 := by apply Nat.mod_mod_of_dvd; omega
        _ = (10000 * (2 * a) + (9997 - 6 * a)) / 10000 % 2 := by rw [h8]
        _ = (10000 * (2 * a) / 10000 + (9997 - 6 * a) / 10000) % 2 := by
          congr 1
          apply Nat.add_div_eq_of_add_mod_lt
          calc
            _ = 0 + (9997 - 6 * a) % 10000 := by congr 1; simp
            _ = (9997 - 6 * a) % 10000 := by ring
            _ < _ := by apply Nat.mod_lt; norm_num
        _ = (10000 * (2 * a) / 10000 + 0) % 2 := by
          congr 2
          apply Nat.div_eq_zero_iff.mpr
          right
          linarith
        _ = 10000 * (2 * a) / 10000 % 2 := by congr 1
        _ = 2 * a % 2 := by congr 1; simp
        _ = 0 := by omega
      specialize h4 4 (by
        dsimp [hasIthDigit]
        by_contra! c3
        convert_to 2 * a = 0 using 1 at c3
        . calc
            _ = (10000 * (2 * a) + (9997 - 6 * a)) / 10000 := by rw [h8]
            _ = (10000 * (2 * a) / 10000 + (9997 - 6 * a) / 10000) := by
              apply Nat.add_div_eq_of_add_mod_lt
              calc
                _ = 0 + (9997 - 6 * a) % 10000 := by congr 1; simp
                _ = (9997 - 6 * a) % 10000 := by ring
                _ < _ := by apply Nat.mod_lt; norm_num
            _ = (10000 * (2 * a) / 10000 + 0) := by
              congr 1
              apply Nat.div_eq_zero_iff.mpr
              right
              linarith
            _ = 10000 * (2 * a) / 10000 := by ring
            _ = _ := by simp
        convert_to m = 9997 using 1 at h6
        . calc
            _ = 9997 * (0 + 1) := by congr 2
            _ = _ := by norm_num
        contradiction)
      omega

-- The smallest value for $2a + 1$ is when $a = 1667$, giving $2a + 1 = 3335$.
-- So the multiple is no less than $3335 \cdot 9997 = 33339995$.
    linarith

-- Verify that $33339995$ consists exclusively of odd digits.
  . split_ands
    . norm_num
    . norm_num
    . norm_num
    . intro i
      obtain h1 | h1 : i ≥ 8 ∨ i ≤ 7 := by omega
      . intro h2
        replace h2 : 10 ^ i ≤ 33339995 := by simpa [hasIthDigit, Nat.div_eq_zero_iff] using h2
        suffices 10 ^ 8 ≤ 33339995 by norm_num at this
        calc
          _ ≤ 10 ^ i := by
            apply Nat.pow_le_pow_of_le_right
            . norm_num
            . exact h1
          _ ≤ _ := h2
      . intro h2
        dsimp [ithDigit]
        interval_cases i
        all_goals norm_num
