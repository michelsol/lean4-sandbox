import Mathlib

open Nat

/-
Find all nonnegative integer solutions to  $ 2^{a}+3^{b}+5^{c}=n! $
-/
theorem number_theory_605406 :
    { (a, b, c, n) : ℕ × ℕ × ℕ × ℕ | 2 ^ a + 3 ^ b + 5 ^ c = n ! }
    = {(2, 0, 0, 3), (1, 1, 0, 3), (4, 1, 1, 4)} := by

  ext x
  let ⟨a, b, c, n⟩ := x
  dsimp

  constructor
  . intro h

-- For $n ≤ 4$, one can check that the only solutions are:
-- $2^{2}+3^{0}+5^{0}=3! $
-- $ 2^{1}+3^{1}+5^{0}=3! $
-- $ 2^{4}+3^{1}+5^{1}=4! $

    have h1 (hn : n ≤ 4) :
        (a, b, c, n) = (2, 0, 0, 3) ∨ (a, b, c, n) = (1, 1, 0, 3) ∨ (a, b, c, n) = (4, 1, 1, 4) := by
      obtain hn | hn | hn | hn | hn : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
      all_goals subst hn
      . simp at h
        have h2 : 2 ^ a ≥ 1 := by apply one_le_pow'
        have h3 : 3 ^ b ≥ 1 := by apply one_le_pow'
        have h4 : 5 ^ c ≥ 1 := by apply one_le_pow'
        omega
      . simp at h
        have h2 : 2 ^ a ≥ 1 := by apply one_le_pow'
        have h3 : 3 ^ b ≥ 1 := by apply one_le_pow'
        have h4 : 5 ^ c ≥ 1 := by apply one_le_pow'
        omega
      . simp at h
        have h2 : 2 ^ a ≥ 1 := by apply one_le_pow'
        have h3 : 3 ^ b ≥ 1 := by apply one_le_pow'
        have h4 : 5 ^ c ≥ 1 := by apply one_le_pow'
        omega
      . replace h : 2 ^ a + 3 ^ b + 5 ^ c = 6 := by convert h using 0
        have h2 : 2 ^ a ≥ 1 := by apply one_le_pow'
        have h3 : 3 ^ b ≥ 1 := by apply one_le_pow'
        have h4 : 5 ^ c ≥ 1 := by apply one_le_pow'
        have h5 : a ≤ 2 := by
          by_contra c0
          replace c0 : a ≥ 3 := by omega
          have c1 : 2 ^ a ≥ 2 ^ 3 := by refine Nat.pow_le_pow_right (by norm_num) c0
          have c2 : 2 ^ a + 3 ^ b + 5 ^ c ≥ 2 ^ 3 + 1 + 1 := by linarith
          rw [h] at c2
          omega
        have h6 : b ≤ 1 := by
          by_contra c0
          replace c0 : b ≥ 2 := by omega
          have c1 : 3 ^ b ≥ 3 ^ 2 := by refine Nat.pow_le_pow_right (by norm_num) c0
          have c2 : 2 ^ a + 3 ^ b + 5 ^ c ≥ 1 + 3 ^ 2 + 1 := by linarith
          rw [h] at c2
          omega
        have h7 : c = 0 := by
          by_contra c0
          replace c0 : c ≥ 1 := by omega
          have c1 : 5 ^ c ≥ 5 ^ 1 := by refine Nat.pow_le_pow_right (by norm_num) c0
          have c2 : 2 ^ a + 3 ^ b + 5 ^ c ≥ 1 + 1 + 5 ^ 1 := by linarith
          rw [h] at c2
          omega
        subst h7
        interval_cases a
        all_goals interval_cases b
        all_goals simp at h
        . simp
        . simp
      . replace h : 2 ^ a + 3 ^ b + 5 ^ c = 24 := by convert h using 0
        have h2 : 2 ^ a ≥ 1 := by apply one_le_pow'
        have h3 : 3 ^ b ≥ 1 := by apply one_le_pow'
        have h4 : 5 ^ c ≥ 1 := by apply one_le_pow'
        have h5 : a ≤ 4 := by
          by_contra c0
          replace c0 : a ≥ 5 := by omega
          have c1 : 2 ^ a ≥ 2 ^ 5 := by refine Nat.pow_le_pow_right (by norm_num) c0
          have c2 : 2 ^ a + 3 ^ b + 5 ^ c ≥ 2 ^ 5 + 1 + 1 := by linarith
          rw [h] at c2
          omega
        have h6 : b ≤ 2 := by
          by_contra c0
          replace c0 : b ≥ 3 := by omega
          have c1 : 3 ^ b ≥ 3 ^ 3 := by refine Nat.pow_le_pow_right (by norm_num) c0
          have c2 : 2 ^ a + 3 ^ b + 5 ^ c ≥ 1 + 3 ^ 3 + 1 := by linarith
          rw [h] at c2
          omega
        have h7 : c ≤ 1 := by
          by_contra c0
          replace c0 : c ≥ 2 := by omega
          have c1 : 5 ^ c ≥ 5 ^ 2 := by refine Nat.pow_le_pow_right (by norm_num) c0
          have c2 : 2 ^ a + 3 ^ b + 5 ^ c ≥ 1 + 1 + 5 ^ 2 := by linarith
          rw [h] at c2
          omega
        interval_cases a
        all_goals interval_cases b
        all_goals interval_cases c
        all_goals simp at h
        simp

-- Now it suffices to prove that there are no solutions for $n \geq 5$.
    suffices ¬n ≥ 5 by simpa using h1 (by omega)
    intro hn

-- A tricky way to do this is to take modulo 120,
-- since $ 2^{a} \quad(\bmod 120) \in\{1,2,4,8,16,32,64\} $
    have h2 (a : ℕ) : 2 ^ a % 120 ∈ ({1, 2, 4, 8, 16, 32, 64} : Set ℕ) := by
      induction' a with a ih
      . simp
      . simp at ih ⊢
        omega

-- $3^{b} \quad(\bmod 120) \in\{1,3,9,27,81\} $
    have h3 (b : ℕ) : 3 ^ b % 120 ∈ ({1, 3, 9, 27, 81} : Set ℕ) := by
      induction' b with b ih
      . simp
      . simp at ih ⊢
        omega

-- $ 5^{c} \quad(\bmod 120) \in\{1,5,25\} $
    have h4 (c : ℕ) : 5 ^ c % 120 ∈ ({1, 5, 25} : Set ℕ) := by
      induction' c with c ih
      . simp
      . simp at ih ⊢
        omega

-- and by inspection one notes that no three elements have vanishing sum modulo 120.
    have h5 (a b c : ℕ) : ¬(2 ^ a + 3 ^ b + 5 ^ c) % 120 = 0 := by
      specialize h2 a
      specialize h3 b
      specialize h4 c
      simp at h2 h3 h4 ⊢
      omega

    specialize h2 a
    specialize h3 b
    specialize h4 c
    specialize h5 a b c
    simp at h5

-- Therefore, $n ! \bmod 120 \ne 0$.
    have h6 : n ! % 120 ≠ 0 := by omega
-- But, $n ! \bmod (1×2×3×4×5 = 120) = 0$ since $n \geq 5$. Which is a contradiction.
    have h7 : 5 ! ∣ n ! := by
      apply factorial_dvd_factorial
      omega
    replace h7 : 120 ∣ n ! := by convert h7 using 0
    omega
  .
--  Conversely, we check that the answers are indeed solutions.
    intro h
    obtain h | h | h :
      (a, b, c, n) = (2, 0, 0, 3) ∨ (a, b, c, n) = (1, 1, 0, 3) ∨ (a, b, c, n) = (4, 1, 1, 4) := by
      simpa using h
    all_goals
      simp at h
      simp [h]
      decide
