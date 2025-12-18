import Mathlib

/-
What is the smallest positive integer that has exactly 768 divisors?
Express your answer in its prime factorization form.
-/

-- #eval (2 ^ 5 * 3 ^ 3 * 5 * 7 * 11 * 13 * 17)

theorem number_theory_619022 : IsLeast {n : ℕ | n.divisors.card = 768} 73513440 := by
  constructor
  swap
  . dsimp [lowerBounds]
    intro n h1
    have hn : n ≠ 0 := by
      by_contra! c1
      subst c1
      simp at h1
    have h2 := n.card_divisors hn
    replace h1 : ∏ p ∈ n.primeFactors, (n.factorization p + 1) = 2 ^ 8 * 3 := by
      simpa [h2] using h1
    have : n = ∏ p ∈ n.primeFactors, p ^ (n.factorization p) := by
      rw [←Nat.prod_factorization_eq_prod_primeFactors]
      symm
      exact Nat.factorization_prod_pow_eq_self hn
    let S := {f : Fin 9 → Fin 10 | ∑ k, f k = 9}
    sorry
  . dsimp
    sorry

-- #eval {f : Fin 9 → Fin 10 | ∑ k, f k = 1}.toFinset.card
-- #eval ![0, 0]
