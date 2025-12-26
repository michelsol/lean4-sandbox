import Mathlib

open Nat

/-
Let $a_n$ be the last nonzero digit in the decimal representation of the number $n!$.
Does the sequence $a_1,a_2,...,a_n,...$ become periodic after a finite number of terms?
-/

theorem number_theory_24347
  (lastNonZeroDigit : ℕ → ℕ)
  (lastNonZeroDigit_def : ∀ n, lastNonZeroDigit n = if n = 0 then 0 else if n ≡ 0 [MOD 10] then lastNonZeroDigit (n / 10) else n)
  : let a (n : ℕ) := lastNonZeroDigit n !
    ¬(∃ n₀, ∃ T > 0, Function.Periodic (λ n => a (n + n₀)) T)
  := by
  -- We assume the sequence eventually becomes periodic, and we will derive a contradiction.
  intro a
  intro ⟨n₀, T, hT, periodic_a⟩
  -- Thanks to Euler's theorem,
  -- we can find integers $k > m > 0$, as large as we like, such that $10^k \equiv 10^m \mod T$.
  -- We will choose $k$ so that $10^k > n₀$.
  let T' := T / (2 ^ T.factorization 2 * 5 ^ T.factorization 5)
  let v := max (T.factorization 2) (T.factorization 5)
  let k := v + φ T' + n₀
  let m := v + n₀
  have _10_pow_k_modeq_10_pow_m : 10 ^ k ≡ 10 ^ m [MOD T] := by
    have h1 : 10 ^ φ T' ≡ 1 [MOD T'] := by
      have h1: Coprime 10 T' := by
        sorry
      exact ModEq.pow_totient h1
    replace h1 : 10 ^ (v + φ T') ≡ 10 ^ v [MOD T] := by
      replace h1 := ModEq.mul_left' (10 ^ v) h1
      sorry
    sorry
  have k_ge_1 : k ≥ 1 := sorry
  have k_ge_m : k ≥ m := sorry
  have _10_pow_k_ge_10_pow_m : 10 ^ k ≥ 10 ^ m := sorry
  have _10_pow_k_gt_n₀ : 10 ^ k > n₀ :=
    have : k > n₀ := sorry
    sorry
  -- For $k \ge 1$, we have $a_{10^k-1} = a_{10^k}$ and hence, taking $k$ sufficiently large and
  --  using the periodicity, we see that $a_{2\cdot 10^k - 10^m - 1}=a_{2\cdot 10^k - 10^m}$.
  have a_10_pow_k_sub_one : ∀ k ≥ 1, a (10 ^ k - 1) = a (10 ^ k) := by
    have h1 : ∀ n ≥ 5, lastNonZeroDigit n ! = lastNonZeroDigit (n ! / 10) := by
      have h1 : ∀ n ≥ 5, n ! ≡ 0 [MOD 10] := by
        apply le_induction
        . decide
        . intro n hn ihn
          rw [factorial_succ]
          exact ModEq.mul rfl ihn
      intro n hn
      conv_lhs => rw [lastNonZeroDigit_def]
      simp [factorial_ne_zero, h1 n hn]
    intro k hk
    have h2 : 10 ^ k ≥ 5 := sorry
    specialize h1 _ h2
    suffices (10 ^ k - 1)! = (10 ^ k)! / 10 from by simp [a, this, h1]
    sorry
  have h1 : a (2 * 10 ^ k - 10 ^ m - 1) = a (2 * 10 ^ k - 10 ^ m) := calc
    _ = a (10 ^ k - 1) := by
      have : 2 * 10 ^ k - 10 ^ m - 1 = 10 ^ k - 1 + (10 ^ k - 10 ^ m) := by
        zify
        have : 10 ^ k ≥ 1 := one_le_pow k 10 (by norm_num)
        have : 10 ^ m ≥ 1 := one_le_pow m 10 (by norm_num)
        have : 2 * 10 ^ k ≥ 10 ^ m := by omega
        have : 2 * 10 ^ k - 10 ^ m ≥ 1 := by omega
        push_cast [*]
        ring_nf
      rw [this]
      obtain ⟨c, hc⟩ := (modEq_iff_dvd' (by simpa)).mp _10_pow_k_modeq_10_pow_m.symm
      rw [hc]
      have h1 := periodic_a.nat_mul c (10 ^ k + 1 - n₀)
      sorry
    _ = a (10 ^ k) := a_10_pow_k_sub_one k k_ge_1
    _ = _ := by
      have : 2 * 10 ^ k - 10 ^ m = 10 ^ k + (10 ^ k - 10 ^ m) := by
        zify
        have : 2 * 10 ^ k ≥ 10 ^ m := by omega
        push_cast [*]
        ring_nf
      rw [this]
      obtain ⟨c, hc⟩ := (modEq_iff_dvd' (by simpa)).mp _10_pow_k_modeq_10_pow_m.symm
      rw [hc]
      have h1 := periodic_a.nat_mul c (10 ^ k - n₀)
      sorry
  -- Since $(2 \cdot 10^k - 10^m)! = (2 \cdot 10^k - 10^m)(2 \cdot 10^k - 10^m - 1)!$ and the last
  -- nonzero digit of $2 \cdot 10^k - 10^m$ is nine,
  -- we must have $a_{2\cdot 10^k - 10^m - 1}=5$.
  have h2 : (2 * 10 ^ k - 10 ^ m)! = (2 * 10 ^ k - 10 ^ m) * (2 * 10 ^ k - 10 ^ m - 1)! := by
    sorry
  have h3 : lastNonZeroDigit (2 * 10 ^ k - 10 ^ m) = 9 := sorry
  have h4 : a (2 * 10 ^ k - 10 ^ m - 1) = 5 := sorry
  let n := 2 * 10 ^ k - 10 ^ m - 1
  replace h4 : lastNonZeroDigit n ! = 5 := h4
  have h5 : (n !).factorization 5 > (n !).factorization 2 := by
    have h1 : ∀ n, lastNonZeroDigit n =
        (n / 10 ^ min (n.factorization 2) (n.factorization 5)) % 10 := by
      sorry
    sorry
  -- So with $n=2\cdot 10^k - 10^m - 1$, this means $5$ divides $n!$ with a greater power than $2$ does.
  -- But Legendre's formula for $n!$ can be used to show that $v_2(n!) \le v_5(n!)$. This is a contradiction.
  have h6 : (n !).factorization 2 ≥ (n !).factorization 5 := by
    sorry
  omega
