/-
This file was edited by Aristotle.

Lean Toolchain version: leanprover/lean4:v4.20.0-rc5
Mathlib version: d62eab0cc36ea522904895389c301cf8d844fd69 (May 9, 2025)

Your Lean code is run in a custom environment, which uses these headers:

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

The following was proved by Aristotle:

- theorem number_theory_607783
    : (λ (a, b, c, d) ↦ a + b + c + d) ''
        { (a, b, c, d) : ℕ × ℕ × ℕ × ℕ |
            a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧
            (a * b : ℝ) / (a + b) + (c * d : ℝ) / (c + d) =
            ((a + b) * (c + d) : ℝ) / (a + b + c + d) } =
      { n : ℕ | n > 0 ∧ ∃ (k : ℕ) (_ : k > 1), (k : ℤ) ^ 2 ∣ n }
-/

import Mathlib


/-
Let $a, b, c, d$ be positive integers satisfying  $ \frac{a b}{a+b}+\frac{c d}{c+d}=\frac{(a+b)(c+d)}{a+b+c+d} $
Determine all possible values of $a+b+c+d$.
Answer: The possible values are the positive integers that are not square-free.
-/
theorem number_theory_607783
    : (λ (a, b, c, d) ↦ a + b + c + d) ''
        { (a, b, c, d) : ℕ × ℕ × ℕ × ℕ |
            a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧
            (a * b : ℝ) / (a + b) + (c * d : ℝ) / (c + d) =
            ((a + b) * (c + d) : ℝ) / (a + b + c + d) } =
      { n : ℕ | n > 0 ∧ ∃ (k : ℕ) (_ : k > 1), (k : ℤ) ^ 2 ∣ n } := by
  ext n
  suffices (∃ (a b c d : ℕ), (
              a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧
              (a * b : ℝ) / (a + b) + (c * d : ℝ) / (c + d) =
              ((a + b) * (c + d) : ℝ) / (a + b + c + d)
            ) ∧ a + b + c + d = n
      ) ↔ n > 0 ∧ ∃ (k : ℕ) (_ : k > 1), (k : ℤ) ^ 2 ∣ n by simpa using this
  constructor
  swap
  .
-- First, note that if we take $a=\ell, b=k \ell, c=k \ell, d=k^{2} \ell$ for some positive integers $k$ and $\ell$,
    let a (k l : ℕ) := l
    let b (k l : ℕ) := k * l
    let c (k l : ℕ) := k * l
    let d (k l : ℕ) := k ^ 2 * l

-- then we have $ \frac{a b}{a+b}+\frac{c d}{c+d}=\frac{k \ell^{2}}{\ell+k \ell}+\frac{k^{3} \ell^{2}}{k \ell+k^{2} \ell}=\frac{k \ell}{k+1}+\frac{k^{2} \ell}{k+1}=k \ell $

    have h1 (k : ℕ) (hk : k > 0) (l : ℕ) (hl : l > 0) :
        let a := a k l
        let b := b k l
        let c := c k l
        let d := d k l
        (a * b : ℝ) / (a + b) + (c * d : ℝ) / (c + d) = k * l := by
        -- Substitute the values of $a$, $b$, $c$, and $d$ into the equation and simplify.
        field_simp [a, b, c, d]
        ring

-- and $ \frac{(a+b)(c+d)}{a+b+c+d}=\frac{(\ell+k \ell)\left(k \ell+k^{2} \ell\right)}{\ell+k \ell+k \ell+k^{2} \ell}=\frac{k(k+1)^{2} \ell^{2}}{\ell(k+1)^{2}}=k \ell $

    have h2 (k : ℕ) (hk : k > 0) (l : ℕ) (hl : l > 0) :
        let a := a k l
        let b := b k l
        let c := c k l
        let d := d k l
        ((a + b) * (c + d) : ℝ) / (a + b + c + d) = k * l := by
        -- Substitute the values of $a$, $b$, $c$, and $d$ into the expression.
        simp [a, b, c, d];
        -- Combine and simplify the numerator and denominator.
        field_simp
        ring

-- so that $ \frac{a b}{a+b}+\frac{c d}{c+d}=k \ell=\frac{(a+b)(c+d)}{a+b+c+d} $

    have h3 (k : ℕ) (hk : k > 0) (l : ℕ) (hl : l > 0) :
        let a := a k l
        let b := b k l
        let c := c k l
        let d := d k l
        (a * b : ℝ) / (a + b) + (c * d : ℝ) / (c + d) =
        ((a + b) * (c + d) : ℝ) / (a + b + c + d) := by
      intro a b c d
      specialize h1 k hk l hl
      specialize h2 k hk l hl
      calc
        (_ : ℝ) = k * l := h1
        _ = _ := h2.symm

-- This means that $a+b+c+d=\ell\left(1+2 k+k^{2}\right)=\ell(k+1)^{2}$ can be attained.
-- We conclude that all non-square-free positive integers can be attained.
    intro ⟨hn, k', hk', l', h4⟩
    have ⟨k, hk, h5⟩: ∃ (k : ℕ) (_ : k > 0), k' = k + 1 := by
      use k' - 1, by omega
      omega
    subst h5
    have ⟨l, hl, h5⟩ : ∃ (l : ℕ) (_ : l > 0), l' = l := by
      use l'.toNat
      have : l'.toNat = l' := by
        apply Int.toNat_of_nonneg
        nlinarith
      use by nlinarith
      simpa using this
    subst h5
    norm_cast at h4
    specialize h3 k hk l hl
    dsimp at h3
    use a k l, b k l, c k l, d k l
    constructor
    . split_ands
      . positivity
      . positivity
      . positivity
      . positivity
      . exact h3
    . rw [h4]
      ring

-- Now, we will show that if $ \frac{a b}{a+b}+\frac{c d}{c+d}=\frac{(a+b)(c+d)}{a+b+c+d} $ then $a+b+c+d$ is not square-free.
  . intro ⟨a, b, c, d, ⟨ha, hb, hc, hd, h1⟩, h2⟩
    constructor
    . omega
-- We argue by contradiction.
-- Suppose that $a+b+c+d$ is square-free,
    subst h2
    by_contra! h2
    replace h2 (k : ℕ) (hk : k > 1) :  ¬(k : ℤ) ^ 2 ∣ a + b + c + d := by simpa using h2 k hk

-- and note that after multiplying by $(a+b)(c+d)(a+b+c+d)$,
-- we obtain $ (a b(c+d)+c d(a+b))(a+b+c+d)=(a+b)^{2}(c+d)^{2} .$
    have h3 : (a * b * (c + d) + c * d * (a + b)) * (a + b + c + d) = (a + b) ^ 2 * (c + d) ^ 2 := by
      field_simp at h1
      rify
      convert h1 using 1
      all_goals ring

-- A prime factor of $a+b+c+d$ must divide $a+b$ or $c+d$,
    have h4 (p : ℕ) (hp : p.Prime) (c1 : (p : ℤ) ∣ a + b + c + d)
        : (p : ℤ) ∣ a + b ∨ (p : ℤ) ∣ c + d := by
      -- obtain ⟨k, c1⟩ := c1
      zify at h3
      have c2 : (p : ℤ) ∣ (a * b * (c + d) + c * d * (a + b)) * (a + b + c + d) := by
        exact Dvd.dvd.mul_left c1 _
      have c3 : (p : ℤ) ∣ (a + b) ^ 2 * (c + d) ^ 2 := by
        convert c2 using 1
        rw [h3]
      obtain c4 | c4 : (p : ℤ) ∣ (a + b) ^ 2 ∨ (p : ℤ) ∣ (c + d) ^ 2 := by
        exact Int.Prime.dvd_mul' hp c3
      . left
        exact Int.Prime.dvd_pow' hp c4
      . right
        exact Int.Prime.dvd_pow' hp c4

-- and therefore divides both $a+b$ and $c+d$.
    have h5 (p : ℕ) (hp : p.Prime) (c1 : (p : ℤ) ∣ a + b + c + d) : (p : ℤ) ∣ a + b := by
      obtain h4 | h4 := h4 p hp c1
      . exact h4
      . replace c1 : (p : ℤ) ∣ (a + b) + (c + d) := by convert c1 using 1; ring
        exact (Int.dvd_iff_dvd_of_dvd_add c1).mpr h4
    have h6 (p : ℕ) (hp : p.Prime) (c1 : (p : ℤ) ∣ a + b + c + d) : (p : ℤ) ∣ c + d := by
      obtain h4 | h4 := h4 p hp c1
      . replace c1 : (p : ℤ) ∣ (a + b) + (c + d) := by convert c1 using 1; ring
        exact (Int.dvd_iff_dvd_of_dvd_add c1).mp h4
      . exact h4

-- Because $a+b+c+d$ is square-free,
-- the fact that every prime factor of $a+b+c+d$ divides $a+b$ implies
-- that $a+b+c+d$ itself divides $a+b$.
    have h7 : (a + b + c + d : ℤ) ∣ a + b := by
      suffices a + b + c + d ∣ a + b by norm_cast
      -- We prove that $a+b+c+d$ is Squarefree so as to use Nat.prod_primeFactors_of_squarefree
      have h2' : Squarefree (a + b + c + d) := by
        dsimp [Squarefree]
        intro k hk2
        specialize h2 k
        obtain hk | hk | hk : k = 0 ∨ k = 1 ∨ k > 1 := by omega
        . subst hk
          omega
        . exact Nat.isUnit_iff.mpr hk
        . specialize h2 hk
          zify at hk2
          suffices ¬(k * k : ℤ) ∣ a + b + c + d by contradiction
          convert h2 using 2
          ring
      have c1 := (a + b + c + d).prod_primeFactors_of_squarefree h2'
      rw [←c1]
      refine Finset.prod_primes_dvd (a + b) ?_ ?_
      . intro p hp
        exact Nat.prime_iff.mp (Nat.prime_of_mem_primeFactors hp)
      . intro p hp1
        have hp2 := Nat.dvd_of_mem_primeFactors hp1
        have hp3 := Nat.prime_of_mem_primeFactors hp1
        zify at hp2 ⊢
        exact h5 p hp3 hp2

-- Because $a+b < a+b+c+d$, this is impossible.
-- So $a+b+c+d$ cannot be square-free.
    have h8 : a + b < a + b + c + d := by omega
    have h9 : a + b + c + d ∣ a + b := by norm_cast at h7
    have h10 : a + b + c + d ≤ a + b := Nat.le_of_dvd (by omega) h9
    omega