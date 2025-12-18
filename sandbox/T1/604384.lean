import Mathlib

open Polynomial
/-
The polynomial $ A(x) = x^{2} + a x + b $ with integer coefficients
has the property that for every prime number $ p $, there exists an integer $ k $
such that both $ A(k) $ and $ A(k+1) $ are divisible by $ p $.
Prove that there exists an integer $ m $ such that $ A(m) = A(m+1) = 0 $.
-/
theorem algebra_604384
    (a b : ℤ)
    (A : ℤ[X])
    (hA1 : A = X ^ 2 + C a * X + C b)
    (hA2 : ∀ p : ℕ, p.Prime → ∃ k : ℤ, A.eval k = (0 : ZMod p) ∧ A.eval (k + 1) = (0 : ZMod p))
    : ∃ m : ℤ, A.eval m = 0 ∧ A.eval (m + 1) = 0 := by

-- Let $p$ be a prime number
-- and let $k$ be such that $A(k)$ and $A(k+1)$ are both divisible by $p$.

-- The difference of $A(k)$ and $A(k+1)$ is then also divisible by $p$
-- and this is equal to $ A(k+1)-A(k)=(k+1)^{2}+a(k+1)+b-\left(k^{2}+a k+b\right)=2 k+1+a, $
-- so $2 k \equiv-1-a \bmod p$.
  have h1 (p : ℕ) (hp : p.Prime)
      (k : ℤ) (hk1 : A.eval k = (0 : ZMod p)) (hk2 : A.eval (k + 1) = (0 : ZMod p))
      : 2 * k = (-1 - a : ZMod p) := by
    have g1 := calc
        (0 : ZMod p) = A.eval (k + 1) - A.eval k := by
          simp [hk1, hk2]
        A.eval (k + 1) - A.eval k = ((k + 1) ^ 2 + a * (k + 1) + b - (k ^ 2 + a * k + b) : ZMod p) := by
          simp [hA1]
        _ = (2 * k + 1 + a : ZMod p) := by
          ring
    symm
    apply_fun λ x : ZMod p ↦ x - 1 - a at g1
    ring_nf at g1 ⊢
    simpa using g1

-- Since $A(k)$ is divisible by $p$, $4 A(k)$ is also divisible by $p$,
  have h2 (p : ℕ) (hp : p.Prime)
      (k : ℤ) (hk1 : A.eval k = (0 : ZMod p))
      : 4 * A.eval k = (0 : ZMod p) := by simp [hk1]

-- modulo $p$ we have $ 4 A(k)=4 k^{2}+4 a k+4 b \equiv(-1-a)^{2}+2(-1-a) a+4 b=-a^{2}+4 b+1 \quad \bmod p $
  have h3 (p : ℕ) (hp : p.Prime)
      (k : ℤ) (hk1 : A.eval k = (0 : ZMod p)) (hk2 : A.eval (k + 1) = (0 : ZMod p))
      : 4 * A.eval k = (-a ^ 2 + 4 * b + 1 : ZMod p) := by
    have g1 : 4 * A.eval k = (0 : ZMod p) := by
      simp [hk1]
    calc
      (4 * A.eval k : ZMod p) = 4 * k ^ 2 + 4 * a * k + 4 * b := by
        simp [hA1]
        ring
      _ = (2 * k) ^2 + 2 * (2 * k) * a + 4 * b := by
        ring
      _ = (-1 - a) ^ 2 + 2 * (-1 - a) * a + 4 * b := by
        specialize h1 p hp k hk1 hk2
        congr 4
      _ = -a ^ 2 + 4 * b + 1 := by
        ring

-- The right-hand side is no longer dependent on $k$.
-- We see that for every prime number $p$, the number $-a^{2}+4 b+1$ must be divisible by $p$.
  have h4 (p : ℕ) (hp : p.Prime) : -a ^ 2 + 4 * b + 1 = (0 : ZMod p) := by
    obtain ⟨k, hk1, hk2⟩ := hA2 p hp
    specialize h2 p hp k hk1
    specialize h3 p hp k hk1 hk2
    rw [←h3]
    rw [h2]

-- This can only be true if $-a^{2}+4 b+1=0$.
-- Therefore, $a^{2}=4 b+1$.
  have h5 : a ^ 2 = 4 * b + 1 := by
    suffices -a ^ 2 + 4 * b + 1 = 0 from by linarith
    suffices (-a ^ 2 + 4 * b + 1).natAbs = 0 from by exact Int.natAbs_eq_zero.mp this
    by_contra! g0
    have g1 (p : ℕ) (hp : p.Prime) : (p : ℤ) ∣ -a ^ 2 + 4 * b + 1 := by
      specialize h4 p hp
      norm_cast at h4
      simpa only [ZMod.intCast_zmod_eq_zero_iff_dvd] using h4
    have g2 (p : ℕ) (hp : p.Prime) : p ≤ (-a ^ 2 + 4 * b + 1).natAbs := by
      specialize g1 p hp
      have g3 : (p : ℤ) ∣ (-a ^ 2 + 4 * b + 1).natAbs := by exact Int.dvd_natAbs.mpr g1
      norm_cast at g3
      exact Nat.le_of_dvd (by omega) g3
    have ⟨p, g3, g4⟩ := Nat.exists_infinite_primes ((-a ^ 2 + 4 * b + 1).natAbs + 1)
    specialize g2 p g4
    omega

-- We see that $a$ must be odd, and we write $a=2 c+1$ with $c \in \mathbb{Z}$.
  have ⟨c, h6⟩ : ∃ c : ℤ, a = 2 * c + 1 := by
    suffices a % 2 = 1 from by
      apply Odd.exists_bit1
      exact Int.odd_iff.mpr this
    apply_fun (. % 2) at h5
    replace h5 : a ^ 2 % 2 = 1 := by omega
    replace h5 : a * a % 2 = 1 := by convert h5 using 2; ring
    rw [Int.mul_emod] at h5
    by_contra h6
    replace h6 : a % 2 = 0 := by omega
    rw [h6] at h5
    omega

-- Then $4 b+1=a^{2}=4 c^{2}+4 c+1$, so $b=c^{2}+c$.
  have h7 : b = c ^ 2 + c := by
    have g1 := calc
      4 * b + 1 = a ^ 2 := by rw [h5]
      _ = 4 * c ^ 2 + 4 * c + 1 := by
        apply_fun (. ^ 2) at h6
        ring_nf at h6 ⊢
        simpa using h6
    linarith

-- The polynomial is therefore of the form $A(x)=x^{2}+(2 c+1) x+\left(c^{2}+c\right)$ with $c$ an integer.
  have h8 : A = X ^ 2 + C (2 * c + 1) * X + C (c ^ 2 + c) := by
    rw [hA1, h6, h7]

-- We can factor this as $A(x)=(x+c)(x+c+1)$,
  have h9 : A = (X + C c) * (X + C (c + 1)) := by
    symm
    calc
      (X + C c) * (X + C (c + 1)) = X ^ 2 + (C (c + 1) + C c) * X + C c * C (c + 1) := by
        ring
      _ = X ^ 2 + (C (2 * c + 1)) * X + C (c ^ 2 + c) := by
        congr 3
        . simp
          ring
        . simp
          ring
      _ = A := by rw [h8]

-- from which it follows that $x=-c$ and $x=-c-1$ are the roots of the polynomial.
-- These are both integers.
-- We conclude that $m=-c-1$ satisfies $A(m)=A(m+1)=0$.
  use -c - 1
  constructor
  . simp [h9]
  . simp [h9]
