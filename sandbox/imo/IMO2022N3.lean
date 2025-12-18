import Mathlib

open Real

/- Let $a>1$ be a positive integer, and let $d>1$ be a positive integer coprime to $a$.

Let $x_{1}=1$ and, for $k \geqslant 1$, define  $ x_{k+1}= \begin{cases}x_{k}+d & \text { if } a \text { doesn't divide } x_{k} \\ x_{k} / a & \text { if } a \text { divides } x_{k}\end{cases} $

Find the greatest positive integer $n$ for which there exists
an index $k$ such that $x_{k}$ is divisible by $a^{n}$.
-/
theorem number_theory_24371
    (a : ℕ)
    (ha : a > 1)
    (d : ℕ)
    (hd : d > 1)
    (hda : Nat.Coprime d a)
    (x : ℕ → ℕ)
    (hx1 : x 1 = 1)
    (hx : ∀ k ≥ 1, x (k + 1) = if (a : ℤ) ∣ x k then x k / a else x k + d) :
    IsGreatest {n | 0 < n ∧ ∃ k ≥ 1, (a : ℤ) ^ n ∣ x k} ⌈log d / log a⌉₊ := by

-- We will show that n is the only exponent with $d < a^n < a d$  i.e. $n = \lceil \frac{\log d}{\log a} \rceil$
  set n := ⌈log d / log a⌉₊ with h0
  have h0' := h0.symm
  rw [Nat.ceil_eq_iff] at h0'
  swap
  . sorry
  have hn1 : d < a ^ n := by
    sorry
  have hn2 : a ^ n < a * d := by
    sorry

-- By trivial induction, $x_{k}$ is coprime to $d$.
  have h2 (k : ℕ) (hk : k ≥ 1) : Nat.Coprime (x k) d := by
    revert k
    apply Nat.le_induction
    . simp [hx1]
    . intro k hk ih
      rw [hx k hk]
      split_ifs with c1
      . refine Nat.Coprime.coprime_div_left ih ?_
        norm_cast at c1
      . exact Nat.coprime_add_self_left.mpr ih

-- There can be at most $a-1$ consecutive increasing terms in the sequence.
  have h3 (k : ℕ) (hk : k ≥ 1) (m : ℕ) (hm : ∀ i ≤ m, x (k + i) = x k + d * i) : m < a := by
    obtain ⟨i, hi, c1⟩ : ∃ i < a, x k + (d : ZMod a) * i = 0 := by
      have : NeZero a := by apply NeZero.of_pos; omega
      use ((d : ZMod a)⁻¹ * -x k).val
      use by apply ZMod.val_lt
      calc
        _ = x k + d * (d : ZMod a)⁻¹ * -x k := by simp; ring
        _ = x k + 1 * -x k := by
          congr 2
          exact ZMod.coe_mul_inv_eq_one d hda
        _ = _ := by ring
    by_contra! h3
    have c2 := hm i (by linarith)
    have c3 : x (k + i + 1) = x (k + i) + d := calc
      _ = x (k + (i + 1)) := by ring_nf
      _ = x k + d * (i + 1) := by rw [hm (i + 1) (by linarith)]
      _ = x k + d * i + d := by ring
      _ = x (k + i) + d := by congr 1; rw [c2]
    have c4 : (a : ℤ) ∣ x (k + i) := by
      norm_cast at c1
      rw [←c2] at c1
      rw [←ZMod.intCast_zmod_eq_zero_iff_dvd]
      simpa using c1
    have c5 : x (k + i + 1) = x (k + i) / a := by simpa [c4] using hx (k + i) (by omega)
    have c6 : x (k + i) ≥ x (k + i + 1) := by
      rw [c5]
      exact Nat.div_le_self (x (k + i)) a
    have c7 : x (k + i) < x (k + i + 1) := by rw [c3]; omega
    omega

-- Using that fact by induction
-- it also holds that $x_{k} < a d$ if $x_{k}=x_{k-1}+d$
  have h4 (k : ℕ) (hk : k ≥ 2) (h : ¬(a : ℤ) ∣ x (k - 1)) : x k < a * d := by
    sorry

-- and that $x_{k} < d$ if $x_{k}=\frac{x_{k-1}}{a}$ or $k=1$.
  have h5 (k : ℕ) (hk : k ≥ 2) (h : (a : ℤ) ∣ x (k - 1)) : x k < d := by
    sorry

-- This gives the upper bound on the exponent.
  constructor
  swap
  . intro i ⟨hi, ⟨k, hk, h6⟩⟩
    obtain h7 | h7 : k = 1 ∨ k ≥ 2 := by omega
    . sorry
    . sorry

-- It remains to show that some $x_{k}$ is divisible by $a^{n}$
  . constructor
    . sorry
    .
-- We now know that the sequence is (eventually) periodic,
-- and that both increasing and decreasing steps happen infinitely many times.
      have h6 : ∃ i0 ≥ 1, ∃ T > 0, (λ i ↦ x (i + i0)).Periodic T := sorry

-- Denote $a^{-k}$ the multiplicative inverse of $a^{k}$ modulo $d$.
-- The sequence contains elements congruent to $1, a^{-1}, a^{-2}, \ldots$ modulo $d$.
-- Let $x_{k_{0}}$ the first element such that $x_{k_{0}} \equiv a^{-n}(\bmod d)$.
      obtain ⟨k0, h7, h8⟩ : ∃ k0 ≥ 1, x k0 = (a ^ n : ZMod d)⁻¹ := by
        sorry

-- We have either $k_{0}=1$ or $x_{k_{0}}=$ $x_{k_{0}-1} / a$
-- in both cases $x_{k_{0}} < d < a^{n} < d a$
      have h9 : x k0 < d := by sorry

-- and therefore $ x_{k_{0}} \in\left\{a^{n}-d, a^{n}-2 d, \ldots, a^{n}-(a-1) d\right\} $
      obtain ⟨i, hi, h10⟩ : ∃ i < a, x k0 = a ^ n - d * i := by
        sorry

-- In this set no element is divisible by $a$,
      have h11 : ¬a ∣ x k0 := by
        sorry

-- so therefore the sequence will visit the value $a^{n}$ in the next $a-1$ steps.
      obtain ⟨j, hj, h12⟩ : ∃ j < a, x (k0 + i) = a ^ n := by sorry
      use k0 + i
      use by omega
      simp [h12]
