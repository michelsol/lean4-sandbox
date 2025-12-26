import Mathlib

open Finset

/-
Prove that there exist two strictly increasing sequences
$\left(a_{n}\right)$ and $\left(b_{n}\right)$ such that
$a_{n}\left(a_{n}+1\right)$ divides $b_{n}^{2}+1$ for every natural number $n$.
-/

theorem number_theory_24942 :
    ∃ (a b : ℕ → ℕ) (_ : StrictMono a) (_ : StrictMono b),
      ∀ n, (a n * (a n + 1) : ℤ) ∣ b n ^ 2 + 1 := by
-- We first prove the following lemma.
-- Lemma. For $d, c \in ℤ$ and $d^{2} \mid c^{2}+1$ there exists
-- $b \in ℤ$ such that $d^{2}\left(d^{2}+1\right) \mid b^{2}+1$.
  have lemma1 (d c : ℕ) (hdc : (d ^ 2 : ℤ) ∣ c ^ 2 + 1) :
    let b := c + d ^ 2 * (c - d : ℤ)
    (d ^ 2 * (d ^ 2 + 1) : ℤ) ∣ b ^ 2 + 1 := by
-- Proof. It is enough to set $b=c+d^{2} c-d^{3}=c+d^{2}(c-d)$.
    obtain ⟨k, hk⟩ := hdc
    suffices (d ^ 2 * (d ^ 2 + 1) : ℤ) ∣
        c ^ 2 + 1 + d ^ 4 * (c - d : ℤ) ^ 2 + 2 * c * d ^ 2 * (c - d : ℤ) from by
      ring_nf at this ⊢; simpa
    rw [hk]
    suffices (d ^ 2 * (d ^ 2 + 1) : ℤ) ∣ d ^ 2 * (k +
        d ^ 2 * (c - d : ℤ) ^ 2 + 2 * c * (c - d : ℤ)) from by
      ring_nf at this ⊢; simpa
    suffices (d ^ 2 + 1 : ℤ) ∣ k + d ^ 2 * (c - d : ℤ) ^ 2 + 2 * c * (c - d  : ℤ) from by
      exact Int.mul_dvd_mul_left _ this
    suffices (d ^ 2 + 1 : ℤ) ∣ (d ^ 2 + 1) * (c - d : ℤ) ^ 2 + (c ^ 2 + 1) + k - 1 - d ^ 2 from by
      ring_nf at this ⊢; simpa
    rw [hk]
    suffices (d ^ 2 + 1 : ℤ) ∣ (d ^ 2 + 1) * ((c - d : ℤ) ^ 2 + k - 1) from by
      ring_nf at this ⊢; simpa
    simp

-- Using the lemma it suffices to find increasing sequences $d_{n}$ and $c_{n}$ such that
-- $c_{n}-d_{n}$ is an increasing sequence and $d_{n}^{2} \mid c_{n}^{2}+1$.
  suffices ∃ (d c : ℕ → ℕ) (_ : StrictMono c) (_ : StrictMono d)
      (_ : ∀ n, c n ≥ d n)
      (_ : StrictMono (c - d)),
      ∀ n, (d n ^ 2 : ℤ) ∣ c n ^ 2 + 1 from by
    obtain ⟨d, c, strictmono_c, strictmono_d, c_ge_d, strictmono_c_sub_d, hdc⟩ := this
-- We obtain the desired sequences $a_{n}$ and $b_{n}$ from
-- $a_{n}=d_{n}^{2}$ and $b_{n}=c_{n}+d_{n}^{2}\left(c_{n}-d_{n}\right)$.
    have hb n := lemma1 (d n) (c n) (hdc n)
    use λ n ↦ d n ^ 2, λ n ↦ c n + d n ^ 2 * (c n - d n)
    use by
      intro i j hij
      specialize strictmono_d hij
      show d i ^ 2 < d j ^ 2
      gcongr
    use by
      intro i j hij
      specialize strictmono_c hij
      specialize strictmono_d hij
      have : c i - d i < c j - d j := strictmono_c_sub_d hij
      show c i + d i ^ 2 * (c i - d i) < c j + d j ^ 2 * (c j - d j)
      gcongr
    intro n
    specialize hb n
    push_cast [c_ge_d n]
    exact hb

-- It is easy to check that $d_{n}=2^{2 (n + 1)}+1$ and $c_{n}=2^{(n + 1) d_{n}}$
-- satisfy the required conditions.
  let d n := 2 ^ (2 * (n + 1)) + 1
  let c n := 2 ^ ((n + 1) * d n)
  have c_ge_d n : c n ≥ d n := by
    dsimp only [c, d]
    apply Nat.pow_lt_pow_of_lt
    . norm_num
    sorry
  use d, c
  use by
    dsimp only [c, d]
    apply strictMono_nat_of_lt_succ
    intro n
    gcongr <;> omega
  use by
    dsimp only [c, d]
    apply strictMono_nat_of_lt_succ
    intro n
    gcongr <;> omega
  use c_ge_d
  use by
    apply strictMono_nat_of_lt_succ
    intro n
    dsimp [c, d]
    zify [c_ge_d]
    sorry
  use by
    intro n
-- Thanks to our choice of $c_n$ and $d_n$, we obtain $c_n^2 = (d_n - 1)^{d_n}$
    have : (c n) ^ 2 = (d n  + (-1) : ℤ) ^ d n := by
      dsimp only [c]
      push_cast
      sorry
-- And use the binomial theorem.
    replace : c n ^ 2 + 1 =
        ∑ m ∈ Finset.range (d n + 1), d n ^ m * (-1 : ℤ) ^ (d n - m) * ((d n).choose m) + 1 := by
      rw [←add_pow]
      omega
-- Extract the first term.
    replace : c n ^ 2 + 1 =
        ∑ m ∈ Finset.Icc 1 (d n), d n ^ m * (-1 : ℤ) ^ (d n - m) * ((d n).choose m)
          + ((-1 : ℤ) ^ (d n) + 1) := by
      sorry
-- $d_n$ is obviously odd so we can simplify the sum.
    replace : c n ^ 2 + 1 =
        ∑ m ∈ Finset.Icc 1 (d n), d n ^ m * (-1 : ℤ) ^ (d n - m) * ((d n).choose m) := by
      sorry
    rw [this]
-- $d_n^2$ divides every term of the sum, so it must divide $c_n^2 + 1$ and we're done.
    sorry
