-- p706
import Mathlib

/- Let $$p$$ be a prime number.
Prove that there exists a prime number $$q$$ such that for every integer $$n$$,
the number $$n^{p}-p$$ is not divisible by $$q$$. -/
theorem number_theory_25152
    (p : ℕ) (hp : Prime p) :
    ∃ (q : ℕ) (hq : Prime q), ∀ n : ℤ, ¬(q : ℤ) ∣ n ^ p - p := by
-- Suppose that for every prime $$q$$, there exists an $$n$$ for which $$n^{p} \equiv p(\bmod$$ $$q$$ ).
  by_contra! h1
  replace h1 : ∀ q : ℕ, Prime q → ∃ n : ℤ, n ^ p ≡ p [ZMOD q] := by
    intro q hq
    obtain ⟨n, c1⟩ := h1 q hq
    use n
    rw [Int.modEq_iff_dvd, ←Int.dvd_neg]
    simpa using c1

-- Choose a prime $$q=k p+1$$ with $$k ∈ ℕ$$
  obtain ⟨k, h2⟩ : ∃ k : ℕ, Prime (k * p + 1) := by
    have ⟨q, hq, ⟨c1, c2⟩⟩ := Nat.exists_prime_gt_modEq_one 0 hp.ne_zero
    symm at c2
    rw [Nat.modEq_iff_dvd'] at c2
    . obtain ⟨k, hk⟩ := c2
      use k
      replace hk : q = p * k + 1 := by omega
      rw [hk] at hq
      rw [Nat.prime_iff] at hq
      ring_nf at hq ⊢
      simpa using hq
    . simpa using c1
  set q := k * p + 1
  have ⟨n, h3⟩ := h1 q h2

-- By Fermat's theorem we deduce that $$p^{k} \equiv$$ $$n^{k p}=n^{q-1} \equiv 1(\bmod q)$$,
  have h4 : p ^ k ≡ 1 [ZMOD q] := calc
      _ ≡ n ^ (k * p) [ZMOD q] := by
        sorry
      _ = n ^ (q - 1) := by
        sorry
      _ ≡ 1 [ZMOD q] := by
        sorry

-- so $$q \mid p^{k}-1$$.
  symm at h4
  rw [Int.modEq_iff_dvd] at h4

-- It is known that any prime $$q$$ such that $$q \left\lvert, \frac{p^{p}-1}{p-1}\right.$$ must satisfy $$q \equiv 1(\bmod$$ $$p$$ ).
  have h5 (q : ℕ) (hq : Prime q) (c1 : (q : ℤ) ∣ (p ^ p - 1) / (p - 1)) : q ≡ 1 [ZMOD p] := by
    sorry

-- Indeed, from $$q \mid p^{q-1}-1$$ it follows that $$q \mid p^{\operatorname{gcd}(p, q-1)}-1$$;
  have h6 : (q : ℤ) ∣ p ^ (q - 1) - 1 := by
    sorry
  have h7 : (q : ℤ) ∣ p ^ (Nat.gcd p (q - 1)) - 1 := by
    sorry

-- but $$q \nmid p-1$$ because $$\frac{p^{p}-1}{p-1} \equiv 1(\bmod p-1)$$,
  have h8 : (p ^ p - 1) / (p - 1) ≡ 1 [ZMOD (p - 1)] := by
    sorry
  have h9 : ¬(q : ℤ) ∣ p - 1 := by
    sorry

-- so $$\operatorname{gcd}(p, q-1) \neq 1$$.
  have h10 : ¬(Nat.gcd p (q - 1) = 1) := by
    sorry
-- Hence $$\operatorname{gcd}(p, q-1)=p$$.
  have h11 : Nat.gcd p (q - 1) = p := by
    sorry

-- Now suppose $$q$$ is any prime divisor of $$\frac{p^{p}-1}{p-1}$$.
  sorry
-- Then $$q \mid \operatorname{gcd}\left(p^{k}-1, p^{p}-1\right)=$$ $$p^{\operatorname{gcd}(p, k)}-1$$,
-- which implies that $$\operatorname{gcd}(p, k) > 1$$, so $$p \mid k$$.
-- Consequently $$q \equiv 1$$ $$\left(\bmod p^{2}\right)$$.

-- However, the number $$\frac{p^{p}-1}{p-1}=p^{p-1}+\cdots+p+1$$ must have
-- at least one prime divisor that is not congruent to 1 modulo $$p^{2}$$.
-- Thus we arrived at a contradiction.
