import Mathlib

open Finset

/-
Is it possible to find 100 positive integers not exceeding 25,000 such that all pairwise sums of them are different?
-/

theorem number_theory_25086 :
    -- Yes.
    ∃ (a : ℕ → ℕ) (I : Finset _) (_ : #I = 100)
    (_ : ∀ n ∈ I, a n > 0) (_ : ∀ n ∈ I, a n ≤ 25000),
      ∀ i ∈ I, ∀ j ∈ I, ∀ i' ∈ I, ∀ j' ∈ I,
        ({i, j} : Set _) ≠ {i', j'} → a i + a j ≠ a i' + a j' := by
  -- The desired result is an immediate consequence of the following fact applied on $p=101$.
  -- Lemma. For any odd prime number $p$, there exist $p$ nonnegative integers less than $2 p^{2}$ with all pairwise sums mutually distinct.
  suffices h1 : ∀ p, p.Prime → ∃ (a : ℕ → ℕ) (_ : ∀ n ∈ Icc 1 p, a n < 2 * p ^ 2), ∀ i ∈ Icc 1 p, ∀ j ∈ Icc 1 p, ∀ i' ∈ Icc 1 p, ∀ j' ∈ Icc 1 p,
        ({i, j} : Set ℕ) ≠ {i', j'} → a i + a j ≠ a i' + a j' from by
    obtain ⟨a, h2, h3⟩ := h1 101 (by decide)
    -- If there are no zeros
    sorry

  sorry
-- Proof of the lemma. We claim that the numbers $a_{n}=2 n p+\left(n^{2}\right)$ have the desired property, where $(x)$ denotes the remainder of $x$ upon division by $p$. Suppose that $a_{k}+a_{l}=a_{m}+a_{n}$. By the construction of $a_{i}$, we have $2 p(k+l) \leq a_{k}+a_{l}&lt;2 p(k+l+1)$. Hence we must have $k+l=m+n$, and therefore also $\left(k^{2}\right)+\left(l^{2}\right)=\left(m^{2}\right)+\left(n^{2}\right)$. Thus $$ k+l \equiv m+n \quad \text { and } \quad k^{2}+l^{2} \equiv m^{2}+n^{2} \quad(\bmod p) . $$ But then it holds that $(k-l)^{2}=2\left(k^{2}+l^{2}\right)-(k+l)^{2} \equiv(m-n)^{2}(\bmod$ $p)$, so $k-l \equiv \pm(m-n)$, which leads to $(k, l)=(m, n)$. This proves the lemma.
