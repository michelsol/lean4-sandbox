import Mathlib

open Finset

/- Determine whether there exists an infinite sequence of nonzero digits $a_{1}, a_{2}, a_{3}, \ldots$
and a positive integer $N$ such that for every integer $k>N$,
the number $\overline{a_{k} a_{k-1} \ldots a_{1}}$ is a perfect square.
-/
theorem number_theory_24377 :
    ¬∃ (a : ℕ → ℕ)
      (ha1 : ∀ k ≥ 1, a k >= 1)
      (ha2 : ∀ k ≥ 1, a k <= 9)
      (N : ℕ),
      ∀ k > N, ∃ x : ℕ, ∑ i ∈ Icc 1 k, a i * 10 ^ (i - 1) = x * x := by
  by_contra! h
-- Assume that $a_{1}, a_{2}, a_{3}, \ldots$ is such a sequence.
  obtain ⟨a, ha1, ha2, N, ha3⟩ := h

-- For each positive integer $k$, let $y_{k}=$ $\overline{a_{k} a_{k-1} \ldots a_{1}}$.
  let y k := ∑ i ∈ Icc 1 k, a i * 10 ^ (i - 1)
-- By the assumption, for each $k > N$ there exists a positive integer $x_{k}$ such that $y_{k}=x_{k}^{2}$.
  replace ha3 : ∀ k > N, ∃ x : ℕ, y k = x * x := ha3
  choose! x hx using ha3

-- For every $n$, let $5^{\gamma_{n}}$ be the greatest power of 5 dividing $x_{n}$.
  let γ n := multiplicity 5 (x n)

-- I. Let us show first that $2 \gamma_{n} \geqslant n$ for every positive integer $n > N$.
  have H1 (n : ℕ) (hn : n > N) : 2 * γ n ≥ n := by
-- Assume, to the contrary, that there exists a positive integer $n > N$ such that $2 \gamma_{n} < n$,
    by_contra! H1

-- Consider $k ≥ n$
-- This yields $ y_{k+1}=\overline{a_{k+1} a_{k} \ldots a_{1}}=10^{k} a_{k+1}+\overline{a_{k} a_{k-1} \ldots a_{1}}=10^{k} a_{k+1}+y_{k}=5^{2 \gamma_{k}}\left(2^{k} 5^{k-2 \gamma_{k}} a_{k+1}+\frac{y_{k}}{5^{2 \gamma_{k}}}\right) . $
-- For $k ≥ n$
    have h1 k (hk : k ≥ n) : y (k + 1) = 5 ^ (2 * γ k) * (2 ^ k * 5 ^ (k - 2 * γ k) * a (k + 1) + y k / 5 ^ (2 * γ k)) := by
      calc
        _ = ∑ i ∈ Icc 1 (k + 1), a i * 10 ^ (i - 1) := by sorry
        _ = 10 ^ k * a (k + 1) + ∑ i ∈ Icc 1 k, a i * 10 ^ (i - 1) := by sorry
        _ = 10 ^ k * a (k + 1) + y k := by rfl
        _ = _ := by sorry

-- Since $5 \nmid y_{k} / 5^{2 \gamma_{k}}$, we obtain $\gamma_{k+1}=\gamma_{k} < k < k+1$.
    have h2 k (hk : k ≥ n) : γ (k + 1) = γ k := by
      sorry

-- By the same arguments we obtain that $\gamma_{n}=\gamma_{n+1}=\gamma_{n+2}=\ldots$.
    have h3 k (hk : k ≥ n) : γ k = γ n := by
      revert k
      apply Nat.le_induction
      . rfl
      . intro k hk h; rw [h2 k hk, h]

-- Denote this common value by $\gamma$.
    let Γ := γ n

-- Now, for each $k \geqslant n$ we have $ \left(x_{k+1}-x_{k}\right)\left(x_{k+1}+x_{k}\right)=x_{k+1}^{2}-x_{k}^{2}=y_{k+1}-y_{k}=a_{k+1} \cdot 10^{k} . $
    have h4 k (hk : k ≥ n) : (x (k + 1) - x k : ℤ) * (x (k + 1) + x k : ℤ) = a (k + 1) * 10 ^ k := by
      calc
        _ = (x (k + 1) : ℤ) ^ 2 - (x k : ℤ) ^ 2 := by ring_nf
        _ = y (k + 1) - y k := by
          rw [hx k (by omega), hx (k + 1) (by omega)]
          ring_nf
          norm_cast
        _ = a (k + 1) * 10 ^ k := by sorry

-- One of the numbers $x_{k+1}-x_{k}$ and $x_{k+1}+x_{k}$ is not divisible by $5^{\gamma+1}$
    have h5 k (hk : k ≥ n) : ¬(5 ^ (Γ + 1) ∣ (x (k + 1) - x k : ℤ)) ∨ ¬(5 ^ (Γ + 1) ∣ (x (k + 1) + x k : ℤ)) := by
-- since otherwise one would have $5^{\gamma+1} \mid\left(\left(x_{k+1}-x_{k}\right)+\left(x_{k+1}+x_{k}\right)\right)=2 x_{k+1}$.
      sorry

-- On the other hand, we have $5^{k} \mid\left(x_{k+1}-x_{k}\right)\left(x_{k+1}+x_{k}\right)$, so $5^{k-\gamma}$ divides one of these two factors.
    have h6 k (hk : k ≥ n) : 5 ^ (k - Γ) ∣ (x (k + 1) - x k : ℤ) ∨ 5 ^ (k - Γ) ∣ (x (k + 1) + x k : ℤ) := by
      sorry

-- Thus we get $ 5^{k-\gamma} \leqslant \max \left\{x_{k+1}-x_{k}, x_{k+1}+x_{k}\right\} < 2 x_{k+1}=2 \sqrt{y_{k+1}} < 2 \cdot 10^{(k+1) / 2} $
    have h7 k (hk : k ≥ n) : 5 ^ (k - Γ) < 2 * 10 ^ ((k + 1) / 2) := by
      zify
      calc
      _ ≤ (x (k + 1) - x k : ℤ) ⊔ (x (k + 1) + x k) := sorry
      _ < (2 * x (k + 1)) := sorry
      _ = 2 * Int.sqrt (y (k + 1)) := by sorry
      _ < _ := sorry

-- which implies $5^{2 k} < 4 \cdot 5^{2 \gamma} \cdot 10^{k+1}$, or $(5 / 2)^{k} < 40 \cdot 5^{2 \gamma}$.
    have h8 k (hk : k ≥ n) : (5 / 2 : ℚ) ^ k < 40 * 5 ^ (2 * Γ) := by
      sorry

-- The last inequality is clearly false for sufficiently large values of $k$.
    sorry
-- This contradiction shows that $2 \gamma_{n} \geqslant n$ for all $n > N$.


-- II. Consider now any integer $k > \max \{N / 2,2\}$. We will show a contradiction.
  obtain ⟨k, hk⟩ : ∃ k, k > (N / 2) ⊔ 2 := by use ((N / 2) ⊔ 2 + 1); omega

-- Since $2 \gamma_{2 k+1} \geqslant 2 k+1$ and $2 \gamma_{2 k+2} \geqslant 2 k+2$, we have $\gamma_{2 k+1} \geqslant k+1$ and $\gamma_{2 k+2} \geqslant k+1$.
  have h2 : γ (2 * k + 1) ≥ k + 1 := sorry
  have h2' : γ (2 * k + 2) ≥ k + 1 := sorry

-- So, from $y_{2 k+2}=a_{2 k+2} \cdot 10^{2 k+1}+y_{2 k+1}$ we obtain $5^{2 k+2} \mid y_{2 k+2}-y_{2 k+1}=a_{2 k+2} \cdot 10^{2 k+1}$
  have h3 : 5 ^ (2 * k + 2) ∣ (a (2 * (k + 2)) * 10 ^ (2 * k + 1) : ℤ) := by
    sorry

-- and thus $5 \mid a_{2 k+2}$, which implies $a_{2 k+2}=5$.
  have h4 : a (2 * (k + 2)) = 5 := by
    specialize ha1 (2 * (k + 2)) (by omega)
    specialize ha2 (2 * (k + 2)) (by omega)
    have c1 : 5 ∣ (a (2 * (k + 2)) : ℤ) := by
      sorry
    omega

-- Therefore, $ \left(x_{2 k+2}-x_{2 k+1}\right)\left(x_{2 k+2}+x_{2 k+1}\right)=x_{2 k+2}^{2}-x_{2 k+1}^{2}=y_{2 k+2}-y_{2 k+1}=5 \cdot 10^{2 k+1}=2^{2 k+1} \cdot 5^{2 k+2} . $
  have h5 :
      (x (2 * (k + 2)) - x (2 * (k + 1)) : ℤ) * (x (2 * (k + 2)) + x (2 * (k + 1))) =
        2 ^ (2 * k + 1) * 5 ^ (2 * k + 2) := by
    calc
      _ = (x (2 * (k + 2)) : ℤ) ^ 2 - (x (2 * (k + 1)) : ℤ) ^ 2 := by ring_nf
      _ = y (2 * (k + 2)) - y (2 * (k + 1)) := by
        sorry
      _ = 5 * 10 ^ (2 * k + 1) := by
        sorry
      _ = _ := by
        sorry

-- Setting $A_{k}=x_{2 k+2} / 5^{k+1}$ and $B_{k}=x_{2 k+1} / 5^{k+1}$, which are integers,
  let A k := x (2 * (k + 2)) / 5 ^ (k + 1)
  let B k := x (2 * (k + 1)) / 5 ^ (k + 1)

-- we obtain $ \left(A_{k}-B_{k}\right)\left(A_{k}+B_{k}\right)=2^{2 k+1} . $
  have h6 :
      (A k - B k : ℤ) * (A k + B k) = 2 ^ (2 * k + 1) := by
    sorry

-- Both $A_{k}$ and $B_{k}$ are odd, since otherwise $y_{2 k+2}$ or $y_{2 k+1}$ would be a multiple of 10
-- which is false by $a_{1} \neq 0$;
  have h7 : A k % 2 = 1 ∧ B k % 2 = 1 := by
    sorry

-- so one of the numbers $A_{k}-B_{k}$ and $A_{k}+B_{k}$ is not divisible by 4 .
  have h8 :
      ¬(4 ∣ (A k - B k : ℤ)) ∨ ¬(4 ∣ (A k + B k : ℤ)) := by
    omega

-- Therefore (1) yields $A_{k}-B_{k}=2$
  have h9 : (A k - B k : ℤ) = 2 := by
    sorry

-- and $A_{k}+B_{k}=2^{2 k}$,
  have h9' : (A k + B k : ℤ) = 2 ^ (2 * k) := by
    sorry

-- hence $A_{k}=2^{2 k-1}+1$
  have h10 : A k = 2 ^ (2 * k - 1) + 1 := by
    sorry

-- and thus $ x_{2 k+2}=5^{k+1} A_{k}=10^{k+1} \cdot 2^{k-2}+5^{k+1} > 10^{k+1}, $ since $k \geqslant 2$.
  have h11 :
      x (2 * (k + 2)) > 10 ^ (k + 1) := by
    sorry

-- This implies that $y_{2 k+2} > 10^{2 k+2}$
  have h12 :
      y (2 * (k + 2)) > 10 ^ (2 * k + 2) := by
    sorry

-- which contradicts the fact that $y_{2 k+2}$ contains $2 k+2$ digits.
  have h13 :
      y (2 * (k + 2)) < 10 ^ (2 * k + 2) := by
    sorry

  sorry
-- The desired result follows.
