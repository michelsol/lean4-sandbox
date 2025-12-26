import Mathlib

open Finset

/-
Find all positive integers $a_1,  a_2, ..., a_n$ such that
$$\dfrac{99}{100}=\dfrac{a_0}{a_1}+\dfrac{a_1}{a_2}+...+\dfrac{a_{n-1}}{a_n}$$
where $a_0=1$ and $(a_{k+1}-1)a_{k-1} \ge a_k^2(a_k-1)$ for $k=1,2,...,n-1$.
-/

theorem algebra_25092
    (n : ℕ)
    (n_ge : n ≥ 1)
    (a : ℕ → ℤ)
    (a0_eq : a 0 = 1)
    (a_pos : ∀ i ∈ Icc 0 n, a i ≥ 1)
    (hsum : ∑ k ∈ Ico 0 n, (a k / a (k + 1) : ℝ) = (99 / 100 : ℝ))
    (hineq : ∀ k ∈ Ico 1 n, (a (k + 1) - 1) * a (k - 1) ≥ a k ^ 2 * (a k - 1))
    : n = 4 ∧ a 1 = 2 ∧ a 2 = 5 ∧ a 3 = 56 ∧ a 4 = 78400 := by
/-
Let $a_{1}, a_{2}, \ldots, a_{n}$ satisfy the conditions of the problem.
Then $a_{k}>a_{k-1}$, and hence $a_{k} \geq 2$ for $k=1, \ldots, n$.
-/
  have h1 : ∀ k ∈ Ico 0 n, a (k + 1) > a k := by
    -- all $a_k / a_{k+1}$ are < 1 otherwise the sum would be ≥ 1 as they are all positive.
    have h1 : ∀ k ∈ Ico 0 n, (a k / a (k + 1) : ℝ) < 1 := by
      by_contra h
      push_neg at h
      sorry
    intro k hk
    specialize h1 k hk
    specialize a_pos (k + 1) (by simp at hk ⊢; omega)
    replace h1 := (div_lt_iff (by norm_cast)).mp h1
    norm_cast at h1
    ring_nf at h1 ⊢
    assumption

  have h2 : ∀ k ∈ Icc 1 n, a k ≥ 2 := by
    simp only [mem_Icc, and_imp]
    apply Nat.le_induction
    . intro hn
      specialize h1 0 (by simp; omega)
      ring_nf at h1; omega
    . intro k hk ih hkn
      specialize ih (by omega)
      specialize h1 k (by simp; omega)
      omega
/-
The inequality $\left(a_{k+1}-1\right) a_{k-1} \geq$ $a_{k}^{2}\left(a_{k}-1\right)$
can be rewritten as
$$ \frac{a_{k-1}}{a_{k}}+\frac{a_{k}}{a_{k+1}-1} \leq \frac{a_{k-1}}{a_{k}-1} . $$
-/
  have h3 : ∀ k ∈ Ico 1 n,
      (a (k - 1) / a k : ℝ) + (a k / (a (k + 1) - 1) : ℝ) ≤ (a (k - 1) / (a k - 1) : ℝ) := by
    intro k hk
    specialize hineq k hk
    suffices (a (k - 1) / a k : ℝ) + (a k / (a (k + 1) - 1) : ℝ) - (a (k - 1) / (a k - 1) : ℝ) ≤ 0 from by
      linarith
    have : (a k : ℝ) > 0 := sorry
    have : (a k - 1 : ℝ) > 0 := sorry
    have : (a (k + 1) - 1 : ℝ) > 0 := sorry
    sorry
/-
Summing these inequalities for $k=i+1, \ldots, n-1$ and using the obvious inequality
 $\frac{a_{n-1}}{a_{n}}<\frac{a_{n-1}}{a_{n}-1}$, we obtain
  $\frac{a_{i}}{a_{i+1}}+\cdots+\frac{a_{n-1}}{a_{n}}<\frac{a_{i}}{a_{i+1}-1}$.
-/
  have h3' : (a (n - 1) / a n : ℝ) < (a (n - 1) / (a n - 1) : ℝ) := sorry
  have h4 : ∀ i ∈ Ico 0 n,
      ∑ k ∈ Icc (i+1) n, (a (k - 1) / a k : ℝ) < (a i / (a (i + 1) - 1) : ℝ) := by
    intro i hi
    replace h3 : ∑ k ∈ Ico (i+1) n, ((a (k - 1) / a k : ℝ) + (a k / (a (k + 1) - 1) : ℝ)) ≤
      ∑ k ∈ Ico (i+1) n, (a (k - 1) / (a k - 1) : ℝ) := sorry
    replace h3 : ∑ k ∈ Ico (i+1) n, (a (k - 1) / a k : ℝ)
        + ∑ k ∈ Ico (i+1) n, (a k / (a (k + 1) - 1) : ℝ) ≤
      ∑ k ∈ Ico (i+1) n, (a (k - 1) / (a k - 1) : ℝ) := sorry
    replace h3 : ∑ k ∈ Ico (i+1) n, (a (k - 1) / a k : ℝ) ≤
      ∑ k ∈ Ico (i+1) n, (a (k - 1) / (a k - 1) : ℝ)
      - ∑ k ∈ Ico (i+1) n, (a k / (a (k + 1) - 1) : ℝ) := by linarith
    replace h3 : ∑ k ∈ Ico (i+1) n, (a (k - 1) / a k : ℝ) ≤
      ∑ k ∈ Ico i (n-1), (a k / (a (k + 1) - 1) : ℝ)
      - ∑ k ∈ Ico (i+1) n, (a k / (a (k + 1) - 1) : ℝ) := sorry
    replace h3 : ∑ k ∈ Ico (i+1) n, (a (k - 1) / a k : ℝ) ≤
      (a i / (a (i + 1) - 1) : ℝ) - (a (n - 1) / (a n - 1) : ℝ) := sorry
    replace h3 : ∑ k ∈ Icc (i+1) n, (a (k - 1) / a k : ℝ) - (a (n - 1) / a n : ℝ) ≤
      (a i / (a (i + 1) - 1) : ℝ) - (a (n - 1) / (a n - 1) : ℝ) := sorry
    linarith
/-
Therefore
$$ \frac{a_{i}}{a_{i+1}} \leq \frac{99}{100}-\frac{a_{0}}{a_{1}}-\cdots-
\frac{a_{i-1}}{a_{i}}<\frac{a_{i}}{a_{i+1}-1} \quad \text { for } i=1,2, \ldots, n-1 $$
-/
  have h5l : ∀ i ∈ Ico 0 n, (a i / a (i + 1) : ℝ) ≤ (99 / 100 : ℝ) - ∑ k ∈ Ico 0 i, (a k / a (k + 1)) := by
    intro i hi
    have h5 : ∑ k ∈ Icc 0 i, (a k / a (k + 1)) ≤ (99 / 100 : ℝ) := sorry
    replace h5 : ∑ k ∈ Ico 0 i, (a k / a (k + 1)) + (a i / a (i + 1) : ℝ) ≤ (99 / 100 : ℝ) := sorry
    linarith

  have h5r : ∀ i ∈ Ico 0 n,
      (99 / 100 : ℝ) - ∑ k ∈ Ico 0 i, (a k / a (k + 1) : ℝ) < (a i / (a (i + 1) - 1) : ℝ) := by
    intro i hi
    have h5 : ∑ k ∈ Ico i n, (a k / a (k + 1) : ℝ) < (a i / (a (i + 1) - 1) : ℝ) := by
      specialize h4 i (by simp at hi ⊢; omega)
      suffices ∑ k ∈ Icc (i + 1) n, (a (k - 1) / a k : ℝ) = ∑ k ∈ Ico i n, (a k / a (k + 1) : ℝ)
      from by linarith
      sorry
    have h5 : ∑ k ∈ Ico 0 n, (a k / a (k + 1) : ℝ) - ∑ k ∈ Ico 0 i, (a k / a (k + 1) : ℝ) < (a i / (a (i + 1) - 1) : ℝ) := by
      sorry
    simpa [←hsum] using h5

  let f i : ℝ := 1 / ((1 / a i : ℝ) * ((99 / 100 : ℝ) - ∑ k ∈ Ico 0 i, (a k / a (k + 1) : ℝ)))

  have h6l : ∀ i ∈ Ico 0 n, (a (i + 1) : ℝ) - 1 < f i := by
    intro i hi
    have := h5r i hi
    replace := (1 / a i : ℝ) * ((99 / 100 : ℝ) - ∑ k ∈ Ico 0 i, (a k / a (k + 1) : ℝ)) < (1 / (a (i + 1) - 1) : ℝ)
    sorry

  have h6r : ∀ i ∈ Ico 0 n, f i ≤ (a (i + 1) : ℝ) := by
    intro i hi
    have := h5l i hi
    replace : (1 / a (i + 1) : ℝ) ≤ (1 / a i : ℝ) * ((99 / 100 : ℝ) - ∑ k ∈ Ico 0 i, (a k / a (k + 1))) := sorry
    sorry
/-
Consequently, given $a_{0}, a_{1}, \ldots, a_{i}$,
there is at most one possibility for $a_{i+1}$.
In our case, (1) yields $a_{1}=2, a_{2}=5, a_{3}=56, a_{4}=78400$.
$n = 1, 2, 3$ would not satisfy the conditions of the problem, $n = 4$ works,
and $n$ cannot be greater than 5 as we would have $a_5 = 0$.
so $n = 4$ and we have a unique solution.
-/
  have h6 : ∀ i ∈ Ico 0 n, a (i + 1) = -⌊-f i⌋ := by
    sorry

  have a1_eq : a 1 = 2 := by
    specialize h6 0 (by simp; omega)
    norm_num [f, a0_eq, range] at h6
    assumption

  replace n_ge : n ≥ 2 := by
    suffices n ≠ 1 from by omega
    intro hn
    simp [range, f, *] at hsum
    norm_num at hsum

  have a2_eq : a 2 = 5 := by
    specialize h6 1 (by simp; omega)
    norm_num [f, a0_eq, a1_eq, range] at h6
    assumption

  replace n_ge : n ≥ 3 := by
    suffices n ≠ 2 from by omega
    intro hn
    simp [range, f, *] at hsum
    norm_num at hsum

  have a3_eq : a 3 = 56 := by
    specialize h6 2 (by simp; omega)
    norm_num [f, a0_eq, a1_eq, a2_eq, range] at h6
    assumption

  replace n_ge : n ≥ 4 := by
    suffices n ≠ 3 from by omega
    intro hn
    simp [range, f, *] at hsum
    norm_num at hsum

  have a4_eq : a 4 = 78400 := by
    specialize h6 3 (by simp; omega)
    norm_num [f, a0_eq, a1_eq, a2_eq, a3_eq, range] at h6
    assumption

  have n_eq_4 : n = 4 := by
    suffices n < 5 from by omega
    by_contra hn
    specialize h6 4 (by simp; omega)
    norm_num [f, a0_eq, a1_eq, a2_eq, a3_eq, a4_eq, range] at h6
    specialize a_pos 5 (by simp at hn ⊢; omega)
    omega

  omega
