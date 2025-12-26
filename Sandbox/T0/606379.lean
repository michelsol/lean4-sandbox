import Mathlib

open Finset Filter Topology

/-
Find all functions $f: \mathbb{Z}^{2} \rightarrow[0,1]$ such that for any integers $x$ and $y$,

  $ f(x, y)=\frac{f(x-1, y)+f(x, y-1)}{2} $
-/
theorem algebra_606379
    (f : ℤ → ℤ → ℝ)
    (hf : ∀ x y, 0 ≤ f x y ∧ f x y ≤ 1)
    : (∀ x y, f x y = (f (x - 1) y + f x (y - 1)) / 2) ↔ ∃ c : ℝ, ∀ x y, f x y = c := by
  constructor
-- We start by showing that constant functions work which is easy.
  swap
  . intro ⟨c, h1⟩
    intro x y
    simp only [h1]
    ring
-- We now show that functions satisying the functional equation are constant.
  . intro h1

-- We define $\binom{n}{k}=0$ when $k ∉ [0,n]$ for convenience.
    let choose (n k : ℤ) : ℤ := if 0 ≤ k ∧ k ≤ n then n.toNat.choose k.toNat else 0

-- First, iterating the functional equation relation to the $n$th level shows

-- that $ f(x, y)=\frac{1}{2^{n}} \sum_{i=0}^{n}\binom{n}{i} f(x-i, y-(n-i)) $
    have h2 (n : ℤ) (hn : n ≥ 0) x y : f x y = (1 / 2 ^ n) * ∑ i ∈ Icc 0 n, choose n i * f (x - i) (y - (n - i)) := by
      revert n x y
      apply Int.le_induction
      . intro x y
        simp [choose]
      . intro n hn ih
        sorry

-- In particular,
-- $ \begin{aligned} |f(x, y)-f(x-1, y+1)| & =\frac{1}{2^{n}}\left|\sum_{i=0}^{n+1} f(x-i, y-(n-i)) \cdot\left(\binom{n}{i}-\binom{n}{i-1}\right)\right| \ & \leq \frac{1}{2^{n}} \sum_{i=0}^{n+1}\left|\binom{n}{i}-\binom{n}{i-1}\right| \ & =\frac{1}{2^{n}} \cdot 2\binom{n}{\lfloor n / 2\rfloor} \end{aligned} $
    have h3 (n : ℤ) (hn : n ≥ 0) x y := calc
      |f x y - f (x - 1) (y + 1)| =
        |(1 / 2 ^ n) * ∑ i ∈ Icc 0 (n + 1), f (x - i) (y - (n - i)) * (choose n i - choose n (i - 1))| := by
        iterate 2 rw [h2 n hn]
        sorry
      _ =
        |1 / 2 ^ n| * |∑ i ∈ Icc 0 (n + 1), f (x - i) (y - (n - i)) * (choose n i - choose n (i - 1))| := by
        apply abs_mul
      _ =
        (1 / 2 ^ n) * |∑ i ∈ Icc 0 (n + 1), f (x - i) (y - (n - i)) * (choose n i - choose n (i - 1))| := by
        congr 1
        sorry
      _≤
        (1 / 2 ^ n) * ∑ i ∈ Icc 0 (n + 1), |f (x - i) (y - (n - i)) * (choose n i - choose n (i - 1))| := by
        gcongr
        apply abs_sum_le_sum_abs
      _ ≤ (1 / 2 ^ n) * ∑ i ∈ Icc 0 (n + 1), |choose n i - choose n (i - 1)| := by
        gcongr
        push_cast
        apply sum_le_sum
        intro i hi
        calc
          _ = |f (x - i) (y - (n - i))| * |choose n i - choose n (i - 1)| := by
            push_cast
            apply abs_mul
          _ ≤ 1 * |choose n i - choose n (i - 1)| := by
            gcongr
            specialize hf (x - i) (y - (n - i))
            sorry
          _ = _ := by simp
      _ = (1 / 2 ^ n) * 2 * choose n (n / 2) := by
        sorry

-- Since $ \binom{n}{\lfloor n / 2\rfloor}=o\left(2^{n}\right) $,

    have h4 : (λ n : ℕ ↦ (choose n (n / 2) : ℝ)) =o[atTop] (λ n : ℕ ↦ (2 ^ n : ℝ)) := by
      sorry

    replace h4 : Tendsto (λ n : ℕ ↦ ((1 / 2 ^ n) * 2 * choose n (n / 2) : ℝ)) atTop (𝓝 0) := by
      suffices Tendsto (λ n : ℕ ↦ 2 * ((choose n (n / 2) : ℝ) / 2 ^ n)) atTop (𝓝 0) from by
        convert this using 1
        ext n
        field_simp
      sorry

-- we have $\lim_{n → ∞} |f(x,y) - f(x-1,y+1)| = 0$ and , $f(x,y) = f(x-1,y+1)$ for all $x,y$.
    have h5 : ∀ x y, Tendsto (λ n : ℕ ↦ |f x y - f (x - 1) (y + 1)|) atTop (𝓝 0) := by
      intro x y
      have g3 : Tendsto (λ _ ↦ 0 : ℕ → ℝ) atTop (𝓝 0) := by
        sorry
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le g3 h4
      . intro n
        simp
      . intro n
        simpa using h3 n (by simp) x y

    have h6 x y : f x y = f (x - 1) (y + 1) := by
      specialize h5 x y
      simp at h5
      linarith


-- Furthermore $f(x,y+1)=\frac{f(x,y)+f(x-1,y+1)}{2}=f(x,y)$.
    have h7 x y : f x (y + 1) = f x y := calc
      _ = (f x y + f (x - 1) (y + 1)) / 2 := by
        rw [h1]
        ring_nf
      _ = _ := by
        rw [h6]
        ring

-- It follows that $f$ must be constant.
    use f 0 0
    sorry
