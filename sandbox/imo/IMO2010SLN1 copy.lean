import Mathlib

open Finset

/-
Find the least positive integer $n$ for which there exists a set
$\left\{s_{1}, s_{2}, \ldots, s_{n}\right\}$
consisting of $n$ distinct positive integers such that
$$ \left(1-\frac{1}{s_{1}}\right)\left(1-\frac{1}{s_{2}}\right)
\ldots\left(1-\frac{1}{s_{n}}\right)=\frac{51}{2010} $$
-/

set_option maxHeartbeats 1000000
theorem number_theory_23989 :
    IsLeast { n : ℕ | ∃ (s : ℕ → ℕ) (_ : ∀ i ∈ Icc 1 n, s i ≥ 1) (_ : Set.InjOn s (Set.Icc 1 n)),
      ∏ i ∈ Icc 1 n, (1 - 1 / s i : ℚ) = (51 / 2010 : ℚ) } 39 := by
  constructor
  . use λ
      | 0  => 0
      | 1  =>  2 | 2  =>  3 | 3  =>  4 | 4  =>  5 | 5  =>  6
      | 6  =>  7 | 7  =>  8 | 8  =>  9 | 9  => 10 | 10 => 11
      | 11 => 12 | 12 => 13 | 13 => 14 | 14 => 15 | 15 => 16
      | 16 => 17 | 17 => 18 | 18 => 19 | 19 => 20 | 20 => 21
      | 21 => 22 | 22 => 23 | 23 => 24 | 24 => 25 | 25 => 26
      | 26 => 27 | 27 => 28 | 28 => 29 | 29 => 30 | 30 => 31
      | 31 => 32 | 32 => 33 | 33 => 35 | 34 => 36 | 35 => 37
      | 36 => 38 | 37 => 39 | 38 => 40 | 39 => 67 | _ + 40 => 0
    use by decide
    use by simp [Set.InjOn]; decide
    have : Icc 1 39 =
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
      21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39}
    := by ext x; simp; omega
    -- have : Icc 1 39 = {1, 2} := sorry
    -- norm_num [this]
    -- decide
    sorry
  . dsimp [lowerBounds]
    sorry
