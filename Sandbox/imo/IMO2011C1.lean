import Mathlib

open Finset Function

/-
Let $n>0$ be an integer. We are given a balance and $n$ weights of weight $2^{0}, 2^{1}, \ldots, 2^{n-1}$. In a sequence of $n$ moves we place all weights on the balance. In the first move we choose a weight and put it on the left pan. In each of the following moves we choose one of the remaining weights and we add it either to the left or to the right pan. Compute the number of ways in which we can perform these $n$ moves in such a way that the right pan is never heavier than the left pan.  ## $\mathrm{C} 2$  Suppose that 1000 students are standing in a circle. Prove that there exists an integer $k$ with $100 \leq k \leq 300$ such that in this circle there exists a contiguous group of $2 k$ students, for which the first half contains the same number of girls as the second half.
-/

theorem combinatorics_24026
    (n : ℕ)
    (hn : n > 0) :
    {(p, w) : (ℕ → ℕ) × (ℕ → ℕ) |
      (∀ m ∈ Icc 1 n, p m = 0 ∨ p m = 1)
      ∧ (∀ m ∉ Icc 1 n, p m = 0)
      ∧ p 1 = 0
      ∧ (Set.BijOn w (Icc 1 n) ((Ico 0 n).image (2 ^ .)))
      ∧ (∀ m ∉ Icc 1 n, w m = 0)
      ∧ (∀ m ∈ Icc 1 n, ∑ m' ∈ Icc 1 n with m' ≤ m ∧ p m' = 0, w m' ≥ ∑ m' ∈ Icc 1 n with m' ≤ m ∧ p m' = 1, w m')
      }.ncard = ∏ k ∈ Icc 1 n, (2 * k - 1) := by
  revert n
  set s := λ (M W : Finset ℕ) ↦ {(p, w) : (ℕ → ℕ) × (ℕ → ℕ) |
      (∀ m ∈ M, p m = 0 ∨ p m = 1)
      ∧ (∀ m ∉ M, p m = 0)
      ∧ p 1 = 0
      ∧ (Set.BijOn w M W)
      ∧ (∀ m ∉ M, w m = 0)
      ∧ (∀ m ∈ M, ∑ m' ∈ M with m' ≤ m ∧ p m' = 0, w m' ≥ ∑ m' ∈ M with m' ≤ m ∧ p m' = 1, w m')
      }

  let label
      {α : Type _} [Zero α] [LinearOrder α]
      (s : Finset α) i0 k :=
    (s.sort (. ≤ .)).getD (k - i0) 0

  set f := λ n ↦ (s (Icc 1 n) ((Ico 0 n).image (2 ^ .))).ncard
  show ∀ n > 0, f n = _
  suffices ∀ n ≥ 1, ∀ M, #M = n → (s M ((Ico 0 n).image (2 ^ .))).ncard = ∏ k ∈ Icc 1 n, (2 * k - 1) from by intro n hn; exact this n hn (Icc 1 n) (by simp)

  apply Nat.strongRec
  intro n ih hn M hM
  let m := label M 1
  let W := ((Ico 0 n).image (2 ^ .))

  rcases (by omega : n = 1 ∨ n ≥ 2) with hn | hn
  . sorry

-- Assume $n \geq 2$. We claim $$ f(n)=(2 n-1) f(n-1) . $$
  have h1 : f n = (2 * n - 1) * f (n - 1) := by
-- Firstly, note that after the first move the left pan is always at least 1 heavier than the right one.
    have c1 p w (h : (p, w) ∈ s M W) : 2 ^ w (m 1) ≥ 1 := by
      sorry

    -- have c2 : ∃ k, w (m k) = 1 := by sorry

-- Hence, any valid way of placing the $n$ weights on the scale gives rise, by not considering weight 1 , to a valid way of placing the weights $2,2^{2}, \ldots, 2^{n-1}$.
    have c2 p w (h : (p, w) ∈ s M W) : (p, w) ∈ s (M \ {w.invFunOn M 1}) (W \ {1}) := by
      sorry

    have c3 p w (h : (p, w) ∈ s M W) : w.invFunOn M 1 ∈ M := by
      sorry

    have c4 p w (h : (p, w) ∈ s M W) (h' : w.invFunOn M 1 ≠ m 1) : p (w.invFunOn M 1) ∈ ({0, 1} : Finset ℕ) := by
      sorry

    sorry

-- If we divide the weight of each weight by 2 , the answer does not change. So these $n-1$ weights can be placed on the scale in $f(n-1)$ valid ways. Now we look at weight 1 . If it is put on the scale in the first move, then it has to be placed on the left side, otherwise it can be placed either on the left or on the right side, because after the first move the difference between the weights on the left pan and the weights on the right pan is at least 2 . Hence, there are exactly $2 n-1$ different ways of inserting weight 1 in each of the $f(n-1)$ valid sequences for the $n-1$ weights in order to get a valid sequence for the $n$ weights. This proves the claim.


-- Since $f(1)=1$, by induction we obtain for all positive integers $n$ $$ f(n)=(2 n-1) ! !=1 \cdot 3 \cdot 5 \cdot \ldots \cdot(2 n-1) $$
  have h2 : f 1 = 1 := by
    sorry

  -- apply Nat.le_induction
  -- . simpa using h2
  -- . intro n hn ih
  --   simp at hn
  --   specialize h1 (n + 1) (by omega)
  --   simp [prod_Icc_succ_top, h1, ih, mul_comm]
  sorry
