import Mathlib

open Finset Real

/-
Let $n \geqslant 3$ be an integer, and let $x_{1}, x_{2}, \ldots, x_{n}$ be real numbers in the interval $[0,1]$.
Let $s=x_{1}+x_{2}+\ldots+x_{n}$, and assume that $s \geqslant 3$.
Prove that there exist integers $i$ and $j$ with $1 \leqslant i < j \leqslant n$ such that  $ 2^{j-i} x_{i} x_{j}>2^{s-3} $
-/

theorem algebra_24299
    (n : ℤ) (hn : n ≥ 3)
    (x : ℤ → ℝ) (hx : ∀ k ∈ Icc 1 n, 0 ≤ x k ∧ x k ≤ 1)
    (s : ℝ) (hs1 : s = ∑ k ∈ Icc 1 n, x k) (hs2 : s ≥ 3) :
    ∃ i ∈ Icc 1 n, ∃ j ∈ Icc 1 n, 2 ^ (j - i) * x i * x j > 2 ^ (s - 3) := by

-- Let $1 \leqslant a < b \leqslant n$ be such that $2^{b-a} x_{a} x_{b}$ is maximal.
  let Y := (Icc 1 n ×ˢ Icc 1 n).image λ (a, b) ↦ 2 ^ (b - a) * x a * x b
  have hY : Y.Nonempty := by simp [Y]; omega
  obtain ⟨⟨a, b⟩, hab, h1⟩ := mem_image.mp (Y.isGreatest_max' hY).left
  replace h1 : 2 ^ (b - a) * x a * x b = Y.max' hY := h1
  replace h1 : ∀ a' ∈ Icc 1 n, ∀ b' ∈ Icc 1 n, 2 ^ (b' - a') * x a' * x b' ≤ 2 ^ (b - a) * x a * x b := by
    rw [h1]
    intro a' ha' b' hb'
    have c1 : ∀ (l : ℝ) (a b : ℤ), (a, b) ∈ ((Icc 1 n) ×ˢ (Icc 1 n)).toSet → 2 ^ (b - a) * x a * x b = l → l ≤ Y.max' hY := by
      simpa [upperBounds, Y] using (Y.isGreatest_max' hY).right
    exact c1 (2 ^ (b' - a') * x a' * x b') a' b' (by simp at ha' hb' ⊢; tauto) rfl
  clear! Y
  have ha : 1 ≤ a ∧ a ≤ n := by simp at hab; omega
  have hb : 1 ≤ b ∧ b ≤ n := by simp at hab; omega

-- This choice of $a$ and $b$ implies that $x_{a+t} \leqslant 2^{t} x_{a}$ for all $1-a \leqslant t \leqslant b-a-1$,
  have h2 t (ht : 1 - a ≤ t ∧ t ≤ b - a - 1) : x (a + t) ≤ 2 ^ t * x a := by
    sorry

-- and similarly $x_{b-t} \leqslant 2^{t} x_{b}$ for all $b-n \leqslant t \leqslant b-a+1$.
  have h3 t (ht : b - n ≤ t ∧ t ≤ b - a + 1) : x (b - t) ≤ 2 ^ t * x b := by
    sorry

-- Now, suppose that $x_{a} \in\left(\frac{1}{2^{u+1}}, \frac{1}{2^{u}}\right]$
  have ⟨u, h4⟩ : ∃ u : ℤ, 1 / 2 ^ (u + 1) < x a ∧ x a ≤ 1 / 2 ^ u := by
    sorry
-- u is nonnegative, since $x_{a} ∈ \left(0, 1\right]$.
  have hu : u ≥ 0 := sorry

-- and $x_{b} \in\left(\frac{1}{2^{v+1}}, \frac{1}{2^{v}}\right]$,
  have ⟨v, h5⟩ : ∃ v : ℤ, 1 / 2 ^ (v + 1) < x b ∧ x b ≤ 1 / 2 ^ v := by
    sorry
-- v is nonnegative, since $x_{b} ∈ \left(0, 1\right]$.
  have hv : v ≥ 0 := sorry

-- and write $x_{a}=2^{-\alpha}, x_{b}=2^{-\beta}$.
  have ⟨α, h6⟩ : ∃ α : ℝ, x a = 2 ^ (-α) := by
    use -logb 2 (x a)
    rw [neg_neg]
    rw [rpow_logb]
    . norm_num
    . norm_num
    . sorry

  have ⟨β, h7⟩ : ∃ β : ℝ, x b = 2 ^ (-β) := by
    use -logb 2 (x b)
    rw [neg_neg]
    rw [rpow_logb]
    . norm_num
    . norm_num
    . sorry

-- Then $ \sum_{i=1}^{a+u-1} x_{i} \leqslant 2^{u} x_{a}\left(\frac{1}{2}+\frac{1}{4}+\ldots+\frac{1}{2^{a+u-1}}\right) < 2^{u} x_{a} \leqslant 1 $
  have h8 : ∑ i ∈ Icc 1 (a + u - 1), x i < 2 ^ u * x a := calc
      _ ≤ 2 ^ u * x a * ∑ i ∈ Icc 1 (a + u - 1), 1 / 2 ^ i := by
        sorry
      _ < 2 ^ u * x a := by
        sorry
  have h8' : ∑ i ∈ Icc 1 (a + u - 1), x i < 1 := calc
      _ < 2 ^ u * x a := h8
      _ ≤ 1 := by
        sorry

-- and similarly, $ \sum_{i=b-v+1}^{n} x_{i} \leqslant 2^{v} x_{b}\left(\frac{1}{2}+\frac{1}{4}+\ldots+\frac{1}{2^{n-b+v}}\right) < 2^{v} x_{b} \leqslant 1 $
  have h9 : ∑ i ∈ Icc (b - v + 1) n, x i < 2 ^ v * x b := calc
      _ ≤ 2 ^ v * x b * ∑ i ∈ Icc 1 (n - b + v), 1 / 2 ^ i := by
        sorry
      _ < 2 ^ v * x b := by
        sorry
  have h9' : ∑ i ∈ Icc (b - v + 1) n, x i < 1 := calc
      _ < 2 ^ v * x b := h9
      _ ≤ 1 := by
        sorry

-- In other words, the sum of the $x_{i}$ 's for $i$ outside
-- of the interval $[a+u, b-v]$ is strictly less than 2.
  have h10 : ∑ i ∈ Icc 1 n \ Icc (a + u) (b - v), x i < 2 := by
    sorry

-- Since the total sum is at least 3 ,
-- and each term is at most 1 ,
-- it follows that this interval must have at least two integers.
-- i.e., $a+u < b-v$.
  have h11 : a + u < b - v := by
    sorry

-- Thus, by bounding the sum of the $x_{i}$ for $i \in[1, a+u] \cup[b-v, n]$ like above,
  have h12 : ∑ i ∈ Icc 1 (a + u), x i < 2 ^ (u + 1) * x a := by
    sorry

  have h13 : ∑ i ∈ Icc (b - v) n, x i < 2 ^ (v + 1) * x b := by
    sorry

-- and trivially bounding each $x_{i} \in(a+u, b-v)$ by 1 ,
  have h14 : ∑ i ∈ Ioo (a + u) (b - v), x i ≤ (b - v) - (a + u) - 1 := by
    sorry

-- we obtain $ s < 2^{u+1} x_{a}+2^{v+1} x_{b}+((b-v)-(a+u)-1)=b-a+\left(2^{u+1-\alpha}+2^{v+1-\beta}-(u+v+1)\right) . $
  have h15 : s < b - a + (2 ^ (u + 1 - α) + 2 ^ (v + 1 - β) - (u + v + 1)) := by
    calc
      _ = _ := hs1
      _ = (∑ i ∈ Icc 1 (a + u), x i) + (∑ i ∈ Ioo (a + u) (b - v), x i) + (∑ i ∈ Icc (b - v) n, x i) := by
        have c1 : Icc 1 n = Icc 1 (a + u) ∪ Ioo (a + u) (b - v) ∪ Icc (b - v) n := by
          ext k; simp; omega
        rw [c1]
        iterate 2 rw [sum_union]
        . sorry
        . sorry
      _ < 2 ^ (u + 1) * x a + 2 ^ (v + 1) * x b + ((b - v) - (a + u) - 1) := by linarith
      _ = _ := by
        sorry

-- Now recall $\alpha \in(u, u+1]$ and $\beta \in(v, v+1]$,
  have h16 : α > u ∧ α ≤ u + 1 := by sorry

  have h17 : β > v ∧ β ≤ v + 1 := by sorry

-- so applying Bernoulli's inequality
-- yields $s - (b - a) ≤ \left.2^{u+1-\alpha}+2^{v+1-\beta}-u-v-1 \leqslant(1+(u+1-\alpha))\right)+(1+(v+1-\beta))-u-v-1=3-\alpha-\beta$.
  have h18 : s - (b - a) < 3 - α - β := by
    calc
      _ < (2 : ℝ) ^ (u + 1 - α) + 2 ^ (v + 1 - β) - u - v - 1 := by linarith
      _ ≤ (1 + (u + 1 - α)) + (1 + (v + 1 - β)) - u - v - 1 := by
        gcongr
        . have c0 : u + 1 - α ≥ 0 := by linarith
          have c1 : u + 1 - α ≤ 1 := by linarith
          set r := u + 1 - α
          let x : ℝ := 1
          suffices (1 + x) ^ r ≤ 1 + r * x from by norm_num [x] at this; simpa
          refine rpow_one_add_le_one_add_mul_self ?_ c0 c1
          norm_num [x]
        . have c0 : v + 1 - β ≥ 0 := by linarith
          have c1 : v + 1 - β ≤ 1 := by linarith
          set r := v + 1 - β
          let x : ℝ := 1
          suffices (1 + x) ^ r ≤ 1 + r * x from by norm_num [x] at this; simpa
          refine rpow_one_add_le_one_add_mul_self ?_ c0 c1
          norm_num [x]
      _ = _ := by linarith

-- It follows that $s-3 < b-a-\alpha-\beta$,
  replace h18 : s - 3 < b - a - α - β := by linarith

-- and so $ 2^{s-3} < 2^{b-a-\alpha-\beta}=2^{b-a} x_{a} x_{b} . $
  replace h18 : 2 ^ (s - 3) < 2 ^ (b - a) * x a * x b := by
    calc
      _ < (2 : ℝ) ^ (b - a - α - β) := by
        refine (rpow_lt_rpow_left_iff ?_).mpr h18
        norm_num
      _ = (2 : ℝ) ^ (b - a) * 2 ^ (-α) * 2 ^ (-β) := by
        rw [rpow_sub]
        rw [rpow_sub]
        rw [rpow_neg]
        rw [rpow_neg]
        . norm_cast
        all_goals norm_num
      _ = _ := by
        congr 2
        . simp [h6]
        . simp [h7]

  use a, by simp [ha]
  use b, by simp [hb]
