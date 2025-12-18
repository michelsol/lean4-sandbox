import Mathlib

open Finset

/-
Let $$n \geqslant 3$$ be an integer, and $$x_{1}, x_{2}, \ldots, x_{n}$$ be real numbers in the interval $$[0,1]$$.
Suppose the sum $$s=x_{1}+x_{2}+\cdots+x_{n}$$ satisfies $$s \geqslant 3$$.
Prove that there exists integers $$i$$ and $$j$$ such that $$2^{j-i} x_{i} x_{j}>2^{s-3}$$.
-/

theorem inequalities_605762
    (n : ℤ) (hn : n ≥ 3)
    (x : ℤ → ℝ) (hx : ∀ k ∈ Icc 1 n, 0 ≤ x k ∧ x k ≤ 1)
    (s : ℝ) (hs1 : s = ∑ k ∈ Icc 1 n, x k) (hs2 : s ≥ 3) :
    ∃ i ∈ Icc 1 n, ∃ j ∈ Icc 1 n, 2 ^ (j - i) * x i * x j > 2 ^ (s - 3) := by

-- In the following, we set $$x_{t}=0$$ if $$t \leqslant 0$$ or $$t \geqslant n+1$$, which does not change the problem.
  wlog h1 : ∀ t ∉ Icc 1 n, x t = 0
  . specialize this n hn (λ k ↦ if k ∈ Icc 1 n then x k else 0) (λ k hk ↦ by simpa [hk] using hx k hk)
    specialize this s (by rw [hs1]; apply sum_congr rfl; intro k hk; simp [hk]) hs2
    specialize this (by intro k hk; simp [hk])
    obtain ⟨i, hi, j, hj, h2⟩ := this
    use i, hi, j, hj
    simpa [hi, hj] using h2

-- Let $$u$$ and $$v$$ be two indices for which $$2^{u-v} x_{u} x_{v}$$ is maximal.
  let Y := (Icc 1 n ×ˢ Icc 1 n).image λ (u, v) ↦ 2 ^ (u - v) * x u * x v
  have hY : Y.Nonempty := by simp [Y]; omega
  obtain ⟨⟨u, v⟩, huv, h2⟩ := mem_image.mp (Y.isGreatest_max' hY).left
  replace h2 : 2 ^ (u - v) * x u * x v = Y.max' hY := h2
  replace h2 : ∀ u' ∈ Icc 1 n, ∀ v' ∈ Icc 1 n, 2 ^ (u' - v') * x u' * x v' ≤ 2 ^ (u - v) * x u * x v := by
    intro k hk
    have c1 := (Y.isGreatest_max' hY).right
    sorry

-- This product is at least $$\max \left\{x_{i}^{2}\right\} \geqslant(s / n)^{2}$$, so it is non-zero,
  have h3 : 2 ^ (u - v) * x u * x v > 0 := by
    let Y2 := (Icc 1 n).image λ k ↦ x k ^ 2
    have hY2 : Y2.Nonempty := by simp [Y2]; omega
    obtain ⟨i0, hi0, c0⟩ := mem_image.mp (Y2.isGreatest_max' hY2).left
    replace c0 : x i0 ^ 2 = Y2.max' hY2 := c0
    replace c0 : ∀ k ∈ Icc 1 n, x k ^ 2 ≤ x i0 ^ 2 := by
      intro k hk
      simpa [←c0] using (Y2.isGreatest_max' hY2).right (by simp at hk; simp [Y2]; use k)
    calc
      _ ≥ x i0 * x i0 := by simpa using h2 i0 hi0 i0 hi0
      _ = x i0 ^ 2 := by ring_nf
      _ ≥ (s / n) ^ 2 := calc
          _ ≥ ((∑ k ∈ Icc 1 n, x k) / n) ^ 2 := by
            gcongr
            . sorry
            calc
              _ ≤ (∑ k ∈ Icc 1 n, x i0) / n := by
                apply div_le_div_of_nonneg_right
                swap
                . norm_cast; omega
                apply sum_le_sum
                intro i hi
                specialize c0 i hi
                have c1 := (hx i hi).left
                have c2 := (hx i0 hi0).left
                exact (sq_le_sq₀ c1 c2).mp c0
              _ = _ := by
                have c1 : (n : ℝ) ≥ 0 := by norm_cast; omega
                field_simp
                lift n to ℕ
                . omega
                . simp; ring_nf
          _ = _ := by rw [hs1]
      _ > _ := by positivity

-- meaning that $$x_{u}$$ and $$x_{v}$$ are non-zero.
  have h4 : x u ≠ 0 := by intro h4; simp [h4] at h3
  have h5 : x v ≠ 0 := by intro h5; simp [h5] at h3

-- By definition, we know that $$\max \left\{2^{u-t} x_{u} x_{t}, 2^{t-v} x_{t} x_{v}\right\} \leqslant 2^{u-v} x_{u} x_{v}$$,
  have h6 t : 2 ^ (u - t) * x u * x t ⊔ 2 ^ (t - v) * x t * x v ≤ 2 ^ (u - v) * x u * x v := by
    sorry

-- that is, $$x_{t} \leqslant \min \left\{1,2^{u-t} x_{u}, 2^{t-v} x_{v}\right\}$$, for any integer $$t$$.
  have h7 t : x t ≤ 1 ⊓ 2 ^ (u - t) * x u ⊓ 2 ^ (t - v) * x v := by
    sorry

-- Furthermore, there exists a real number $$\tau$$ such that $$2^{u-\tau} x_{u}=2^{\tau-v} x_{v}$$:

-- this is the real number $$ \tau=\frac{u+v+\log _{2}\left(x_{u} / x_{v}\right)}{2} $$
  let τ := (u + v + Real.logb 2 (x u / x v)) / 2
  have h8 : 2 ^ (u - τ) * x u = 2 ^ (τ - v) * x v := by
    sorry

-- We then set $$\alpha=2^{u-\tau} x_{u}=2^{\tau-v} x_{v}$$,
  let α := 2 ^ (u - τ) * x u

-- that is, $$\alpha=2^{(u-v) / 2} \sqrt{x_{u} x_{v}}$$,
  have h9 : α = 2 ^ ((u - v) / 2) * √(x u * x v) := by
    sorry

-- and we easily verify that $$x_{t} \leqslant \alpha / 2^{|t-\tau|}$$ for any integer $$t$$.
  have h10 t : x t ≤ α / (2 ^ |t - τ|) := by sorry

-- Now let $$w=\tau-\lfloor\tau\rfloor$$, so that $$0 \leqslant w \leqslant 1$$.
  let w := τ - ⌊τ⌋
  have h11 : 0 ≤ w ∧ w ≤ 1 := by
    sorry

-- Since the function $$f: x \mapsto 2^{x}+2^{1-x}$$ is convex and $$f(0)=f(1)=3$$, we then have
  let f (x : ℝ) : ℝ := 2 ^ x + 2 ^ (1 - x)
  have hf1 : ConvexOn ℝ .univ f := by
    sorry
  have hf2 : f 0 = 3 := by simp [f]; norm_num
  have hf3 : f 1 = 3 := by simp [f]; norm_num

-- $$ 3 \leqslant s=\sum_{t \leqslant \tau-w} x_{t}+\sum_{t \geqslant \tau+1-w} x_{t} \leqslant \sum_{k \geqslant 0} \alpha 2^{-w-k}+\sum_{k \geqslant 0} \alpha 2^{w-1-k}=f(1-w) \alpha \leqslant 3 \alpha, $$
  have h12 : 3 ≤ 3 * α := by
    calc
      _ ≤ s := by
        sorry
      _ = ∑ t ∈ Icc 1 ⌊τ - w⌋, x t + ∑ t ∈ Icc ⌈τ + 1 - w⌉ n, x t := by
        sorry
      _ ≤ ∑ k ∈ Icc 1 n, α * (2 ^ (-w - k)) + ∑ k ∈ Icc 1 n, α * (2 ^ (w - 1 - k)) := by
        sorry
      _ ≤ ∑' k : ℕ, α * (2 ^ (-w - k)) + ∑' k : ℕ, α * (2 ^ (w - 1 - k)) := by
        sorry
      _ ≤ α * f (1 - w) := by
        sorry
      _ ≤ α * (w * 3 + (1 - w) * 3) := by
        gcongr
        . sorry
        . have c1 := @hf1.right 0 (by simp) 1 (by simp) w (1 - w) (by linarith) (by linarith) (by linarith)
          simpa [hf2, hf3] using c1
      _ = 3 * α := by ring_nf

-- which shows that $$\log _{2}(\alpha) \geqslant 0$$.
  have h13 : Real.logb 2 α ≥ 0 := by
    sorry

-- We then set $$\mu=\left\lfloor\tau-\log _{2}(\alpha)\right\rfloor$$ and $$\nu=\left\lceil\tau+\log _{2}(\alpha)\right\rceil$$,
  let μ := ⌊τ - Real.logb 2 α⌋
  let ν := ⌈τ + Real.logb 2 α⌉
-- and $$y=\tau-\log _{2}(\alpha)-\mu$$, and finally $$z=\nu-\tau-\log _{2}(\alpha)$$,
  let y := τ - Real.logb 2 α - μ
  let z := ν - τ - Real.logb 2 α

-- so that $$\mu \leqslant \nu, 0 \leqslant y \leqslant 1$$ and $$0 \leqslant z \leqslant 1$$.
  have h14 : μ ≤ ν ∧ 0 ≤ y ∧ y ≤ 1 := by
    sorry

  have h15 : 0 ≤ z ∧ z ≤ 1 := by
    sorry

--This time, it is the function $$g: x \mapsto 2^{1-x}+x$$ that is convex and satisfies $$g(0)=g(1)=2$$.
  let g (x : ℝ) := 2 ^ (1 - x) + x
  have hg1 : ConvexOn ℝ .univ g := by
    sorry
  have hg2 : g 0 = 2 := by simp [g]
  have hg3 : g 1 = 2 := by simp [g]; norm_num

-- We conclude that $$ \begin{aligned} s & \leqslant \sum_{t \leqslant \mu} x_{t}+\left(x_{\mu+1}+\cdots+x_{\nu-1}\right)+\sum_{t \geqslant \nu} x_{t} \ & 2^{s-3}. \end{aligned} $$
  sorry
