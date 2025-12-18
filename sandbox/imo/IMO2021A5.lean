import Mathlib

open Finset Real

/-
Let $n \geqslant 2$ be an integer,
and let $a_{1}, a_{2}, \ldots, a_{n}$ be positive real numbers
such that $a_{1}+a_{2}+\cdots+a_{n}=1$.
Prove that
$$ \sum_{k=1}^{n} \frac{a_{k}}{1-a_{k}}\left(a_{1}+a_{2}+\cdots+a_{k-1}\right)^{2}<\frac{1}{3} $$
-/

theorem algebra_24137
    (n : ℕ) (hn : 2 ≤ n)
    (a : ℕ → ℝ)
    (ha1 : ∀ k ∈ Icc 1 n, 0 < a k)
    (ha2 : ∑ k ∈ Icc 1 n, a k = 1)
    : ∑ k ∈ Icc 1 n, a k / (1 - a k) * (∑ i ∈ Icc 1 (k - 1), a i) ^ 2 < 1 / 3 := by

-- For all $k \leqslant n$, let  $$ s_{k}=a_{1}+a_{2}+\cdots+a_{k} \quad
  let s k := ∑ i ∈ Icc 1 k, a i
-- \text { and } \quad b_{k}=\frac{a_{k} s_{k-1}^{2}}{1-a_{k}} $$
  let b k := a k * s (k - 1) ^ 2 / (1 - a k)
-- with the convention that $s_{0}=0$.
  have s0 : s 0 = 0 := by simp [s]

-- Note that $a_{k} \in(0,1)$.
  have h1 k (hk1 : k ≥ 1) (hk2 : k ≤ n) : a k > 0 := by
    exact ha1 k (by simp; omega)

  have h2 k (hk1 : k ≥ 1) (hk2 : k ≤ n) : a k < 1 := by
    calc
      _ = ∑ i ∈ Icc k k, a i := by simp
      _ < ∑ i ∈ Icc 1 n, a i := by
        rcases (by omega : k = 1 ∨ k > 1) with hk3 | hk3
        . have c1 : 2 ∈ Icc 1 n := by simp; omega
          apply sum_lt_sum_of_subset _ c1
          . simp; omega
          . apply ha1 _ (by simp; omega)
          . intro x hx hx2; specialize ha1 x hx; linarith
          . intro x; simp; omega
        . have c1 : 1 ∈ Icc 1 n := by simp; omega
          apply sum_lt_sum_of_subset _ c1
          . simp; omega
          . apply ha1 _ (by simp; omega)
          . intro x hx hx2; specialize ha1 x hx; linarith
          . intro x; simp; omega
      _ = _ := ha2

-- And $s_{k} \in(0,1)$.
  have h3 k (hk1 : k ≥ 1) (hk2 : k ≤ n) : s k > 0 := by
    suffices ∑ i ∈ Icc 1 k, a i > ∑ i ∈ Icc 1 k, 0 from by simpa
    apply sum_lt_sum_of_nonempty
    . use 1; simp; omega
    . intro i hi; exact ha1 i (by simp at hi ⊢; omega)

  have h4 k (hk1 : k ≥ 1) (hk2 : k ≤ n) : s k ≤ 1 := by
    dsimp [s]
    rw [←ha2]
    apply sum_le_sum_of_subset_of_nonneg
    . intro x; simp; omega
    . intro i hi hi2
      simp at hi hi2
      specialize ha1 i (by simp; omega)
      linarith

-- Note that $b_{k}$ is exactly a summand in the sum we need to estimate.
-- We shall prove the inequality  $$ b_{k}<\frac{s_{k}^{3}-s_{k-1}^{3}}{3} $$    (1)
  have h5 k (hk : k ∈ Icc 1 n) : b k < (s k ^ 3 - s (k - 1) ^ 3) / 3 := by
    have hk1 : k ≥ 1 := by simp at hk; omega
    have hk2 : k ≤ n := by simp at hk; omega
-- Notice that $1 - a_k > 0$.
    have c1 : 1 - a k > 0 := by specialize h2 k (by omega) (by omega); linarith
-- And $s_k = s_{k-1} + a_k$.
    have c2 : s k = s (k - 1) + a k := by
      dsimp only [s]
      have d2 : {k} ⊆ Icc 1 k := by intro x; simp; omega
      rw [←sum_sdiff d2]
      have d3 : Icc 1 k \ {k} = Icc 1 (k - 1) := by ext x; simp; omega
      simp [d3]
-- Indeed, it suffices to check that
-- $$ \begin{aligned} (1) & \Longleftrightarrow 0
-- < \left(1-a_{k}\right)\left(\left(s_{k-1}+a_{k}\right)^{3}-s_{k-1}^{3}\right)-3 a_{k} s_{k-1}^{2}
-- \\ & \Longleftrightarrow 0
-- < \left(1-a_{k}\right)\left(3 s_{k-1}^{2}+3 s_{k-1} a_{k}+a_{k}^{2}\right)-3 s_{k-1}^{2}
-- \\ & \Longleftrightarrow 0
-- < -3 a_{k} s_{k-1}^{2}+3\left(1-a_{k}\right) s_{k-1} a_{k}+\left(1-a_{k}\right) a_{k}^{2}
-- \\ & \Longleftrightarrow 0
-- < 3\left(1-a_{k}-s_{k-1}\right) s_{k-1} a_{k}+\left(1-a_{k}\right) a_{k}^{2} \end{aligned} $$
    suffices d1 : 0 < 3 * (1 - a k - s (k - 1)) * s (k - 1) * a k + (1 - a k) * a k ^ 2 from by
      suffices d2 : b k < (s k ^ 3 - s (k - 1) ^ 3) / 3
          ↔ 0 < 3 * (1 - a k - s (k - 1)) * s (k - 1) * a k + (1 - a k) * a k ^ 2
          from by exact d2.mpr d1
      calc
        _ ↔ 0 < (s k ^ 3 - s (k - 1) ^ 3) / 3 - a k * s (k - 1) ^ 2 / (1 - a k) := by
          constructor <;> (intro h; linarith)
        _ ↔ 0 < (1 - a k) * (s k ^ 3 - s (k - 1) ^ 3) - 3 * a k * s (k - 1) ^ 2 := by
          field_simp
          constructor <;> (intro h; linarith)
        _ ↔ 0 < (1 - a k) * ((s (k - 1) + a k) ^ 3 - s (k - 1) ^ 3) - 3 * a k * s (k - 1) ^ 2 := by
          rw [c2]
        _ ↔ a k * 0 < a k * ((1 - a k) * (3 * s (k - 1) ^ 2 + 3 * s (k - 1) * a k + a k ^ 2) - 3 * s (k - 1) ^ 2) := by
          ring_nf
        _ ↔ 0 < (1 - a k) * (3 * s (k - 1) ^ 2 + 3 * s (k - 1) * a k + a k ^ 2) - 3 * s (k - 1) ^ 2 := by
          specialize ha1 k (by simp; omega)
          simp [ha1]
        _ ↔ 0 < - 3 * a k * s (k - 1) ^ 2 + 3 * (1 - a k) * s (k - 1) * a k + (1 - a k) * a k ^ 2 := by
          ring_nf
        _ ↔ _ := by ring_nf
    have c3 := h1 k (by omega) (by omega)
    have c4 := h2 k (by omega) (by omega)
    have c5 : 1 - a k > 0 := by linarith
    suffices
      (0 * 0 * 0 * 0 ≤ 3 * (1 - a k - s (k - 1)) * s (k - 1) * a k)
      ∧ (0 * 0 ^ 2 < (1 - a k) * a k ^ 2)
        from by
      linarith
    split_ands
    . suffices 0 ≤ 3 ∧ 0 ≤ (1 - a k - s (k - 1)) ∧ 0 ≤ s (k - 1) ∧ 0 ≤ a k from by
        obtain ⟨d1, d2, d3, d4⟩ := this; gcongr; simp
      split_ands
      . norm_num
      . suffices s (k - 1) + a k ≤ 1 from by linarith
        rw [←c2]
        exact h4 k (by omega) (by omega)
      . rcases (by omega : k ≥ 2 ∨ k = 1) with hk3 | hk3
        . specialize h3 (k - 1) (by omega) (by omega); linarith
        . subst hk3; simp [s]
      . linarith
    . gcongr

-- Thus, adding inequalities (1) for $k=1, \ldots, n$,
  have h6 : ∑ k ∈ Icc 1 n, b k < ∑ k ∈ Icc 1 n, (s k ^ 3 - s (k - 1) ^ 3) / 3 := by
    apply sum_lt_sum_of_nonempty
    . simp; omega
    . exact h5

-- we conclude that  $$ b_{1}+b_{2}+\cdots+b_{n}<\frac{s_{n}^{3}-s_{0}^{3}}{3}=\frac{1}{3} $$
-- as desired.
  calc
    _ = ∑ k ∈ Icc 1 n, b k := by apply sum_congr rfl; intro k hk; ring_nf
    _ < _ := h6
    _ = _ := by
      rw [←sum_div]
      congr 1
-- Simplify telescoping sums.
      rw [sum_sub_distrib]
      have c1 : ∑ k ∈ Icc 1 n, s (k - 1) ^ 3 = ∑ k ∈ Icc 0 (n - 1), s k ^ 3 := by
        apply sum_nbij (. - 1)
        . simp; omega
        . intro i hi j hj h; simp at hi hj h; omega
        . intro i hi; simp at hi ⊢; use i + 1; omega
        . simp
      rw [c1]
      have c2 : {n} ⊆ Icc 1 n := by intro x; simp; omega
      rw [←sum_sdiff c2]
      replace c2 : Icc 1 n \ {n} = Icc 1 (n - 1) := by ext x; simp; omega
      rw [c2]
      replace c2 : {0} ⊆ Icc 0 (n - 1) := by intro x; simp; omega
      rw [←sum_sdiff c2]
      replace c2 : Icc 0 (n - 1) \ {0} = Icc 1 (n - 1) := by ext x; simp; omega
      rw [c2]
      simp [s, ha2]
