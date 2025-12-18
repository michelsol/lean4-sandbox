import Mathlib

-- p123, 424
open Real Finset

/- A function $f: I \rightarrow \mathbb{R}$, defined on an interval $I$, is called concave if $f(\theta x+(1-\theta) y) \geq \theta f(x)+(1-\theta) f(y)$ for all $x, y \in I$ and $0 \leq \theta \leq 1$. Assume that the functions $f_{1}, \ldots, f_{n}$, having all nonnegative values, are concave. Prove that the function $\left(f_{1} f_{2} \ldots f_{n}\right)^{1 / n}$ is concave. -/
theorem inequalities_23662
    (n : ℕ)
    (hn : 0 < n)
    (f : ℕ → ℝ → ℝ)
    (hf : ∀ i ∈ Icc 1 n, ConcaveOn ℝ Set.univ (f i))
    (hf2 : ∀ i ∈ Icc 1 n, ∀ x, f i x ≥ 0)
    : ConcaveOn ℝ Set.univ ((∏ i ∈ Icc 1 n, f i) ^ (1 / n : ℝ)) := by

-- Set $F(x)=f_{1}(x) f_{2}(x) \cdots f_{n}(x)$, we must prove concavity of $F^{1 / n}$.
  set F := ∏ i ∈ Icc 1 n, f i

-- $F$ is nonnegative
  have hF (x : ℝ) : F x ≥ 0 := by
    simp only [F, prod_apply]
    apply prod_nonneg (hf2 . . x)

-- By the assumption,  $$ \begin{aligned} F(\theta x+(1-\theta) y) & \geq \prod_{i=1}^{n}\left[\theta f_{i}(x)+(1-\theta) f(y)\right] \\ & =\sum_{k=0}^{n} \theta^{k}(1-\theta)^{n-k} \sum f_{i_{1}}(x) \ldots f_{i_{k}}(x) f_{i_{k+1}}(y) f_{i_{n}}(y) \end{aligned} $$
-- where the second sum goes through all $\binom{n}{k} k$-subsets $\left\{i_{1}, \ldots, i_{k}\right\}$ of $\{1, \ldots, n\}$.
  have h1 (x y θ : ℝ) (hθ : θ ∈ Set.Icc 0 1) : F (θ * x + (1 - θ) * y)
      ≥ ∑ k ∈ Icc 0 n, θ ^ k * (1 - θ) ^ (n - k) *
          ∑ s ∈ (Icc 1 n).powerset with #s = k, (∏ j ∈ s, f j x) * (∏ j ∈ Icc 1 n \ s, f j y) := by
    calc
      _ ≥ ∏ i ∈ Icc 1 n, (θ * f i x + (1 - θ) * f i y) := by
        simp at hθ
        have hθ1 : θ ≥ 0 := by linarith
        have hθ2 : 1 - θ ≥ 0 := by linarith
        simp only [F, prod_apply]
        apply prod_le_prod
        . intro i hi
          have c1 := hf2 i hi x
          have c2 := hf2 i hi y
          positivity
        . intro i hi
          apply (hf i hi).right
          . simp
          . simp
          . exact hθ1
          . exact hθ2
          . linarith
      _ = _ := by
        rw [prod_add]
        have c1 : (Icc 1 n).powerset = (Icc 0 n).biUnion λ k ↦ {s ∈ (Icc 1 n).powerset | #s = k} := by
          sorry
        conv_lhs => rw [c1]
        rw [sum_biUnion]
        . apply sum_congr rfl
          intro k hk
          conv_rhs => rw [mul_sum]
          apply sum_congr rfl
          intro s hs
          sorry
        . intro i hi j hj hij s hsi hsj x hx
          specialize hsi hx
          specialize hsj hx
          simp at hsi
          simp at hsj
          replace hsi := hsi.right
          replace hsj := hsj.right
          omega

-- The inequality between the arithmetic and geometric means now gives us  $$ \sum f_{i_{1}}(x) f_{i_{2}}(x) \cdots f_{i_{k}}(x) f_{i_{k+1}}(y) f_{i_{n}}(y) \geq\binom{ n}{k} F(x)^{k / n} F(y)^{(n-k) / n} $$
  have h2 (x y θ : ℝ) (hθ : θ ∈ Set.Icc 0 1) (k : ℕ) (hk : k ∈ Icc 0 n) :
      ∑ s ∈ (Icc 1 n).powerset with #s = k, (∏ j ∈ s, f j x) * (∏ j ∈ Icc 1 n \ s, f j y)
        ≥ (n.choose k) * F x ^ (k / n : ℝ) * F y ^ ((n - k) / n : ℝ) := by
    let S := {s ∈ (Icc 1 n).powerset | #s = k}
    have c1 := geom_mean_le_arith_mean S (λ _ => 1) (λ s => (∏ j ∈ s, f j x) * (∏ j ∈ Icc 1 n \ s, f j y)) (by simp) sorry sorry
    sorry

-- Inserting this in the above inequality and using the binomial formula, we finally obtain  $$ \begin{aligned} F(\theta x+(1-\theta) y) & \geq \sum_{k=0}^{n} \theta^{k}(1-\theta)^{n-k}\binom{n}{k} F(x)^{k / n} F(y)^{(n-k) / n} \\ & =\left(\theta F(x)^{1 / n}+(1-\theta) F(y)^{1 / n}\right)^{n}, \end{aligned} $$
  have h3 (x y θ : ℝ) (hθ : θ ∈ Set.Icc 0 1) : F (θ * x + (1 - θ) * y) ≥ (θ * F x ^ (1 / n : ℝ) + (1 - θ) * F y ^ (1 / n : ℝ)) ^ n := by
    calc
      _ ≥ _ := h1 x y θ hθ
      _ ≥ ∑ k ∈ Icc 0 n, θ ^ k * (1 - θ) ^ (n - k) * n.choose k * F x ^ (k / n : ℝ) * F y ^ ((n - k) / n : ℝ) := by
        apply sum_le_sum
        intro k hk
        suffices (θ ^ k * (1 - θ) ^ (n - k)) *
            (n.choose k * F x ^ (k / n : ℝ) * F y ^ ((n - k) / n : ℝ))
          ≤ (θ ^ k * (1 - θ) ^ (n - k)) *
            (∑ s ∈ (Icc 1 n).powerset with #s = k, (∏ j ∈ s, f j x) * (∏ j ∈ Icc 1 n \ s, f j y)) from by ring_nf at this ⊢; simpa
        gcongr
        . sorry
        . exact h2 x y θ hθ k hk
      _ = ∑ k ∈ Icc 0 n, θ ^ k * (1 - θ) ^ (n - k) * n.choose k * F x ^ (1 / n : ℝ) ^ k * F y ^ (1 / n : ℝ) ^ (n - k) := by
        apply sum_congr rfl
        intro k hk
        congr 2
        . sorry
        . sorry
      _ = ∑ k ∈ Icc 0 n, (θ * F x ^ (1 / n : ℝ)) ^ k * ((1 - θ) * F y ^ (1 / n : ℝ)) ^ (n - k) * n.choose k := by
        sorry
      _ = _ := by
        -- use the binomial formula
        rw [show Icc 0 n = range (n + 1) from by ext x; simp; omega]
        rw [add_pow]

-- which proves the assertion.
  split_ands
  . exact convex_univ
  intro x hx y hy θ γ hθ hγ hθγ
  rw [show γ = 1 - θ from by linarith]
  dsimp
  specialize h3 x y θ (by split_ands <;> linarith)
  have h4 : MonotoneOn (λ t : ℝ ↦ t ^ (n : ℝ)⁻¹) (Set.Ici 0) := by
    replace hn : n ≥ 1 := by omega
    rify at hn
    apply monotoneOn_rpow_Ici_of_exponent_nonneg
    sorry
  specialize h4 _ _ h3
  . dsimp
    have c1 := hF x
    have c2 := hF y
    sorry
  . apply hF
  . dsimp at h4
    rw [pow_rpow_inv_natCast] at h4
    . simpa using h4
    . sorry
    . omega
