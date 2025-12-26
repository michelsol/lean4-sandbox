import Mathlib

open Real Set InnerProductSpace

/-
Determine the minimum of $a^2+b^2$ if $a$ and $b$ are real numbers for which the equation
$$ x^4 + a x^3 + b x^2 + a x + 1 = 0$$  has at least one real solution.
-/

theorem algebra_24964 : IsLeast ({ (a, b) : ℝ × ℝ |
  ∃ x : ℝ, x ^ 4 + a * x ^ 3 + b * x ^ 2 + a * x + 1 = 0 }.image λ (a, b) ↦ a ^ 2 + b ^ 2)
  (4 / 5 : ℝ) := by
  constructor
  swap
  . suffices ∀ (m : ℝ) (a b x : ℝ), x ^ 4 + a * x ^ 3 + b * x ^ 2 + a * x + 1 = 0 → a ^ 2 + b ^ 2 = m → 4 / 5 ≤ m from by simpa [lowerBounds]
    suffices ∀ (a b x : ℝ), x ^ 4 + a * x ^ 3 + b * x ^ 2 + a * x + 1 = 0 → 4 / 5 ≤ a ^ 2 + b ^ 2 from by
      intro m a b x h hm; specialize this a b x h; linarith
    intro a b x heq
    have x_ne_0 : x ≠ 0 := by intro h; subst h; norm_num at heq
/-
Putting $x+\frac{1}{x}=t$ we also get $x^{2}+\frac{1}{x^{2}}=t^{2}-2$,
and the given equation reduces to $t^{2}+a t+b-2=0$.
-/
    let t := x + 1 / x
    have ht1 : x ^ 2 + 1 / x ^ 2 = t ^ 2 - 2 := by ring_nf; simp [x_ne_0]
    have ht2 : t ^ 2 + a * t + b - 2 = 0 := by field_simp [t]; ring_nf; linear_combination x*heq
/-
Since $x^2 - tx + 1=0$ has 1 real root, $|t| \geq 2, t \in \mathbb{R}$.
-/
    have ht3 : x ^ 2 - t * x + 1 = 0 := by field_simp [t]; ring_nf
    have ht4 : t ^ 2 - 4 ≥ 0 := by
      replace ht3 : 1 * x * x + (- t) * x + 1 = 0 := by ring_nf at ht3 ⊢; simpa
      rw [quadratic_eq_zero_iff_discrim_eq_sq (by norm_num) x] at ht3
      replace ht3 : t ^ 2 - 4 = (2 * x + -t) ^ 2 := by simpa [discrim] using ht3
      rw [ht3]
      apply sq_nonneg
    replace ht4 : |t| ≥ 2 := by
      suffices |t| ≥ |2| from by simpa
      apply sq_le_sq.mp
      linarith
/-
By the Cauchy-Schwarz inequality we have
$$ \left(a^{2}+b^{2}\right)\left(t^{2}+1\right) \geq(a t+b)^{2}=\left(t^{2}-2\right)^{2} $$
-/
    have h1 : (a ^ 2 + b ^ 2) * (t ^ 2 + 1) ≥ (t ^ 2 - 2) ^ 2 := by
      set u := (WithLp.equiv 2 _).symm (a, b)
      set v := (WithLp.equiv 2 _).symm (t, (1 : ℝ))
      calc
      _ = (a ^ 2 + b ^ 2) * (t ^ 2 + 1 ^ 2) := by ring_nf
      _ = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
        congr; all_goals
        . simp [u, v, norm_sq_eq_inner (𝕜 := ℝ)]; ring_nf
      _ = (‖u‖ * ‖v‖) ^ 2 := by ring_nf
      _ ≥ ⟪u, v⟫_ℝ ^ 2 := by
        apply sq_le_sq.mpr
        rw [abs_mul]
        iterate 2 rw [abs_norm]
        exact abs_real_inner_le_norm u v
      _ = (a * t + b * 1) ^ 2 := by simp [u, v]
      _ = (a * t + b) ^ 2 := by ring_nf
      _ = (2 - t ^ 2) ^ 2 := by congr 1; linarith
      _ = _ := by linarith
    skip
/-
It follows that $a^{2}+b^{2} \geq h(t)=\frac{\left(t^{2}-2\right)^{2}}{t^{2}+1}$.
-/
    replace h1 : (a ^ 2 + b ^ 2) ≥ (t ^ 2 + 1) + 9 / (t ^ 2 + 1) - 6 := by
      have : t ^ 2 + 1 > 0 := sorry
      calc
        (a ^ 2 + b ^ 2) ≥ (t ^ 2 - 2) ^ 2 / (t ^ 2 + 1) := by
          sorry
        _ = _ := by field_simp; ring_nf
    let h (t : ℝ) := (t ^ 2 + 1) + 9 / (t ^ 2 + 1) - 6
/-
Since $h(t)=\left(t^{2}+1\right)+\frac{9}{t^{2}+1}-6$ is increasing for $t \geq 2$,
we conclude that $a^{2}+b^{2} \geq h(2)=\frac{4}{5}$.
-/
    have mono_h : MonotoneOn h (Ici 2) := by
      apply monotoneOn_of_deriv_nonneg
      . exact convex_Ici 2
      . sorry
      . sorry
      . intro x hx
        replace hx : 2 < x := by simpa using hx
        have hx2 : x ^ 2 + 1 ≠ 0 := sorry
        dsimp [h]
        rw [deriv_sub]
        . rw [deriv_add]
          . rw [deriv_add]
            . rw [deriv_div]
              . suffices 0 ≤ 2 * x + -(9 * (2 * x)) / (x ^ 2 + 1) ^ 2 from by simpa
                suffices 0 ≤ (2 * x * (x ^ 2 + 1) ^ 2 + -(9 * (2 * x))) / (x ^ 2 + 1) ^ 2 from sorry
                suffices 0 ≤ (2 * x * (x ^ 2 + 1) ^ 2 + -(9 * (2 * x))) from by sorry
                nlinarith
              . sorry
              . sorry
              . simpa
            . simp
            . simp
          . sorry
          . sorry
        . apply DifferentiableAt.add
          . simp
          . apply DifferentiableAt.div
            . simp
            . simp
            . simpa
        . simp

    calc
      a ^ 2 + b ^ 2 ≥ h t := h1
      _ = h |t| := by simp [h]
      _ ≥ h 2 :=
        have h2 : (2 : ℝ) ∈ Ici 2 := by simp
        have h3 : |t| ∈ Ici 2 := by simp; linarith
        mono_h h2 h3 ht4
      _ = _ := by norm_num [h]
/-
The cases of equality are easy to examine: These are $a= \pm -\frac{4}{5}$ and $b=-\frac{2}{5}$ and $x = 1$.
-/
  . use (-4/5, -2/5)
    norm_num
    use 1
    norm_num
