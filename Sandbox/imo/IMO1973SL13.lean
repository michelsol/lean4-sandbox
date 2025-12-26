import Mathlib

open Real Set

/-
Show that $\frac{20}{60} < \sin 20^{\circ} < \frac{21}{60}$.
-/

theorem other_23710 : 20 / 60 < sin (20 * π / 180) ∧ sin (20 * π / 180) < 21 / 60 := by
-- From elementary trigonometry we have $\sin 3 t=3 \sin t-4 \sin ^{3} t$.
  have h1 t : sin (3 * t) = 3 * sin t - 4 * sin t ^ 3 := sin_three_mul t

-- Hence, if we denote $y=\sin 20^{\circ}$,
  set y := sin (20 * π / 180)

-- we have $\sqrt{3} / 2=\sin 60^{\circ}=3 y-4 y^{3}$.
  have h2 : √3 / 2 = 3 * y - 4 * y ^ 3 := by
    calc
      _ = sin (π / 3) := by rw [sin_pi_div_three]
      _ = sin (3 * (20 * π / 180)) := by ring_nf
      _ = _ := by rw [h1]

-- We now show that $0 < y < 1 / 2$.
  have h3 : y ∈ Ico 0 (1 / 2) := by
    split_ands
-- We have $0 < y$.
    . apply sin_nonneg_of_mem_Icc
      split_ands
      . cancel_denoms; exact pi_nonneg
      . cancel_denoms; gcongr; norm_num
-- And $y < \sin 30^{\circ} = 1 / 2$.
    . have c1 : 1 / 2 = sin (π / 6) := by rw [sin_pi_div_six]
      rw [c1]
      dsimp [y]
      apply sin_lt_sin_of_lt_of_le_pi_div_two
      . cancel_denoms
        suffices  (-90) * π ≤ 20 * π from by linarith
        gcongr
        norm_num
      . cancel_denoms
        suffices 1 * π ≤ 3 * π from by linarith
        gcongr
        norm_num
      . cancel_denoms
        gcongr
        norm_num

-- The function $f(x)=3 x-4 x^{3}$ is strictly increasing on $[0,1 / 2)$
  let f (x : ℝ) := 3 * x - 4 * x ^ 3
  have h5 : StrictMonoOn f (Ico 0 (1 / 2)) := by
-- because $f^{\prime}(x)=3-12 x^{2}>0$ for $0 \leq x < 1 / 2$.
    apply strictMonoOn_of_deriv_pos
    . apply convex_Ico
    . apply ContinuousOn.sub
      . apply ContinuousOn.mul
        . apply continuousOn_const
        . apply continuousOn_id'
      . apply ContinuousOn.mul
        . apply continuousOn_const
        . apply continuousOn_pow
    . intro x hx
      dsimp [f]
      rw [deriv_sub]
      . rw [deriv_mul]
        . simp at hx ⊢
          nlinarith
        . simp
        . simp
      . apply DifferentiableAt.mul <;> simp
      . simp

-- Now the desired inequality
-- $\frac{20}{60}=\frac{1}{3} < \sin 20^{\circ} < \frac{21}{60}=\frac{7}{20}$
  suffices 1 / 3 < y ∧ y < 7 / 20 from by ring_nf at this ⊢; simpa

-- follows from  $$ f\left(\frac{1}{3}\right) < \frac{\sqrt{3}}{2} < f\left(\frac{7}{20}\right) $$
-- which is directly verified.
  replace h2 : f y = √3 / 2 := by linarith
  split_ands
  . apply (h5.lt_iff_lt (by norm_num) h3).mp
    rw [h2]
    cancel_denoms
    apply (sq_lt_sq₀ (by norm_num) (by norm_num)).mp
    norm_num [mul_pow]
  . apply (h5.lt_iff_lt h3 (by norm_num)).mp
    rw [h2]
    cancel_denoms
    apply (sq_lt_sq₀ (by norm_num) (by norm_num)).mp
    norm_num [mul_pow]
