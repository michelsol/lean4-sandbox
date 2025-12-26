import Mathlib

-- The probability that a fair six-sided die roll is even is 1/2.
example :
    ((PMF.uniformOfFinset (Finset.Icc 1 6) (by simp)).toMeasure {n | n % 2 = 0}).toReal =
      1 / 2 := by
  suffices {n ∈ Finset.Icc 1 6 | n % 2 = 0}.card * 2 = 6 by
    simp
    field_simp
    norm_cast
    convert this
  decide

-- The probability that the sum of two fair six-sided die rolls is 7 is 1/6.
open Finset in
example :
    ((PMF.uniformOfFinset (Icc 1 6 ×ˢ Icc 1 6) (by simp)).toMeasure
      {p | p.1 + p.2 = 7}).toReal = 1 / 6 := by
  suffices {p ∈ Icc 1 6 ×ˢ Icc 1 6 | p.1 + p.2 = 7}.card * 6 = 36 by
    rw [PMF.toMeasure_uniformOfFinset_apply]
    · simp
      field_simp
      norm_cast
      convert this
    · simp only [measurableSet_setOf]
      exact measurable_from_prod_countable_right fun _ _ a => a
  decide


open ProbabilityTheory
variable {Ω : Type*} [MeasurableSpace Ω] {X : PMF Ω}
  (hX : Measurable X)
  -- (h : HasLaw X (uniformOn (Finset.Icc 1 6) (by simp)))
