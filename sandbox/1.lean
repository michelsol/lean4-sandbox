import Mathlib

universe u

open Set Filter Topology

namespace Froda

lemma jump_discontinuities_of_monotone {f : ℝ → ℝ} (h_mono : Monotone f) :
    ∀ x, ¬ ContinuousAt f x →
      (sSup (f '' Iio x)) < (sInf (f '' Ioi x)) := by
  intro x hx
  contrapose! hx
  unfold ContinuousAt
  rw [Metric.tendsto_nhds_nhds]
  intro ε hε
  -- Note that there is a 𝑦 < 𝑥 such that 𝑓(𝑦) is no
  -- more than 𝜖/2 less than the supremum of the function values to the left of 𝑥
  set s := sSup (f '' Iio x)
  have h1 : s ≤ s := by apply le_refl
  replace h1 := (Real.le_sSup_iff (by
    unfold BddAbove upperBounds
    use f x
    suffices ∀ a < x, f a ≤ f x by simpa using this
    intro y hyx; exact h_mono hyx.le) (by simp)).mp h1
  obtain ⟨y, hxy, h1⟩ : ∃ y < x, _ := by simpa using h1 (-ε / 2) (by linarith)
  -- Similarly, there is a 𝑧 > 𝑥 such that 𝑓(𝑧) is no more than 𝜖/2 greater than the
  -- infimum of the function values to the right of 𝑥.
  set t := sInf (f '' Ioi x)
  have h2 : t ≤ t := by apply le_refl
  replace h2 := (Real.sInf_le_iff (by
    unfold BddBelow lowerBounds
    use f x
    suffices ∀ (a : ℝ), x < a → f x ≤ f a by simpa using this
    intro y hxy
    exact h_mono hxy.le
    ) (by simp)).mp h2
  obtain ⟨z, hzx, h2⟩ : ∃ z > x, _ := by simpa using h2 (ε / 2) (by linarith)

  -- By our assumption, we have that 𝑓(𝑧) − 𝑓(𝑦) < 𝜖.
  have h3 : f z - f y < ε := by linarith

  use min (x - y) (z - x)
  use by
    apply lt_min
    · linarith
    · linarith

  intro w (hw : |_ - _| < _)
  obtain ⟨hw1, hw2⟩ := by simpa [lt_min_iff] using hw
  clear hw

  obtain ⟨hw1, hw1'⟩ := by simpa [abs_lt] using hw1
  obtain ⟨hw2, hw2'⟩ := by simpa [abs_lt] using hw2
  have := h_mono hw1.le
  have := h_mono hw2'.le
  have := h_mono hzx.le
  have := h_mono hxy.le

  -- we have 𝑓(𝑤) is within 𝜖 of 𝑓(𝑦)
  have h4 : |f w - f y| < ε := by rw [abs_lt]; split_ands <;> linarith

  -- we have 𝑓(𝑤) is within 𝜖 of 𝑓(z)
  have h5 : |f w - f z| < ε := by rw [abs_lt]; split_ands <;> linarith

  obtain ⟨h4, h4'⟩ := by simpa [abs_lt] using h4
  obtain ⟨h5, h5'⟩ := by simpa [abs_lt] using h5

  change |_ - _| < ε
  rw [abs_lt]; split_ands <;> linarith

lemma Monotone.sInf_Ioi_le_sSup_Iio {f : ℝ → ℝ} (h_mono : Monotone f) (x y : ℝ) (hxy : x < y) :
    sInf (f '' Ioi x) ≤ sSup (f '' Iio y) := by
  -- Consider 𝑧 such that 𝑥 < 𝑧 < 𝑦. We have that 𝑧 is included in both the set of values to
  -- the right of 𝑥 and the set of values to the left of 𝑦.
  -- Therefore, the infimum of the function value to the right of 𝑥 is less than or equal to 𝑓(𝑧)
  have h3 z (hz1 : x < z) (hz2 : z < y) : sInf (f '' Ioi x) ≤ f z := by
    rw [Real.sInf_le_iff]
    · intro ε hε
      use f z
      use by simp; use z
      linarith
    · use f x
      simp [lowerBounds]
      suffices ∀ a > x, f x ≤ f a by simpa using this
      intro y hyx; exact h_mono hyx.le
    · use f y
      simp
      use y

  have h4 z (hz1 : x < z) (hz2 : z < y) : f z ≤ sSup (f '' Iio y) := by
    rw [Real.le_sSup_iff]
    · intro ε hε
      use f z
      use by simp; use z
      linarith
    · use f y
      simp [upperBounds]
      suffices ∀ a < y, f a ≤ f y by simpa using this
      intro y hyy; exact h_mono hyy.le
    · use f x
      simp
      use x

  specialize h3 ((x + y) / 2) (by linarith) (by linarith)
  specialize h4 ((x + y) / 2) (by linarith) (by linarith)
  linarith


theorem Real.countable_not_continuousAt (f : ℝ → ℝ) (h_mono : Monotone f) :
    {x | ¬ ContinuousAt f x}.Countable := by
  set D := {x | ¬ ContinuousAt f x}
  -- For any 𝑥 ∈ 𝐷, we have that the
  -- supremum of the values of the function over inputs 𝑦 < 𝑥, which we can denote 𝑓(𝑥−),
  -- is strictly less than the infimum of the values of the function over inputs 𝑧 > 𝑥
  -- which we can denote 𝑓(𝑥+).
  set fminus := fun x => sSup (f '' Iio x)
  set fplus := fun x => sInf (f '' Ioi x)
  have h1 x (hx : x ∈ D) : fminus x < fplus x := jump_discontinuities_of_monotone h_mono x hx

  -- There is therefore a rational number 𝑞(x) such that: 𝑓(𝑥−) < 𝑞(x) < 𝑓(𝑥+)
  have h2 x (hx : x ∈ D) : ∃ q : ℚ, fminus x < q ∧ q < fplus x := by
    exact exists_rat_btwn (h1 x hx)

  -- we can use the axiom of choice to construct the mapping 𝑥 ↦ 𝑞𝑥
  choose! q hq using h2

  -- and since the function is monotone,
  -- we have that for any 𝑦 < 𝑥 discontinuities, 𝑞𝑦 ≤ 𝑓(𝑦+) ≤ 𝑓(𝑥−) < 𝑞𝑥.
  have h3 x y (hx : x ∈ D) (hy : y ∈ D) (hxy : y < x) : q y ≤ fplus y := by
    specialize hq y hy
    exact le_of_lt hq.2
  have h4 x y (hx : x ∈ D) (hy : y ∈ D) (hxy : y < x) : fplus y ≤ fminus x := by
    unfold fplus fminus
    exact Monotone.sInf_Ioi_le_sSup_Iio h_mono y x hxy
  have h5 x y (hx : x ∈ D) (hy : y ∈ D) (hxy : y < x) : fminus x < q x := by
    specialize hq x hx
    exact hq.1

  -- q is injective from the set of discontinuities 𝐷 to the set of rational numbers ℚ,
  -- and 𝐷 is therefore countable
  have h6 : Set.InjOn q D := by
    intro x hx y hy hxy
    obtain h2 | h2 | h2 : x < y ∨ x = y ∨ y < x := by apply lt_trichotomy
    · specialize h3 y x hy hx h2
      specialize h4 y x hy hx h2
      specialize h5 y x hy hx h2
      rify at hxy
      linarith
    · simp [h2]
    · specialize h3 x y hx hy h2
      specialize h4 x y hx hy h2
      specialize h5 x y hx hy h2
      rify at hxy
      linarith

  apply Set.countable_iff_exists_injOn.mpr
  obtain ⟨r, hr⟩ : ∃ f : ℚ → ℕ, f.Injective := Countable.exists_injective_nat'
  have hr' : Set.InjOn r univ := by
    intro x hx y hy hxy
    apply hr
    exact hxy

  use r ∘ q
  apply Set.InjOn.comp hr' h6
  intro x hx
  simp


end Froda
