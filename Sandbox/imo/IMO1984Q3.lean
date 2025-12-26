import Mathlib

open Set EuclideanGeometry

/-
In a plane two different points $O$ and $A$ are given.
For each point $X \neq O$ of the plane denote by $\alpha(X)$ the angle $A O X$
measured in radians $(0 \leq \alpha(X)<2 \pi)$ and by $C(X)$ the circle
with center $O$ and radius $O X+\frac{\alpha(X)}{O X}$.
Suppose each point of the plane is colored by one of a finite number of colors.
Show that there exists a point $X$ with $\alpha(X)>0$ such that its color
appears somewhere on the circle $C(X)$.
-/

theorem other_23942
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2)]
    [Module.Oriented ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2)]
    (O : EuclideanSpace ℝ (Fin 2))
    (A : EuclideanSpace ℝ (Fin 2))
    (O_ne_A : O ≠ A)
-- $\alpha(X)$ is the angle $A O X$ measured in radians $(0 \leq \alpha(X)<2 \pi)$
    (α : EuclideanSpace ℝ (Fin 2) → ℝ)
    (α_def : ∀ X, α X = (toIcoMod_periodic two_pi_pos 0).lift (∡ A O X))
    (C : EuclideanSpace ℝ (Fin 2) → Set (EuclideanSpace ℝ (Fin 2)))
    (C_def : ∀ X, C X = {Y | dist O Y = dist O X + α X / dist O X})
    (colorNum : ℕ)
    (color : EuclideanSpace ℝ (Fin 2) → Fin colorNum)
    : ∃ (X : EuclideanSpace ℝ (Fin 2)) (_ : α X > 0), ∃ Y ∈ C X, color X = color Y := by
-- Suppose that the statement of the problem is false.
  by_contra h1
  push_neg at h1

-- Consider $0 < r < s < 1$ and the two circles $R=(O, r)$ and $S=(O, s)$.
-- We will show that R and S have distinct sets of colors.
  have h2 (r s : ℝ) (zero_lt_r : 0 < r) (r_lt_s : r < s) (s_lt_1 : s < 1) :
      let R : Set (EuclideanSpace ℝ (Fin 2)) := {Y | dist O Y = r}
      let S : Set (EuclideanSpace ℝ (Fin 2)) := {Y | dist O Y = s}
      color '' R ≠ color '' S := by
    intro R S

-- Let $X \in R$ with $\alpha(X)=r(s-r)<2 \pi$.
    let o : Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2) := o
    let rot_r_mul_s_sub_r := o.rotation (r * (s - r))
    let v := rot_r_mul_s_sub_r (A - O)
    let X := (r / ‖v‖) • v + O
    have A_sub_O_ne_0 : A - O ≠ 0 := by
      intro h
      apply O_ne_A
      apply_fun (. + O) at h
      simpa using h.symm
    have norm_v_ne_0 : ‖v‖ ≠ 0 := by
      suffices v ≠ 0 from by simpa
      intro h
      replace h : rot_r_mul_s_sub_r (A - O) = rot_r_mul_s_sub_r 0 := by simpa [v] using h
      replace h := rot_r_mul_s_sub_r.injective h
      contradiction
    have X_mem_R : X ∈ R := by
      suffices ‖v‖ ≠ 0 from by field_simp [R, X, norm_smul]; linarith
      assumption
    have αX_eq : α X = r * (s - r) := by
      rw [α_def]
      simp only [oangle, vsub_eq_sub]
      have : X - O = (r / ‖v‖) • v := by simp [X]
      rw [this, o.oangle_smul_right_of_pos _ _ (by positivity)]
      rw [o.oangle_rotation_right (by simpa) (by simpa)]
      rw [Orientation.oangle_self, zero_add]
      erw [toIcoMod_eq_self two_pi_pos]
      split_ands
      . nlinarith
      . trans 1
        . nlinarith
        . have := Real.pi_gt_three
          linarith

-- $X$ satisfies $C(X)=S$.
    have CX_eq : C X = S := by
      ext Y
      suffices dist O Y = dist O X + r * (s - r) / dist O X ↔ dist O Y = s from by
        simpa [C_def, S, αX_eq]
      suffices dist O X + r * (s - r) / dist O X = s from by simp [this]
      field_simp [show dist O X = r from by simpa [R] using X_mem_R]

-- It follows that the color of the point $X$ does not appear on $S$.
    have h2 : ∀ Y ∈ S, color X ≠ color Y := by
      specialize h1 X (by rw [αX_eq]; nlinarith)
      rwa [CX_eq] at h1

-- Consequently, the set of colors that appear on $R$ is not the same as
-- the set of colors that appear on $S$.
    intro h3
    have : color X ∈ color '' S := by rw [←h3]; use X
    obtain ⟨Y, Y_mem_S, hY⟩ := this
    exact h2 Y Y_mem_S hY.symm

-- Hence any two distinct circles with center at $O$ and radii < 1 have distinct sets of colors.
  have h3 : ∀ r ∈ Ioo 0 1, ∀ s ∈ Ioo 0 1, r ≠ s →
      color '' {Y | dist O Y = r} ≠ color '' {Y | dist O Y = s} := by
    intro r hr s hs hrs
    simp at hr hs
    have : r < s ∨ s < r := lt_or_gt_of_ne hrs
    rcases this with h | h
    . exact h2 r s (by linarith) (by linarith) (by linarith)
    . exact (h2 s r (by linarith) (by linarith) (by linarith)).symm

-- This is a contradiction, since there are infinitely many such circles
-- but only finitely many possible sets of colors.
  let f (r : ℝ) := color '' {Y | dist O Y = r}
  have inj_f : InjOn f (Ioo 0 1) := by
    intro r hr s hs hrs
    specialize h3 r hr s hs
    simp [f] at hrs
    contrapose h3
    simp [h3, hrs]
  have maps_f : MapsTo f (Ioo 0 1) .univ := by exact λ _ _ => trivial
  have := infinite_of_injOn_mapsTo inj_f maps_f (Ioo_infinite (by linarith))
  apply this
  exact finite_univ
