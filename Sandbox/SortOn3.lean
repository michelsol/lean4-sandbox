import Mathlib

namespace Finset

variable {α β : Type _} [LinearOrder β]
variable (s : Finset α) (f : α → β) (H : s.Nonempty)

noncomputable def argmax : α :=
  have h := (image f s).isGreatest_max' (by simp [H])
  (Finset.mem_image.mp h.1).choose

theorem argmax_mem : s.argmax f H ∈ s := by
  have h := (image f s).isGreatest_max' (by simp [H])
  exact (Finset.mem_image.mp h.1).choose_spec.1

theorem apply_argmax_eq : f (s.argmax f H) = (s.image f).max' (by simp [H]) := by
  have h := (image f s).isGreatest_max' (by simp [H])
  exact (Finset.mem_image.mp h.1).choose_spec.2

theorem le_argmax : ∀ a ∈ s, f a ≤ f (s.argmax f H) := by
  have h := (image f s).isGreatest_max' (by simp [H])
  simpa [upperBounds, apply_argmax_eq] using h.2

noncomputable def argmin : α :=
  have h := (image f s).isLeast_min' (by simp [H])
  (Finset.mem_image.mp h.1).choose

theorem argmin_mem : s.argmin f H ∈ s := by
  have h := (image f s).isLeast_min' (by simp [H])
  exact (Finset.mem_image.mp h.1).choose_spec.1

theorem apply_argmin_eq : f (s.argmin f H) = (s.image f).min' (by simp [H]) := by
  have h := (image f s).isLeast_min' (by simp [H])
  exact (Finset.mem_image.mp h.1).choose_spec.2

theorem argmin_le : ∀ a ∈ s, f (s.argmin f H) ≤ f a := by
  have h := (image f s).isLeast_min' (by simp [H])
  simpa [lowerBounds, apply_argmin_eq] using h.2

end Finset


section
open Finset

variable {α : Type _} [LinearOrder α]
variable {ι : Type _} [Fintype ι] [LinearOrder ι]

-- theorem nonempty_sdiff_image_of_lt
--     {n k : ℕ} (hk : k < n) (y : Fin k → Fin n) : (univ \ univ.image y).Nonempty := by
--   apply nonempty_of_ne_empty
--   by_contra! h1
--   replace h1 : #(univ.image y) = n := by simp at h1; simp [h1]
--   have h2 : #(univ.image y) ≤ k := by convert univ.card_image_le using 1; simp
--   omega

-- noncomputable def fsort (f : ι → α) : Fin (Fintype.card ι) → ι :=
--   let n := Fintype.card ι
--   let wfr : WellFoundedRelation (Fin n) := inferInstance
--   wfr.wf.fix fun k ih => (univ \ univ.image fun j : Fin k => ih ⟨j.1, by omega⟩ j.2).argmin f
--     sorry

noncomputable def fsort {n : ℕ} (f : Fin n → α) : Fin n → Fin n :=
  let wfr : WellFoundedRelation (Fin n) := inferInstance
  wfr.wf.fix fun k ih => (univ \ univ.image fun j : Fin k => ih ⟨j.1, by omega⟩ j.2).argmin f
    sorry

noncomputable def fsort' (f : ι → α) : ι → ι :=
  let e := Fintype.orderIsoFinOfCardEq ι rfl
  e ∘ fsort (f ∘ e) ∘ e.symm

end
