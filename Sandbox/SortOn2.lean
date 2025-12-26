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

theorem nonempty_sdiff_image_of_lt
    {n k : ℕ} (hk : k < n) (y : Fin k → Fin n) : (univ \ univ.image y).Nonempty := by
  apply nonempty_of_ne_empty
  by_contra! h1
  replace h1 : #(univ.image y) = n := by simp at h1; simp [h1]
  have h2 : #(univ.image y) ≤ k := by convert univ.card_image_le using 1; simp
  omega

noncomputable def fsort {n : ℕ} (f : Fin n → α) : Fin n → Fin n :=
  let wfr : WellFoundedRelation (Fin n) := inferInstance
  wfr.wf.fix fun k ih => (univ \ univ.image fun j => ih ⟨j.1, by omega⟩ j.2).argmin f
    (nonempty_sdiff_image_of_lt k.2 _)

theorem fsort_eq {n : ℕ} (f : Fin n → α) (k : Fin n) : fsort f k =
    (univ \ univ.image fun j => fsort f ⟨j.1, by omega⟩).argmin f (nonempty_sdiff_image_of_lt k.2 _)
     := by
  let wfr : WellFoundedRelation (Fin n) := inferInstance
  apply wfr.wf.fix_eq

theorem bijective_fsort {n : ℕ} (f : Fin n → α) : (fsort f).Bijective := by
  apply (Fintype.bijective_iff_injective_and_card (fsort f)).mpr ⟨?_, rfl⟩
  intro ⟨i, hi⟩ ⟨j, hj⟩ hij
  wlog h1 : j ≤ i
  · symm
    simpa using this f j hj i hi hij.symm (by omega)
  obtain h1 | h1 : i = j ∨ j < i := by omega
  · simpa using h1
  · let si := univ \ univ.image fun k : Fin i => fsort f ⟨k.1, by omega⟩
    have h2 := si.argmin_mem f (nonempty_sdiff_image_of_lt hi _)
    conv_lhs at hij => rw [fsort_eq]
    rw [hij] at h2
    simp [si] at h2
    simpa using h2 ⟨j, by omega⟩

theorem monotone_fsort {n : ℕ} (f : Fin n → α) : Monotone (f ∘ fsort f) := by
  intro ⟨k, hk⟩ ⟨j, hj⟩ (h1 : k ≤ j)
  simp only [Function.comp_apply]
  rw [fsort_eq]
  apply argmin_le
  simp only [mem_sdiff, mem_univ, mem_image, true_and, not_exists]
  intro ⟨i, hi⟩ hij
  have h : i = j := by simpa using (bijective_fsort f).injective hij
  omega

theorem strictmono_fsort_of_injective {n : ℕ} {f : Fin n → α} (hf : f.Injective) :
    StrictMono (f ∘ fsort f) := by
  have h1 := monotone_fsort f
  have h2 := (bijective_fsort f).injective
  exact (Monotone.strictMono_iff_injective h1).mpr (hf.comp h2)

theorem image_comp_fsort {n : ℕ} (f : Fin n → α) : univ.image (f ∘ fsort f) = univ.image f := by
  apply coe_inj.mp
  simp only [coe_image, Set.image_comp]
  congr 1
  simpa using (bijective_fsort f).surjective.range_eq

end

section
variable {α : Type _} [LinearOrder α]
variable {ι : Type _} [Fintype ι] [LinearOrder ι]

noncomputable def familySort (f : ι → α) : ι → ι :=
  let e := Fintype.orderIsoFinOfCardEq ι rfl
  e ∘ fsort (f ∘ e) ∘ e.symm

theorem bijective_familySort (f : ι → α) : (familySort f).Bijective := by
  let e := Fintype.orderIsoFinOfCardEq ι rfl
  apply e.bijective.comp
  apply Function.Bijective.comp ?_ e.symm.bijective
  apply bijective_fsort

theorem monotone_familySort (f : ι → α) : Monotone (f ∘ familySort f) := by
  let e := Fintype.orderIsoFinOfCardEq ι rfl
  have h1 := monotone_fsort (f ∘ e)
  apply h1.comp
  apply e.symm.monotone

theorem strictmono_familySort_of_injective {f : ι → α} (hf : f.Injective) :
    StrictMono (f ∘ familySort f) := by
  let e := Fintype.orderIsoFinOfCardEq ι rfl
  have h1 := strictmono_fsort_of_injective (hf.comp e.injective)
  apply h1.comp
  apply e.symm.strictMono

open Finset in
theorem image_comp_familySort (f : ι → α) : univ.image (f ∘ familySort f) = univ.image f := by
  apply coe_inj.mp
  simp only [coe_image, Set.image_comp]
  congr 1
  simpa using (bijective_familySort f).surjective.range_eq

end


example (n : ℕ) : (2 * ∑' k : ℕ, if k ≤ n then k else 0) = n * (n + 1) := by
  induction' n with n ih
  · calc
      _ = 2 * ∑' k : ℕ, 0 := by
        congr 2 with k
        simp
      _ = _ := by simp
  · let a := ∑' k : ℕ, if k ≤ n then k else 0
    let b := ∑' k : ℕ, if k = n + 1 then k else 0
    calc
    _ = 2 * ∑' k : ℕ, ((if k ≤ n then k else 0) + if k = n + 1 then k else 0) := by
      congr 2 with k
      split_ifs with h1 h2 h3
      all_goals omega
    _ = 2 * (a + b) := by
      congr 1
      apply Summable.tsum_add
      · apply summable_of_finite_support
        apply BddAbove.finite
        apply bddAbove_def.mpr
        use n
        simp
        omega
      · apply summable_of_finite_support
        apply BddAbove.finite
        apply bddAbove_def.mpr
        use n + 1
        simp
    _ = 2 * a + 2 * b := by ring
    _ = n * (n + 1) + 2 * (n + 1) := by
      congr 2
      calc
      _ = ∑' k : ℕ, if k = n + 1 then n + 1 else 0 := by
        congr! 2 with k
        split_ifs with h1
        all_goals omega
      _ = _ := by simp
    _ = _ := by ring



example : ¬IsIntegral ℤ (1 / 2 : ℚ) := by
  suffices ∀ p, p.Monic → ¬Polynomial.eval₂ (Int.castRingHom ℚ) (1 / 2) p = 0 by
    simpa [IsIntegral, RingHom.IsIntegralElem] using this
  intro p h1 h2
  simp [Polynomial.eval₂_def, Polynomial.sum] at h2
  sorry
