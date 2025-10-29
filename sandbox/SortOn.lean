import Mathlib

namespace Finset

variable {α β : Type _} [LinearOrder β]
variable (f : α → β) (s : Finset α) (H : s.Nonempty)

noncomputable def argmin : α :=
  have h := (image f s).isLeast_min' (by simp [H])
  (Finset.mem_image.mp h.1).choose

theorem argmin_mem : argmin f s H ∈ s := by
  have h := (image f s).isLeast_min' (by simp [H])
  exact (Finset.mem_image.mp h.1).choose_spec.1

theorem apply_argmin : f (argmin f s H) = (s.image f).min' (by simp [H]) := by
  have h := (image f s).isLeast_min' (by simp [H])
  exact (Finset.mem_image.mp h.1).choose_spec.2

theorem apply_argmin_le : ∀ a ∈ s, f (argmin f s H) ≤ f a := by
  have h := (image f s).isLeast_min' (by simp [H])
  simpa [lowerBounds, apply_argmin f s H] using h.2

noncomputable def argmax : α :=
  have h := (image f s).isGreatest_max' (by simp [H])
  (Finset.mem_image.mp h.1).choose

theorem argmax_mem : argmax f s H ∈ s := by
  have h := (image f s).isGreatest_max' (by simp [H])
  exact (Finset.mem_image.mp h.1).choose_spec.1

theorem apply_argmax : f (argmax f s H) = (s.image f).max' (by simp [H]) := by
  have h := (image f s).isGreatest_max' (by simp [H])
  exact (Finset.mem_image.mp h.1).choose_spec.2

theorem apply_argmax_le : ∀ a ∈ s, f a ≤ f (argmax f s H) := by
  have h := (image f s).isGreatest_max' (by simp [H])
  simpa [upperBounds, apply_argmax f s H] using h.2

end Finset


section

open Finset

variable {ι : Type _} [Zero ι] [DecidableEq ι]
variable (s : Finset ι)

noncomputable def sortOn {α : Type _} [Zero α] [LinearOrder α] (x : ι → α) : ℕ → ι :=
  Nat.lt_wfRel.wf.fix (fun n ih =>
    if hn : n < #s then
    let label_lt_n k := if hk : k < n then ih k hk else 0
    argmin x (s \ (range n).image label_lt_n) (by
      apply nonempty_of_ne_empty
      intro h1
      apply_fun (#·) at h1
      conv_rhs at h1 => simp
      have c1 := le_card_sdiff ((range n).image label_lt_n) s
      have c2 : #((range n).image label_lt_n) ≤ n := by simpa using (range n).card_image_le
      omega)
    else 0)

theorem nonempty_sdiff_image_range_of_lt_card (φ : ℕ → ι) {n : ℕ} (hn : n < #s) :
    (s \ (range n).image φ).Nonempty := by
  apply nonempty_of_ne_empty
  intro h1
  apply_fun (#·) at h1
  conv_rhs at h1 => simp
  have c1 := le_card_sdiff ((range n).image φ) s
  have c2 : #((range n).image φ) ≤ n := by simpa using (range n).card_image_le
  omega

theorem sortOn_eq
    {α : Type _} [Zero α] [LinearOrder α] (x : ι → α)
    (n : ℕ) (hn : n < #s) :
    sortOn s x n = (s \ (range n).image (sortOn s x)).argmin x
      (nonempty_sdiff_image_range_of_lt_card s _ hn) := by
    dsimp only [sortOn]
    conv_lhs => rw [Nat.lt_wfRel.wf.fix_eq]
    split_ifs
    symm
    have h0 := nonempty_sdiff_image_range_of_lt_card s (sortOn s x) hn
    congr 2
    ext k
    simp only [mem_image, mem_range]
    constructor <;> intro ⟨l, h1, h2⟩
    · use l, h1
      simpa [h1] using h2
    · simp [h1] at h2
      use l

end

section
open Finset

noncomputable def sortOn2 {α : Type _} [Zero α] [LinearOrder α] {m : ℕ} (x : Fin m → α) :
    Fin m → Fin m :=
  let wfRel : WellFoundedRelation (Fin m) := inferInstance
  wfRel.wf.fix (fun ⟨n, hn⟩ ih =>
    let label_lt_n (k : Fin n) := ih ⟨k.1, by omega⟩ k.2
    argmin x (univ \ univ.image label_lt_n) (by
      apply nonempty_of_ne_empty
      intro h1
      apply_fun (#·) at h1
      conv_rhs at h1 => simp
      have c1 := le_card_sdiff (univ.image label_lt_n) univ
      -- have c2 : #(univ.image label_lt_n) ≤ n := by simpa using univ.card_image_le
      sorry
      )
    )
    -- argmin x (s \ (range n).image label_lt_n)
    -- (by
    --   have c1 := le_card_sdiff ((range n).image label_lt_n) s
    --   have c2 : #((range n).image label_lt_n) ≤ n := by simpa using (range n).card_image_le
    --   omega)


-- #check Set.Finite.fin_embedding

end
