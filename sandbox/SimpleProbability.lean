import Mathlib

def Pmf (α : Type _) [Fintype α] := { f : α → ℝ // (∀ a, 0 ≤ f a) ∧ ∑ a, f a = 1 }

namespace Pmf
variable {α} [Fintype α] (p : Pmf α)

def probability (s : Finset α) := ∑ a ∈ s, p.val a

theorem probability_le_probability_of_subset {s t : Finset α} (h : s ⊆ t) :
    p.probability s ≤ p.probability t := by
  unfold probability
  apply Finset.sum_le_sum_of_subset_of_nonneg h
  intro a ha1 ha2
  exact p.prop.left a

theorem probability_empty : p.probability ∅ = 0 := by
  simp [probability]

theorem probability_univ : p.probability Finset.univ = 1 := by
  simp [probability, p.prop.right]

theorem probability_nonneg (s : Finset α) : 0 ≤ p.probability s := by
  convert_to p.probability ∅ ≤ p.probability s using 1
  apply p.probability_le_probability_of_subset
  apply Finset.empty_subset

theorem probability_le_one (s : Finset α) : p.probability s ≤ 1 := by
  convert_to p.probability s ≤ p.probability Finset.univ using 1
  · exact p.probability_univ.symm
  apply p.probability_le_probability_of_subset
  apply Finset.subset_univ

variable [DecidableEq α]

theorem probability_sdiff_of_subset {s t : Finset α} (h : s ⊆ t) :
    p.probability (t \ s) = p.probability t - p.probability s := by
  apply Finset.sum_sdiff_eq_sub h

theorem probability_compl (s : Finset α) : p.probability sᶜ = 1 - p.probability s := by
  convert_to p.probability (.univ \ s) = p.probability .univ - p.probability s using 2
  · apply p.probability_univ.symm
  apply p.probability_sdiff_of_subset
  apply Finset.subset_univ

theorem probability_union_of_disjoint {s t : Finset α} (h : Disjoint s t) :
    p.probability (s ∪ t) = p.probability s + p.probability t := by
  exact Finset.sum_union h

theorem probability_union {s t : Finset α} :
    p.probability (s ∪ t) = p.probability s + p.probability t - p.probability (s ∩ t) := by
  calc
    _ = p.probability (s \ (s ∩ t) ∪ t \ (s ∩ t) ∪ s ∩ t) := by
      congr 1
      grind
    _ = p.probability (s \ (s ∩ t))
        + p.probability (t \ (s ∩ t)) + p.probability (s ∩ t) := by
      iterate 2 rw [probability_union_of_disjoint]
      iterate 2
      · intro r h1 h2 x hx
        specialize h1 hx
        specialize h2 hx
        grind
    _ = (p.probability s - p.probability (s ∩ t))
        + (p.probability t - p.probability (s ∩ t)) + p.probability (s ∩ t) := by
      congr 2
      · apply probability_sdiff_of_subset
        exact Finset.inter_subset_left
      · apply probability_sdiff_of_subset
        exact Finset.inter_subset_right
    _ = _ := by linarith

noncomputable def uniform (n : ℕ) (hn : n ≠ 0) : Pmf (Fin n) :=
  ⟨fun _ => 1 / n, by simp, by simp [hn]⟩

theorem uniform_probability (n : ℕ) (hn : n ≠ 0) (s : Finset (Fin n)) :
    (uniform n hn).probability s = s.card / n := by
  simp [probability, uniform]
  rfl

end Pmf
