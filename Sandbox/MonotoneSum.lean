import Mathlib


open Finset


-- when summing a fixed number of terms in a monotone sequence
-- smallest sum is on the left

theorem sum_Ico_card_le_sum_of_monotoneOn
    {α : Type _} [Preorder α] [AddCommMonoid α] [AddLeftMono α]
    (a b : ℕ) (s : Finset ℕ) (hs : s ⊆ Icc a b) (f : ℕ → α) (hf : MonotoneOn f (Icc a b)) :
    ∑ i ∈ Ico a (a + s.card), f i ≤ ∑ i ∈ s, f i := by
  induction' hs2 : s.card with n ih generalizing s
  . simp [card_eq_zero] at hs2
    simp [hs2]
  . obtain ⟨j, hj1, hj2⟩ : ∃ j ∈ s, j ≥ a + n := by
      by_contra h
      push_neg at h
      replace h : s ⊆ Ico a (a + n) := by
        intro x hx
        specialize hs hx
        specialize h x hx
        simp at hs ⊢; omega
      replace h := card_le_card h
      simp at h
      omega
    have c1 := card_le_card hs
    simp at c1
    have h1 : {a + n} ⊆ Ico a (a + (n + 1 : ℕ)) := by intro k; simp; omega
    rw [←sum_sdiff h1]
    replace h1 : Ico a (a + (n + 1 : ℕ)) \ {a + n} = Ico a (a + n) := by ext k; simp; omega
    rw [h1]
    replace h1 : {j} ⊆ s := by intro k hk; simp at hk; subst hk; exact hj1
    rw [←sum_sdiff h1]
    iterate 2 rw [sum_singleton]
    have h2 : f (a + n) ≤ f j := hf (by simp; omega) (hs hj1) hj2
    specialize ih (s \ {j})
      (by intro k hk; simp at hk; exact hs hk.1)
      (by simp [card_sdiff h1]; omega)
    exact add_le_add ih h2

-- when summing a fixed number of terms in a monotone sequence
-- largest sum is on the right

theorem sum_le_sum_Icc_card_of_monotoneOn
    {α : Type _} [Preorder α] [AddCommMonoid α] [AddLeftMono α]
    (a b : ℕ) (s : Finset ℕ) (hs : s ⊆ Icc a b) (f : ℕ → α) (hf : MonotoneOn f (Icc a b)) :
    ∑ i ∈ s, f i ≤ ∑ i ∈ Icc (b + 1 - s.card) b, f i := by
  induction' hs2 : s.card with n ih generalizing s
  . simp [card_eq_zero] at hs2
    simp [hs2]
  . obtain ⟨j, hj1, hj2⟩ : ∃ j ∈ s, j ≤ b - n := by
      by_contra h
      push_neg at h
      replace h : s ⊆ Ioc (b - n) b := by
        intro x hx
        specialize hs hx
        specialize h x hx
        simp at hs ⊢; omega
      replace h := card_le_card h
      simp at h
      omega
    have c1 := card_le_card hs
    simp at c1
    have h1 : {b - n} ⊆ Icc (b + 1 - (n + 1 : ℕ)) b := by intro k hk; simp at hk ⊢; omega
    rw [←sum_sdiff h1]
    replace h1 : Icc (b + 1 - (n + 1 : ℕ)) b \ {b - n} = Icc (b + 1 - n) b := by ext k; simp; omega
    rw [h1]
    have h1 : {j} ⊆ s := by intro k hk; simp at hk; subst hk; exact hj1
    rw [←sum_sdiff h1]
    iterate 2 rw [sum_singleton]
    have h2 : f j ≤ f (b - n) := hf (hs hj1) (by simp; omega) hj2
    specialize ih (s \ {j})
      (by intro k hk; simp at hk; exact hs hk.1)
      (by simp [card_sdiff h1]; omega)
    exact add_le_add ih h2
