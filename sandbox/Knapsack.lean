import Mathlib

noncomputable def Finset.argmax' {α β} [LinearOrder β]
    (f : α → β) (s : Finset α) (H : s.Nonempty) : α :=
  have h := (image f s).isGreatest_max' (by simp [H])
  (Finset.mem_image.mp h.1).choose

theorem Finset.argmax'_mem {α β} [LinearOrder β] (f : α → β) (s : Finset α) (H : s.Nonempty) :
    s.argmax' f H ∈ s := by
  have h := (image f s).isGreatest_max' (by simp [H])
  exact (Finset.mem_image.mp h.1).choose_spec.1

theorem Finset.f_argmax'_eq {α β} [LinearOrder β] (f : α → β) (s : Finset α) (H : s.Nonempty) :
    f (s.argmax' f H) = (s.image f).max' (by simp [H]) := by
  have h := (image f s).isGreatest_max' (by simp [H])
  exact (Finset.mem_image.mp h.1).choose_spec.2

theorem Finset.le_argmax' {α β} [LinearOrder β] (f : α → β) (s : Finset α) (H : s.Nonempty) :
    ∀ a ∈ s, f a ≤ f (s.argmax' f H) := by
  have h := (image f s).isGreatest_max' (by simp [H])
  simpa [upperBounds, f_argmax'_eq] using h.2



def choiceWeight (n : Nat) (w : Fin n → Nat) (c : Fin n → Bool) :=
  ∑ k : Fin n, w k * if c k then 1 else 0

def choiceValue (n : Nat) (v : Fin n → Nat) (c : Fin n → Bool) :=
  ∑ k : Fin n, v k * if c k then 1 else 0

def validChoices (n : Nat) (W : Nat) (w : Fin n → Nat) : Finset (Fin n → Bool) :=
  {c : Fin n → Bool | choiceWeight n w c ≤ W}

theorem validChoicesNonempty (n : Nat) (W : Nat) (w : Fin n → Nat) :
    (validChoices n W w).Nonempty := by
  use 0
  simp [validChoices, choiceWeight]

def validValues (n : Nat) (W : Nat) (w : Fin n → Nat) (v : Fin n → Nat) :=
  (validChoices n W w).image (choiceValue n v)

noncomputable def choiceWithMaxValue (n : Nat) (W : Nat) (w : Fin n → Nat) (v : Fin n → Nat) :=
    (validChoices n W w).argmax' (choiceValue n v) (validChoicesNonempty n W w)

def maxValue (n : Nat) (W : Nat) (w : Fin n → Nat) (v : Fin n → Nat) :=
    ((validChoices n W w).image (choiceValue n v)).max'
      (Finset.image_nonempty.mpr (validChoicesNonempty n W w))


theorem knapsack_dp_transition_equation (n : Nat) (hn : n > 0)
    (W : Nat) (w : Fin n → Nat) (v : Fin n → Nat) :
    -- let $$f_{i, j}$$ be the dynamic programming state holding the maximum total value
    -- the knapsack can carry with capacity  $j$ , when only the first  $i$  items are considered.
    let f (i : Fin n) (j : Nat) := maxValue i.1 j (w ⟨·, by omega⟩) (v ⟨·, by omega⟩)
    ∀ (i : Fin n) (hi : i.1 > 0) (j : Nat),
      f i j = max (f ⟨i - 1, by omega⟩ j) (f ⟨i - 1, by omega⟩ (j - w i) + v i) := by
  intro f i hi j
  unfold f
  conv_lhs => unfold maxValue
  -- have c : choiceValue i.1 (v ⟨·, by omega⟩) (c ⟨., by omega⟩) = choiceValue (i.1 - 1) (v ⟨·, by omega⟩) := by
  --   sorry
  sorry
