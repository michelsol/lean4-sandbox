import Mathlib

set_option quotPrecheck false in
notation "∑' " x " in " s ", " r => ∑' x, if x ∈ s then r else 0

open Set ENNReal Classical
theorem tsum_union {β} (s t : Set β) (f : β → ENNReal) (hs : Disjoint s t) :
  (∑' x in s ∪ t, f x) = (∑' x in s, f x) + (∑' x in t, f x) := by
  rw [← ENNReal.tsum_add]
  grind only [mem_union, disjoint_left, zero_add, add_zero]

-- example (n : ℕ) : ∑' k in Icc 1 n, (k : ℝ≥0∞) = 0 := by
--   sorry
