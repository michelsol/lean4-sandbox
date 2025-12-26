import Mathlib

open Real

/-
Prove that for all positive real numbers $a,b,c$
$$\dfrac{a}{\sqrt{a^2+8bc}}+\dfrac{b}{\sqrt{b^2+8ca}}+\dfrac{c}{\sqrt{c^2+8ab}} \ge 1$$
-/

theorem algebra_25094 (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 ≤
    a / sqrt (a ^ 2 + 8 * b * c) + b / sqrt (b ^ 2 + 8 * c * a) + c / sqrt (c ^ 2 + 8 * a * b) :=
  have h1 {a b c} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
      1 ≤ a ^ 3 / sqrt ((a ^ 3) ^ 2 + 8 * b ^ 3 * c ^ 3) +
        b ^ 3 / sqrt ((b ^ 3) ^ 2 + 8 * c ^ 3 * a ^ 3) +
          c ^ 3 / sqrt ((c ^ 3) ^ 2 + 8 * a ^ 3 * b ^ 3) :=
    have bound {a b c} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
        a ^ 4 / (a ^ 4 + b ^ 4 + c ^ 4) ≤ a ^ 3 / sqrt ((a ^ 3) ^ 2 + 8 * b ^ 3 * c ^ 3) := by
      rw [div_le_div_iff (by positivity) (by positivity)]
      calc a ^ 4 * sqrt ((a ^ 3) ^ 2 + (8:ℝ) * b ^ 3 * c ^ 3)
          = a ^ 3 * (a * sqrt ((a ^ 3) ^ 2 + (8:ℝ) * b ^ 3 * c ^ 3)) := by ring
        _ ≤ a ^ 3 * (a ^ 4 + b ^ 4 + c ^ 4) := ?_
      gcongr
      apply le_of_pow_le_pow_left two_ne_zero (by positivity)
      rw [mul_pow, sq_sqrt (by positivity), ← sub_nonneg]
      calc
        (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 - a ^ 2 * ((a ^ 3) ^ 2 + 8 * b ^ 3 * c ^ 3)
          = 2 * (a ^ 2 * (b ^ 2 - c ^ 2)) ^ 2 + (b ^ 4 - c ^ 4) ^ 2 +
            (2 * (a ^ 2 * b * c - b ^ 2 * c ^ 2)) ^ 2 := by ring
        _ ≥ 0 := by positivity
    have H : a ^ 4 + b ^ 4 + c ^ 4 ≠ 0 := by positivity
    calc
      _ ≥ _ := add_le_add (add_le_add (bound ha hb hc) (bound hb hc ha)) (bound hc ha hb)
      _ = 1 := by ring_nf at H ⊢; field_simp
  have h3 : ∀ {x : ℝ}, 0 < x → (x ^ (3 : ℝ)⁻¹) ^ 3 = x := by
    intro x hx
    have := rpow_inv_natCast_pow hx.le three_ne_zero
    norm_num at this ⊢
    simpa
  calc
    1 ≤ _ := h1 (rpow_pos_of_pos ha _) (rpow_pos_of_pos hb _) (rpow_pos_of_pos hc _)
    _ = _ := by rw [h3 ha, h3 hb, h3 hc]
