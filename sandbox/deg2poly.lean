import Mathlib

structure deg2poly (R : Type) [Field R] [Pow R R] where
  a : R
  b : R
  c : R
  a_ne_zero : a ≠ 0

namespace deg2poly

variable {R : Type} [Field R] [Pow R R] (p : deg2poly R)

noncomputable def sqrt (a : R) := a ^ (2 : R)⁻¹

def eval x := p.a * x ^ 2 + p.b * x + p.c

def Δ := p.b ^ 2 - 4 * p.a * p.c

noncomputable def x1 := (-p.b + sqrt p.Δ) / (2 * p.a)

noncomputable def x2 := (-p.b - sqrt p.Δ) / (2 * p.a)

theorem eq_expanded_form (x : R) : p.eval x = p.a * x ^ 2 + p.b * x + p.c := by rfl

theorem eq_factored_form [CharZero R] (x : R) :
    p.eval x = p.a * (x - p.x1) * (x - p.x2) := by
  symm
  calc
    _ = p.a * x ^ 2 + p.a * (-p.x1 - p.x2) * x + p.a * p.x1 * p.x2 := by ring
    _ = _ := by
      congr 3
      · unfold x1 x2
        ring_nf
        field_simp [p.a_ne_zero]
      · calc
          _ = ((-p.b + sqrt p.Δ) * (-p.b - sqrt p.Δ)) * (p.a / (4 * p.a ^ 2)) := by
            unfold x1 x2
            ring
          _ = (p.b ^ 2 - sqrt p.Δ ^ 2) * (1 / (4 * p.a)) := by
            congr 1
            · ring
            · field_simp
          _ = (p.b ^ 2 - p.Δ) * (1 / (4 * p.a)) := by
            congr 2
            unfold sqrt
            sorry
          _ = (4 * p.a * p.c) / (4 * p.a) := by
            unfold Δ
            ring
          _ = _ := by
            field_simp [p.a_ne_zero]
    _ = _ := (p.eq_expanded_form x).symm

end deg2poly


#exit
example (a b c : ℝ) (ha : a ≠ 0) (x : ℝ) (hx : a * x ^ 2 + b * x + c = 0)
  (hΔ : b ^ 2 - 4 * a * c ≥ 0) :
    let Δ := b ^ 2 - 4 * a * c
    let x1 := (-b + √Δ) / (2 * a)
    let x2 := (-b - √Δ) / (2 * a)
    x = x1 ∨ x = x2 := by
  intro Δ x1 x2
  convert_to a * (x - x1) * (x - x2) = 0 using 1 at hx
  · symm
    calc
      _ = a * x ^ 2 + a * (-x1 - x2) * x + a * x1 * x2 := by ring
      _ = _ := by
        congr 3
        · unfold x1 x2
          ring_nf
          field_simp
        · calc
            _ = ((-b + √Δ) * (-b - √Δ)) * (a / (4 * a ^ 2)) := by ring
            _ = (b ^ 2 - √Δ ^ 2) * (1 / (4 * a)) := by
              congr 1
              · ring
              · field_simp
            _ = (b ^ 2 - Δ) * (1 / (4 * a)) := by
              congr 2
              exact Real.sq_sqrt hΔ
            _ = (4 * a * c) / (4 * a) := by ring
            _ = _ := by field_simp
  obtain hx | hx : x - x1 = 0 ∨ x - x2 = 0 := by simpa [ha] using hx
  · left
    linarith only [hx]
  · right
    linarith only [hx]


noncomputable def Complex.sqrt (a : ℂ) : ℂ := a ^ (2 : ℂ)⁻¹

open Complex in
example (a b c : ℂ) (ha : a ≠ 0) (x : ℂ) (hx : a * x ^ 2 + b * x + c = 0) :
    let Δ : ℂ := b ^ 2 - 4 * a * c
    let x1 := (-b + sqrt Δ) / (2 * a)
    let x2 := (-b - sqrt Δ) / (2 * a)
    x = x1 ∨ x = x2 := by
  intro Δ x1 x2
  convert_to a * (x - x1) * (x - x2) = 0 using 1 at hx
  · symm
    calc
      _ = a * x ^ 2 + a * (-x1 - x2) * x + a * x1 * x2 := by ring
      _ = _ := by
        congr 3
        · unfold x1 x2
          ring_nf
          field_simp
        · calc
            _ = ((-b + sqrt Δ) * (-b - sqrt Δ)) * (a / (4 * a ^ 2)) := by ring
            _ = (b ^ 2 - sqrt Δ ^ 2) * (1 / (4 * a)) := by
              congr 1
              · ring
              · field_simp
            _ = (b ^ 2 - Δ) * (1 / (4 * a)) := by
              congr 2
              simp [sqrt]
            _ = (4 * a * c) / (4 * a) := by ring
            _ = _ := by field_simp
  obtain hx | hx : x - x1 = 0 ∨ x - x2 = 0 := by simpa [ha] using hx
  · left
    linear_combination hx
  · right
    linear_combination hx
