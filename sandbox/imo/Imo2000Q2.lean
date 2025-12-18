/-
Copyright (c) 2024 Julien Michel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julien Michel
-/
import Mathlib

theorem am_gm (m n p : ℝ) (hm : m ≥ 0) (hn : n ≥ 0) (hp : p ≥ 0) :
    m * n * p ≤ (m + n) * 2⁻¹ * (n + p) * 2⁻¹ * (p + m) * 2⁻¹ := by
  have half_ge_0 : (2 : ℝ)⁻¹ ≥ 0 := by norm_num
  have h1 := Real.geom_mean_le_arith_mean2_weighted half_ge_0 half_ge_0 hm hn (by norm_num)
  have h2 := Real.geom_mean_le_arith_mean2_weighted half_ge_0 half_ge_0 hn hp (by norm_num)
  have h3 := Real.geom_mean_le_arith_mean2_weighted half_ge_0 half_ge_0 hp hm (by norm_num)
  have := mul_le_mul_of_nonneg h1 h2 (by positivity) (by positivity)
  have := mul_le_mul_of_nonneg this h3 (by positivity) (by positivity)
  conv at this =>
    lhs
    ring
    simp [←Real.rpow_mul_natCast hm]
    simp [←Real.rpow_mul_natCast hn]
    simp [←Real.rpow_mul_natCast hp]
  linarith


theorem reformulation (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) :
    (-x + y + z) * (x - y + z) * (x + y - z) ≤ x * y * z := by
  have : x * y * z > 0 := by positivity
  by_cases h1 : (-x + y + z) ≥ 0
  case neg =>
    have : -(-x + y + z) > 0 := by linarith
    have : (x - y + z) > 0 := by linarith
    have : (x + y - z) > 0 := by linarith
    have :  -(-x + y + z) * (x - y + z) * (x + y - z) > 0 := by positivity
    linarith
  by_cases h2 : (x - y + z) ≥ 0
  case neg =>
    have : (-x + y + z) > 0 := by linarith
    have : -(x - y + z) > 0 := by linarith
    have : (x + y - z) > 0 := by linarith
    have :  (-x + y + z) * -(x - y + z) * (x + y - z) > 0 := by positivity
    linarith
  by_cases h3 : (x + y - z) ≥ 0
  case neg =>
    have : (-x + y + z) > 0 := by linarith
    have : (x - y + z) > 0 := by linarith
    have : -(x + y - z) > 0 := by linarith
    have :  (-x + y + z) * (x - y + z) * -(x + y - z) > 0 := by positivity
    linarith
  let m := -x + y + z
  let n := x - y + z
  let p := x + y - z
  show m * n * p ≤ _
  have : x = (p + n) * 2⁻¹ := by linarith
  rw [this]
  have : y = (m + p) * 2⁻¹ := by linarith
  rw [this]
  have : z = (m + n) * 2⁻¹ := by linarith
  rw [this]
  have := am_gm m n p h1 h2 h3
  linarith

theorem imo2000_q2 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b *c = 1) :
    (a - 1 + b⁻¹) * (b - 1 + c⁻¹) * (c - 1 + a⁻¹) ≤ 1 := by
  have ha' : a ≠ 0 := (ne_of_lt ha).symm
  have hb' : b ≠ 0 := (ne_of_lt hb).symm
  have hc' : c ≠ 0 := (ne_of_lt hc).symm
  have hab' : a * b ≠ 0 := mul_ne_zero ha' hb'
  have : c = (a*b)⁻¹ := (DivisionMonoid.inv_eq_of_mul (a * b) c h).symm
  subst this
  rw [inv_inv]
  rw [←mul_le_mul_right hb]
  conv =>
    lhs
    rw [mul_comm, ←mul_assoc, ←mul_assoc]
    lhs; lhs
    simp [mul_add, mul_sub, hb']
  rw [←mul_le_mul_right ha]
  rw [←mul_le_mul_right hb]
  conv =>
    lhs
    rw [mul_assoc, mul_assoc]
    rhs
    simp [add_mul, sub_mul, -mul_inv_rev, hab', ha']
  have := reformulation (a*b) b 1 (mul_pos ha hb) hb (by simp)
  linarith
