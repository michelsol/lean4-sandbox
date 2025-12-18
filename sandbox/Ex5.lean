import Mathlib


open Filter
open Topology
open Finset

theorem stolz_cesaro_infty_case_1
  (a b : ℕ → ℝ) (hb1 : StrictMono b) (hb2 : Tendsto b atTop atTop) (l : ℝ)
  (h1 : Tendsto (fun n => (a (n + 1) - a n) / (b (n + 1) - b n)) atTop (𝓝 l))
  : Tendsto (fun n => a n / b n) atTop (𝓝 l) := by

  replace h1 : ∀ ε > 0, ∃ ν > 0, ∀ n > ν, |(a (n + 1) - a n) / (b (n + 1) - b n) - l| < ε / 2 := by
    rw [Metric.tendsto_atTop] at h1
    intro ε hε
    specialize h1 (ε / 2) (by positivity)
    obtain ⟨N, h1⟩ := h1
    use N + 1, by omega
    intro n hn
    specialize h1 n (by omega)
    convert h1 using 1

  replace h1 : ∀ ε > 0, ∃ ν > 0, ∀ n > ν,
      l - ε / 2 < (a (n + 1) - a n) / (b (n + 1) - b n) ∧
      (a (n + 1) - a n) / (b (n + 1) - b n) < l + ε / 2 := by
    intro ε hε
    specialize h1 ε hε
    obtain ⟨ν, h1, h2⟩ := h1
    use ν, h1
    intro n hn
    specialize h2 n hn
    rw [abs_lt] at h2
    split_ands
    all_goals linarith

  have h2 : ∀ ε > 0, ∃ ν > 0, ∀ n > ν,
      (l - ε / 2) * (b (n + 1) - b n) < a (n + 1) - a n ∧
      a (n + 1) - a n < (l + ε / 2) * (b (n + 1) - b n) := by
    intro ε hε
    specialize h1 ε hε
    obtain ⟨ν, h1, h2⟩ := h1
    use ν, h1
    intro n hn
    specialize h2 n hn
    obtain ⟨h2, h3⟩ := h2
    have h4 : b (n + 1) - b n > 0 := by
      apply sub_pos.mpr
      apply hb1
      omega
    split_ands
    · field_simp at h2 ⊢
      convert h2 using 1
    · field_simp at h3 ⊢
      convert h3 using 1

  have h3 (ν n : ℕ) (hν : ν > 0) (hn : n > ν) :
      a n = ∑ k ∈ Ico (ν + 1) n, (a (k + 1) - a k) + a (ν + 1) := by
    convert_to a n = (a n - a (ν + 1)) + a (ν + 1) using 2
    · apply sum_Ico_sub
      exact hn
    linarith

  have h4 : ∀ ε > 0, ∃ ν > 0, ∀ n > ν + 1,
      (l - ε / 2) * (b n - b (ν + 1)) + a (ν + 1) < a n ∧
      a n < (l + ε / 2) * (b n - b (ν + 1)) + a (ν + 1) := by
    intro ε hε
    specialize h2 ε hε
    obtain ⟨ν, hν, h2⟩ := h2
    use ν, hν
    intro n hn
    specialize h3 ν n hν (by omega)
    split_ands
    · calc
      _ = (l - ε / 2) * ∑ k ∈ Ico (ν + 1) n, (b (k + 1) - b k) + a (ν + 1) := by
        congr 2
        rw [sum_Ico_sub]
        omega
      _ = ∑ k ∈ Ico (ν + 1) n, (l - ε / 2) * (b (k + 1) - b k) + a (ν + 1) := by
        congr 1
        rw [mul_sum]
      _ < ∑ k ∈ Ico (ν + 1) n, (a (k + 1) - a k) + a (ν + 1) := by
        gcongr 2 with k hk
        · simp; omega
        simp at hk
        specialize h2 k (by omega)
        linarith
      _ = _ := h3.symm
    · calc
      _ = _ := h3
      _ < ∑ k ∈ Ico (ν + 1) n, (l + ε / 2) * (b (k + 1) - b k) + a (ν + 1) := by
        gcongr 2 with k hk
        · simp; omega
        simp at hk
        specialize h2 k (by omega)
        linarith
      _ = (l + ε / 2) * ∑ k ∈ Ico (ν + 1) n, (b (k + 1) - b k) + a (ν + 1) := by
        congr 1
        rw [mul_sum]
      _ = _ := by
        congr 2
        rw [sum_Ico_sub]
        omega

  obtain ⟨n0, hn0, h5⟩ : ∃ n0 > 0, ∀ n > n0, b n > 0 := by
    rw [tendsto_atTop_atTop] at hb2
    specialize hb2 1
    obtain ⟨n0, hb2⟩ := hb2
    use n0 ⊔ 1
    split_ands
    · omega
    · intro n hn
      specialize hb2 n (by omega)
      linarith

  let c ε ν n := (a (ν + 1) - b (ν + 1) * (l - ε / 2)) / b n
  let d ε ν n := (a (ν + 1) - b (ν + 1) * (l + ε / 2)) / b n

  have h6 : ∀ ε > 0, ∃ ν > 0, ∀ n > (ν + 1) ⊔ n0,
      (l - ε / 2) + c ε ν n < a n / b n ∧ a n / b n < (l + ε / 2) + d ε ν n
        := by
    intro ε hε
    unfold c d
    specialize h4 ε hε
    obtain ⟨ν, hν, h4⟩ := h4
    use ν
    split_ands
    · omega
    · intro n hn
      specialize h4 n (by omega)
      obtain ⟨c1, c2⟩ := h4
      specialize h5 n (by omega)
      split_ands
      all_goals
        field_simp
        linarith

  have h7 ν : ∀ ε > 0, ∃ n1, ∀ n ≥ n1, |c ε ν n| < ε / 2 := by
    intro ε hε
    unfold c
    rw [tendsto_atTop_atTop] at hb2
    specialize hb2 (|a (ν + 1) - b (ν + 1) * (l - ε / 2)| / (ε / 2) + 1)
    obtain ⟨n1, hb2⟩ := hb2
    use n1 ⊔ (n0 + 1)
    intro n hn
    specialize hb2 n (by omega)
    specialize h5 n (by omega)
    rw [abs_div, abs_eq_self.mpr h5.le]
    field_simp at hb2 ⊢
    linarith

  have h8 ν : ∀ ε > 0, ∃ n2, ∀ n ≥ n2, |d ε ν n| < ε / 2 := by
    intro ε hε
    unfold d
    rw [tendsto_atTop_atTop] at hb2
    specialize hb2 (|a (ν + 1) - b (ν + 1) * (l + ε / 2)| / (ε / 2) + 1)
    obtain ⟨n2, hb2⟩ := hb2
    use n2 ⊔ (n0 + 1)
    intro n hn
    specialize hb2 n (by omega)
    specialize h5 n (by omega)
    rw [abs_div, abs_eq_self.mpr h5.le]
    field_simp at hb2 ⊢
    linarith

  have h9 : ∀ ε > 0, ∃ ν > 0, ∀ n > ν,
      l - ε < a n / b n ∧ a n / b n < l + ε := by
    intro ε hε
    specialize h6 ε hε
    obtain ⟨ν, hν, h6⟩ := h6
    specialize h7 ν ε hε
    obtain ⟨n1, h7⟩ := h7
    specialize h8 ν ε hε
    obtain ⟨n2, h8⟩ := h8
    use (ν + 1) ⊔ n0 ⊔ n1 ⊔ n2, by omega
    intro n hn
    specialize h6 n (by omega)
    obtain ⟨h6, h6'⟩ := h6
    specialize h7 n (by omega)
    specialize h8 n (by omega)
    rw [abs_lt] at h7 h8
    split_ands
    all_goals linarith

  replace h9 : ∀ ε > 0, ∃ ν > 0, ∀ n > ν,
      -ε < a n / b n - l ∧ a n / b n - l < ε := by
    convert h9 using 8 with ε hε ν n hn
    all_goals
      constructor
      all_goals
        intro _
        linarith

  rw [Metric.tendsto_atTop]
  intro ε hε
  specialize h9 ε hε
  obtain ⟨ν, hν, h9⟩ := h9
  use ν + 1
  intro n hn
  specialize h9 n (by omega)
  rw [dist_eq_norm, Real.norm_eq_abs, abs_lt]
  split_ands
  all_goals linarith
