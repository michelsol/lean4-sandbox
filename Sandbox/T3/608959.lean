import Mathlib

open Real Set

theorem algebra_608959
    (f : ℝ → ℝ)
    (hf : ∀ x, f x = if x < 1 / 2 then 2 * x else 2 - 2 * x) :
    ∫ x in (0)..1, √((deriv (f^[2012]) x)^2 + 1) = √(4 ^ 2012 + 1) := by

-- When there are $n$ copies of $f$, the graph consists of $2^{n}$ segments,
-- each of which goes $1 / 2^{n}$ units to the right, and alternately 1 unit up or down.
  have h1 (n : ℕ) (hn : n ≥ 1) (k : ℕ) (hk : k < 2 ^ (n - 1))
      (x : ℝ) (hx1 : x > -1 / 2 ^ n) (hx2 : x < 1 / 2 ^ n) :
      f^[n] (x + (2 * k + 1) / 2 ^ n) = if x < 0 then 1 + x * 2 ^ n else 1 - x * 2 ^ n := by
    revert n k x
    apply Nat.le_induction
    . intro k hk x hx1 hx2
      replace hk : k = 0 := by omega
      subst hk
      dsimp
      rw [hf]
      split_ifs with h2 h3 h3
      all_goals simp at h2 h3
      . ring
      . linarith
      . linarith
      . ring
    . intro n hn ih k hk x hx1 hx2
      rw [Function.iterate_succ_apply, hf]
      split_ifs with h2 h3 h3
      . calc
          _ = f^[n] (2 * x + (2 * k + 1) / 2 ^ n) := by ring_nf
          _ = _ := by
            specialize ih k sorry (2 * x) sorry sorry
            rw [ih]
            split_ifs with h4
            . ring
            . linarith
      . calc
          _ = f^[n] (2 * x + (2 * k + 1) / 2 ^ n) := by ring_nf
          _ = _ := by
            specialize ih k sorry (2 * x) sorry sorry
            rw [ih]
            split_ifs with h4
            . linarith
            . ring
      . calc
          _ = f^[n] (- 2 * x + 2 - (2 * k + 1) / 2 ^ n) := by ring_nf
          _ = f^[n] (- 2 * x + 2 ^ (n + 1) / 2 ^ n - (2 * k + 1) / 2 ^ n) := by
            congr 3
            symm
            calc
              (_ : ℝ) = 2 ^ (n + 1 : ℤ) / 2 ^ (n : ℤ) := by norm_cast
              (_ : ℝ) = 2 ^ ((n + 1) - n : ℤ) := by
                symm
                apply zpow_sub₀
                norm_num
              _ = _ := by ring_nf
          _ = f^[n] (- 2 * x + (2 * (2 ^ n - 1 - k : ℕ) + 1) / 2 ^ n) := by
            have c1 : 2 ^ n ≥ 1 := by sorry
            have c2 : 2 ^ n - 1 ≥ k := by sorry
            push_cast [c1, c2]
            ring_nf
          _ = _ := by
            specialize ih (2 ^ n - 1 - k) sorry (-2 * x) sorry sorry
            rw [ih]
            split_ifs with h4
            . linarith
            . ring
      . calc
          _ = f^[n] (- 2 * x + 2 - (2 * k + 1) / 2 ^ n) := by ring_nf
          _ = f^[n] (- 2 * x + 2 ^ (n + 1) / 2 ^ n - (2 * k + 1) / 2 ^ n) := by
            congr 3
            symm
            calc
              (_ : ℝ) = 2 ^ (n + 1 : ℤ) / 2 ^ (n : ℤ) := by norm_cast
              (_ : ℝ) = 2 ^ ((n + 1) - n : ℤ) := by
                symm
                apply zpow_sub₀
                norm_num
              _ = _ := by ring_nf
          _ = f^[n] (- 2 * x + (2 * (2 ^ n - 1 - k : ℕ) + 1) / 2 ^ n) := by
            have c1 : 2 ^ n ≥ 1 := by sorry
            have c2 : 2 ^ n - 1 ≥ k := by sorry
            push_cast [c1, c2]
            ring_nf
          _ = _ := by
            specialize ih (2 ^ n - 1 - k) sorry (-2 * x) sorry sorry
            rw [ih]
            split_ifs with h4
            . ring
            . replace h3 : x = 0 := by linarith
              subst h3
              simp

  have h2 (n : ℕ) (hn : n ≥ 1) (k : ℕ) (hk : k < 2 ^ (n - 1))
      (x : ℝ) (hx1 : x > k / 2 ^ (n - 1)) (hx2 : x < (k + 1) / 2 ^ (n - 1))
      : f^[n] x = if x < (2 * k + 1) / 2 ^ n
                then 1 + (x - (2 * k + 1) / 2 ^ n) * 2 ^ n
                else 1 - (x - (2 * k + 1) / 2 ^ n) * 2 ^ n := by
    specialize h1 n hn k hk (x - (2 * k + 1) / 2 ^ n) (by sorry) (by sorry)
    convert h1 using 1
    . congr 1
      ring
    . split_ifs with c1 c2 c2
      . ring
      . linarith
      . linarith
      . ring

  have h3 (n : ℕ) (hn : n ≥ 1) (k : ℕ) (hk : k < 2 ^ (n - 1))
      : ∀ x ∈ Ioo (k / 2 ^ (n - 1) : ℝ) ((k + 1 / 2) / 2 ^ (n - 1)), deriv f^[n] x = 2 ^ n := by
    intro x ⟨hx1, hx2⟩
    set a := (k / 2 ^ (n - 1) : ℝ)
    set b := ((k + 1 / 2) / 2 ^ (n - 1) : ℝ)
    calc
      deriv f^[n] x = derivWithin f^[n] (Ioo a b) x := by
        symm
        refine derivWithin_of_isOpen ?_ ?_
        . exact isOpen_Ioo
        . tauto
      _ = derivWithin (λ x : ℝ ↦ 1 + (x - (2 * k + 1) / 2 ^ n) * 2 ^ n) (Ioo a b) x := by
        suffices EqOn f^[n] (λ x : ℝ ↦ 1 + (x - (2 * k + 1) / 2 ^ n) * 2 ^ n) (Ioo a b) by
          exact derivWithin_congr this (this (by tauto))
        intro x ⟨hx1, hx2⟩
        specialize h2 n hn k hk x hx1 sorry
        split_ifs at h2 with h3
        . simpa using h2
        . exfalso
          sorry
      _ = deriv (λ x : ℝ ↦ 1 + (x - (2 * k + 1) / 2 ^ n) * 2 ^ n) x := by
        refine derivWithin_of_isOpen ?_ ?_
        . exact isOpen_Ioo
        . tauto
      _ = _ := by
        rw [deriv_add]
        . simp
        . fun_prop
        . fun_prop

  have h4 (n : ℕ) (hn : n ≥ 1) (k : ℕ) (hk : k < 2 ^ (n - 1))
      : ∀ x ∈ Ioo ((k + 1 / 2) / 2 ^ (n - 1) : ℝ) ((k + 1) / 2 ^ (n - 1)), deriv f^[n] x = -2 ^ n := by
    intro x ⟨hx1, hx2⟩
    set a := ((k + 1 / 2) / 2 ^ (n - 1) : ℝ)
    set b := ((k + 1) / 2 ^ (n - 1) : ℝ)
    calc
      deriv f^[n] x = derivWithin f^[n] (Ioo a b) x := by
        symm
        refine derivWithin_of_isOpen ?_ ?_
        . exact isOpen_Ioo
        . tauto
      _ = derivWithin (λ x : ℝ ↦ 1 - (x - (2 * k + 1) / 2 ^ n) * 2 ^ n) (Ioo a b) x := by
        suffices EqOn f^[n] (λ x : ℝ ↦ 1 - (x - (2 * k + 1) / 2 ^ n) * 2 ^ n) (Ioo a b) by
          exact derivWithin_congr this (this (by tauto))
        intro x ⟨hx1, hx2⟩
        specialize h2 n hn k hk x sorry hx2
        split_ifs at h2 with h3
        . exfalso
          sorry
        . simpa using h2
      _ = deriv (λ x : ℝ ↦ 1 - (x - (2 * k + 1) / 2 ^ n) * 2 ^ n) x := by
        refine derivWithin_of_isOpen ?_ ?_
        . exact isOpen_Ioo
        . tauto
      _ = _ := by
        rw [deriv_sub]
        . simp
        . fun_prop
        . fun_prop


-- So, the length is $$ 2^{n} \sqrt{1+\frac{1}{2^{2 n}}}=\sqrt{4^{n}+1} $$
-- Taking $n=2012$, the answer is $$ \sqrt{4^{2012}+1} $$
  have hn : 2012 ≥ 1 := by norm_num
  generalize 2012 = n at hn ⊢
  specialize h3 n hn
  specialize h4 n hn

  let A (k : ℕ) := Ioo (k / 2 ^ (n - 1) : ℝ) ((k + 1 / 2) / 2 ^ (n - 1))
  let B (k : ℕ) := Ioo ((k + 1 / 2) / 2 ^ (n - 1) : ℝ) ((k + 1) / 2 ^ (n - 1))

  calc
    ∫ x in (0)..1, √(deriv f^[n] x ^ 2 + 1) = ∫ x in Ioc 0 1, √(deriv f^[n] x ^ 2 + 1) := by
      simp [intervalIntegral]
    _ = ∫ x in ⋃ k ∈ Finset.Ico (0 : ℕ) (2 ^ (n - 1)), A k ∪ B k, √(deriv f^[n] x ^ 2 + 1) := by
      sorry
    _ = ∑ k ∈ Finset.Ico (0 : ℕ) (2 ^ (n - 1)), ∫ x in A k ∪ B k, √(deriv f^[n] x ^ 2 + 1) := by
      apply MeasureTheory.integral_finset_biUnion
      . sorry
      . sorry
      . sorry
    _ = ∑ k ∈ Finset.Ico (0 : ℕ) (2 ^ (n - 1)),
      ((∫ x in A k, √(deriv f^[n] x ^ 2 + 1)) + ∫ x in B k, √(deriv f^[n] x ^ 2 + 1)) := by
      apply Finset.sum_congr rfl
      intro k hk
      apply MeasureTheory.setIntegral_union
      . sorry
      . sorry
      . sorry
      . sorry
    _ = ∑ k ∈ Finset.Ico (0 : ℕ) (2 ^ (n - 1)),
      ((∫ x in A k, √(1 + 4 ^ n)) + ∫ x in B k, √(1 + 4 ^ n)) := by
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      . apply MeasureTheory.setIntegral_congr_fun₀
        . exact nullMeasurableSet_Ioo
        . intro x hx
          beta_reduce
          congr 1
          calc
              deriv f^[n] x ^ 2 + 1 = (2 ^ n) ^ 2 + 1 := by
                specialize h3 k (by simpa using hk) x hx
                rw [h3]
              _ = (2 ^ 2) ^ n + 1 := by
                congr 1
                apply pow_right_comm
              _ = _ := by ring
      . apply MeasureTheory.setIntegral_congr_fun₀
        . exact nullMeasurableSet_Ioo
        . intro x hx
          beta_reduce
          congr 1
          calc
              deriv f^[n] x ^ 2 + 1 = (2 ^ n) ^ 2 + 1  := by
                specialize h4 k (by simpa using hk) x hx
                rw [h4]
                ring
              _ = (2 ^ 2) ^ n + 1 := by
                congr 1
                apply pow_right_comm
              _ = _ := by ring
    _ = ∑ k ∈ Finset.Ico (0 : ℕ) (2 ^ (n - 1)),
      ((1 / 2 ^ n * √(1 + 4 ^ n)) + (1 / 2 ^ n * √(1 + 4 ^ n))) := by
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      . sorry
      . sorry
    _ = ∑ k ∈ Finset.Ico (0 : ℕ) (2 ^ (n - 1)), (1 / 2 ^ (n - 1) * √(1 + 4 ^ n)) := by
      apply Finset.sum_congr rfl
      intro k hk
      sorry
    _ = ((2 ^ (n - 1)) * 1 / 2 ^ (n - 1)) * √(1 + 4 ^ n) := by simp
    _ = (1) * √(1 + 4 ^ n) := by simp
    _ = √(4 ^ n + 1) := by ring_nf
