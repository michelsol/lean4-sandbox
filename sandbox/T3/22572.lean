import Mathlib

open Real Complex Finset Polynomial

/- What is the smallest positive integer $n$ such that all the roots of $z^4 + z^2 + 1 = 0$ are
$n^{\text{th}}$ roots of unity? -/
theorem calculus_22572 :
  IsLeast {n : ℕ | n > 0 ∧ ∀ z : ℂ, z ^ 4 + z ^ 2 + 1 = 0 → ∃ k : ℕ, z = cexp (I * 2 * π * k / n)} 6 := by

-- Multiplying the equation $z^4 + z^2 + 1 = 0$ by $z^2 - 1 = (z - 1)(z + 1)$, we get $z^6 - 1 = 0$.
-- Therefore, every root of $z^4 + z^2 + 1 = 0$ is a sixth root of unity which is not 1 nor -1.

  have h1 (z : ℂ) : z ^ 4 + z ^ 2 + 1 = ∏ k ∈ ({1, 2, 4, 5} : Finset ℕ), (z - cexp (I * 2 * π * k / 6)) := by
    revert z
    suffices X ^ 4 + X ^ 2 + C 1 = ∏ k ∈ ({1, 2, 4, 5} : Finset ℕ), (X - C (cexp (I * 2 * π * k / 6))) by
      intro z
      apply_fun Polynomial.eval z at this
      simpa using this
    apply_fun (. * ((X - C 1) * (X + C 1)))
    swap
    · apply mul_left_injective₀
      apply leadingCoeff_ne_zero.mp
      rw [leadingCoeff_mul, leadingCoeff_X_add_C, leadingCoeff_X_sub_C]
      norm_num
    beta_reduce
    calc
    (_ : ℂ[X]) = X ^ 6 - C 1 := by
      ring_nf
      simp
    _ = X ^ 6 - 1 := by simp
    _ = ∏ c ∈ nthRootsFinset 6 ℂ, (X - C c) := by
      have c1 : IsPrimitiveRoot (cexp (I * 2 * π / 6)) 6 := by
        apply (IsPrimitiveRoot.iff (by norm_num)).mpr
        split_ands
        · have exp_pow_nat (z : ℂ) (n : ℕ) : exp z ^ n = exp (z * n) := by
            induction' n with n ih
            · simp
            · calc
              _ = exp z ^ n * exp z := by rfl
              _ = exp (z * n) * exp z := by rw [ih]
              _ = exp (z * n + z) := by rw [Complex.exp_add]
              _ = _ := by
                push_cast
                ring_nf
          calc
          cexp (I * 2 * π / 6) ^ 6 = cexp (I * 2 * π) := by simp [exp_pow_nat]
          _ = _ := by
            refine Complex.exp_eq_one_iff.mpr ?_
            use 1
            ring
        · intro l hl1 hl2
          sorry
      exact X_pow_sub_one_eq_prod (by norm_num) c1
    _ = ∏ c ∈ ((Ico 0 6).image fun k : ℕ ↦ cexp (I * 2 * π * k / 6)), (X - C c) := by
      congr 1
      ext z
      suffices z ^ 6 = 1 ↔ (∃ (k : ℕ), k < 6 ∧ cexp (I * 2 * π * k / 6) = z) by simpa using this
      suffices z ^ 6 = 1 ↔ (∃ (k : ℤ), cexp (I * 2 * π * k / 6) = z) by
        rw [this]
        constructor
        · intro ⟨k, c1⟩
          use (k % 6).toNat, by omega
          calc
          cexp (I * 2 * π * ((k % 6).toNat : ℤ) / 6) = cexp (I * 2 * π * (k - (k / 6) * 6 : ℤ) / 6) := by
            congr 4
            omega
          _ = cexp (I * 2 * π * k / 6 - I * 2 * π * (((k / 6) * 6 : ℤ) / 6)) := by
            congr 1
            push_cast
            ring
          _ = cexp (I * 2 * π * k / 6 - I * 2 * π * (k / 6 : ℤ)) := by
            congr 3
            simp
          _ = cexp (I * 2 * π * k / 6) / cexp (I * 2 * π * (k / 6 : ℤ)) := by rw [Complex.exp_sub]
          _ = cexp (I * 2 * π * k / 6) / 1 := by
            congr 1
            refine Complex.exp_eq_one_iff.mpr ?_
            use (k / 6 : ℤ)
            ring
          _ = _ := by simpa using c1
        · intro ⟨k, c1⟩
          use k, c1.right
      constructor
      · intro c1
        have c2 := c1
        apply_fun (fun x => (arg x : Angle)) at c2

        have arg_pow_coe_angle (z : ℂ) (hz : z ≠ 0) (n : ℕ) : (arg (z ^ n) : Angle) = n • arg z := by
          induction' n with n ih
          · simp
          · calc
            (_ : Angle) = arg (z ^ n * z) := by rfl
            _ = arg (z ^ n) + arg z := by
              rw [Complex.arg_mul_coe_angle]
              · exact pow_ne_zero n hz
              · exact hz
            _ = n • arg z + arg z := by rw [ih]
            _ = _ := by module

        rw [arg_pow_coe_angle] at c2
        · norm_cast at c2
          erw [QuotientAddGroup.eq_iff_sub_mem] at c2
          rw [AddSubgroup.mem_zmultiples_iff] at c2
          obtain ⟨k, c2⟩ := c2
          convert_to 2 * π * k = 6 * z.arg using 1 at c2
          · simp; ring
          · simp
          use k
          sorry
        · exact right_ne_zero_of_mul_eq_one c1
      · sorry
    _ = ∏ k ∈ Ico (0 : ℕ) 6, (X - C (cexp (I * 2 * π * k / 6))) := by
      rw [prod_nbij fun k : ℕ ↦ cexp (I * 2 * π * k / 6)]
      · intro k hk
        simp only [mem_image]
        use k
      · intro i hi j hj hij
        simp at hi hj
        beta_reduce at hij
        rw [exp_eq_exp_iff_exists_int] at hij
        obtain ⟨k, hij⟩ := hij
        sorry
      · intro y hy
        obtain ⟨k, hk, hy⟩ := by simpa using hy
        simp only [Set.mem_image]
        use k
        simp [hk, hy]
      · simp
    _ = _ := by
      sorry

  have h2 (z : ℂ) :
      z ^ 4 + z ^ 2 + 1 = 0 ↔ ∃ k ∈ ({1, 2, 4, 5} : Finset ℕ), z = cexp (I * 2 * π * k / 6) := by
    rw [h1 z, prod_eq_zero_iff]
    constructor
    all_goals
      intro ⟨k, h2, h3⟩
      use k, h2
      linear_combination h3

-- The complex number $e^{2 \pi i/6}$ is a primitive sixth root of unity,
-- so by definition, the smallest positive integer $n$ such that $(e^{2 \pi i/6})^n = 1$ is 6.
-- Therefore, the smallest possible value of $n$ is $\boxed{6}$.
  constructor
  · split_ands
    · norm_num
    · intro z hz
      specialize h2 z
      obtain ⟨k, c1, c2⟩ := h2.mp hz
      use k, c2
  · intro n ⟨c1, c2⟩
    specialize c2 (cexp (I * 2 * π / 6))
    rw [h2] at c2
    specialize c2 (by use 1, by simp, by simp)
    obtain ⟨k, c2⟩ := c2
    replace c2 := exp_eq_exp_iff_exists_int.mp c2
    obtain ⟨m, c2⟩ := c2
    apply_fun (. * 6 * n / I / (π : ℂ)) at c2
    ring_nf at c2
    convert_to (2 * n : ℂ) = 12 * k + 12 * m * n using 1 at c2
    . calc
      _ = (I * I⁻¹) * (π * (π : ℂ)⁻¹) * 2 * n := by ring
      _ = _ := by
        norm_cast
        field_simp
    . congr 1
      · calc
        _ = (I * I⁻¹) * (π * (π : ℂ)⁻¹) * (n * (n : ℂ)⁻¹) * 12 * k := by ring
        _ = _ := by
          have d1 : (n : ℂ) ≠ 0 := by
            norm_cast
            omega
          norm_cast
          field_simp
      · calc
        _ = (I * I⁻¹) * (π * (π : ℂ)⁻¹) * 12 * m * n  := by ring
        _ = _ := by
          norm_cast
          field_simp
    convert_to 2 * n = 12 * k + 12 * m * n using 1 at c2
    · norm_cast

    replace c2 : (2 - 12 * m) * n = 12 * k := by linarith
    have c3 : 3 ∣ (2 - 12 * m) * n := by
      rw [c2]
      omega
    replace c3 : (3 : ℤ) ∣ n := by
      apply IsCoprime.dvd_of_dvd_mul_left ?_ c3
      rw [Prime.coprime_iff_not_dvd]
      · omega
      · simp
        decide

    suffices n ≠ 3 by omega
    by_contra! c4
    subst c4
    omega
