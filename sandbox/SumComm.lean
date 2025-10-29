import Mathlib

open Finset

-- swap sum over Icc's

theorem sum_Icc_Icc_comm {M : Type _} [AddCommMonoid M] (a b : ℕ) (f : ℕ → ℕ → M) :
  (∑ i ∈ Icc a b, ∑ j ∈ Icc i b, f i j) =
    ∑ j ∈ Icc a b, ∑ i ∈ Icc a j, f i j := sum_Ico_Ico_comm a (b + 1) f

theorem sum_Icc_Icc_comm' {M : Type _} [AddCommMonoid M] (a b : ℕ) (f : ℕ → ℕ → M) :
  (∑ i ∈ Icc a b, ∑ j ∈ Icc (i + 1) b, f i j) =
    ∑ j ∈ Icc a b, ∑ i ∈ Ico a j, f i j := sum_Ico_Ico_comm' a (b + 1) f


-- expand a sum of squares

theorem sq_sum_eq_sum_sq_add (x : ℕ → ℝ) (a b : ℕ) : (∑ i ∈ Icc a b, x i) ^ 2 =
    (∑ i ∈ Icc a b, x i ^ 2) + 2 * ∑ i ∈ Icc a b, ∑ j ∈ Icc (i + 1) b, x i * x j := calc
    _ = ∑ i ∈ Icc a b, ∑ j ∈ Icc a b, x i * x j := by rw [sq, sum_mul_sum]
    _ = ∑ i ∈ Icc a b, (∑ j ∈ Ico a i, x i * x j + x i * x i + ∑ j ∈ Icc (i + 1) b, x i * x j) := by
      apply sum_congr rfl
      intro i hi
      have : Icc a b = Ico a i ∪ {i} ∪ Icc (i + 1) b := by ext x; simp at hi ⊢; omega
      rw [this]
      iterate 2 rw [sum_union (by
        intro s hs1 hs2 t hts; specialize hs1 hts; specialize hs2 hts; simp at hs1 hs2 ⊢; omega)]
      simp
    _ = ∑ i ∈ Icc a b, ∑ j ∈ Ico a i, x i * x j
        + ∑ i ∈ Icc a b, x i * x i + ∑ i ∈ Icc a b, ∑ j ∈ Icc (i + 1) b, x i * x j := by
      simp [sum_add_distrib]
    _ = _ := by
      have : ∑ i ∈ Icc a b, x i * x i = ∑ i ∈ Icc a b, x i ^ 2 := by
        apply sum_congr rfl; intro i hi; ring_nf
      rw [this]
      have : ∑ i ∈ Icc a b, ∑ j ∈ Ico a i, x i * x j
          = ∑ j ∈ Icc a b, ∑ i ∈ Icc (j + 1) b, x j * x i := calc
        _ = ∑ j ∈ Icc a b, ∑ i ∈ Icc (j + 1) b, x i * x j := by
          exact Eq.symm (sum_Icc_Icc_comm' a b fun i j => x j * x i)
        _ = _ := by apply sum_congr rfl; intro j hj; apply sum_congr rfl; intro i hi; ring_nf
      rw [this]
      linarith
