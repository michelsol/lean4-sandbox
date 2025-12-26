import Mathlib

open Finset Polynomial

/-
Let $r_{1}, r_{2}, \ldots, r_{7}$ be the distinct complex roots of the polynomial $P(x)=x^{7}-7$. Let
$$
K=\prod_{1 \leq i < j \leq 7}\left(r_{i}+r_{j}\right)
$$
that is, the product of all numbers of the form $r_{i}+r_{j}$,
where $i$ and $j$ are integers for which $1 \leq i < j \leq 7$.
Determine the value of $K^{2}$.
-/
theorem algebra_608902
    (P : Polynomial ℂ) (hP : P = X ^ 7 - C 7)
    (r : ℕ → ℂ) (hr : ∀ i ∈ Icc 1 7, P.eval (r i) = 0) (hr2 : Set.InjOn r (Set.Icc 1 7))
    (K : ℂ) (hK : K = ∏ i ∈ Icc 1 7, ∏ j ∈ Icc (i + 1) 7, (r i + r j))
    : K ^ 2 = 7 ^ 6 := by

-- We first note that $x^{7}-7=\left(x-r_{1}\right)\left(x-r_{2}\right) \cdots\left(x-r_{7}\right)$,
  have h1 : X ^ 7 - C 7 = ∏ i ∈ Icc 1 7, (X - C (r i)) := calc
    X ^ 7 - C 7 = (Multiset.map (X - C ·) (X ^ 7 - C 7 : ℂ[X]).roots).prod := by
      rw [(X ^ 7 - C 7 : ℂ[X]).eq_prod_roots_of_splits_id (IsAlgClosed.splits _)]
      simp
    _ = (Multiset.map (X - C ·) ((Multiset.Icc 1 7).map r)).prod := by
      congr 2
      rw [←hP]
      symm
      apply Multiset.eq_of_le_of_card_le
      · rw [Multiset.le_iff_subset]
        · intro y hy
          obtain ⟨i, c1, c2⟩ := by simpa only [Multiset.mem_map] using hy
          subst c2
          refine mem_roots'.mpr ?_
          split_ands
          · refine leadingCoeff_ne_zero.mp ?_
            simp [hP]
          · simpa using hr i (by simpa using c1)
        · rw [Multiset.nodup_map_iff_of_inj_on]
          · exact Multiset.nodup_Icc
          · simpa [Set.InjOn] using hr2
      · calc
        P.roots.card ≤ P.natDegree := by exact card_roots' P
        _ = 7 := by simp [hP]
        _ = _ := by exact rfl
    _ = _ := by rfl

-- which implies, replacing $x$ by $-x$ and taking the negative of the equation,
-- that $\left(x+r_{1}\right)\left(x+r_{2}\right) \cdots\left(x+r_{7}\right)=x^{7}+7$.
  have h2 : ∏ i ∈ Icc 1 7, (X + C (r i)) = X ^ 7 + C 7 := by
    symm
    calc
    (X ^ 7 + C 7 : ℂ[X]) = -(-X ^ 7 - C 7) := by ring
    _ = -((-X) ^ 7 - C 7) := by ring
    _ = -(X ^ 7 - C 7 : ℂ[X]).comp (-X) := by simp
    _ = -∏ i ∈ Icc 1 7, (-X - C (r i)) := by simp [h1, Polynomial.prod_comp]
    _ = -∏ i ∈ Icc 1 7, (-1) * (X + C (r i)) := by
      congr 1
      apply prod_congr rfl
      intro i hi
      ring
    _ = _ := by
      rw [prod_mul_distrib]
      simp
      ring


-- Also note that the product of the $r_{i}$ is just the constant term, so $r_{1} r_{2} \cdots r_{7}=7$.
  have h3 := calc
    ∏ i ∈ Icc 1 7, r i = (∏ i ∈ Icc 1 7, (X + C (r i))).eval 0 := by simp [eval_prod]
    _ = (X ^ 7 + C 7 : ℂ[X]).eval 0 := by congr 1
    _ = 7 := by simp

-- Now, we have that

-- $$ 2^{7} \cdot 7 \cdot K^{2} =\left(\prod_{i=1}^{7} 2 r_{i}\right) K^{2} $$

-- $$=\prod_{i=1}^{7} 2 r_{i} \left(\prod_{1 \leq i < j \leq 7}r_{i}+r_{j}\right)^{2}$$

-- $$=\prod_{1 \leq i=j \leq 7}\left(r_{i}+r_{j}\right) \prod_{1 \leq i < j \leq 7}\left(r_{i}+r_{j}\right) \prod_{1 \leq j < i \leq 7}\left(r_{i}+r_{j}\right)$$

-- $$=\prod_{1 \leq i, j \leq 7}\left(r_{i}+r_{j}\right) =\prod_{i=1}^{7} \prod_{j=1}^{7}\left(r_{i}+r_{j}\right) . $$

  have h4 := calc
    2 ^ 7 * 7 * K ^ 2 = (∏ i ∈ Icc 1 7, (2 * r i)) * K ^ 2 := by simp [prod_mul_distrib, h3]
    _ =
        (∏ i ∈ Icc 1 7, ∏ j ∈ Icc (i + 1) 7, (r i + r j)) *
        (∏ i ∈ Icc 1 7, (2 * r i)) *
        (∏ i ∈ Icc 1 7, ∏ j ∈ Icc (i + 1) 7, (r i + r j)) := by
      rw [hK]
      ring
    _ = (∏ i ∈ Icc 1 7, ∏ j ∈ Icc 1 (i - 1), (r i + r j)) *
        (∏ i ∈ Icc 1 7, ∏ j ∈ Icc i i, (r i + r j)) *
        (∏ i ∈ Icc 1 7, ∏ j ∈ Icc (i + 1) 7, (r i + r j)) := by
      congr 2
      · calc
        ∏ i ∈ Icc 1 7, ∏ j ∈ Icc (i + 1) 7, (r i + r j) =
        ∏ i ∈ Icc 1 7, ∏ j ∈ Icc 1 7 with i < j, (r i + r j) := by
          apply prod_congr rfl
          intro i hi
          apply prod_congr ?_ (by simp)
          ext k; simp; omega
        _ = ∏ i ∈ Icc 1 7, ∏ j ∈ Icc 1 7, if i < j then (r i + r j) else 1 := by
          apply prod_congr rfl
          intro i hi
          simp [prod_ite]
        _ = ∏ i ∈ Icc 1 7, ∏ j ∈ Icc 1 7, if i > j then (r i + r j) else 1 := by
          rw [prod_comm]
          apply prod_congr rfl
          intro i hi
          apply prod_congr rfl
          intro j hj
          ring_nf
        _ = ∏ i ∈ Icc 1 7, ∏ j ∈ Icc 1 7 with i > j, (r i + r j) := by
          apply prod_congr rfl
          intro i hi
          simp [prod_ite]
        _ = _ := by
          apply prod_congr rfl
          intro i hi
          apply prod_congr ?_ (by simp)
          ext k; simp at hi ⊢; omega
      · apply prod_congr rfl
        intro i hi
        simp
        ring
    _ = ∏ i ∈ Icc 1 7,
          (∏ j ∈ Icc 1 (i - 1), (r i + r j)) *
          (∏ j ∈ Icc i i, (r i + r j)) *
          (∏ j ∈ Icc (i + 1) 7, (r i + r j)) := by iterate 2 rw [←prod_mul_distrib]
    _ = (∏ i ∈ Icc 1 7, ∏ j ∈ Icc 1 7, (r i + r j)) := by
      apply prod_congr rfl
      intro i hi
      have c1 : Icc 1 7 = Icc 1 (i - 1) ∪ Icc i i ∪ Icc (i + 1) 7 := by ext k; simp at hi ⊢; omega
      rw [c1]
      iterate 2 rw [prod_union]
      · refine disjoint_iff_inter_eq_empty.mpr ?_
        ext x; simp; omega
      · refine disjoint_iff_inter_eq_empty.mpr ?_
        ext x; simp; omega

-- However, note that for any fixed $i, \prod_{j=1}^{7}\left(r_{i}+r_{j}\right)$ is just the result
-- of substuting $x=r_{i}$ into $\left(x+r_{1}\right)(x+$ $\left.r_{2}\right) \cdots\left(x+r_{7}\right)$.

-- Hence, $$ \prod_{j=1}^{7}\left(r_{i}+r_{j}\right)=r_{i}^{7}+7=\left(r_{i}^{7}-7\right)+14=14 $$

  have h5 (i : ℕ) (hi : i ∈ Icc 1 7) := calc
    ∏ j ∈ Icc 1 7, (r i + r j) = (r i ^ 7 + 7) := calc
      _ = (∏ j ∈ Icc 1 7, (X + C (r j))).eval (r i) := by simp [eval_prod]
      _ = (X ^ 7 + C 7 : ℂ[X]).eval (r i) := by rw [h2]
      _ = _ := by simp
    _ = (r i ^ 7 - 7) + 14 := by ring
    _ = (P.eval (r i)) + 14 := by simp [hP]
    _ = 14 := by simp [hr i hi]

-- Therefore, taking the product over all $i$ gives $14^{7}$
  have h6 := calc
    ∏ i ∈ Icc 1 7, (∏ j ∈ Icc 1 7, (r i + r j)) = ∏ i ∈ Icc 1 7, 14 := by
      apply prod_congr rfl
      exact h5
    _ = 14 ^ 7 := by simp

-- which yields $K^{2}=7^{6}=117649$.
  have h7 : 2 ^ 7 * 7 * K ^ 2 = 14 ^ 7 := calc
    _ = _ := h4
    _ = _ := h6

  apply_fun (fun x : ℂ => x / (2 ^ 7 * 7)) at h7
  convert h7 using 1
  · simp
  · norm_num
