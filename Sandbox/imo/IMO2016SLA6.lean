import Mathlib

open Finset

/-
The equation  $$ (x-1)(x-2) \cdots(x-2016)=(x-1)(x-2) \cdots(x-2016) $$
is written on the board.
One tries to erase some linear factors from both sides so that each side
still has at least one factor, and the resulting equation has no real roots.
Find the least number of linear factors one needs to erase to achieve this.
-/

theorem algebra_24745
    (n : ℕ)
    (hn : n > 0) :
    IsLeast {k : ℕ | ∃ s1 s2 : Finset ℕ,
      s1 ⊂ Icc 1 2016 ∧ s2 ⊂ Icc 1 2016 ∧ s1.card + s2.card = k
      ∧ ¬∃ x : ℝ, ∏ i ∈ Icc 1 2016 \ s1, (x - i) = ∏ i ∈ Icc 1 2016 \ s2, (x - i)} 2016 := by
  constructor
  swap
-- Since there are 2016 common linear factors on both sides,
-- we need to erase at least 2016 factors.
  . dsimp [lowerBounds]
    intro k
    intro ⟨s1, s2, hs1, hs2, hs12, h⟩
    by_contra h1
    push_neg at h1
    have h2 : s1 ∪ s2 ⊂ Icc 1 2016 := by
      constructor
      . intro x hx
        simp only [mem_union] at hx
        rcases hx with hx | hx
        . exact hs1.1 hx
        . exact hs2.1 hx
      . by_contra h
        replace h : 2016 ≤ card (s1 ∪ s2) := by simpa using card_le_card h
        have := card_union_le s1 s2
        omega
-- If there were less than 2016 erased factors,
-- there would be one common factor $(x - j)$ on both sides which would provide the real root j.
    have h3 : ∃ j, j ∈ Icc 1 2016 \ s1 ∧ j ∈ Icc 1 2016 \ s2 := by
      sorry
    obtain ⟨j, hj1, hj2⟩ := h3
    apply h
    use j
    have : {j} ⊆ Icc 1 2016 \ s1 := by simpa using hj1
    rw [←prod_sdiff this]
    have : {j} ⊆ Icc 1 2016 \ s2 := by simpa using hj2
    rw [←prod_sdiff this]
    simp

-- We claim that the equation has no real roots if we erase
-- all factors $(x-k)$ on the left-hand side with $k \equiv 2,3(\bmod 4)$,
-- and all factors $(x-m)$ on the right-hand side with $m \equiv 0,1(\bmod 4)$.
  . dsimp
    let t1 := (Icc 0 503).image (4 * . + 1)
    let t2 := (Icc 0 503).image (4 * . + 2)
    let t3 := (Icc 0 503).image (4 * . + 3)
    let t4 := (Icc 0 503).image (4 * . + 4)
    use t2 ∪ t3
    use t1 ∪ t4
    use by
      rw [ssubset_iff]
      use 4
      split_ands
      . simp [t2, t3]; omega
      . intro k hk; simp [t2, t3] at hk ⊢; rcases hk with hk | hk | hk <;> omega
    use by
      rw [ssubset_iff]
      use 2
      split_ands
      . simp [t1, t4]
      . intro k hk; simp [t1, t4] at hk ⊢
        rcases hk with hk | hk | hk <;> omega
    split_ands

-- The minimum number of linear factors to be erased will thus be 2016.
    . iterate 2 rw [card_union]
      have disj_t2_t3 : t2 ∩ t3 = ∅ := by ext x; simp [t2, t3]; omega
      have disj_t1_t4 : t1 ∩ t4 = ∅ := by ext x; simp [t1, t4]; omega
      suffices t1.card + t2.card + t3.card + t4.card = 2016 from by
        simp [disj_t2_t3, disj_t1_t4]; ring_nf at this ⊢; simpa
      iterate 4 rw [card_image_of_injOn (by intro i hi j hj hij; simpa using hij)]
      simp

-- Therefore, it suffices to show that no real number $x$ satisfies
-- $$ \prod_{j=0}^{503}(x-4 j-1)(x-4 j-4)=\prod_{j=0}^{503}(x-4 j-2)(x-4 j-3) $$
    . suffices h : ∀ (x : ℝ),
          ¬∏ j ∈ Icc (0 : ℕ) 503, (x - 4 * j - 1) * (x - 4 * j - 4) =
              ∏ j ∈ Icc (0 : ℕ) 503, (x - 4 * j - 2) * (x - 4 * j - 3) from by
        have disj_t2_t3 : Disjoint t2 t3 := sorry
        have disj_t1_t4 : Disjoint t1 t4 := sorry
        have h1 : Icc 1 2016 = t1 ∪ t2 ∪ t3 ∪ t4 := by
          ext i
          simp [t1, t2, t3, t4]
          sorry
        have : Icc 1 2016 \ (t2 ∪ t3) = t1 ∪ t4 := by sorry
        rw [this]
        replace : Icc 1 2016 \ (t1 ∪ t4) = t2 ∪ t3 := by sorry
        rw [this]
        simp only [prod_union disj_t1_t4, prod_union disj_t2_t3]
        simpa [t1, t2, t3, t4, ←sub_sub, ←prod_mul_distrib]

      intro x

-- We will derive a contradiction in four different cases :
      have hx :
          (∃ k ∈ Icc (1 : ℕ) 2016, x = k)
          ∨ (∃ k ∈ Icc (0 : ℕ) 503,
              (4 * k + 1 < x ∧ x < 4 * k + 2) ∨ (4 * k + 3 < x ∧ x < 4 * k + 4))
          ∨ (x < 1 ∨ x > 2016 ∨ (∃ k ∈ Icc (1 : ℕ) 503, 4 * k < x ∧ x < 4 * k + 1))
          ∨ (∃ k ∈ Icc (0 : ℕ) 503, (4 * k + 2 < x ∧ x < 4 * k + 3))
           := by
        sorry
      rcases hx with hx | hx | hx | hx

-- - Case 1. $x=1,2, \ldots, 2016$.
-- In this case, one side of (1) is zero while the other side is not.
-- This shows $x$ cannot satisfy (1).
      . obtain ⟨k, hk, hx⟩ := hx
        replace hx : ∃ j ∈ Icc (0 : ℕ) 503, ∃ l ∈ Icc (1 : ℕ) 4, x = 4 * j + l := by sorry
        obtain ⟨j0, hj0, l, hl, hx⟩ := hx
        rcases (by simp at hl; omega : l = 1 ∨ l = 4 ∨ l = 2 ∨ l = 3) with hl | hl | hl | hl
        . have : {j0} ⊆ Icc 0 503 := sorry
          rw [←prod_sdiff this]
          intro h
          conv_lhs at h => simp [hx, hl]
          symm at h
          rw [prod_eq_zero_iff] at h
          obtain ⟨j1, hj1, h2⟩ := h
          sorry
        . have : {j0} ⊆ Icc 0 503 := sorry
          rw [←prod_sdiff this]
          intro h
          conv_lhs at h => simp [hx, hl]
          symm at h
          rw [prod_eq_zero_iff] at h
          obtain ⟨j1, hj1, h2⟩ := h
          sorry
        . have : {j0} ⊆ Icc 0 503 := sorry
          intro h
          conv_rhs at h => rw [←prod_sdiff this]
          simp [hx, hl] at h
          rw [prod_eq_zero_iff] at h
          obtain ⟨j1, hj1, h2⟩ := h
          sorry
        . have : {j0} ⊆ Icc 0 503 := sorry
          intro h
          conv_rhs at h => rw [←prod_sdiff this]
          simp [hx, hl] at h
          rw [prod_eq_zero_iff] at h
          obtain ⟨j1, hj1, h2⟩ := h
          sorry

-- - Case 2. $4 k+1 < x < 4 k+2$ or $4 k+3 < x < 4 k+4$ for some $k=0,1, \ldots, 503$.
      . obtain ⟨k, hk, hx⟩ := hx
        intro h
        set lhs := ∏ j ∈ Icc (0 : ℕ) 503, (x - 4 * j - 1) * (x - 4 * j - 4)
        set rhs := ∏ j ∈ Icc (0 : ℕ) 503, (x - 4 * j - 2) * (x - 4 * j - 3)
-- For $j=0,1, \ldots, 503$ with $j \neq k$, the product $(x-4 j-1)(x-4 j-4)$ is positive.
        have h1 : ∀ j ∈ Icc 0 503, j ≠ k → (x - 4 * j - 1) * (x - 4 * j - 4) > 0 := sorry
-- For $j=k$, the product $(x-4 k-1)(x-4 k-4)$ is negative.
        have h2 : (x - 4 * k - 1) * (x - 4 * k - 4) < 0 := by
          sorry
-- This shows the left-hand side of (1) is negative.
        have h3 : lhs < 0 := sorry

-- On the other hand, each product $(x-4 j-2)(x-4 j-3)$ on the right-hand side of (1) is positive.
        have h4 : ∀ j ∈ Icc (0 : ℕ) 503, (x - 4 * j - 2) * (x - 4 * j - 3) > 0 := sorry
-- This yields a contradiction.
        have h5 : rhs > 0 := sorry
        linarith

-- - Case 3. $x < 1$ or $x > 2016$ or $4 k < x < 4 k+1$ for some $k=1,2, \ldots, 503$.
      . intro h1
-- The equation (1) can be rewritten as
-- $$ 1=\prod_{j=0}^{503} \frac{(x-4 j-1)(x-4 j-4)}{(x-4 j-2)(x-4 j-3)}
-- =\prod_{j=0}^{503}\left(1-\frac{2}{(x-4 j-2)(x-4 j-3)}\right) $$
        have h2 : ∏ j ∈ Icc (0 : ℕ) 503, (1 - 2 / ((x - 4 * j - 2) * (x - 4 * j - 3))) = 1 := by
          trans ∏ j ∈ Icc (0 : ℕ) 503,
              ((x - 4 * j - 1) * (x - 4 * j - 4) / ((x - 4 * j - 2) * (x - 4 * j - 3)))
          . sorry
          . rw [prod_div_distrib]
            sorry
-- Note that $(x-4 j-2)(x-4 j-3)>2$ for $0 \leqslant j \leqslant 503$ in this case.
        have h3 : ∀ j ∈ Icc (0 : ℕ) 503, (x - 4 * j - 2) * (x - 4 * j - 3) > 2 := sorry
-- So each term in the product lies strictly between 0 and 1 ,
        let term (j : ℕ) := (1 - 2 / ((x - 4 * j - 2) * (x - 4 * j - 3)))
        have h4 : ∀ j ∈ Icc (0 : ℕ) 503, term j > 0 ∧ term j < 1 := sorry
-- and the whole product must be less than 1 , which is impossible.
        have h5 : ∏ j ∈ Icc (0 : ℕ) 503, term j < 1 := by
          sorry
        linarith

-- - Case 4. $4 k+2 < x < 4 k+3$ for some $k=0,1, \ldots, 503$.
      . intro h1
        obtain ⟨k, hk, hx⟩ := hx
-- This time we rewrite (1) as
-- $$ \begin{aligned} 1 & =\frac{x-1}{x-2} \cdot
-- \frac{x-2016}{x-2015} \prod_{j=1}^{503} \frac{(x-4 j)(x-4 j-1)}{(x-4 j+1)(x-4 j-2)} \\ &
-- =\frac{x-1}{x-2} \cdot
-- \frac{x-2016}{x-2015} \prod_{j=1}^{503}\left(1+\frac{2}{(x-4 j+1)(x-4 j-2)}\right) \end{aligned} $$
        let term (j : ℕ) := (1 + 2 / ((x - 4 * j + 1) * (x - 4 * j - 2)))
        let rhs := ((x - 1) / (x - 2)) * ((x - 2016) / (x - 2015)) * ∏ j ∈ Icc (1 : ℕ) 503, term j
        have h2 : 1 = rhs := by
          trans ((x - 1) / (x - 2)) * ((x - 2016) / (x - 2015)) *
              ∏ j ∈ Icc (1 : ℕ) 503,
                (((x - 4 * j) * (x - 4 * j - 1)) / ((x - 4 * j + 1) * (x - 4 * j - 2)))
          . sorry
          . sorry
        symm at h2
-- Clearly, $\frac{x-1}{x-2}$ and $\frac{x-2016}{x-2015}$ are both greater than 1 .
        have h3 : ((x - 1) / (x - 2)) > 1 := by
          suffices x - 1 > x - 2 from by
            have h1 : x - 2 > 0 := by linarith
            exact (one_lt_div h1).mpr this
          linarith
        have h4 : ((x - 2016) / (x - 2015)) > 1 := sorry
-- For the range of $x$ in this case, each term in the product is also greater than 1 .
        have h5 : ∀ j ∈ Icc (1 : ℕ) 503, term j > 1 := sorry
        have h6 : ∏ j ∈ Icc (1 : ℕ) 503, term j > 1 := by
          sorry
-- Then the right-hand side must be greater than 1 and hence a contradiction arises.
        have h7 : rhs > 1 := calc
          rhs > 1 * 1 * 1 := by dsimp [rhs]; gcongr
          _ = 1 := by norm_num
        linarith
