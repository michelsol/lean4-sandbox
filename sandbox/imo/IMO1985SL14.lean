import Mathlib

open Finset

/- A set of 1985 points is distributed around the circumference of a circle and each of the points is marked with 1 or -1 . A point is called "good" if the partial sums that can be formed by starting at that point and proceeding around the circle for any distance in either direction are all strictly positive. Show that if the number of points marked with -1 is less than 662 , there must be at least one good point. -/

theorem other_23960
    (x : ℤ → ℤ)
    (hx1 : x.Periodic 1985)
    (hx2 : ∀ i, x i = 1 ∨ x i = -1)
    (good : ℤ → Prop)
    (good_def : ∀ i0, good i0 ↔ (∀ N : ℕ, ∑ i ∈ Icc i0 (i0 + N), x i > 0) ∧ (∀ N : ℕ, ∑ i ∈ Icc (i0 - N) i0, x i > 0))
    (h0 : #{i ∈ Icc 1 1985 | x i = -1} < 662)
    : ∃ i0, good i0 := by

  -- It suffices to prove the existence of a good point in the case of exactly 661 -1 's.
  wlog h1 : #{i ∈ Icc 1 1985 | x i = -1} = 661
  . let A j := {i ∈ Icc (j + 1) 1985 | x i = -1}
    let c j := j + #(A j)
    have c1 j (hj : j ∈ Icc 0 1984) : c (j + 1) - c j ∈ ({0, 1} : Finset _) := by
      dsimp [c]
      rcases hx2 (j + 1) with hx2 | hx2
      . have d1 : A (j + 1) = A j := by
          ext k
          constructor
          . simp [A]
            omega
          . intro hk
            simp [A] at hk ⊢
            have e1 : j + 1 ≠ k := by intro e1; subst e1; omega
            omega
        rw [d1]
        simp
      . have d1 : A (j + 1) = A j \ {j + 1} := by ext k; simp [A]; omega
        rw [d1, card_sdiff (by
          intro k hk
          simp at hk
          subst hk
          simp [A] at hj ⊢
          omega)]
        simp
        omega
    have c2 : {j ∈ Icc 0 1985 | c j ≤ 661}.Nonempty := by use 0; simp [c, A]; omega
    have ⟨c3, c4⟩ := {j ∈ Icc 0 1985 | c j ≤ 661}.isGreatest_max' c2
    set j0 := {j ∈ Icc 0 1985 | c j ≤ 661}.max' c2
    replace c3 : (0 ≤ j0 ∧ j0 ≤ 1985) ∧ c j0 ≤ 661 := by simpa using c3
    have c5 : c j0 = 661 := by
      dsimp [upperBounds] at c4
      have d1 : c 1985 = 1985 := by simp [c, A]
      have d2 : j0 ≠ 1985 := by intro d2; simp [d2] at c3; omega
      have d3 : c (j0 + 1) > 661 := by
        by_contra! d3
        have e1 : j0 + 1 ∈ {j ∈ Icc 0 1985 | c j ≤ 661} := by simp; omega
        specialize c4 e1
        omega
      specialize c1 j0 (by simp; omega)
      simp at c1
      omega
    dsimp [c, A] at c5

    let x' (i : ℤ) := if i % 1985 ≥ 1 ∧ i % 1985 ≤ j0 then -1 else x i
    have h2' : #{i ∈ Icc 1 1985 | x' i = -1} = 661 := by
      set A := {i ∈ Icc 1 1985 | x i = -1}
      set B := {i ∈ Icc 1 j0 | x i = -1}
      set C := {i ∈ Icc (j0 + 1) 1985 | x i = -1}
      set A' := {i ∈ Icc 1 1985 | x' i = -1}
      set B' := {i ∈ Icc 1 j0 | x' i = -1}
      set C' := {i ∈ Icc (j0 + 1) 1985 | x' i = -1}
      have d1 : A' = B' ∪ C' := by ext k; simp [A', B', C']; omega
      rw [d1, card_union_of_disjoint (by
        intro s hsb hsc i hi
        specialize hsb hi
        specialize hsc hi
        simp [B'] at hsb
        simp [C'] at hsc
        omega)]
      have d2 : B' = Icc 1 j0 := by ext k; simp [B', x']; omega
      have d3 : C' = C := by ext k; simp [C', C, x']; omega
      rw [d2, d3]
      simp
      omega
    let good' (i0 : ℤ) := (∀ (N : ℕ), ∑ i ∈ Icc i0 (i0 + N), x' i > 0) ∧ (∀ (N : ℕ), ∑ i ∈ Icc (i0 - N) i0, x' i > 0)
    obtain ⟨i0, c6⟩ := this x' (by intro k; simp [x', hx1 k])
      (by intro i; dsimp [x']; specialize hx2 i; omega)
      good' (by simp [good'])
      (by omega)
      h2'
    use i0
    dsimp [good'] at c6
    rw [good_def]
    split_ands <;> intro N
    . replace c6 := c6.left N
      calc
        _ ≥ ∑ i ∈ Icc i0 (i0 + N), x' i := by
          apply sum_le_sum
          intro i hi
          specialize hx2 i
          simp [x']
          omega
        _ > 0 := c6
    . replace c6 := c6.right N
      calc
        _ ≥ ∑ i ∈ Icc (i0 - N) i0, x' i := by
          apply sum_le_sum
          intro i hi
          specialize hx2 i
          simp [x']
          omega
        _ > 0 := c6

  -- Noticing that 1985 = 3 * 661 + 2, it suffices to prove by induction on $$n$$ that in any arrangement with $$3 n+2$$ points $$n$$ of which are -1 's a good point exists.
  suffices ∀ (n : ℕ) (hn : n ≥ 1)
      (x : ℤ → ℤ)
      (hx1 : x.Periodic (3 * n + 2))
      (hx2 : ∀ i, x i = 1 ∨ x i = -1)
      (good : ℤ → Prop)
      (good_def : ∀ i0, good i0 ↔ (∀ N : ℕ, ∑ i ∈ Icc i0 (i0 + N), x i > 0) ∧ (∀ N : ℕ, ∑ i ∈ Icc (i0 - N) i0, x i > 0))
      (h0 : #{i ∈ Icc 1 (3 * n + 2) | x i = -1} = n),
      ∃ i0, good i0 from by
    exact this 661 (by norm_num) x hx1 hx2 good good_def h1
  clear * -
  apply Nat.le_induction

  -- For $$n=1$$ this is clear by inspection.
  . intro x hx1 hx2 good good_def h0
    rw [card_eq_one] at h0
    obtain ⟨j0, h0⟩ := h0
    -- Only one $j0 ∈ {1, ..., 5}$ satisfies $x_j0 = -1$
    replace h0 : ∀ i, (1 ≤ i ∧ i ≤ 5) ∧ x i = -1 ↔ i = j0 := by simpa [Finset.ext_iff] using h0
    -- Pick $x_j0 + 2$ so that its partial sums begin with at least two 1's and will remain positive
    use j0 + 2
    rw [good_def]
    simp at hx1
    split_ands
    . intro N
      -- Decompose the partial sum, by grouping every 5 terms each having sum 3.
      let A := (Ico 0 (N / 5 : ℤ)).biUnion λ i ↦ Ico (j0 + 2 + 5 * i) (j0 + 2 + 5 * i + 5)
      let B := Icc (j0 + 2 + 5 * (N / 5)) (j0 + 2 + N)
      have c1 : Icc (j0 + 2) (j0 + 2 + N) = A ∪ B := by
        ext k
        simp [A, B]
        constructor <;> intro d1
        . by_cases d2 : k ≥ (j0 + 2 + 5 * (N / 5))
          . simp [d2, d1]
          push_neg at d2
          left
          use (k - (j0 + 2)) / 5
          omega
        . obtain ⟨j, d1⟩ | d1 := d1
          all_goals omega
      rw [c1]
      rw [sum_union sorry]
      rw [sum_biUnion sorry]
      sorry
    -- The situation is similar if the partial sum goes the other way
    . sorry
  -- Assume that the assertion holds for all arrangements of $$3 n+2$$ points and consider an arrangement of $$3(n+1)+2$$ points.
  . intro n hn ih
    intro x hx1 hx2 good good_def h0
    -- Now there exists a sequence of consecutive -1 's surrounded by two +1 's.
    obtain ⟨k0, hk0, m, hm, h1, h2, h3⟩ : ∃ k0 ≥ 0, ∃ m ≥ 2, x k0 = 1 ∧ (∀ k ∈ Ioo k0 (k0 + m), x k = -1) ∧ x (k0 + m) = 1 := by
      sorry
    -- There is a point $$P$$ which is good for the arrangement obtained by removing the two +1 's bordering the sequence of -1 's and one of these -1 's.
    let x' (i : ℤ) :=
      let i' := i % (3 * n + 2)
      if i' < k0 then
        x i'
      else if i' < k0 + m - 2 then
        x (i' + 2) -- ignore +1 on the lhs, and the -1 next to it
      else
        x (i' + 3) -- ignore +1 on the rhs
    have hx'1 : x'.Periodic (3 * n + 2) := by simp [x']
    have hx'2 i : x' i = 1 ∨ x' i = -1 := by
      dsimp [x']
      split_ifs
      all_goals simp [hx2]
    let good' (i0 : ℤ) := (∀ (N : ℕ), ∑ i ∈ Icc i0 (i0 + N), x' i > 0) ∧ (∀ (N : ℕ), ∑ i ∈ Icc (i0 - N) i0, x' i > 0)
    specialize ih x' hx'1 hx'2 good' (by simp [good'])
    -- as we removed one -1, the new arrangement has n -1's
    specialize ih sorry
    -- From the induction hypothesis, we get a good point $P$ from the 3n+2 arrangement.
    obtain ⟨p, h4⟩ := ih
    -- Since $$P$$ is out of this sequence, clearly the removal either leaves a partial sum as it was or diminishes it by 1 , so $$P$$ is good for the original arrangement.
    use p
    dsimp [good'] at h4
    rw [good_def]
    split_ands <;> intro N
    . replace h4 := h4.left N
      sorry
    . replace h4 := h4.right N
      sorry
