import Mathlib

/-
Determine all functions $f:\mathbb{R} \rightarrow \mathbb{R}$ such that the equality $$f([x]y)=f(x)[f(y)]$$
holds for all $x, y \in \mathbb{R}$. Here, by $[x]$ we denote the greatest integer not exceeding $x$.
-/

theorem algebra_23905 (f : ℝ → ℝ) :
    (∀ x y : ℝ, f (⌊x⌋ * y) = f x * ⌊f y⌋)
     ↔ ∃ (C : ℝ) (_ : C = 0 ∨ 1 ≤ C ∧ C < 2), ∀ x : ℝ, f x = C
    := by
  constructor
  swap
  -- First, check that the answer satisfies the equation.
  . intro ⟨C, hC, f_eq⟩ x y
    rcases hC with hC | ⟨hC1, hC2⟩
    . simp [f_eq, hC]
    . have : ⌊C⌋ = 1 := by rw [Int.floor_eq_iff]; norm_cast
      simp [f_eq, this]
  -- Now consider a function satisfying the equation.
  . intro hf
    have f0y : ∀ y, f 0 = f 0 * ⌊f y⌋ := by simpa using hf 0
    by_cases f0 : f 0 = 0
    swap
    -- Case 1. Assume $f 0 ≠ 0$
    . have floor_fy : ∀ y, ⌊f y⌋ = 1 := by
        intro y
        specialize f0y y
        simpa [f0] using f0y
      -- We get $f(x) = f(0) = C$ with $1 ≤ C < 2$
      replace hf : ∀ x, f x = f 0 := by
        intro x
        specialize hf x 0
        simpa [floor_fy] using hf.symm
      use f 0
      have := floor_fy 0
      rw [Int.floor_eq_iff] at this
      norm_num at this
      use by right; exact this
    -- Case 2. Assume $f 0 = 0$
    . by_cases hfα : ∃ (α : ℝ) (_ : 0 < α) (_ : α < 1), f α ≠ 0
      -- Subcase 2a. Suppose there exists $0 < α < 1$ such that $f(α) ≠ 0$
      . obtain ⟨α, α_gt_0, α_lt_1, fα⟩ := hfα
        have floorα : ⌊α⌋ = 0 := by rw [Int.floor_eq_iff]; norm_num; split_ands <;> linarith
        have : ∀ y, f y = 0 := by
          intro y
          have h1 : ⌊f y⌋ = 0 := by
            specialize hf α y
            rw [Int.floor_eq_iff]
            norm_num
            simpa [floorα, f0, fα] using hf
          simpa [h1] using hf 1 y
        specialize this α
        contradiction
      -- Subcase 2b. Conversely, we have $f(α) = 0$ for all $0 ≤ α < 1$
      . push_neg at hfα
        use 0, by left; rfl
        intro z
        by_cases hz0 : z = 0
        . simpa [hz0] using f0
        -- There exists an integer $N$ such that $α = z / N ∈ (0, 1)$
        -- We will then conclude from the fact that $f(z) = f(⌊N⌋α) = f(N)⌊f(α)⌋ = 0$
        . let N := if z ≥ 0 then ⌊z⌋ + 1 else ⌊z⌋ - 1
          let α : ℝ := z / N
          have : α > 0 ∧ α < 1 := by
            by_cases hz : z ≥ 0
            . have z_pos : z > 0 := lt_of_le_of_ne hz (Ne.symm hz0)
              dsimp [α, N]
              split_ifs
              push_cast
              have h : 0 < (⌊z⌋ + 1 : ℝ) := by
                have := Int.floor_nonneg.mpr hz
                norm_cast
                omega
              split_ands
              . exact div_pos z_pos h
              . suffices z < ⌊z⌋ + 1 from Bound.div_lt_one_of_pos_of_lt h this
                exact Int.lt_floor_add_one z
            . have z_neg : z < 0 := by simpa using hz
              dsimp [α, N]
              split_ifs
              push_cast
              have h : (⌊z⌋ - 1 : ℝ) < 0 := by
                have := Int.floor_le_neg_one_iff.mpr z_neg
                norm_cast
                omega
              split_ands
              . exact div_pos_of_neg_of_neg z_neg h
              . suffices z > ⌊z⌋ - 1 from (div_lt_one_of_neg h).mpr this
                suffices z ≥ ⌊z⌋ from by linarith
                exact Int.floor_le z
          specialize hfα α this.1 this.2
          have N_ne_0 : (N : ℝ) ≠ 0 := by
            norm_cast
            dsimp [N]
            by_cases hz : z ≥ 0
            . split_ifs; have := Int.floor_nonneg.mpr hz; linarith
            . split_ifs; push_neg at hz; have := Int.floor_le_neg_one_iff.mpr hz; linarith
          calc
            _ = f (α * N) := by rw [Eq.symm (div_mul_cancel₀ z N_ne_0)]
            _ = f (N * α) := by ring_nf
            _ = f (⌊(N : ℝ)⌋ * α) := by simp
            _ = f (N) * ⌊f α⌋ := hf ..
            _ = _ := by simp [hfα]
