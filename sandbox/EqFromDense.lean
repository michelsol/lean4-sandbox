import Mathlib

open Real Filter Topology

-- if two functions coincide over a dense set in ℝ
-- and one is continuous and the other is monotone
-- then they coincide everywhere

-- Remark : It'd be useful to generalize this to intervals or subsets in ℝ
-- But one might have to use other API's than Dense

theorem eq_of_eq_of_dense_of_mono_of_continuous
    [TopologicalSpace α]
    [ConditionallyCompleteLinearOrder α]
    [OrderTopology α]
    [DenselyOrdered α]
    [NoMinOrder α]
    [NoMaxOrder α]
    [FirstCountableTopology α]
    (f g : α → α)
    (s : Set α)
    (hs : Dense s)
    (hf : Monotone f)
    (hg : Continuous g)
    (h : ∀ x ∈ s, f x = g x) : ∀ x, f x = g x := by
  intro x

  have h1 : f.leftLim x = g x := by
    obtain ⟨u', hu1, hu2, hu3⟩ := exists_seq_strictMono_tendsto_nhdsWithin x
    have hu0 (n : ℕ) : u' n < u' (n + 1) := by apply hu1; omega
    let u n := (hs.exists_between (hu0 n)).choose
    replace hu0 n : u n ∈ s ∧ u' n < u n ∧ u n < u' (n + 1) := (hs.exists_between (hu0 n)).choose_spec
    replace hu1 : StrictMono u := by
      apply strictMono_nat_of_lt_succ
      intro n
      have c1 := (hu0 n).2.2
      have c2 := (hu0 (n + 1)).2.1
      exact lt_trans c1 c2
    replace hu2 n : u n < x := by
      have c1 := hu2 (n + 1)
      have c2 := (hu0 n).2.2
      exact lt_trans c2 c1
    replace hu3 : Tendsto u atTop (𝓝[<] x) := by
      rw [tendsto_nhdsWithin_iff]
      split_ands
      . replace hu3 := tendsto_nhds_of_tendsto_nhdsWithin hu3
        have c1 : Tendsto (λ _ : ℕ ↦ x) atTop (𝓝 x) := tendsto_const_nhds
        apply tendsto_of_tendsto_of_tendsto_of_le_of_le hu3 c1
        . intro n
          have := (hu0 n).2.1
          exact le_of_lt this
        . intro n
          have := hu2 n
          exact le_of_lt (hu2 n)
      . simp only [eventually_atTop]
        use 0
        intro n hn
        exact hu2 n
    have c2 : Tendsto (f ∘ u) atTop (𝓝 (f.leftLim x)) := (hf.tendsto_leftLim x).comp hu3
    have c3 : Tendsto (g ∘ u) atTop (𝓝 (g x)) := by
      exact (hg.tendsto' x (g x) rfl).comp (tendsto_nhds_of_tendsto_nhdsWithin hu3)
    have c4 : f ∘ u = g ∘ u := by ext n; exact h (u n) (hu0 n).1
    rw [c4] at c2
    exact tendsto_nhds_unique c2 c3

  have h2 : f.rightLim x = g x := by
    obtain ⟨u', hu1, hu2, hu3⟩ := exists_seq_strictAnti_tendsto_nhdsWithin x
    have hu0 (n : ℕ) : u' n > u' (n + 1) := by apply hu1; omega
    let u n := (hs.exists_between (hu0 n)).choose
    replace hu0 n : u n ∈ s ∧ u' (n + 1) < u n ∧ u n < u' n := (hs.exists_between (hu0 n)).choose_spec
    replace hu1 : StrictAnti u := by
      apply strictAnti_nat_of_succ_lt
      intro n
      have c1 := (hu0 n).2.1
      have c2 := (hu0 (n + 1)).2.2
      exact gt_trans c1 c2
    replace hu2 n : u n > x := by
      have c1 := hu2 (n + 1)
      have c2 := (hu0 n).2.1
      exact gt_trans c2 c1
    replace hu3 : Tendsto u atTop (𝓝[>] x) := by
      rw [tendsto_nhdsWithin_iff]
      split_ands
      . replace hu3 := tendsto_nhds_of_tendsto_nhdsWithin hu3
        have c1 : Tendsto (λ _ : ℕ ↦ x) atTop (𝓝 x) := tendsto_const_nhds
        apply tendsto_of_tendsto_of_tendsto_of_le_of_le c1 hu3
        . intro n
          have := hu2 n
          exact le_of_lt this
        . intro n
          have := (hu0 n).2.2
          exact le_of_lt this
      . simp only [eventually_atTop]
        use 0
        intro n hn
        exact hu2 n
    have c2 : Tendsto (f ∘ u) atTop (𝓝 (f.rightLim x)) := (hf.tendsto_rightLim x).comp hu3
    have c3 : Tendsto (g ∘ u) atTop (𝓝 (g x)) := by
      exact (hg.tendsto' x (g x) rfl).comp (tendsto_nhds_of_tendsto_nhdsWithin hu3)
    have c4 : f ∘ u = g ∘ u := by ext n; exact h (u n) (hu0 n).1
    rw [c4] at c2
    exact tendsto_nhds_unique c2 c3

  have h3 : f.leftLim x ≤ f x := hf.leftLim_le (by apply le_refl)
  have h4 : f x ≤ f.rightLim x := hf.le_rightLim (by apply le_refl)
  have h5 : f x ≤ g x := le_of_le_of_eq h4 h2
  have h6 : g x ≤ f x := le_of_eq_of_le h1.symm h3
  exact le_antisymm h5 h6


-- If two continuous functions coincide over a dense set in ℝ
-- then they coincide everywhere
-- exists in mathlib as  DenseRange.equalizer  / Dense.denseRange_val
