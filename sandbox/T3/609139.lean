import Mathlib

open Finset

/-
There are $n$ children and $n$ toys such that each child has a strict preference ordering on the toys.
We want to distribute the toys:
say a distribution $A$ dominates a distribution $B \neq A$ if
in $A$, each child receives at least as preferable of an toy as in $B$.
Prove that if some distribution is not dominated by any other,
then at least one child gets his/her favorite toy in that distribution.
-/
theorem combinatorics_609139
    (n : ℕ) (hn : n ≥ 1)
    (preference : Fin n → Equiv.Perm (Fin n))
    (dominates : Equiv.Perm (Fin n) → Equiv.Perm (Fin n) → Prop)
    (dominates_def : ∀ A B, dominates A B ↔ ∀ c, preference c (A c) ≥ preference c (B c))
    (A0 : Equiv.Perm (Fin n))
    (hA0 : ∀ B ≠ A0, ¬dominates B A0)
    : ∃ c : Fin n, preference c (A0 c) = n - 1 := by

-- Suppose we have a distribution $A$ assigning each child $C_{i}, i=1,2, \ldots, n$, toy $T_{i}$,
-- such that no child $C_{i}$ gets their top preference $T_{i}^{\prime} \neq T_{i}$.
  by_contra! h1

  let T' (i : Fin n) := (preference i).invFun ⟨n - 1, by omega⟩

-- Then, pick an arbitrary child $C_{1}$ and construct the sequence of children $C_{i_{1}}, C_{i_{2}}, C_{i_{3}}, \ldots$
-- where $i_{1}=1$ and $C_{i_{k+1}}$ was assigned the favorite toy $T_{i_{k}}^{\prime}$ of the last child $C_{i_{k}}$.
  obtain ⟨C, h2, h3⟩ : ∃ C : ℕ → Fin n,
      C 0 = ⟨0, by omega⟩ ∧
      ∀ (k : ℕ), A0 (C (k + 1)) = T' (C k) := by
    let FC (k : ℕ) (cih : (y : ℕ) → y < k → Fin n) : Fin n :=
      if hk : k = 0 then ⟨0, by omega⟩ else A0.invFun (T' (cih (k - 1) (by simp_wf; omega)))
    let C : ℕ → Fin n := Nat.lt_wfRel.wf.fix FC
    have hc k : C (k + 1) = A0.invFun (T' (C k)) := by
      unfold C
      rw [WellFounded.fix_eq]
      simp [FC]
    use C
    split_ands
    . unfold C
      rw [WellFounded.fix_eq]
      simp [FC]
    . intro k
      specialize hc k
      apply_fun A0 at hc
      convert hc using 1
      simp

-- Eventually, some $C_{i_{k}}=C_{i_{j}}$;
  obtain ⟨i0, j0, h4, h4', h5, h6, h7⟩ :
      ∃ (i0 j0 : ℕ) (_ : i0 ≥ 1) (_ : i0 < j0) (_ : j0 - i0 < n) (_ : Set.InjOn C (Ico i0 j0)), C i0 = C j0 := by
    sorry

-- at this point, construct a new distribution by passing the toys around this cycle
-- so that each of these children gets their favorite toy, and leave other children's toys unchanged.
  let A : Equiv.Perm (Fin n) := {
    toFun := λ c ↦ if hc : ∃ k ∈ Ico i0 j0, C k = c then T' c else A0 c
    invFun := λ t ↦ if ht : ∃ k ∈ Ico i0 j0, A0 (C k) = t then
      C (if ht.choose > i0 then ht.choose - 1 else j0 - 1) else A0.invFun t
    left_inv := by
      intro c
      dsimp
      split_ifs with c1 c2 c2
      . obtain ⟨k, c0, c1⟩ := c1
        subst c1
        symm
        obtain ⟨c3, c4⟩ := c2.choose_spec
        set k' := c2.choose
        rw [←h3] at c4
        replace c4 : C k' = C (k + 1) := by simpa using c4
        obtain c5 | c5 : k < j0 - 1 ∨ k = j0 - 1 := by simp at c0; omega
        . have c6 : k + 1 ∈ Ico i0 j0 := by simp at c0 ⊢; omega
          have c7 := h6 c3 c6 c4
          split_ifs with c8
          . simp [c7]
          . simp at c0; omega
        . subst c5
          convert_to C k' = C j0 using 2 at c4
          . omega
          rw [←h7] at c4
          have c6 : i0 ∈ Ico i0 j0 := by simp; omega
          have c7 := h6 c3 c6 c4
          simp [c7]
      . obtain ⟨k, c0, c1⟩ := c1
        subst c1
        exfalso
        apply c2
        obtain c3 | c3 : k < j0 - 1 ∨ k = j0 - 1 := by simp at c0; omega
        . use k + 1
          use by simp at c0 ⊢; omega
          exact h3 k
        . subst c3
          use i0, by simp; omega
          rw [h7]
          convert h3 (j0 - 1) using 3
          omega
      . obtain ⟨k, c2, c3⟩ := c2
        exfalso
        apply c1
        use k, c2
        simpa using c3
      . simp
    right_inv := by
      intro t
      dsimp
      sorry
  }

-- Clearly the resulting distribution dominates the original, so we're done.
  apply hA0 A
  . suffices A (C i0) ≠ A0 (C i0) by tauto
    contrapose! h1
    have c1 : A (C i0) = T' (C i0) := by
      unfold A
      suffices (if ∃ k ∈ Ico i0 j0, C k = C i0 then T' (C i0) else A0 (C i0)) = T' (C i0) by simpa
      have d1 : ∃ k ∈ Ico i0 j0, C k = C i0 := by use i0; simp; omega
      simp only [d1, ↓reduceIte]
    rw [c1] at h1
    unfold T' at h1
    use C i0
    apply_fun preference (C i0) at h1
    apply_fun Fin.val at h1
    symm
    simpa using h1
  . rw [dominates_def]
    intro c
    by_cases hc : ∃ k ∈ Ico i0 j0, C k = c
    . show _ ≤ _
      rw [Fin.le_iff_val_le_val]
      simp [A, ↓hc, T']
      omega
    . simp [A, ↓hc]
