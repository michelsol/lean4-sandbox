import Mathlib

open Finset

/- Fix a positive integer $$n$$.
A tournament on $$n$$ vertices has all its edges colored by $$\chi$$ colors,
so that any two directed edges $$u \rightarrow v$$ and $$v \rightarrow w$$ have different colors.
Over all possible tournaments on $$n$$ vertices, determine the minimum possible value of $$\chi$$.
-/
theorem combinatorics_246479
    (n : ℕ) (hn : n ≥ 1) (V : Type) [Fintype V] (hV : Fintype.card V = n) :
    let Tournament V := ((g : Digraph V) ×' (c : (u v : V) ×' g.Adj u v → ℕ) ×'
      (∀ u v, g.Adj u v ↔ ¬g.Adj v u) ∧
      ∀ (u v w) (huv : g.Adj u v) (hvw : g.Adj v w), c ⟨u, v, huv⟩ ≠ c ⟨v, w, hvw⟩)
    IsLeast (Set.range (λ t : Tournament V ↦ (Set.range t.2.1).ncard)) (Nat.ceil (Nat.log 2 n)) := by
  intro Tournament
  constructor
  . simp only [Set.mem_range, PSigma.exists, exists_prop]
    sorry
  .
-- First, we prove by strong induction on $$n \ge 1$$ that $$\chi \geq \log _{2} n$$ for any coloring and any tournament.
    simp only [Nat.ceil_nat, id_eq]
    revert n V
    apply Nat.strongRec
    intro n ih hn' V hV0 hV
    obtain hn | hn : n = 1 ∨ n ≥ 2 := by omega

-- The base case $$n=1$$ is obvious.
    . subst hn
      simp [lowerBounds]

    . intro χ h0
      obtain ⟨⟨g, color, ⟨h1, h2⟩⟩, h3⟩ := by simpa only [Set.mem_range, PSigma.exists, exists_prop] using h0

      simp only [lowerBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff, Set.mem_setOf_eq] at ih

-- Now given any tournament, consider any used color $$c$$.
      obtain ⟨u0, v0, h4, h5⟩ : ∃ (u v : V) (_ : u ≠ v), g.Adj u v := by
        let u : V := sorry
        let v : V := sorry
        by_cases c1 : g.Adj u v
        . use u, v, by sorry, c1
        . rw [←h1] at c1
          use v, u, by sorry, c1
      let c := color ⟨u0, v0, h5⟩

-- Then it should be possible to divide the tournament
-- into two subsets $$A$$ and $$B$$ such that all $$c$$-colored edges point from $$A$$ to $$B$$
-- (for example by letting $$A$$ be all vertices which are the starting point of a $$c$$-edge).
      obtain ⟨A, B, h6, h7, h8⟩ : ∃ (A B : Set V) (_ : A ∩ B = ∅) (_ : A ∪ B = .univ),
          ∀ (u v : V) (huv : g.Adj u v), (color ⟨u, v, huv⟩ = c) → u ∈ A ∧ v ∈ B := by
        sorry
      let tA : Tournament A := ⟨sorry, sorry, sorry⟩
      let tB : Tournament B := ⟨sorry, sorry, sorry⟩

-- One of $$A$$ and $$B$$ has size at least $$n / 2$$
      obtain h9 | h9 : A.ncard ≥ (n / 2 : ℕ) ∨ B.ncard ≥ (n / 2 : ℕ) := by
        by_contra! h9
        suffices n < n by omega
        calc
          n = Fintype.card V := by simp [hV]
          _ = (.univ : Set V).ncard := by simp [Set.ncard_univ]
          _ = (A ∪ B).ncard := by simp [h6, h7]
          _ = A.ncard + B.ncard := by
            rw [Set.ncard_union_eq]
            rw [Set.disjoint_iff_inter_eq_empty, h6]
          _ < n := by omega

-- If $$A$$ has size at least $$n / 2$$,
-- Since $$A$$ has no $$c$$ edges,
-- and $$A$$ uses at least $$\log _{2}|A|$$ colors other than $$c$$,
-- we get $$ \chi \geq 1+\log _{2}(n / 2)=\log _{2} n $$ completing the induction.
      . specialize ih A.ncard (by sorry) (by omega)
        let h10 : Fintype A := by apply Fintype.ofFinite
        specialize ih A (by rw [Fintype.card_eq_nat_card]; rfl) tA
        calc
          _ = 1 + Nat.log 2 (n / 2) := by
            suffices Nat.log 2 n ≥ 1 by simp [this]
            convert_to Nat.log 2 n ≥ Nat.log 2 2
            . symm; norm_num [Nat.log_eq_one_iff]
            apply Nat.log_mono_right
            omega
          _ ≤ 1 + Nat.log 2 A.ncard := by
            gcongr
            apply Nat.log_mono_right
            exact h9
          _ ≤ 1 + (Set.range tA.snd.fst).ncard := by gcongr
          _ ≤ (Set.range color).ncard := by
            sorry
          _ = _ := h3
-- The argument is similar if $$B$$ has size at least $$n / 2$$.
      . sorry

-- One can read the construction off from the argument above, but here is a concrete description.
-- For each integer $$n$$, consider the tournament whose vertices are $$S=\{0, \ldots, n-1\}$$.
-- Instantiate colors $$c_{1}, c_{2}, \ldots$$.
-- Then for $$v, w \in S$$, we look at the smallest order bit for which they differ; say the $$k$$ th one.
-- If $$v$$ has a zero in the $$k$$ th bit, and $$w$$ has a one in the $$k$$ th bit, we draw $$v \rightarrow w$$.
-- Moreover we color the edge with color $$c_{k}$$. This works and uses at most $$\left\lceil\log _{2} n\right\rceil$$ colors.
