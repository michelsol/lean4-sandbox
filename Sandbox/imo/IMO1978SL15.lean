import Mathlib

open Finset

/-
Let $p$ be a prime and $A=\left\{a_{1}, \ldots, a_{p-1}\right\}$ an arbitrary subset
of the set of natural numbers such that none of its elements is divisible by $p$.
Let us define a mapping $f$ from $\mathcal{P}(A)$ (the set of all subsets of $A$ )
to the set $P=\{0,1, \ldots, p-1\}$ in the following way:
(i) if $B=\left\{a_{i_{1}}, \ldots, a_{i_{k}}\right\} \subset A$
and $\sum_{j=1}^{k} a_{i_{j}} \equiv n(\bmod p)$, then $f(B)=n$,
(ii) $f(\emptyset)=0, \emptyset$ being the empty set.
Prove that for each $n \in P$ there exists $B \subset A$ such that $f(B)=n$.
-/

theorem other_23673
    (p : ℕ)
    (hp : Prime p)
    (a : ℕ → ℕ)
    (ha : Set.InjOn a (Icc 1 (p - 1)))
    (ha2 : ∀ i ∈ Icc 1 (p - 1), (a i : ZMod p) ≠ 0) :
    let A := (Icc 1 (p - 1)).image a
    let f (B : Finset ℕ) : ZMod p := ∑ x ∈ B, x
    ∀ n : ZMod p, ∃ B ⊆ A, f B = n := by
  intro A f


-- p ≥ 1 since p is prime.
  have hp2 : p ≥ 1 := by
    have := hp.ne_zero
    omega

-- Let $C_{n}=\left\{a_{1}, \ldots, a_{n}\right\}\left(C_{0}=\emptyset\right)$
  let C n := (Icc 1 n).image a
-- and $P_{n}=\left\{f(B) \mid B \subseteq C_{n}\right\}$.
  let P n := (C n).powerset.image f

  have hp3 : NeZero p := ⟨by omega⟩

-- Given that $A = C_{p - 1}$, it suffices to show that $|P_{p-1}| ≥ p$
  suffices univ ⊆ A.powerset.image f from by intro n; simpa using this (by simp)
  suffices A.powerset.image f = univ from by simpa
  apply eq_of_subset_of_card_le
  . simp
  suffices #(P (p - 1)) ≥ p from by simpa [hp2]

-- First note that $P_{0}=\{0\}$ contains one element.
  have h2 : P 0 = {0} := by simp [P, C, f]

-- And note that P is a monotone sequence of sets.
  have h3 : MonotoneOn P (Icc 0 (p - 1)) := by
    intro i hi j hj hij
    dsimp [P, C]
    apply image_subset_image
    apply powerset_mono.mpr
    apply image_subset_image
    intro x hx; simp at hx ⊢; omega

-- We will split the proof in two cases, depending of if $P$ is strictly monotone or not.
-- In both cases it will turn out that $|P_{p-1}| ≥ p$.
-- Operations are performed modulo $p$, i.e. in ℤ/pℤ.
  by_cases h4 : StrictMonoOn P (Icc 0 (p - 1))
  swap
-- Suppose that P is not strictly monotone, which means that $P_{n+1}=P_{n}$ for some $n$.
  . obtain ⟨n, hn, h5⟩ : ∃ n ∈ Icc 0 (p - 2), P (n + 1) = P n := by
      by_contra c1
      push_neg at c1
      apply h4
      apply strictMonoOn_of_lt_add_one
      . simp [Set.ordConnected_Icc]
      . suffices ∀ n ∈ Icc 0 (p - 1), n + 1 ∈ Icc 0 (p - 1) → P n ⊂ P (n + 1) from by simpa
        intro n hn hn2
        apply ssubset_of_ne_of_subset
        . exact (c1 n (by simp at hn hn2 ⊢; omega)).symm
        . exact h3 (by simp at hn ⊢; omega) (by simp at hn2 ⊢; omega) (by omega)

  -- As $\left\{a_{n+1}+r \mid r \in P_{n}\right\} \subseteq P_n$,
    have h6 : ((P n).image λ r ↦ (r + a (n + 1) : ZMod p)) ⊆ P n := by
      intro r
      intro h
      obtain ⟨B, c1, c2⟩ : ∃ B ⊆ C n, f B = r + -a (n + 1) := by simpa [P] using h
      rw [←h5]
      suffices ∃ B ⊆ C (n + 1), f B = r by simpa [P]
      use B ∪ {a (n + 1)}
      use by
        have c3 : C (n + 1) = C n ∪ {a (n + 1)} := by
          sorry
        rw [c3]
        apply union_subset_union
        . exact c1
        . simp
      dsimp [f] at c2 ⊢
      rw [sum_union ?_, sum_singleton]
      . apply add_eq_of_eq_add_neg c2
      . suffices a (n + 1) ∉ B from by simpa
        intro c3
        specialize c1 c3
        obtain ⟨i, hi, c4⟩ : ∃ i, (1 ≤ i ∧ i ≤ n) ∧ a i = a (n + 1) := by simpa [C] using c1
        specialize ha (by simp at hn ⊢; omega) (by simp at hn ⊢; omega) c4
        omega

  -- it follows that for each $r \in P_{n}$, also $r + a_{n+1} \in P_{n}$.
    have h7 r (hr : r ∈ P n) : r + a (n + 1) ∈ P n := by
      have c1 : r + a (n + 1) ∈ ((P n).image λ r ↦ (r + a (n + 1) : ZMod p)) := by simpa using hr
      exact h6 c1

  -- Then as $0 \in P_{n}$ we must have $k a_{n+1} \in P_{n}$ for all $k$;
    have h8 (k : ℕ) : (k * a (n + 1) : ZMod p) ∈ P n := by
      have c1 : 0 ∈ P n := by
        suffices P 0 ⊆ P n from by simpa [h2]
        apply h3
        . simp
        . simp at hn ⊢; omega
        . omega
      induction' k with k ih
      . simpa using c1
      . specialize h7 (k * a (n + 1)) ih
        norm_cast at h7 ⊢
        ring_nf at h7 ⊢
        simpa using h7

  -- As a_{n+1} is not zero in ℤ/pℤ, and p is prime, it generates the whole group and $#P_n = p$
    have h9 : P n = univ := by
      sorry

    replace h9 : #(P n) = p := by
      apply_fun (#.) at h9
      simpa using h9

    have h10 : P n ⊆ P (p - 1) := by
      simp at hn
      apply h3
      . simp; omega
      . simp
      . omega

    replace h10 := card_le_card h10
    omega
  .
-- If P is strictly monotone, i.e.  $P_{n+1} \supset P_{n}$ for all $n$,
-- then $\left|P_{n+1}\right| \geq\left|P_{n}\right|+1$
-- and hence $\left|P_{n}\right| \geq n+1$, as claimed.
-- Consequently, $\left|P_{p-1}\right| \geq p$.
    suffices ∀ n ∈ Icc 0 (p - 1), #(P n) ≥ n + 1 from by
      have c1 := hp.ne_zero
      have c2 := hp.ne_one
      specialize this (p - 1) (by simp)
      omega
    intro n hn
    induction' n with n ih
    . simp [h2]
    . specialize ih (by simp at hn ⊢; omega)
      have c1 : n < n + 1 := by omega
      specialize h4 (by simp at hn ⊢; omega) (by simp at hn ⊢; omega) c1
      replace h4 := card_lt_card h4
      omega
