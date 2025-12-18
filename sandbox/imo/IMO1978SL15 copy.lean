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
    (ha2 : ∀ i ∈ Icc 1 (p - 1), a i % p ≠ 0) :
    let A := (Icc 1 (p - 1)).image a
    let 𝓟 := Icc 0 (p - 1)
    let f B := (∑ x ∈ B, x) % p
    ∀ n ∈ 𝓟, ∃ B ⊆ A, f B = n := by
  intro A 𝓟 f

  -- p ≥ 1 since p is prime.
  have hp2 : p ≥ 1 := by
    have := hp.ne_zero
    omega

-- Let $C_{n}=\left\{a_{1}, \ldots, a_{n}\right\}\left(C_{0}=\emptyset\right)$
  let C n := (Icc 1 n).image a
-- and $P_{n}=\left\{f(B) \mid B \subseteq C_{n}\right\}$.
  let P n := (C n).powerset.image f

-- Given that $A = C_{p - 1}$, it suffices to show that $|P_{p-1}| ≥ p$
  suffices 𝓟 ⊆ A.powerset.image f from by intro n hn; simpa using this hn
  suffices 𝓟 = A.powerset.image f from by exact Finset.subset_of_eq this
  symm
  apply eq_of_subset_of_card_le
  . intro n hn
    obtain ⟨B, c1, c2⟩ := by simpa using hn
    dsimp [f] at c2
    suffices (∑ x ∈ B, x) % p < p from by simp [𝓟, ←c2]; omega
    apply Nat.mod_lt
    omega
  suffices #(P (p - 1)) ≥ p from by simpa [𝓟, hp2]

-- First note that $P_{0}=\{0\}$ contains one element.
  have h2 : P 0 = {0} := by simp [P, C, f]

-- And note that P is a monotone sequence of sets.
  have h3 : MonotoneOn P (Icc 1 (p - 1)) := by
    intro i hi j hj hij
    dsimp [P, C]
    apply image_subset_image
    apply powerset_mono.mpr
    apply image_subset_image
    intro x hx; simp at hx ⊢; omega

-- We show that P is strictly monotone by contradiction.
  have h4 : StrictMonoOn P (Icc 1 (p - 1)) := by
-- Suppose that P is not strictly monotone, which means that $P_{n+1}=P_{n}$ for some $n$.
    by_contra h4
    obtain ⟨n, hn, h5⟩ : ∃ n ∈ Icc 1 (p - 2), P (n + 1) = P n := by
      by_contra c1
      push_neg at c1
      apply h4
      apply strictMonoOn_of_lt_add_one
      . simp [Set.ordConnected_Icc]
      . suffices ∀ n ∈ Icc 1 (p - 1), n + 1 ∈ Icc 1 (p - 1) → P n ⊂ P (n + 1) from by simpa
        intro n hn hn2
        apply ssubset_of_ne_of_subset
        . exact (c1 n (by simp at hn hn2 ⊢; omega)).symm
        . exact h3 hn hn2 (by omega)

-- Since $P_{n+1}=$ $\left\{a_{n+1}+r \mid r \in P_{n}\right\}$,
    have h6 : P (n + 1) = (P n).image λ r ↦ a (n + 1) + r := by
      ext x
      dsimp [P]
      have c1 : C (n + 1) = C n ∪ {a (n + 1)} := by
        sorry
      simp
      rw [c1]
      sorry

-- it follows that for each $r \in P_{n}$, also $r + b \in P_{n}$ with $b = a_{n+1}$.
    have h7 r (hr : r ∈ P n) : r + a (n + 1) ∈ P n := by
      sorry

-- Then as $0 \in P_{n}$ we must have $k a_{n+1} \in P_{n}$ for all $k$;
    have h8 (k : ℕ) : k * a (n + 1) ∈ P n := by
      have c1 : 0 ∈ P n := by
        sorry
      sorry

-- Therefore $a_{n+1}$ must be zero as otherwise $P_n$ would be infinite.
    have h10 : a (n + 1) % p = 0 := by
      sorry

-- This is contradiction
    apply ha2 (n + 1) (by simp at hn ⊢; omega) h10

-- Knowing that P is strictly monotone, i.e.  $P_{n+1} \supset P_{n}$ for all $n$,
-- we prove that $P_{m}$ contains at least $m+1$ distinct elements.
  have h5 n (hn : n ∈ 𝓟) : #(P n) ≥ n + 1 := by
    sorry
-- then $\left|P_{n+1}\right| \geq\left|P_{n}\right|+1$
-- and hence $\left|P_{n}\right| \geq n+1$, as claimed.


-- Consequently, $\left|P_{p-1}\right| \geq p$.
  specialize h5 (p - 1) (by simp [𝓟])
  simpa [hp2] using h5
-- (All the operations here are performed modulo $p$.)
