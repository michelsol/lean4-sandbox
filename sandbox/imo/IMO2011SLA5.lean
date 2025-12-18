import Mathlib

open Finset
open Int

/-
Prove that for every positive integer $n$, the set $\{2, 3, 4, . . . , 3n + 1\}$ can be partitioned into
$n$ triples in such a way that the numbers from each triple are the lengths of the sides of some
obtuse triangle.
-/

theorem algebra_24016 :
    -- Three integers $0 < a < b < c$ form an obtuse triplet iff
    -- $c < a + b$ and $a^2 + b^2 < c^2$
    let obtuse (a b c : ℤ) := c < a + b ∧ a ^ 2 + b ^ 2 < c ^ 2
    ∀ n ≥ (1 : ℤ),
      let R := Icc 2 (3 * n + 1)
      ∃ (ι : Type) (I : Finset ι) (card_I : I.card = n) (A : ι → Finset ℤ)
        (nonempty_Ai : ∀ i ∈ I, A i ≠ ∅)
        (disj_Ai : ∀ i ∈ I, ∀ i' ∈ I, i ≠ i' → Disjoint (A i) (A i'))
        (mem_Ai : ∀ j ∈ R, ∃ i ∈ I, j ∈ A i)
        , ∀ i ∈ I,
            ∃ (a b c : ℤ) (a_mem : a ∈ R) (b_mem : b ∈ R) (c_mem : c ∈ R)
              (a_lt_b : a < b) (b_lt_c : b < c)
              (is_triple : A i = {a, b, c})
              (is_obtuse : obtuse a b c)
              , True
    := by
  intro obtuse
  -- We prove by strong induction on $n \ge 1$ that there exists a partition of $[2, 3n + 1]$
  -- into $n$ obtuse triples $(A_i)_{2 ≤ i ≤ n + 1}$ having the form $A_i = \{i, a_i, b_i\}$.
  suffices
    ∀ n ≥ (1 : ℤ),
      let R := Icc 2 (3 * n + 1)
      let I := Icc 2 (n + 1)
      ∃ (a b : ℤ → ℤ),
      let A i := ({i, a i, b i} : Finset ℤ)
      ∃ (nonempty_Ai : ∀ i ∈ I, A i ≠ ∅)
        (disj_Ai : ∀ i ∈ I, ∀ i' ∈ I, i ≠ i' → Disjoint (A i) (A i'))
        (mem_Ai : ∀ j ∈ R, ∃ i ∈ I, j ∈ A i)
        (a_mem : ∀ i ∈ I, a i ∈ R)
        (b_mem : ∀ i ∈ I, b i ∈ R)
        (i_lt_a : ∀ i ∈ I, i < a i)
        (a_lt_b : ∀ i ∈ I, a i < b i)
        (is_obtuse : ∀ i ∈ I, obtuse i (a i) (b i))
        , True from by
    intro n hn R
    have n_ge_0 : n ≥ 0 := by omega
    let I := Icc 2 (n + 1)
    obtain ⟨a, b, h1, h2, h3, a_mem, b_mem, i_lt_a, a_lt_b, is_obtuse, _⟩ := this n hn
    set A := λ i ↦ ({i, a i, b i} : Finset ℤ)
    use ℤ, I, (by rw [card_Icc]; ring_nf; simp [n_ge_0]), A, h1, h2, h3
    intro i hi
    use i, a i, b i
    use (by simp [I, R] at hi ⊢; omega)
    use a_mem i hi, b_mem i hi, i_lt_a i hi, a_lt_b i hi, rfl, is_obtuse i hi
  apply @Int.strongRec 2
  -- For the base case $n = 1$, one can simply set $A_2 = \{2, 3, 4\}$
  . intro n _ _; have hn : n = 1 := by omega
    subst hn
    intro R I
    use λ _ ↦ 3, λ _ ↦ 4
    use by simp [I], by simp [I], by simp [R, I]; omega
    simp [I, R, obtuse]
  . intro n hn ih
    -- Now we turn to the induction step. Let $n > 1$ and put $t = ⌊n/2⌋ < n$. By the induction
    -- hypothesis, there exists a partition of the set $[2, 3t + 1]$ into $t$ obtuse triples
    -- $A'_i=\{i,a_i',b_i'\}$ with $i\in[2,t+1]$
    let t := n / 2
    have t_le_n : t < n := by omega
    have t_ge_1 : t ≥ 1 := by omega
    specialize ih t t_le_n t_ge_1
    obtain ⟨a', b', nonempty_A'i, disj_A'i, mem_A'i,
      a'_mem, b'_mem, i_lt_a', a'_lt_b', is_obtuse', _⟩ := ih
    intro _ R I
    dsimp [R]
    -- For each $i ∈ [2, t + 1]$, define $A_i=\{i,a_i'+(n-t),b_i'+(n-t)\}$
    -- For each $i ∈ [t + 2, n + 1]$, define $A_i = \{i, n + t + i, 2n + i\}$
    let a i := if i ∈ Icc 2 (t + 1) then a' i + (n - t) else
                if i ∈ Icc (t + 2) (n + 1) then n + t + i else 0
    let b i := if i ∈ Icc 2 (t + 1) then b' i + (n - t) else
                if i ∈ Icc (t + 2) (n + 1) then 2 * n + i else 0
    have hI' : ∀ i, i ∈ I ↔
      i ∈ Icc 2 (t + 1) ∧ i ∉ Icc (t + 2) (n + 1)
      ∨ i ∉ Icc 2 (t + 1) ∧ i ∈ Icc (t + 2) (n + 1) := by simp [I]; omega
    use a, b
    -- $A_i$'s are not empty.
    use by
      simp [I]
    -- $A_i$'s are pairwise disjoint.
    use by
      simp only [hI']
      intro i hi j hj hij
      rcases hi with ⟨hi1, hi2⟩ | ⟨hi1, hi2⟩
      rcases hj with ⟨hj1, hj2⟩ | ⟨hj1, hj2⟩
      . dsimp [a, b]; split_ifs
        specialize disj_A'i i hi1 j hj1 hij
        dsimp at disj_A'i
        sorry
      . dsimp [a, b]; split_ifs
        sorry
      rcases hj with ⟨hj1, hj2⟩ | ⟨hj1, hj2⟩
      . dsimp [a, b]; split_ifs
        sorry
      . dsimp [a, b]; split_ifs
        simp at hi1 hi2 hj1 hj2 ⊢; omega
    -- $$\bigcup_{i=2}^{n+1} A_i = [2,3n+1]$$
    use by
      intro j hj
      replace hj : 2 ≤ j ∧ j ≤ t + 1
              ∨ n + 2 ≤ j ∧ j ≤ n + 2 * t + 1
              ∨ t + 2 ≤ j ∧ j ≤ n + 1
              ∨ n + 2 * t + 2 ≤ j ∧ j ≤ 2 * n + t + 1
              ∨ 2 * n + t + 2 ≤ j ∧ j ≤ 3 * n + 1 := by
        simp at hj; omega
      rcases hj with hj | hj | hj | hj | hj
      . use j; simp [I]; omega
      . let i := j - n + t
        have hi : t + 2 ≤ i ∧ i ≤ 3 * t + 1 := by omega
        obtain ⟨i₀, hi₀, hj'⟩ := mem_A'i i (by simp; omega)
        replace hi : i = a' i₀ ∨ i = b' i₀ := by simp at hj' hi₀; omega
        use i₀, (by simp [I] at hi₀ ⊢; omega)
        suffices j = a i₀ ∨ j = b i₀ from by simp at hi₀ ⊢; omega
        dsimp [a, b]; split_ifs
        omega
      . use j; simp [I]; omega
      . let i := j - n - t
        have hi : i ∈ Icc (t + 2) (n + 1) := by simp; omega
        have hi' : i ∉ Icc 2 (t + 1) := by simp; omega
        use i, (by simp [I]; omega)
        suffices j = a i from by simp [this]
        dsimp [a]; split_ifs
        omega
      . let i := j - 2 * n
        have hi : i ∈ Icc (t + 2) (n + 1) := by simp; omega
        have hi' : i ∉ Icc 2 (t + 1) := by simp; omega
        use i, (by simp [I]; omega)
        suffices j = b i from by simp [this]
        dsimp [b]; split_ifs
        omega
    -- Check that $\forall i \in [2, 3n + 1], 2 ≤ i < a_i < b_i ≤ 3n + 1$
    use by
      simp only [hI']; intro i hi
      rcases hi with ⟨hi1, hi2⟩ | ⟨hi1, hi2⟩
      . dsimp [a]; split_ifs; specialize a'_mem i hi1; simp at a'_mem ⊢; omega
      . dsimp [a]; split_ifs; simp at hi2 ⊢; omega
    use by
      simp only [hI']; intro i hi
      rcases hi with ⟨hi1, hi2⟩ | ⟨hi1, hi2⟩
      . dsimp [b]; split_ifs; specialize b'_mem i hi1; simp at b'_mem ⊢; omega
      . dsimp [b]; split_ifs; simp at hi2 ⊢; omega
    use by
      simp only [hI']; intro i hi
      rcases hi with ⟨hi1, hi2⟩ | ⟨hi1, hi2⟩
      . dsimp [a]; split_ifs; specialize i_lt_a' i hi1; omega
      . dsimp [a]; split_ifs; omega
    use by
      simp only [hI']; intro i hi
      rcases hi with ⟨hi1, hi2⟩ | ⟨hi1, hi2⟩
      . dsimp [a, b]; split_ifs; specialize a'_lt_b' i hi1; omega
      . dsimp [a, b]; split_ifs; omega
    -- $A_i$'s are obtuse triplets.
    use by
      simp only [hI']; intro i hi
      rcases hi with ⟨hi1, hi2⟩ | ⟨hi1, hi2⟩
      . dsimp [a, b]; split_ifs
        -- Lemma. Suppose that the numbers $a < b < c$ form an obtuse triple, and let $x$ be any positive integer.
        -- Then the triple $\{a, b + x, c + x\}$ is also obtuse.
        have h0 (a b c : ℤ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0)
            (hab : a < b) (hbc : b < c) (x : ℤ) (hx : x ≥ 0) (h : obtuse a b c) :
            obtuse a (b + x) (c + x) := by
          obtain ⟨h1, h2⟩ := h
          split_ands <;> nlinarith
        apply h0
        . simp at hi1 ⊢; omega
        . specialize a'_mem i hi1; simp at a'_mem ⊢; omega
        . specialize b'_mem i hi1; simp at b'_mem ⊢; omega
        . exact i_lt_a' i hi1
        . exact a'_lt_b' i hi1
        . omega
        . exact is_obtuse' i hi1
      . dsimp [a, b]; split_ifs
        split_ands
        . simp at hi2; omega
        . simp at hi2
          suffices 4 * (2 * n + i) ^ 2 - 4 * (n + t + i) ^ 2 > 4 * i ^ 2 from by omega
          calc
            _ = (2 * (n - t)) * (2 * (3 * n + (t + 2 * i))) := by ring_nf
            _ ≥ n * (2 * (3 * n + (3 * (t + 1) + 1))) := by
              set A := t + 2 * i
              set B := 3 * (t + 1) + 1
              gcongr <;> omega
            _ > n * (9 * n) := by
              have : n > 0 := by omega
              simp only [this, mul_lt_mul_left]; omega
            _ ≥ 4 * (n + 1) ^ 2 := by nlinarith
            _ ≥ _ := by nlinarith
