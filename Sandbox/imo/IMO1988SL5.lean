import Mathlib

open Finset Classical

/-
Let $n$ be an even positive integer.
Let $A_{1}, A_{2}, \ldots, A_{n+1}$ be sets having $n$ elements each such that any two
of them have exactly one element in common while every element of their union belongs
to at least two of the given sets. For which $n$ can one assign to every element of the
union one of the numbers 0 and 1 in such a manner that each of the sets has exactly $n / 2$ zeros?
-/

set_option maxHeartbeats 1000000
theorem other_24172
    (n : ℕ) (hn0 : n > 0) (hn1 : ∃ k, n = 2 * k)
    (α : Type u) (A : ℕ → Finset α)
    (B : Finset α) (B_def : B = (Icc 1 (n + 1)).biUnion A)
    (ha1 : ∀ i ∈ Icc 1 (n + 1), (A i).card = n)
    (ha2 : ∀ i ∈ Icc 1 (n + 1), ∀ j ∈ Icc 1 (n + 1), i ≠ j → (A i ∩ A j).card = 1)
    (ha3 : ∀ x ∈ B, ∃ i1 ∈ Icc 1 (n + 1), ∃ i2 ∈ Icc 1 (n + 1), i1 < i2 ∧ x ∈ A i1 ∧ x ∈ A i2)
    : (∃ (f : α → ℕ) (_ : ∀ x ∈ B, f x = 0 ∨ f x = 1),
        ∀ i ∈ Icc 1 (n + 1), { x ∈ A i | f x = 0 }.card = (n / 2 : ℚ))
          ↔ 4 ∣ n := by
-- Let $n=2 k$.
  obtain ⟨k, hkn⟩ := hn1
  subst hkn
  suffices (∃ (f : α → ℕ) (_ : ∀ x ∈ B, f x = 0 ∨ f x = 1),
              ∀ i ∈ Icc 1 (2 * k + 1), { x ∈ A i | f x = 0 }.card = k)
                ↔ 2 ∣ k from by simpa [show 4 ∣ 2 * k ↔ 2 ∣ k from by omega]
-- Since every element of their union $B$ belongs to at least two sets of $A$,
-- it follows that $A_{j}=\bigcup_{i \neq j} A_{i} \cap A_{j}$ holds for every $1 \leq j \leq 2 k+1$.
  have h1 : ∀ j ∈ Icc 1 (2 * k + 1),
      A j = (Icc 1 (2 * k + 1) \ {j}).biUnion λ i ↦ A i ∩ A j := by
    intro j hj
    ext x
    constructor
    . intro hx
      have : x ∈ B := by rw [B_def, mem_biUnion]; use j
      obtain ⟨i1, hi1, i2, hi2, hi1i2, hxAi1, hxAi2⟩ := ha3 x this
      simp only [mem_biUnion]
      rcases (by omega : i1 ≠ j ∨ i2 ≠ j) with hij | hij
      . use i1
        split_ands
        . simp at hi1 ⊢; omega
        . simp only [mem_inter]; split_ands <;> simpa
      . use i2
        split_ands
        . simp at hi2 ⊢; omega
        . simp only [mem_inter]; split_ands <;> simpa
    . intro hx
      simp only [mem_biUnion, mem_inter] at hx
      obtain ⟨_, _, _, h⟩ := hx
      simpa

-- Since each intersection in the sum has at most one element and $A_{j}$ has $2 k$ elements,
-- it follows that every element of $A_{j}$, in general of $B$, is a member of exactly one other $A_i$.
  have h2 : ∀ j ∈ Icc 1 (2 * k + 1), ∀ x ∈ A j, ∃! i ∈ Icc 1 (2 * k + 1) \ {j}, x ∈ A i := by
    sorry

  let inhabited_α : Inhabited α := by
    use (card_eq_one.mp (ha2 1 (by simp) 2 (by simp; omega) (by omega))).choose
-- Let $a$ be the function that for every two indices $1 \leq j \leq 2 k+1$ and $i \neq j$
-- returns the unique element contained in both $A_{i}$ and $A_{j}$.
  let a (i j : ℕ) :=
    if h : i ∈ Icc 1 (2 * k + 1) ∧ j ∈ Icc 1 (2 * k + 1) ∧ i ≠ j then
      (card_eq_one.mp (ha2 i h.1 j h.2.1 h.2.2)).choose
    else default
  replace ha2 : ∀ i ∈ Icc 1 (2 * k + 1), ∀ j ∈ Icc 1 (2 * k + 1), i ≠ j → A i ∩ A j = {a i j} := by
    intro i hi j hj hij
    dsimp only [a]
    split_ifs with h
    . exact (card_eq_one.mp (ha2 i hi j hj hij)).choose_spec
    . simp [hi, hj, hij] at h
  have symm_a : ∀ i ∈ Icc 1 (2 * k + 1), ∀ j ∈ Icc 1 (2 * k + 1), a i j = a j i := by
    sorry
  replace h1 : ∀ i ∈ Icc 1 (2 * k + 1), ∀ x ∈ A i, ∃! j ∈ Icc 1 (2 * k + 1) \ {i}, x = a i j := by
    sorry
  replace ha3 : ∀ x ∈ B, ∃! i1 ∈ Icc 1 (2 * k + 1), ∃! i2 ∈ Icc 1 (2 * k + 1),
      i1 < i2 ∧ x = a i1 i2 := by
    sorry

-- We now prove that $k$ is even, assuming that the marking described in the problem exists.
  constructor
  . intro ⟨f, hf1, hf2⟩

-- On a $2 k \times 2 k$ matrix let us mark in the $i$ th column and $j$ th row
-- for $i \neq j$ the number that was joined to the element of $B$ in $A_{i} \cap A_{j}$.
-- In the $i$ th row and column let us mark the number of the element of $B$ in $A_{i} \cap A_{2 k+1}$.
    let m (i j : ℕ) := f (if i = j then a i (2 * k + 1) else a i j)

-- The $i$-th row, corresponds to $A_i$, so it must have k zero's.
    have h3 : ∀ i ∈ Icc 1 (2 * k), { j ∈ Icc 1 (2 * k) | m i j = 0 }.card = k :=
      sorry

-- Hence, the total number of zeros in the matrix is $2 k^2$ which is even.
    have h4 : ∀ i ∈ Icc 1 (2 * k),
        { i ∈ Icc 1 (2 * k) ×ˢ Icc 1 (2 * k) | m i.1 i.2 = 0 }.card % 2 = 0 := by
      intro i hi
      trans 2 * k ^ 2 % 2
      . congr 1
        sorry
      . omega

-- The matrix is symmetric with respect to its main diagonal;
    have h5 : ∀ i ∈ Icc 1 (2 * k), ∀ j ∈ Icc 1 (2 * k), m i j = m j i := by
      intro i hi j hj
      dsimp only [m]
      congr 1
      split_ifs with hij <;> try omega
      . rw [hij]
      . exact symm_a i (by simp at hi ⊢; omega) j (by simp at hj ⊢; omega)

-- hence it has an even number of zeros outside its main diagonal.
    have h6 : { i ∈ Icc 1 (2 * k) ×ˢ Icc 1 (2 * k) | i.1 ≠ i.2 ∧ m i.1 i.2 = 0 }.card % 2 = 0 := sorry

-- Hence, the number of zeros on the main diagonal must also be even
    have h7 : { i ∈ Icc 1 (2 * k) ×ˢ Icc 1 (2 * k) | i.1 = i.2 ∧ m i.1 i.2 = 0 }.card % 2 = 0 := sorry
    replace h7 : { i ∈ Icc 1 (2 * k) | m i i = 0 }.card % 2 = 0 := by
      trans { i ∈ Icc 1 (2 * k) ×ˢ Icc 1 (2 * k) | i.1 = i.2 ∧ m i.1 i.2 = 0 }.card % 2
      swap
      exact h7
      congr 1
      iterate 2 rw [card_filter]
      rw [sum_product]
      sorry

-- and this number equals the number of elements in $A_{2 k+1}$ that are marked with 0, which is $k$.
    have  h8 : { i ∈ Icc 1 (2 * k) | m i i = 0 }.card = k := by
      sorry

-- Hence $k$ must be even.
    omega

-- For even $k$ we note that the dimensions of a $2 k \times 2 k$ matrix are divisible by 4 .
  . intro h
    have h3 : 4 ∣ 2 * k := by omega
-- Tiling the entire matrix with the $4 \times 4$ submatrix
-- $$ Q=\left[\begin{array}{llll} 0 & 1 & 0 & 1 \\ 1 & 0 & 1 & 0 \\
-- 0 & 1 & 1 & 0 \\ 1 & 0 & 0 & 1 \end{array}\right] $$
    let f (x : α) :=
      if hx : x ∈ B then
        let i := (ha3 x hx).choose
        let j := ((ha3 x hx).choose_spec.1).2.choose
        -- x = a i j
        if      i % 4 = 1 ∧ j % 4 = 1 then 0
        else if i % 4 = 1 ∧ j % 4 = 2 then 1
        else if i % 4 = 1 ∧ j % 4 = 3 then 0
        else if i % 4 = 1 ∧ j % 4 = 0 then 1
        else if i % 4 = 2 ∧ j % 4 = 1 then 1
        else if i % 4 = 2 ∧ j % 4 = 2 then 0
        else if i % 4 = 2 ∧ j % 4 = 3 then 1
        else if i % 4 = 2 ∧ j % 4 = 0 then 0
        else if i % 4 = 3 ∧ j % 4 = 1 then 0
        else if i % 4 = 3 ∧ j % 4 = 2 then 1
        else if i % 4 = 3 ∧ j % 4 = 3 then 1
        else if i % 4 = 3 ∧ j % 4 = 0 then 0
        else if i % 4 = 0 ∧ j % 4 = 1 then 1
        else if i % 4 = 0 ∧ j % 4 = 2 then 0
        else if i % 4 = 0 ∧ j % 4 = 3 then 0
        else if i % 4 = 0 ∧ j % 4 = 0 then 1
        else 0
      else 0
-- we obtain a marking that indeed satisfies all the conditions of the problem;
    use f
    use by
      intro x hx
      simp only [f, hx, reduceDIte]
      set j := ((ha3 x hx).choose_spec.1).2.choose
      set i := (ha3 x hx).choose
      sorry
-- the number of zero's of each $A_i$ is k
    intro i hi
    sorry
-- hence we have shown that the marking is possible if and only if $k$ is even.
