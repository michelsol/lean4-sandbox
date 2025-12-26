import Mathlib

open Finset

/-
For any set $$ A=\left\{a_{1}, a_{2}, a_{3}, a_{4}\right\}$$  of four distinct positive integers with sum $$ s_{A}=a_{1}+a_{2}+a_{3}+a_{4}$$ , let $$ p_{A}$$  denote the number of pairs $$ (i, j)$$  with $$ 1 \leq i < j \leq 4$$  for which $$ a_{i}+a_{j}$$  divides $$ s_{A}$$ . Among all sets of four distinct positive integers, determine those sets $$ A$$  for which $$ p_{A}$$  is maximal.
-/

theorem algebra_24005 :
    let s (a : ℕ → ℕ) := a 1 + a 2 + a 3 + a 4
    let P (a : ℕ → ℕ) := { ij ∈ Icc 1 4 ×ˢ Icc 1 4 | let (i, j) := ij; i < j ∧ (a i + a j : ℤ) ∣ s a}
    let p (a : ℕ → ℕ) := #(P a)
    let X := {a : ℕ → ℕ | a 1 < a 2 ∧ a 2 < a 3 ∧ a 3 < a 4 }
    let sol1 := ⋃ d ≥ 1, { λ | 1 => d | 2 => 5 * d | 3 => 7 * d | 4 => 11 * d | 0 => 0 | _ + 5 => 0 }
    let sol2 := ⋃ d ≥ 1, { λ | 1 => d | 2 => 11 * d | 3 => 19 * d | 4 => 29 * d | 0 => 0 | _ + 5 => 0 }
    {a ∈ X | ∀ b ∈ X, p b ≤ p a} = sol1 ∪ sol2
  := by
  intro s P p X sol1 sol2

-- We observe that for each pair of indices $$ (i, j)$$  with $$ 1 \leq i < j \leq 4$$ ,
-- the sum $$ a_{i}+a_{j}$$  divides $$ s_{A}$$  if and only if $$ a_{i}+a_{j}$$  divides $$ s_{A}-\left(a_{i}+a_{j}\right)=a_{k}+a_{l}$$ , where $$ k$$  and $$ l$$  are the other two indices.
  have h0 a (ha : a ∈ X) (i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ 4) : (a i + a j : ℤ) ∣ s a ↔ (a i + a j : ℤ) ∣ (s a - (a i + a j)) := by
    sorry

-- Firstly, we will prove that the maximum value of $$ p_{A}$$  is at most 4 .
  have h1 a (ha : a ∈ X) : p a ≤ 4 := by
    dsimp [X] at ha

-- Since there are 6 distinct pairs,
    let Q := { ij ∈ Icc 1 4 ×ˢ Icc 1 4 | let (i, j) := ij; i < j }
    have c2 : P a ⊆ Q := by
      sorry
    have c3 : #Q = 6 := by decide
    have c4 : #(P a) ≤ 6 := by simpa [c3] using card_le_card c2

-- we have to prove that at least two of them do not satisfy the previous condition.
-- We claim that two such pairs are $$ \left(a_{2}, a_{4}\right)$$  and $$ \left(a_{3}, a_{4}\right)$$ .

-- Indeed, note that $$ a_{2}+a_{4} > a_{1}+a_{3}$$  and $$ a_{3}+a_{4} > a_{1}+a_{2}$$ .
-- Hence $$ a_{2}+a_{4}$$  and $$ a_{3}+a_{4}$$  do not divide $$ s_{A}$$ .
    have c5 : (a 2, a 4) ∈ Q := sorry
    have c6 : (a 2, a 4) ∉ P a := by
      have d1 : a 2 + a 4 > a 1 + a 3 := by sorry
      have d2 : ¬ (a 2 + a 4 : ℤ) ∣ s a := by sorry
      sorry
    have c7 : (a 3, a 4) ∈ Q := by sorry
    have c8 : (a 3, a 4) ∉ P a := by
      have d1 : a 3 + a 4 > a 1 + a 2 := by sorry
      have d2 : ¬ (a 3 + a 4 : ℤ) ∣ s a := by sorry
      sorry

-- This proves $$ p_{A} \leq 4$$ .
    sorry

-- There is an $$A=\{1,5,7,11\}$$ such that $$p_A = 4$$.
  have h2 : ∃ a ∈ X, p a = 4 := by
    use λ | 1 => 1 | 2 => 5 | 3 => 7 | 4 => 11 | 0 => 0 | _ + 5 => 0
    use by decide
    decide

-- Knowing that the max of $$p_A$$ is attained at 4, we simplify the goal.
  have h3 : {a ∈ X | p a = 4} = {a ∈ X | ∀ b ∈ X, p b ≤ p a} := by
    ext a
    suffices a ∈ X → (p a = 4 ↔ ∀ b ∈ X, p b ≤ p a) from by
      simpa [h1, X]
    intro ha
    constructor
    . intro ha2
      simpa [ha2] using h1
    . intro h
      obtain ⟨a0, h2, h3⟩ := h2
      specialize h a0 h2
      specialize h1 a ha
      omega
  rw [←h3]

  ext a
  dsimp
  constructor
-- Now suppose $$ p_{A}=4$$ .
  . intro ⟨h4, h5⟩
-- By the previous argument we have $$  \begin{array}{lll} a_{1}+a_{4} \mid a_{2}+a_{3} & \text { and } & a_{2}+a_{3} \mid a_{1}+a_{4}, \ a_{1}+a_{2} \mid a_{3}+a_{4} & \text { and } & a_{3}+a_{4} \not a_{1}+a_{2}, \ a_{1}+a_{3} \mid a_{2}+a_{4} & \text { and } & a_{2}+a_{4} \not a_{1}+a_{3} . \end{array} $$
    have h6  : (a 1 + a 4 : ℤ) ∣ a 2 + a 3 := by sorry
    have h7  : (a 2 + a 3 : ℤ) ∣ a 1 + a 4 := by sorry
    have h8  : (a 1 + a 2 : ℤ) ∣ a 3 + a 4 := by sorry
    have h9  : ¬(a 3 + a 4 : ℤ) ∣ a 1 + a 2 := by sorry
    have h10 : (a 1 + a 3 : ℤ) ∣ a 2 + a 4 := by sorry
    have h11 : ¬(a 2 + a 4 : ℤ) ∣ a 1 + a 3 := by sorry

-- Hence, there exist positive integers $$ m$$  and $$ n$$  with $$ m > n \geq 2$$  such that $$  \left\{\begin{array}{l} a_{1}+a_{4}=a_{2}+a_{3} \ m\left(a_{1}+a_{2}\right)=a_{3}+a_{4} \ n\left(a_{1}+a_{3}\right)=a_{2}+a_{4} \end{array}\right. $$

    obtain ⟨m, n, hn, hmn, h12, h13, h14⟩ : ∃ (m n : ℕ) (_ : n ≥ 2) (_ : m > n),
        a 1 + a 4 = a 2 + a 3
        ∧ m * (a 1 + a 2) = a 3 + a 4
        ∧ n * (a 1 + a 3) = a 2 + a 4 := by
      sorry

-- Adding up the first equation and the third one, we get $$ n\left(a_{1}+a_{3}\right)=2 a_{2}+a_{3}-a_{1}$$ .
    have h15 : n * (a 1 + a 3) = (2 * a 2 + a 3 - a 1 : ℤ) := by
      sorry

-- If $$ n \geq 3$$ , then $$ n\left(a_{1}+a_{3}\right) > 3 a_{3} > 2 a_{2}+a_{3} > 2 a_{2}+a_{3}-a_{1}$$ .
    have h16 (hn2 : n ≥ 3) : n * (a 1 + a 3) > (2 * a 2 + a 3 - a 1 : ℤ) := by
      sorry

-- This is a contradiction.
-- Therefore $$ n=2$$ .
    have h17 : n = 2 := by
      obtain c1 | c1 : n = 2 ∨ n ≥ 3 := by omega
      . exact c1
      . specialize h16 c1
        omega

    subst h17
-- If we multiply by 2 the sum of the first equation (h12) and the third one (h14), we obtain $$  6 a_{1}+2 a_{3}=4 a_{2} $$
    have h18 : 6 * a 1 + 2 * a 3 = 4 * a 2 := by omega

-- while the sum of the first one
-- and the second one is $$  (m+1) a_{1}+(m-1) a_{2}=2 a_{3} . $$
    have h19 : (m + 1) * a 1 + (m - 1 : ℤ) * a 2 = 2 * a 3 := by
      sorry

-- Adding up the last two equations we get $$  (m+7) a_{1}=(5-m) a_{2} . $$
    have h20 : (m + 7) * a 1 = (5 - m : ℤ) * a 2 := by
      zify at h18
      linear_combination h18 + h19

-- It follows that $$ 5-m \geq 1$$ , because the left-hand side of the last equation and $$ a_{2}$$  are positive.
    have h21 : (5 - m : ℤ) ≥ 1 := by
      sorry

-- Since we have $$ m > n=2$$ , the integer $$ m$$  can be equal only to either 3 or 4 .
    have h22 : m = 3 ∨ m = 4 := by omega

-- Substituting $$ (3,2)$$  and $$ (4,2)$$  for $$ (m, n)$$  and solving the previous system of equations,
-- we find the families of solutions $$ \{d, 5 d, 7 d, 11 d\}$$  and $$ \{d, 11 d, 19 d, 29 d\}$$ , where $$ d$$  is any positive integer.
    simp only [Set.mem_union, Set.mem_iUnion, sol1, sol2]
    obtain hm | hm := h22
    all_goals subst hm
    . sorry
    . sorry


-- Conversely, it is straightforward to check that these solutions work
  . intro h4
    simp only [Set.mem_union, Set.mem_iUnion, sol1, sol2] at h4
    obtain ⟨d, hd, h4⟩ | ⟨d, hd, h4⟩ := h4
    . rw [h4]
      split_ands
      . simp; omega
      . simp; omega
      . simp; omega
      . dsimp [p, P]
        sorry
    . rw [h4]
      split_ands
      . simp; omega
      . simp; omega
      . simp; omega
      . dsimp [p, P]
        sorry
