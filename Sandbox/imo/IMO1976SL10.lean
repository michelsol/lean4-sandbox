import Mathlib

open Finset Classical

/-
Find the largest number obtainable as the product of positive integers whose sum is 1976.
-/

theorem other_25081 :
    let S := {k : ℕ | ∃ (a : ℕ → ℕ) (m : ℕ) (hm : m ≥ 1) (ha1 : ∀ i ∈ Icc 1 m, a i > 0) (ha2 : MonotoneOn a (Icc 1 m)) (ha3 : ∑ i ∈ Icc 1 m, a i = 1976), k = ∏ i ∈ Icc 1 m, a i}
    IsGreatest S (2 * 3 ^ 658) := by
  intro S

  let T := {k ∈ Icc 1 (1976 ^ 1976) | k ∈ S}
  have hTS : T = S := by
    ext k
    simp only [T, S]
    constructor
    . intro h
      simp only [coe_filter, Set.mem_setOf_eq] at h
      exact h.right
    . intro ⟨a, m, hm, ha1, ha2, ha3, h1⟩
      simp only [coe_filter, Set.mem_setOf_eq]
      constructor
      . sorry
      . use a, m
  rw [←hTS]
  have hT : T.Nonempty := by
    sorry
  suffices T.max' hT = 2 * 3 ^ 658 from by
    rw [←this]
    apply isGreatest_max'

-- Let $$ M$$  denote the maximal value of $$ a_{1} a_{2} \cdots a_{n}$$ .
  set M := T.max' hT
  have hM1 : ∀ k ∈ T, k ≤ M := (T.isGreatest_max' hT).right
  have hM2 : M ∈ T := (T.isGreatest_max' hT).left
  replace ⟨hM2, hM3⟩ : M ∈ Icc 1 (1976 ^ 1976) ∧ M ∈ S := by simpa [T] using hM2

-- Let $$ a_{1} < a_{2} < \cdots < a_{n}$$  be positive integers whose sum is 1976 .
  obtain ⟨a, n, hn, ha1, ha2, ha3, hM3⟩ := hM3

-- $$n ≥ 2$$ since for example $$ 1976 < 2 \cdot 1974$$ .
  have hn2 : n ≥ 2 := by
    by_contra hn
    replace hn : n = 1 := by omega
    subst hn
    have c1 : M = 1976 := by
      simp at hM3
      simp at ha3
      omega
    simp [c1] at hM1
    let a := λ | 1 => 2 | 2 => 1974 | _ => 0
    have c2 : 2 * 1974 ∈ S := by
      use a, 2, by norm_num, by decide
      use by
        apply monotoneOn_of_le_succ
        . simp [Set.ordConnected_Icc]
        . simp; decide
      use by decide
      decide
    have := hM1 (2 * 1974) (by simpa [←hTS] using c2)
    omega

-- We make the following observations:
-- (1) $$ a_{1}=1$$  does not yield the maximum, since replacing $$ 1, a_{2}$$  by $$ 1+a_{2}$$  increases the product.
  have h1 : a 1 ≠ 1 := by
    by_contra h1
    let a' i := if i = 1 then 1 + a 2 else a (i + 1)
    let k := ∏ i ∈ Icc 1 (n - 1), a' i
    have c1 : k > M := by
      calc
        _ = ∏ i ∈ Icc 2 n, a' (i - 1) := by
          apply prod_nbij (. + 1)
          . simp; omega
          . sorry
          . sorry
          . simp
        _ = (1 + a 2) * ∏ i ∈ Icc 3 n, a' (i - 1) := by
          have d1 : {2} ⊆ Icc 2 n := by
            sorry
          rw [←prod_sdiff d1]
          have d2 : Icc 2 n \ {2} = Icc 3 n := by ext k; simp; omega
          rw [d2]
          have d3 : a' 1 = 1 + a 2 := by
            simp [a']
          simp [d3]
          ring_nf
        _ = (1 + a 2) * ∏ i ∈ Icc 3 n, a i := by
          apply congrArg ((1 + a 2) * .)
          apply prod_congr rfl
          intro i hi
          simp at hi
          have d1 : i ≠ 2 := by omega
          have d2 : i ≥ 1 := by omega
          simp [a', d1, d2]
        _ > a 2 * ∏ i ∈ Icc 3 n, a i := by
          sorry
        _ = ∏ i ∈ Icc 2 n, a i := by
          sorry
        _ = ∏ i ∈ Icc 1 n, a i := by
          sorry
        _ = _ := by rw [hM3]
    have c2 : k ∈ S := by
      use a', n - 1, by omega
      use by
        intro i hi
        dsimp [a']
        by_cases d1 : i = 1
        . simp [d1]
        . simp [d1, ha1 (i + 1) (by simp at hi ⊢; omega)]
      use by
        sorry
      use by
        sorry
    specialize hM1 k (by simpa [←hTS] using c2)
    omega


-- (2) $$ a_{j}-a_{i} \geq 2$$  does not yield the maximal value, since replacing $$ a_{i}, a_{j}$$  by $$ a_{i}+1, a_{j}-1$$  increases the product.
  have h2 i (hi : i ∈ Icc 1 n) j (hj : j ∈ Icc 1 n) (hij : i ≠ j) : a j - a i < 2 := by
    sorry

-- (3) $$ a_{i} \geq 5$$  does not yield the maximal value, since $$ 2\left(a_{i}-2\right)=2 a_{i}-4 > a_{i}$$ .
  have h3 i (hi : i ∈ Icc 1 n) : a i < 5 := by
    sorry

-- Since $$ 4=2^{2}$$ , we may assume that all $$ a_{i}$$  are either 2 or 3 ,
  have h4 i (hi : i ∈ Icc 1 n) : a i = 2 ∨ a i = 3 := by
    sorry

-- and $$ M=2^{k} 3^{l}$$, where $$ 2 k+3 l=1976$$ .
  obtain ⟨k, l, h5, h6⟩ : ∃ k l, M = 2 ^ k * 3 ^ l ∧ 2 * k + 3 * l = 1976 := by
    let A := {i ∈ Icc 1 n | a i = 2}
    let B := {i ∈ Icc 1 n | a i = 3}
    use #A, #B
    have c1 : Icc 1 n = A ∪ B := by
      ext i
      specialize h4 i
      simp at h4
      simp [A, B]
      omega
    rw [c1] at hM3
    rw [prod_union sorry] at hM3
    split_ands
    . calc
        _ = _ := hM3
        _ = (∏ i ∈ A, 2) * (∏ i ∈ B, 3) := by
          sorry
        _ = _ := by simp
    . sorry

-- (4) $$ k \geq 3$$  does not yield the maximal value, since $$ 2 \cdot 2 \cdot 2 < 3 \cdot 3$$ .
  have h7 : k < 3 := by
    sorry

-- Hence $$ k \leq 2$$  and $$ 2 k \equiv 1976(\bmod 3)$$  gives us $$ k=1, l=658$$  and $$ M=2 \cdot 3^{658}$$ .
  have h8 : 2 * k ≡ 1976 [MOD 3] := by
    apply_fun (. % 3) at h6
    simpa using h6

  have h9 : k = 1 := by omega
  have h10 : l = 658 := by omega
  simpa [h9, h10] using h5
