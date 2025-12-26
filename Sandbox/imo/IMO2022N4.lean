import Mathlib

open Finset

/-
Let $a_{1}=11^{11}, a_{2}=12^{12}, a_{3}=13^{13}$,
and  $$ a_{n}=\left|a_{n-1}-a_{n-2}\right|+\left|a_{n-2}-a_{n-3}\right|, \quad n \geq 4 $$
Determine $a_{14^{14}}$.
-/

theorem number_theory_25080
    (a : ℤ → ℤ)
    (ha : ∀ n ≥ 4, a n = |a (n - 1) - a (n - 2)| + |a (n - 2) - a (n - 3)|)
    (ha1 : a 1 = 11 ^ 11)
    (ha2 : a 2 = 12 ^ 12)
    (ha3 : a 3 = 13 ^ 13)
    : a (14 ^ 14) = 1 := by

-- Define $b_{n}=\left|a_{n+1}-a_{n}\right|$.
  let b n := |a (n + 1) - a n|


-- $a_{n+1}=b_{n-1}+b_{n-2}$
  have h1 n (hn : n ≥ 3) : a (n + 1) = b (n - 1) + b (n - 2) := by
    dsimp [b]
    specialize ha (n + 1) (by omega)
    ring_nf at ha ⊢
    simpa

-- $a_{n}=b_{n-2}+b_{n-3}$
  have h2 n (hn : n ≥ 4) : a n = b (n - 2) + b (n - 3) := by
    dsimp [b]
    specialize ha n (by omega)
    ring_nf at ha ⊢
    simpa

-- From the 2 previous equalities we obtain $b_{n}=\left|b_{n-1}-b_{n-3}\right|$.
  have h3 n (hn : n ≥ 4) : b n = |b (n - 1) - b (n - 3)| := by
    conv_lhs => dsimp [b]
    rw [h1 n (by omega), h2 n (by omega)]
    ring_nf

-- From this relation we deduce that $b_{m} \leq \max \left(b_{n}, b_{n+1}, b_{n+2}\right)$
-- for all $m \geq n$,
  have h4 n (hn : n ≥ 4) m (hm : m ≥ n) : b m ≤ b n ⊔ b (n + 1) ⊔ b (n + 2) := by
    sorry

-- and consequently $b_{n}$ is bounded.


-- Lemma. If $\max \left(b_{n}, b_{n+1}, b_{n+2}\right)=M \geq 2$,
-- then $\max \left(b_{n+6}, b_{n+7}, b_{n+8}\right) \leq$ $M-1$.
  have h6 n (hn : n ≥ 4) M (hM : M ≥ 2) (c1 : b n ⊔ b (n + 1) ⊔ b (n + 2) = M) :
      b (n + 6) ⊔ b (n + 7) ⊔ b (n + 8) ≤ M - 1 := by

-- Proof. Assume the opposite.
    by_contra c2
    replace c2 : M ≤ b (n + 6) ⊔ b (n + 7) ⊔ b (n + 8) := by omega
    iterate 2 rw [le_max_iff] at c2

-- Suppose that $b_{j}=M, j \in\{n, n+1, n+2\}$
    obtain ⟨j, hj1, hj2⟩ : ∃ j ∈ ({n, n + 1, n + 2} : Finset ℤ), b j = M := by sorry

-- and let $b_{j+1}=x$ and $b_{j+2}=y$.
    let x := b (j + 1)
    let y := b (j + 2)


-- $x ≤ M$
    have c4 : x ≥ 0 := by simp [x, b]
    have c4' : x ≤ M := by
      specialize h4 n hn (j + 1) (by simp at hj1; omega)
      omega
-- $y ≤ M$
    have c5 : y ≥ 0 := by simp [y, b]
    have c5' : y ≤ M := by
      specialize h4 n hn (j + 2) (by simp at hj1; omega)
      omega
-- $M - y ≤ M$
    have c6 : M - y ≥ 0 := by omega
    have c6' : M - y ≤ M := by simp [y, b]

-- Thus $b_{j+3}=M-y$.
    have c3 : b (j + 3) = M - y := by
      have d1 : b (j + 3) = |b (j + 2) - b j| := by
        specialize h3 (j + 3) (by simp at hj1; omega)
        ring_nf at h3 ⊢; simpa
      rw [d1, hj2]
      show |y - M| = M - y
      rw [abs_eq_neg_self.mpr (by omega)]
      omega

-- Now we split into four cases
-- Either $x, y, M-y$ are all less than $M$ or $x = M$ or $y = M$ or $y = 0$.
-- We will show that in every case $M$ divides both $x$ and $y$.
    have c7 : M ∣ x ∧ M ∣ y := by
      rcases (show x < M ∧ y < M ∧ M - y < M ∨ x = M ∨ y = M ∨ y = 0 from by omega)
        with ⟨c4', c5', c6'⟩ | c4' | c5' | c6'
  -- If $x, y, M-y$ are all < $M$, then all the sequence is < M and the contradiction follows.
      . have d0 : b j = M := by simpa
        have dn : ∀ m > j, 0 ≤ b m ∧ b m < M := by
          have d1 : 0 ≤ b (j + 1) ∧ b (j + 1) < M := by simp [c4', b]
          have d2 : 0 ≤ b (j + 2) ∧ b (j + 2) < M := by simp [c5', b]
          have d3 : 0 ≤ b (j + 3) ∧ b (j + 3) < M := by simp [c3, y]; omega
          apply @Int.strongRec (j+4)
          . intro k hk1 hk2
            rcases (by omega : k = j + 1 ∨ k = j + 2 ∨ k = j + 3) with hk | hk | hk
            all_goals
              subst hk
              omega
          . intro k hk1 ih hk2
            have := ih (k - 1) (by omega) (by omega)
            have := ih (k - 3) (by omega) (by omega)
            have : |b (k - 1) - b (k - 3)| < M := by rw [abs_lt]; omega
            rw [h3 _ (by simp at hj1; omega)]; ring_nf at this ⊢; simpa
        have := dn (n + 6) (by simp at hj1; omega)
        have := dn (n + 7) (by simp at hj1; omega)
        have := dn (n + 8) (by simp at hj1; omega)
        omega

  -- Case $x=M$.
      .
  -- Then from $j$, the sequence has the form $M, M, y, M-y, y, \ldots$,
        have d0 : b j = M := by simpa
        have d1 : b (j + 1) = M := by simpa
        have d2 : b (j + 2) = y := by simp
        have d3 : b (j + 3) = M - y := by simpa
        have d4 : b (j + 4) = y := by
          suffices |b (j + 3) - b (j + 1)| = y from by
            rw [h3 (j + 4) (by simp at hj1; omega)]
            ring_nf at this ⊢
            simpa
          rw [d3, d1]
          simp [y, b]
  -- and since $\max (y, M-y, y)=M$
        have d5 : y ⊔ (M - y) ⊔ y = M := by
          sorry
  -- we must have $y=0$ or $y=M$.
        have d6 : y = 0 ∨ y = M := by omega
        constructor
        . simp [c4']
        . obtain d6 | d6 := d6 <;> simp [d6]

  -- Case $y=M$.
      .
  -- Then from $j$, the sequence has the form $M, x, M, 0, x, M-x, \ldots$,
        have d0 : b j = M := by simpa
        have d1 : b (j + 1) = x := by simp
        have d2 : b (j + 2) = M := by simpa
        have d3 : b (j + 3) = 0 := by omega
        have d4 : b (j + 4) = x := sorry
        have d5 : b (j + 5) = M - x := sorry
  -- and since $\max (0, x, M-x)=M$
        have d6 : 0 ⊔ x ⊔ M - x = M := by
          sorry
  -- we must have $x=0$ or $x=M$.
        have d7 : x = 0 ∨ x = M := by omega
        constructor
        . obtain d7 | d7 := d7 <;> simp [d7]
        . simp [c5']
  -- Case $y=0$.
      .
  -- Then the sequence is $M, x, 0, M, M-x, M-x, x, \ldots$
        have d0 : b j = M := by simpa
        have d1 : b (j + 1) = x := by simp
        have d2 : b (j + 2) = 0 := by simpa
        have d3 : b (j + 3) = M := by omega
        have d4 : b (j + 4) = M - x := sorry
        have d5 : b (j + 5) = M - x := sorry
        have d6 : b (j + 6) = x := sorry
  -- and since $\max (M-x, x, x)=M$,
        have d7 : (M - x) ⊔ x ⊔ x = M := by sorry
  -- we have $x=0$ or $x=M$.
        have d8 : x = 0 ∨ x = M := by omega
        sorry

-- From the recurrence formula $M$ also divides $b_{i}$ for every $i <= j$.
    have c8 i (hi : i ≤ j) : M ∣ b i := by
      sorry
-- However, $b_{2}$ and $b_{4}$ are relatively prime, a contradiction.
    have ha4 : a 4 = 13 ^ 13 - 11 ^ 11 := by
      specialize ha 4 (by norm_num)
      ring_nf at ha
      rw [ha1, ha2, ha3] at ha
      norm_num at ha ⊢
      simpa
    have ha5 : a 5 = 11 ^ 11 - 12 ^ 12 + 13 ^ 13 := by
      specialize ha 5 (by norm_num)
      ring_nf at ha
      rw [ha4, ha2, ha3] at ha
      norm_num at ha ⊢
      simpa
    have c9 : IsCoprime (b 2) (b 4) := by
      dsimp [b]
      rw [ha2, ha3, ha4, ha5]
      norm_num
    have c10 := c8 2 (by simp at hj1; omega)
    have c11 := c8 4 (by simp at hj1; omega)
    rw [Int.isCoprime_iff_gcd_eq_one] at c9
    have c12 := Int.dvd_gcd c10 c11
    rw [c9] at c12
    have c13 := Int.eq_one_of_dvd_one (by omega) c12
    omega

-- From $\max \left(b_{1}, b_{2}, b_{3}\right) \leq 13^{13}$
  have h7 : b 1 ⊔ b 2 ⊔ b 3 ≤ 13 ^ 13 := by
    have ha4 : a 4 = 13 ^ 13 - 11 ^ 11 := by
      specialize ha 4 (by norm_num)
      ring_nf at ha
      rw [ha1, ha2, ha3] at ha
      norm_num at ha ⊢
      simpa
    dsimp [b]
    rw [ha1, ha2, ha3, ha4]
    norm_num

-- and from the lemma we deduce inductively that $b_{n} \leq 1$ for all $n \geq 6 \cdot 13^{13}-5$.
  have h8 n (hn : n ≥ 6 * 13 ^ 13 - 5) : b n ≤ 1 := by
    sorry

-- Hence $a_{n}=b_{n-2}+b_{n-3}$ takes only the values $0,1,2$ for $n \geq 6 \cdot 13^{13}-2$.
  have h9 n (hn : n ≥ 6 * 13 ^ 13 - 2) : a n = 0 ∨ a n = 1 ∨ a n = 2 := by
    have c1 : a n = b (n - 2) + b (n - 3) := by
      specialize ha n (by omega)
      rw [ha]
      dsimp [b]
      ring_nf
    have : b (n - 2) ≥ 0 := by simp [b]
    have : b (n - 2) ≤ 1 := h8 (n - 2) (by omega)
    have : b (n - 3) ≥ 0 := by simp [b]
    have : b (n - 3) ≤ 1 := h8 (n - 3) (by omega)
    omega

-- In particular, $a_{14^{14}}$ is 0,1 , or 2 .
  have h10 : a (14 ^ 14) ∈ ({0, 1, 2} : Set ℤ) := by simpa using h9 (14 ^ 14) (by norm_num)

-- On the other hand, the sequence $a_{n}$ modulo 2 is
-- as follows: $1,0,1,0,0,1,1 ; 1,0,1,0, \ldots$
  have a1 : a 1 % 2 = 1 := by norm_num [ha1]
  have a2 : a 2 % 2 = 0 := by norm_num [ha2]
  have a3 : a 3 % 2 = 1 := by norm_num [ha3]
  have a4 : a 4 % 2 = 0 := sorry
  have a5 : a 5 % 2 = 0 := sorry
  have a6 : a 6 % 2 = 1 := sorry
  have a7 : a 7 % 2 = 1 := sorry
-- and therefore it is periodic with period 7 .
  have h11 : a.Periodic 7 := by
    sorry

-- Finally, $14^{14} \equiv 0$ modulo 7 ,
  have h12 : 14 ^ 14 % 7 = 0 := by norm_num

-- from which we obtain $a_{14^{14}} \equiv a_{7} \equiv 1(\bmod 2)$.
  have h13 : a (14 ^ 14) % 2 = a 7 % 2 := by
    sorry

-- Therefore $a_{14^{14}}=1$.
  specialize h9 (14 ^ 14) (by norm_num)
  omega
