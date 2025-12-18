import Mathlib

open Finset

/-
Suppose that 1000 students are standing in a circle.
Prove that there exists an integer $k$ with $100 \leq k \leq 300$ such that
in this circle there exists a contiguous group of $2 k$ students,
for which the first half contains the same number of girls as the second half.
-/

theorem number_theory_24116
    (a : ℤ → ℤ)
-- Let $a_{i}=1$ if the $i$ th student is a girl, and $a_{i}=0$ otherwise.
    (boyorgirl_a : ∀ k, a k = 0 ∨ a k = 1)
-- Number the students consecutively from 1 to 1000.
-- We expand this notion for all integers $i$ by setting
-- $a_{i+1000}=$ $a_{i-1000}=a_{i}$.
    (periodic_a : Function.Periodic a 1000 )
    : ∃ (k : ℤ) (_ : 100 ≤ k) (_ : k ≤ 300) (i : ℤ),
        { t ∈ Ico i (i + k) | a t = 1 }.card = { t ∈ Ico (i + k) (i + k + k) | a t = 1 }.card := by

-- Let  $$ S_{k}(i)=a_{i}+a_{i+1}+\cdots+a_{i+k-1} $$
  let S (k : ℤ) (i : ℤ) := ∑ t ∈ Ico i (i + k), a t

-- Now the statement of the problem can be reformulated as follows:
-- There exist an integer $k$ with $100 \leq k \leq 300$ and an index $i$ such that
-- $S_{k}(i)=S_{k}(i+k)$.
  suffices ∃ (k : ℤ) (_ : 100 ≤ k) (_ : k ≤ 300) (i : ℤ), S k i = S k (i + k) from by
    obtain ⟨k, k_ge, k_le, i, h⟩ := this
    use k, k_ge, k_le
    use i
    have : ∀ i j, ∑ t ∈ Ico i j, a t = ∑ t ∈ Ico i j, if a t = 1 then 1 else 0 := by
      intro i j
      rw [sum_congr rfl]
      intro t ht
      specialize boyorgirl_a t
      omega
    dsimp [S] at h
    iterate 2 rw [this] at h
    iterate 2 rw [card_filter]
    simpa using h

-- Assume now that this statement is false.
  by_contra h
  push_neg at h

-- Choose an index $i$ such that $S_{100}(i)$ attains the maximal possible value.
  -- Taking the max over [0, 1000)
  let i :=
    let hm := ((Ico 0 1000).image (S 100)).isGreatest_max' (by simp)
    (Finset.mem_image.mp hm.1).choose
  have S100_le : ∀ t ∈ Ico 0 1000, S 100 t ≤ S 100 i := by
    let hm := ((Ico 0 1000).image (S 100)).isGreatest_max' (by simp)
    let M := ((Ico 0 1000).image (S 100)).max' sorry
    obtain ⟨_, S100i : S 100 i = M⟩ := (Finset.mem_image.mp hm.1).choose_spec
    have : ∀ x, ∀ t ∈ Ico 0 1000, S 100 t = x → x ≤ M := by simpa [upperBounds] using hm.2
    intro t ht
    specialize this (S 100 t) t ht rfl
    rwa [S100i]
  -- By periodicity, this is a max over ℤ.
  replace S100_le : ∀ t, S 100 t ≤ S 100 i := by
    sorry

-- In particular, we have $S_{100}(i-100)-S_{100}(i)<0$ and $S_{100}(i)-S_{100}(i+100)>0$,
-- for if we had an equality, then the statement would hold.
  let T k j := S k j - S k (j + 100)
  have h1 : T 100 (i - 100) < 0 := by
    suffices T 100 (i - 100) ≤ 0 ∧ T 100 (i - 100) ≠ 0 from by omega
    dsimp [T]
    split_ands
    . specialize S100_le (i - 100); ring_nf at S100_le ⊢; omega
    . intro h1; specialize h 100 (by norm_num) (by norm_num) (i - 100); omega

  have h1_2 : T 100 i > 0 := by
    sorry

-- This means that the function $S'(j)=S(j)-$ $S(j+100)$ changes sign somewhere
-- on the segment $[i-100, i]$, so there exists some index $j \in$ $[i-100, i-1]$ such that
-- $$ S_{100}(j) \leq S_{100}(j+100)-1, \quad \text { but } \quad S_{100}(j+1)
-- \geq S_{100}(j+101)+1 $$   (1)
  let j := { t ∈ Ico (i - 100) i | T 100 t ≤ 0 }.max' (by use (i - 100); simp; omega)
  have h2 : T 100 j ≤ -1 := by
    sorry
  have h2_2 : T 100 (j + 1) ≥ 1 := by
    sorry

-- Subtracting the first inequality from the second one,
-- we get $a_{j+100}-a_{j} \geq a_{j+200}-a_{j+100}+2$,
  have h3 : a (j + 100) - a j ≥ a (j + 200) - a (j + 100) + 2 := by
    sorry

-- so  $$ a_{j}=0, \quad a_{j+100}=1, \quad a_{j+200}=0 $$
  have aj_eq : a j = 0 := sorry
  have ajadd100_eq : a (j + 100) = 1 := sorry
  have ajadd200_eq : a (j + 200) = 0 := sorry
  clear h3

-- Substituting this into the inequalities of (1),
-- we also obtain $S_{99}(j+1) \leq S_{99}(j+101) \leq S_{99}(j+1)$,
-- which implies  $$ S_{99}(j+1)=S_{99}(j+101) . $$   (2)
  have h4 : S 99 (j + 1) = S 99 (j + 101) := by
    have : S 99 (j + 1) ≤ S 99 (j + 101) := sorry
    have : S 99 (j + 101) ≤ S 99 (j + 1) := sorry
    omega

-- Now let $k$ and $\ell$ be the least positive integers such that
-- $a_{j-k}=1$ and $a_{j+200+\ell}=1$.
  let k := { t ∈ Ico 0 1000 | a (j - t) = 1 }.min' (by
    have := periodic_a (j - 900); use 900; simp; ring_nf at ajadd100_eq this ⊢; omega)
  have k_ge_0 : k ≥ 0 := sorry
  replace hk : ∀ t < k, a (j - t) = 0 := sorry
  let l := { t ∈ Ico 0 1000 | a (j + 200 + t) = 1 }.min' (by
    have := periodic_a (j + 100); use 900; simp; ring_nf at ajadd100_eq this ⊢; omega)
  replace hl : ∀ t < l, a (j + 200 + t) = 0 := sorry
  have l_ge_0 : l ≥ 0 := sorry

-- Assume first that l ≤ k
  rcases (by omega : l ≤ k ∨ k ≤ l) with l_le_k | k_le_l
  .
-- If $k \geq 200$ then we have $a_{j}=a_{j-1}=\cdots=a_{j-199}=0$,
    rcases (by omega : k ≥ 200 ∨ k ≤ 199) with k_ge_200 | k_le_199
    . replace hk : ∀ t < 200, a (j - t) = 0 := by intro t ht; exact hk t (by omega)
-- so $S_{100}(j-199)=S_{100}(j-99)=0$, which contradicts the initial assumption.
      have h1 : S 100 (j - 199) = 0 := by
        apply sum_eq_zero
        intro t ht
        specialize hk (j - t) (by simp at ht ⊢; omega)
        ring_nf at hk ⊢; simpa
      have h2 : S 100 (j - 99) = 0 := sorry
      apply h 100 (by norm_num) (by norm_num) (j - 199)
      ring_nf at h1 h2 ⊢
      omega
-- Hence $\ell \leq k \leq 199$.
-- Finally, we have  $$ \begin{gathered} S_{100+\ell}(j-\ell+1)
-- =\left(a_{j-\ell+1}+\cdots+a_{j}\right)+S_{99}(j+1)+a_{j+100}
-- =S_{99}(j+1)+1, \\
    have h5 : S (100 + l) (j - l + 1) = S 99 (j + 1) + 1 := calc
      _ = S l (j - l + 1) + S 99 (j + 1) + a (j + 100) := sorry
      _ = 0 + S 99 (j + 1) + 1 := sorry
      _ = _ := by simp
-- S_{100+\ell}(j+101)
-- =S_{99}(j+101)+\left(a_{j+200}+\cdots+a_{j+200+\ell-1}\right)+a_{j+200+\ell}
-- =S_{99}(j+101)+1 . \end{gathered} $$
    have h6 : S (100 + l) (j + 101) = S 99 (j + 101) + 1 := calc
      _ = S 99 (j + 101) + S l (j + 200) + a (j + 200 + l) := sorry
      _ = S 99 (j + 101) + 0 + 1 := sorry
      _ = _ := sorry
-- Comparing with (2) we get
-- $S_{100+\ell}(j-\ell+1)=S_{100+\ell}(j+101)$ and $100+\ell \leq 299$,
    rw [←h4] at h6
    -- specialize hk
    apply h (100 + l) (by omega) (by omega) (j - l + 1)
    ring_nf at h5 h6 ⊢
    omega
-- which again contradicts our assumption.

-- The case k ≤ l is symmetrical
  .
    rcases (by omega : l ≥ 200 ∨ l ≤ 199) with l_ge_200 | l_le_199
    . replace hl : ∀ t < 200, a (j + 200 + t) = 0 := by intro t ht; exact hl t (by omega)
      have h1 : S 100 (j + 200) = 0 := by
        sorry
      have h2 : S 100 (j + 300) = 0 := by
        sorry
      apply h 100 (by norm_num) (by norm_num) (j + 200)
      ring_nf at h1 h2 ⊢
      omega

    have h5 : S (100 + k) (j - k) = 1 + S 99 (j + 1) := calc
      _ = a (j - k) + S k (j - k + 1) + S 99 (j + 1) := sorry
      _ = 1 + 0 + S 99 (j + 1) := sorry
      _ = _ := by simp

    have h6 : S (100 + k) (j + 100) = 1 + S 99 (j + 101) := calc
      _ = a (j + 100) + S 99 (j + 101) + S k (j + 200) := sorry
      _ = 1 + S 99 (j + 101) + 0 := sorry
      _ = _ := by simp

    rw [←h4] at h6

    apply h (100 + k) (by omega) (by omega) (j - k)
    ring_nf at h5 h6 ⊢
    omega
