import Mathlib

open Classical Set

/-
A set of three nonnegative integers $\{x, y, z\}$ with $x < y < z$ is called historic
if $\{z-y, y-x\}=\{1776,2001\}$.
Show that the set of all nonnegative integers
can be written as the union of disjoint historic sets.
-/

theorem number_theory_25037
    :  let is_historic x y z := x < y ∧ y < z ∧ (z - y = 1776 ∧ y - x = 2001 ∨ z - y = 2001 ∧ y - x = 1776)
      ∃ (ι : Type) (I : Set ι) (u v w : ι → ℕ) (h0 : ∀ i ∈ I, is_historic (u i) (v i) (w i))
        (disj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → {u i, v i, w i} ∩ {u j, v j, w j} = (∅ : Set ℕ)),
        univ = ⋃ i ∈ I, {u i, v i, w i} :=  by
-- For convenience let us write $a=1776, b=2001,0 < a < b$.
  have hab1 : 1776 < 2001 := by norm_num
  have hab2 : 0 < 1776 := by norm_num
  generalize 1776 = a at *
  generalize 2001 = b at *
  intro is_historic


-- We construct a sequence of historic sets $H_{1}, H_{2}, H_{3}, \ldots$
-- inductively as follows:
-- define the recursive functional first
  let H_F : ∀ n : ℕ, (∀ m < n, ℕ × ℕ × ℕ) → ℕ × ℕ × ℕ
-- $H_0$ is a useless input but allows defining H over ℕ.
  | 0, h => (0, 0, 0)
-- (i) $H_{1}=\{0, a, a+b\}$,
  | 1, h => (0, a, a + b)
-- Consider the case $n + 1 ≥ 2$
  | m + 2, h => let n := m + 1
-- Let $U_{n}=H_{1} \cup$ $\cdots \cup H_{n}$.
    let Un :=
        ⋃ k ∈ Icc 1 n,
            let Hk := (h k (by simp at *; omega))
            let uk := Hk.1
            let vk := Hk.2.1
            let wk := Hk.2.2
            {uk, vk, wk}
-- and (ii) Let $y_{n}$ be the least nonnegative integer not occurring in $U_{n}$.
    let yn := sInf Unᶜ
-- We take $H_{n+1}$ to be $\left\{y_{n}, y_{n}+a, y_{n}+a+b\right\}$ if $y_{n}+a \notin U_{n}$,
    if yn + a ∉ Un then (yn, yn + a, yn + a + b)
-- and $\left\{y_{n}, y_{n}+b, y_{n}+a+b\right\}$ otherwise.
    else (yn, yn + b, yn + a + b)

-- Construct H by strong recursion, satisfying a recursive equation.
  have hH n := Nat.lt_wfRel.wf.fix_eq H_F n
  set H := Nat.lt_wfRel.wf.fix H_F
-- Call u, v, w the 3 numbers making up H.
  let u k := (H k).1
  let v k := (H k).2.1
  let w k := (H k).2.2

  use ℕ, Ioi 0, u, v, w, ?_, ?_, ?_
/- Show that each $H_k$ is an historic set -/
  . intro n hn
    specialize hH n
    match n with
    | 1 =>
      dsimp only [H_F] at hH
      simp [u, v, w, hH, is_historic]
      omega
    | (m + 1) + 1 =>
      set n := m + 1
      dsimp only [H_F] at hH
      set Un := ⋃ k ∈ Icc 1 n, {u k, v k, w k}
      set yn := sInf Unᶜ
      split_ifs at hH with hy
      . simp [u, v, w, hH, is_historic]
        omega
      . simp [u, v, w, hH, is_historic]
        omega
/- Show that the $H_k$'s are pairwise disjoint.-/
  . intro i hi j hj hij
    wlog hij : i < j
    . rw [inter_comm]
      apply this a hab2 b hab1 hH j hj i hi (by omega) (by omega)
    match i, j with
    | 1, (j' + 1) + 1 =>
      set j := j' + 1
      sorry
    | (i' + 1) + 1, (j' + 1) + 1 =>
      set i := i' + 1
      set j := j' + 1
      let hHi := hH (i + 1)
      let hHj := hH (j + 1)
      dsimp only [H_F] at hHi
      set Ui := ⋃ k ∈ Icc 1 i, {u k, v k, w k}
      set yi := sInf Uiᶜ
      dsimp only [H_F] at hHj
      set Uj := ⋃ k ∈ Icc 1 j, {u k, v k, w k}
      set yj := sInf Ujᶜ
      replace hij : i < j := by omega
/- Split in four cases, showing that each would lead to contradiction if intersection was non empty -/
      by_cases hyi : yi + a ∈ Ui
      . by_cases hyj : yj + a ∈ Uj
        . simp [hyi] at hHi
          simp [hyj] at hHj
          suffices {yi, yi + b, yi + a + b} ∩ {yj, yj + b, yj + a + b} = ∅ from by
            simpa [u, v, w, hHi, hHj]
          sorry
        . simp [hyi] at hHi
          simp [hyj] at hHj
          suffices {yi, yi + b, yi + a + b} ∩ {yj, yj + a, yj + a + b} = ∅ from by
            simpa [u, v, w, hHi, hHj]
          sorry
      . by_cases hyj : yj + a ∈ Uj
        . simp [hyi] at hHi
          simp [hyj] at hHj
          suffices {yi, yi + a, yi + a + b} ∩ {yj, yj + b, yj + a + b} = ∅ from by
            simpa [u, v, w, hHi, hHj]
          sorry
        . simp [hyi] at hHi
          simp [hyj] at hHj
          suffices {yi, yi + a, yi + a + b} ∩ {yj, yj + a, yj + a + b} = ∅ from by
            simpa [u, v, w, hHi, hHj]
          sorry

-- Finally, show that the union of historic sets is ℕ
  .
-- It suffices to show that each n ∈ ℕ is in an historic set
    ext n
    suffices ∃ k > 0, n ∈ {u k, v k, w k} from by simpa [-mem_insert_iff]
    revert n
/- We will show by induction, that if all $m < n$ are all covered by $H_k$'s with k ≤ N,
  then $n$ will necessarily also be covered by considering $H_{N+1}$-/
    apply Nat.strongRec
    intro n ihn
    choose! k hk using ihn
    rcases (by omega : n = 0 ∨ n ≥ 1) with hn | hn
    . specialize hH 1
      dsimp only [H_F] at hH
      use 1
      simp [u, v, w, hH, hn]
    . obtain ⟨hN1, hN2⟩ := ((Finset.Ico 0 n).image k).isGreatest_max' (by simp; omega)
      set N := ((Finset.Ico 0 n).image k).max' (by simp; omega)
      replace hk : ∀ m < n, m ∈ ⋃ k ∈ Icc 1 (N + 1), {u k, v k, w k} := by
        intro m hm
        have := (hk m hm).2
        simp [-mem_insert_iff]
        use (k m)
        constructor
        . simp [upperBounds] at hN2
          specialize hN2 m hm
          specialize hk m hm
          omega
        . exact this

      by_contra h2
      push_neg at h2
      specialize h2 (N + 1 + 1) (by omega)
      simp only [mem_insert_iff, mem_singleton_iff, not_or] at h2
      apply h2.1

      specialize hH (N + 1 + 1)
      dsimp only [H_F] at hH
      set Un := ⋃ k ∈ Icc 1 (N + 1), {u k, v k, w k}
      set y := sInf Unᶜ

      have h3 : y = u (N + 1 + 1) := by split_ifs at hH <;> simp [u, hH]
      suffices y = n from by omega
      dsimp [y]
      sorry
