import Mathlib

open Set

/-
A sequence of real numbers $a_{0}, a_{1}, a_{2}, \ldots$ is defined
by the formula  $$ a_{i+1}=\left\lfloor a_{i}\right\rfloor \cdot b_{i}
\quad \text { for } \quad i \geq 0 \text {; } $$
here $a_{0}$ is an arbitrary real number,
$\left\lfloor a_{i}\right\rfloor$ denotes the greatest integer not exceeding $a_{i}$,
and $ b_{i}=a_{i}-\left\lfloor a_{i}\right\rfloor$.
Prove that $a_{i}=a_{i+2}$ for $i$ sufficiently large.
-/

theorem algebra_23526
    (a : ℕ → ℝ) :
    let b i := a i - ⌊a i⌋
    (∀ i, a (i + 1) = ⌊a i⌋ * b i) →
    ∃ N, ∀ i, N ≤ i → a i = a (i + 2) := by
  intro b
  intro h0

-- First note that if $a_{0} \geq 0$, then all $a_{i} \geq 0$.
  have h1 (c1 : a 0 ≥ 0) i : a i ≥ 0 := by
    sorry

-- For $a_{i} \geq 1$ we have (in view of $ b_{i}<1$
-- and $\left\lfloor a_{i}\right\rfloor>0$ )
-- $$ \left\lfloor a_{i+1}\right\rfloor \leq a_{i+1}=
-- \left\lfloor a_{i}\right\rfloor \cdot b_{i}
-- <\left\lfloor a_{i}\right\rfloor $$
  have h2 i (c1 : a i ≥ 1) : ⌊a (i + 1)⌋ < ⌊a i⌋ := by
    have c2 : b i < 1 := by exact Int.fract_lt_one (a i)
    have c3 : ⌊a i⌋ > 0 := sorry
    rify
    calc
      ⌊a (i + 1)⌋ ≤ a (i + 1) := by apply Int.floor_le
      _ = ⌊a i⌋ * b i := by apply h0
      _ < ⌊a i⌋ * 1 := by gcongr
      _ = _ := by simp

-- The result is easy to show when $a_0 ≥ 0$
  have h3 (c1 : a 0 ≥ 0) : ∃ N, ∀ i ≥ N, a i = a (i + 2) := by
    suffices ∃ N, ∀ i ≥ N, a i = 0 from by
      obtain ⟨N, hN⟩ := this
      use N
      intro i hi
      rw [hN i (by omega), hN (i + 2) (by omega)]
    suffices ∃ i, ⌊a i⌋ = 0 from by
      obtain ⟨i, hi⟩ := this
      use (i+1)
      apply Nat.le_induction
      . simp [h0, hi]
      . intro j hj ih
        simp [h0, ih]
-- The sequence $⌊a_i⌋$ is strictly decreasing while in [1, ∞), so it must eventually reach 0
    sorry

-- Now pass to the more interesting situation where $a_{0}<0$
  suffices a 0 < 0 → ∃ N, ∀ i ≥ N, a i = a (i + 2) from by
    have c1 : a 0 ≥ 0 ∨ a 0 < 0 := by apply le_or_lt
    obtain c1 | c1 := c1
    . exact h3 c1
    . exact this c1
  clear h3
  intro h3

-- then all $a_{i} \leq 0$.
  have h4 i : a i ≤ 0 := sorry

-- The result is trivial if the sequence hits 0.
  by_cases h5 : ∃ i, a i = 0
  . obtain ⟨i, hi⟩ := h5
    use i
    suffices ∀ j ≥ i, a j = 0 from by intro j hj; iterate 2 rw [this _ (by omega)]
    apply Nat.le_induction
    . simp [h0, hi]
    . intro j hj ih
      simp [h0, ih]
-- We may assume that the sequence never hits 0.
  push_neg at h5

-- Then we have $\left\lfloor a_{i}\right\rfloor \leq-1$ for all $i$,
-- and so  $$ 1+\left\lfloor a_{i+1}\right\rfloor>a_{i+1}
-- =\left\lfloor a_{i}\right\rfloor \cdot b_{i}
-- >\left\lfloor a_{i}\right\rfloor $$
  have h6 i : 1 + ⌊a (i + 1)⌋ > ⌊a i⌋ := by
    rify
    calc
    _ > a (i + 1) := sorry
    _ = ⌊a i⌋ * b i := sorry
    _ > ⌊a i⌋ := sorry

-- this means that the sequence $\left\lfloor a_{i}\right\rfloor$ is nondecreasing.
  replace h6 i : ⌊a (i + 1)⌋ ≥ ⌊a i⌋ := by have := h6 i; linarith
  replace h6 : Monotone (⌊a .⌋) := by apply monotone_nat_of_le_succ h6

-- And since all its terms are integers from $(-\infty,-1]$,
  have h7 i : ⌊a i⌋ ≤ -1 := sorry

-- this sequence must be constant from some term on:
-- $$ \left\lfloor a_{i}\right\rfloor=c \quad \text { for } \quad i \geq i_{0} $$
  obtain ⟨c, i0, h8⟩ : ∃ c, ∃ i0, ∀ i ≥ i0, ⌊a i⌋ = c := sorry

-- c is a negative integer.
  have h9 : c < 0 := sorry

-- The defining formula becomes
-- $$ a_{i+1}=c \cdot b_{i}=c\left(a_{i}-c\right)=c a_{i}-c^{2} . $$
  have h10 i (hi : i ≥ i0) : a (i + 1) = c * a i - c ^ 2 := by
    calc
      _ = c * b i := by rw [←h8 i hi, h0]
      _ = c * (a i - c) := by congr 1; rw [←h8 i hi]
      _ = _ := by linarith

-- Consider the sequence  $$ d_{i}=a_{i}-\frac{c^{2}}{c-1} $$  (1)
  let d i := a i - c ^ 2 / (c - 1)

-- It satisfies the recursion rule
-- $$ d_{i+1}=a_{i+1}-\frac{c^{2}}{c-1}=c a_{i}-c^{2}-\frac{c^{2}}{c-1}=c d_{i} $$
  have h11 i (hi : i ≥ i0) : d (i + 1) = c * d i := by
    calc
      _ = a (i + 1) - c ^ 2 / (c - 1) := sorry
      _ = c * a i - c ^ 2 - c ^ 2 / (c - 1) := sorry
      _ = _ := sorry

-- implying  $$ d_{i}=c^{i-i_{0}} d_{i_{0}} \quad \text { for } \quad i \geq i_{0} . $$  (2)
  have h12 i (hi : i ≥ i0) : d i = c ^ (i - i0) * d i0 := sorry

-- Since all the numbers $a_{i}$ (for $i \geq i_{0}$ ) lie in $\left[c, c+1\right.$ ),
  have h13 i (hi : i ≥ i0) : a i ∈ Ico (c : ℝ) (c + 1) := sorry

-- the sequence $\left(d_{i}\right)$ is bounded.
  have h14 : Bornology.IsBounded (d '' univ) := sorry

-- The equation (2) can be satisfied only if either $d_{i_{0}}=0$ or $|c|=1$, i.e., $c=-1$.
  have h15 : d i0 = 0 ∨ c = -1 := sorry

-- Dealing with both cases,
-- We will show that (from some point on) the sequence $\left(a_{i}\right)$
-- either is constant or takes alternately two values from the interval $(-1,0)$.
-- The result will follow in both cases.
  rcases h15 with h15 | h15
  .
-- In the first case
-- $d_{i}=0$ for all $i \geq i_{0}$,
    have h16 i (hi : i ≥ i0) : d i = 0 := sorry

-- so that  $$ a_{i}=\frac{c^{2}}{c-1} \quad \text { for } \quad i \geq i_{0} $$
    have h17 i (hi : i ≥ i0) : a i = c ^ 2 / (c - 1) := by
      specialize h16 i hi
      dsimp [d] at h16
      linarith

-- The result follows
    use i0
    intro i hi
    iterate 2 rw [h17 _ (by omega)]
  .
-- In the second case
-- $c=-1$, equations (1) and (2) say that
-- $$ a_{i}=-\frac{1}{2}+(-1)^{i-i_{0}} d_{i_{0}}=
--  \begin{cases}a_{i_{0}} & \text { for } i=i_{0}, i_{0}+2, i_{0}+4, \ldots \\
--  1-a_{i_{0}} & \text { for } i=i_{0}+1, i_{0}+3, i_{0}+5, \ldots\end{cases} $$
    have h16 i (hi : i ≥ i0) : a i = - 1 / 2 + (- 1) ^ (i - i0) * d i0 := by
      specialize h12 i hi
      dsimp only [d] at h12 ⊢
      rw [h15] at h12 ⊢
      norm_num at h12 ⊢
      linarith

    have h17 k : a (2 * k + i0) = a i0 := by
      rw [h16 (2 * k + i0) (by omega)]
      dsimp only [d]
      norm_num [h15]

    have h18 k : a (2 * k + 1 + i0) = -1 - a i0 := by
      rw [h16 (2 * k + 1 + i0) (by omega)]
      dsimp only [d]
      rw [h15]
      norm_num
      ring_nf

-- The result follows
    use i0
    intro i hi
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (i - i0)
    . replace hk : i = 2 * k + i0 := by omega
      rw [hk]
      have c1 := h17 k
      have c2 := h17 (k + 1)
      ring_nf at c1 c2 ⊢
      rw [c1, c2]
    . replace hk : i = 2 * k + 1 + i0 := by omega
      rw [hk]
      have c1 := h18 k
      have c2 := h18 (k + 1)
      ring_nf at c1 c2 ⊢
      rw [c1, c2]
