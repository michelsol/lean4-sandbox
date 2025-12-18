import Mathlib

open Function Finset

/-
Let $M$ be an even positive integer.
The numbers $1, 2, \ldots, M$ are divided into $M/2$ pairs.
The product of the numbers in each pair must not exceed some natural number $N$.
What is the smallest $N$ for which this is possible?
Show that the answer is $\frac{M}{2}(\frac{M}{2}+1)$.
-/
theorem number_theory_639424
    (M : ℕ) (hM1 : M % 2 = 0) (hM2 : M > 0)
    (X : Set ℕ)
    (hX : X = {N : ℕ | ∃ (P : Icc 1 (M / 2) × Fin 2 → Icc 1 M) (_ : P.Bijective),
                ∀ i, (P ⟨i, 0⟩).1 * (P ⟨i, 1⟩).1 ≤ N})
    (Nmin : ℕ) (h1 : Nmin ∈ X) (h2 : ∀ N ∈ X, Nmin ≤ N)
    : Nmin = M / 2 * (M / 2 + 1) := by
-- Let $k = M/2$.
  set k := M / 2
-- The set of numbers to be paired is $S = \{1, 2, \ldots, 2k\}$.
-- We want to find the smallest possible value of $N$. Let this be $N_{min}$.
-- The problem asks us to show that $N_{min} = k(k+1)$.

-- The solution consists of two parts:
-- 1. Show that there exists a pairing such that the maximum product is $k(k+1)$.
-- This will establish that $N_{min} \le k(k+1)$.
-- 2. Show that for any pairing, the maximum product must be at least $k(k+1)$.
-- This will establish that $N_{min} \ge k(k+1)$.

-- Part 1: Construct a pairing to show $N_{min} \le k(k+1)$.
-- Consider the following specific pairing, let's call it $P_0$:\
-- Pair the smallest number with the largest, the second smallest with the second largest, and so on.
-- $P_0 = \{ (1, 2k), (2, 2k-1), \ldots, (i, 2k-i+1), \ldots, (k, k+1) \}$.
  let P0 : Icc 1 k × Fin 2 → Icc 1 M := λ
      | ⟨⟨i, hi⟩, 0⟩ => ⟨i, by simp at hi ⊢; omega⟩
      | ⟨⟨i, hi⟩, 1⟩ => ⟨2 * k - i + 1, by simp at hi ⊢; omega⟩
  have h3 : P0.Bijective := by
    refine Function.bijective_iff_has_inverse.mpr ?_
    use λ ⟨j, hj⟩ ↦
      if hj2 : j ≤ k then ⟨⟨j, by simp at hj hj2 ⊢; omega⟩, 0⟩
      else ⟨⟨2 * k - j + 1, by simp at hj hj2 ⊢; omega⟩, 1⟩
    use by
      intro ⟨⟨i, hi⟩, l⟩
      simp at hi
      match l with
      | 0 =>
        dsimp
        split_ifs with c1
        . simp
        . omega
      | 1 =>
        dsimp
        split_ifs with c1
        . omega
        . simp; omega
    sorry

-- Let $p_i = i(2k-i+1)$ be the product of the numbers in the $i$-th pair $(i, 2k-i+1)$.
-- We want to find the maximum among these products: $\max_{i=1,\ldots,k} p_i$.
-- Consider the function $f(x) = x(2k-x+1) = -x^2 + (2k+1)x$.
-- This is a quadratic function whose graph is a parabola opening downwards. The vertex of the parabola is at $x = -\frac{2k+1}{2(-1)} = \frac{2k+1}{2} = k + \frac{1}{2}$.
-- The values of $i$ are integers $1, 2, \ldots, k$. Since $i \le k < k + 1/2$, the function $f(i)$ is increasing for $i \in \{1, 2, \ldots, k\}$.
-- Thus, the maximum product occurs at the largest possible value of $i$, which is $i=k$.
-- The maximum product is $p_k = k(2k-k+1) = k(k+1)$.
-- For this pairing $P_0$, the maximum product is $k(k+1)$. So, we can choose $N = k(k+1)$.
  have h4 : k * (k + 1) ∈ X := by
    rw [hX]
    use P0, h3
    intro ⟨i, hi⟩
    simp at hi
    dsimp [P0]
    let f (x : ℝ) := x * (2 * k - x + 1)
    have c1 : 2 * k ≥ i := by omega
    rify [c1]
    suffices f i ≤ f k by
      unfold f at this
      convert this using 1
      ring
    have c2 x : f x = -(x - (k + 1 / 2)) ^ 2 + f (k + 1 / 2)  := by ring
    simpa using calc
        f i ≤ f k ↔ -(i - (k + 1 / 2)) ^ 2 + f (k + 1 / 2) ≤ -(k - (k + 1 / 2)) ^ 2 + f (k + 1 / 2) := by
          rw [c2 i, c2 k]
        _ ↔ (k - (k + 1 / 2) : ℝ) ^ 2 ≤ (i - (k + 1 / 2)) ^ 2 := by
          constructor <;> intro d1 <;> linarith
        _ ↔ (i - (k + 1 / 2) : ℝ) ≤ (k - (k + 1 / 2)) := by
          constructor <;> intro d1
          . refine tsub_le_tsub (by simp; omega) (by simp)
          . refine sq_le_sq.mpr ?_
            refine abs_le_abs_of_nonpos ?_ d1
            simp
        _ ↔ (i : ℝ) ≤ k := by
          constructor <;> intro d1 <;> linarith
        _ ↔ True := by simp [hi]

-- This implies that $N_{min} \le k(k+1)$.
  replace h4 : Nmin ≤ k * (k + 1) := h2 (k * (k + 1)) h4

-- Part 2: Show that for any pairing, $N_{min} \ge k(k+1)$.
  suffices Nmin ≥ k * (k + 1) by omega
  suffices ∀ N ∈ X, N ≥ k * (k + 1) by exact this Nmin h1
  intro N hN
  rw [hX] at hN
  obtain ⟨P, h5, h6⟩ := hN

-- Let $P = \{(a_j, b_j) : j=1, \ldots, k\}$ be an arbitrary pairing of the set $S = \{1, 2, \ldots, 2k\}$.
-- Let $N(P) = \max_j (a_j b_j)$. We want to show that $N(P) \ge k(k+1)$ for any $P$.

-- Consider the set of the $k$ largest numbers in $S$, let this set be $S_H = \{k+1, k+2, \ldots, 2k\}$.
  let SH := Icc (k + 1) (2 * k)
-- Also consider the set of the $k-1$ smallest numbers, $S_L = \{1, 2, \ldots, k-1\}$.
  let SL := Icc 1 (k - 1)
-- The number $k$ is in neither $S_H$ nor $S_L$.

-- Let $x$ be any number from $S_H$. So $x \ge k+1$. Let $y$ be its partner in the pairing $P$.
  have h7 : Nonempty ({ x // x ∈ Icc 1 k } × Fin 2) := by
    use ⟨1, by simp; omega⟩, 0, by norm_num
  have h8 x (hx : x ∈ SH) : ∃ (y : ℕ) (hy : y ∈ Icc 1 M),
      let i := P.invFun ⟨x, by simp [SH] at hx ⊢; omega⟩
      P ⟨i.1, i.2⟩ = x ∧ P ⟨i.1, 1 - i.2⟩ = y := by
    sorry
  choose! y h8 h9 using h8

-- If $y \ge k$:
-- In this case, the product $xy \ge (k+1)k$.
-- Since $N(P)$ is the maximum of all products in the pairing $P$, $N(P) \ge xy \ge k(k+1)$.
  have h10 x (hx : x ∈ SH) (c1 : y x ≥ k) : N ≥ k * (k + 1) := by
    let i := P.invFun ⟨x, by simp [SH] at hx ⊢; omega⟩
    calc
      N ≥ _ := h6 i.1
      _ = x * y x := by
        obtain ⟨h9, h10⟩ : (P ⟨i.1, i.2⟩).1 = x ∧ (P ⟨i.1, 1 - i.2⟩).1 = y x := h9 x hx
        obtain c1 | c1 : i.2 = 0 ∨ i.2 = 1 := by omega
        . simp [c1] at h9 h10
          simp [h9, h10]
        . simp [c1] at h9 h10
          simp [h9, h10]
          ring
      _ ≥ (k + 1) * k := by
        gcongr
        simp [SH] at hx
        omega
      _ = _ := by ring

-- If $$y≥k$$ occurs for at least one $x \in S_H$, then the condition $N(P) \ge k(k+1)$ is satisfied.
-- If it never occured, each $x \in S_H$ would be paired with a number $y ∈ S_L$.
-- But this is impossible as $$\#S_H=k$$ and $$\#S_L=k-1$$.
  obtain ⟨x, h11, h12⟩ : ∃ x ∈ SH, y x ≥ k := by
    by_contra! h11
    have c1 : Set.InjOn y SH := sorry
    have c2 : SH.image y ⊆ SL := by
      intro z hz
      obtain ⟨x, hx1, hx2⟩ := by simpa only [mem_image] using hz
      specialize h11 x hx1
      rw [hx2] at h11
      specialize h8 x hx1
      simp at h8
      simp [SL]
      omega
    replace c2 : #(SH.image y) ≤ #SL := by exact card_le_card c2
    have c3 : #(SH.image y) = #SH := by exact card_image_of_injOn c1
    rw [c3] at c2
    simp [SH, SL] at c2
    omega

-- This shows that $N_{min} \ge k(k+1)$.
  exact h10 x h11 h12
