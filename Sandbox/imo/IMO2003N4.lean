import Mathlib

open Finset

/- Let $b$ be an integer greater than 5 .
For each positive integer $n$, consider the number  $ x_{n}=\underbrace{11 \ldots 1}_{n-1} \underbrace{22 \ldots 2}_{n} 5, $  written in base $b$.

Prove that the following condition holds if and only if $b=10$ :
There exists a positive integer $M$ such that for every integer $n$ greater than $M$,
the number $x_{n}$ is a perfect square.
-/
theorem number_theory_25150
    (b : ℤ)
    (hb : b > 5)
    (x : ℕ → ℤ)
    (hx : ∀ n > 0, x n = 5 + ∑ i ∈ Icc 1 n, 2 * b ^ i + ∑ i ∈ Icc (n + 1) (2 * n - 1), b ^ i)
    : (∃ (M : ℕ) (_ : M > 0), ∀ n > M, ∃ k, x n = k * k) ↔ b = 10 := by
  constructor
-- Assume that $b \geq 6$ has the required property.
  . intro ⟨M, hM, h1⟩
    replace hb : b ≥ 6 := by omega

-- Consider the sequence $y_{n}=(b-1) x_{n}$.
    let y n := (b - 1) * x n

-- From the definition of $x_{n}$ we easily find that $y_{n}=b^{2 n}+$ $b^{n+1}+3 b-5$.
    have h2 n (hn : n > 0) : y n = b ^ (2 * n) + b ^ (n + 1) + 3 * b - 5 := by
      specialize hx n hn
      dsimp [y]
      rw [hx]
      qify
      rw [show Icc 1 n = Ico 1 (n + 1) from rfl]
      rw [show Icc (n + 1) (2 * n - 1) = Ico (n + 1) (2 * n) from by ext i; simp; omega]
      rw [←mul_sum]
      rw [geom_sum_Ico]
      . rw [geom_sum_Ico]
        . have : (b - 1 : ℚ) ≠ 0 := by norm_cast; omega
          field_simp
          ring
        . norm_cast; omega
        . omega
      . norm_cast; omega
      . omega

-- Then $y_{n} y_{n+1}=(b-1)^{2} x_{n} x_{n+1}$ is a perfect square for all $n > M$.
    have h3 n (hn : n > 0) : y n * y (n + 1) = (b - 1) ^ 2 * x n * x (n + 1) := by
      ring

    have h3' n (hn : n > M) : ∃ k, y n * y (n + 1) = k * k := by
      have ⟨k1, c1⟩ := h1 n hn
      have ⟨k2, c2⟩ := h1 (n + 1) (by omega)
      dsimp [y]
      rw [c1, c2]
      use (b - 1) * k1 * k2
      ring

-- Also, straightforward calculation
-- implies $ \left(b^{2 n+1}+\frac{b^{n+2}+b^{n+1}}{2}-b^{3}\right)^{2} < y_{n} y_{n+1} < \left(b^{2 n+1}+\frac{b^{n+2}+b^{n+1}}{2}+b^{3}\right)^{2} $
-- (We use ℤ division as $b^{n+2} - b^{n+1}$ is even.)
    have h4 n (hn : n > 0) :
      (b ^ (2 * n + 1) + (b ^ (n + 2) + b ^ (n + 1)) / 2 - b ^ 3) ^ 2 < y n * y (n + 1) := by
      sorry

    have h4' n (hn : n > 0 ) : y n * y (n + 1) < (b ^ (2 * n + 1) + (b ^ (n + 2) + b ^ (n + 1)) / 2 + b ^ 3) ^ 2 := by
      sorry

-- Hence for every $n > M$ there is an integer $a_{n}$ such that $\left|a_{n}\right| < b^{3}$
-- and $ \begin{aligned} y_{n} y_{n+1} & =\left(b^{2 n}+b^{n+1}+3 b-5\right)\left(b^{2 n+2}+b^{n+2}+3 b-5\right) \ & =\left(b^{2 n+1}+\frac{b^{n+1}(b+1)}{2}+a_{n}\right)^{2} . \end{aligned} $  (1)
    have h5 n (hn : n > M) : ∃ a : ℤ, |a| < b ^ 3 ∧
      y n * y (n + 1) = (b ^ (2 * n + 1) + (b ^ (n + 1) * (b + 1)) / 2 + a) ^ 2 := by
      sorry

    choose! a ha using h5
    have h5' n (hn : n > M) := (ha n hn).left
    have h5 n (hn : n > M) := (ha n hn).right -- (1)

-- Now considering this equation modulo $b^{n}$ we obtain $(3 b-5)^{2} \equiv a_{n}^{2}$,
    have h6 n (hn : n > M) : (3 * b - 5) ^ 2 ≡ a n ^ 2 [ZMOD b ^ n] := by
      sorry

-- For $n > M$ and $ > 3$ we get $a_{n}= \pm(3 b-5)$.
    have h7 n (hn : n > M) (hn' : n > 3) : a n = 3 * b - 5 ∨ a n = -(3 * b - 5) := by
      sorry

-- We will split into two cases.
    by_cases h7' : ∃ (n : ℕ) (hn : n > M) (hn' : n > 3), a n = 3 * b - 5
-- If $a_{n}=3 b-5$ for some n.
    . replace ⟨n, hn, h7⟩ := h7'
-- then  substituting in (1) yields $\frac{1}{4} b^{2 n}\left(b^{4}-14 b^{3}+45 b^{2}-\right.$ $52 b+20)=0$,
-- with the unique positive integer solution $b=10$.
      have h8 : (1 / 4 : ℚ) * b ^ (2 * n) * (b ^ 4 - 14 * b ^ 3 + 45 * b ^ 2 - 52 * b + 20) = 0 := by
        sorry

      have h9 : b ^ 4 - 14 * b ^ 3 + 45 * b ^ 2 - 52 * b + 20 = 0 := by
        apply_fun ((4 / b ^ (2 * n) : ℚ) * .) at h8
        have c1 : b ≠ 0 := by omega
        qify
        simpa [c1] using h8

      have h10 : (b - 10) * (b - 2) * (b - 1) * (b - 1) = 0 := by
        ring_nf at h9 ⊢
        simpa using h9
      iterate 3 rw [mul_eq_zero] at h10
      omega

-- Also, if $a_{n}=-3 b+5$,
    .
      push_neg at h7'
      replace h7' n (hn : n > M) (hn' : n > 3) : a n = -(3 * b - 5) := by
        specialize h7 n hn hn'
        specialize h7' n hn hn'
        omega
-- we similarly obtain $\frac{1}{4} b^{2 n}\left(b^{4}-14 b^{3}-3 b^{2}+28 b+20\right)-$ $2 b^{n+1}\left(3 b^{2}-2 b-5\right)=0$ for each $n$,
      have h8 n (hn : n > M) (hn' : n > 3) :
          (1 / 4 : ℚ) * b ^ (2 * n) * (b ^ 4 - 14 * b ^ 3 - 3 * b ^ 2 + 28 * b + 20) -
          2 * b ^ (n + 1) * (3 * b ^ 2 - 2 * b - 5) = 0 := by
        sorry

-- which is impossible.
      exfalso
      sorry

-- For $b=10$ it is easy to show that $x_{n}=\left(\frac{10^{n}+5}{3}\right)^{2}$ for all $n$.
  . intro h1
    subst h1
    have h2 n (hn : n > 0) : x n = ((10 ^ n + 5) / 3) ^ 2 := by
      specialize hx n hn
      sorry

    use 1, by simp
    intro n hn
    specialize h2 n (by omega)
    rw [h2]
    use (10 ^ n + 5) / 3
    ring
