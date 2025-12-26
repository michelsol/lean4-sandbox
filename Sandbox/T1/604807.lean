import Mathlib

open Finset

/-
Let $$n$$  be an odd natural number, and let $$x$$ and $$y$$ be two rational numbers
satisfying $$x^{n}+2 y=y^{n}+2 x$$
Show that $$x=y$$.
-/
theorem algebra_604807
    (n : ℕ) (hn : Odd n)
    (x y : ℚ) (h : x ^ n + 2 * y = y ^ n + 2 * x) : x = y := by

-- We first consider ($$\boxtimes$$)
-- Let $$n \geqslant 3$$ be an odd natural number.
-- Furthermore, let $$a, b$$, and $$c$$ be three integers such that
-- $$ a^{n-1}+a^{n-2} b+\ldots+b^{n-1}=2 c^{n-1} $$
-- Then $$a=b=c=0$$.

  have h1 (n : ℕ) (hn : n ≥ 3) (a b c : ℤ)
      (g1 : ∑ k ∈ Ico 0 n, a ^ (n - 1 - k) * b ^ k = 2 * c ^ (n - 1)) :
      a = 0 ∧ b = 0 ∧ c = 0 := by
-- If this were false for some $$n$$,
-- we could choose a counterexample $$(a, b, c)$$ for which
-- the expression $$|a|+|b|+|c|$$ takes its smallest positive value.
    revert a b c
    by_contra! h1
    let S := {(a, b, c) : ℤ × ℤ × ℤ |
      ∑ k ∈ Ico 0 n, a ^ (n - 1 - k) * b ^ k = 2 * c ^ (n - 1)
      ∧ |a| + |b| + |c| > 0}
    have hS : S.Nonempty := by
      obtain ⟨a, b, c, g1, g2⟩ := h1
      use (a, b, c)
      constructor
      . exact g1
      . sorry
    have ⟨a, b, c, ⟨g1, g2⟩, g3⟩ : ∃ (a b c : ℤ) (_ : (a, b, c) ∈ S),
        ∀ (a' b' c' : ℤ), (a', b', c') ∈ S → |a'| + |b'| + |c'| > |a| + |b| + |c| := by
      sorry
-- If both $$a$$ and $$b$$ were odd,
-- the left side would be the sum of an odd number of odd summands and thus odd,
-- while the right side is even.
-- Therefore, at least one of the numbers $$a$$ and $$b$$ must be even.
    have g4 : a % 2 = 0 ∨ b % 2 = 0 := by
      by_contra! g4
      sorry
-- If, for example, $$a$$ is even, the left side has the same parity as $$b^{n-1}$$,
-- and the right side is even, so $$b$$ must also be even.
-- Similarly, one sees that $$a$$ must be even if $$b$$ is assumed to be even.
-- Therefore, both $$a$$ and $$b$$ are even.
    have g5 : a % 2 = 0 ∧ b % 2 = 0 := by
      sorry
-- Consequently, the left side is divisible by $$2^{n-1}$$ and thus, in particular, by 4,
    have g6 : (∑ k ∈ Ico 0 n, a ^ (n - 1 - k) * b ^ k) % 4 = 0 := by
      sorry
-- which implies that $$c^{n-1}$$ and hence $$c$$ is also even.
    have g7 : c % 2 = 0 := by
      rw [g1] at g6
      have f1 : c ^ (n - 1) % 2 = 0 := by omega
      by_contra! f2
      replace f2 : c % 2 = 1 := by omega
      have f3 k : c ^ k % 2 = 1 := by
        induction' k with k ih
        . simp
        . rw [pow_succ, Int.mul_emod, ih]
          omega
      specialize f3 (n - 1)
      omega
-- If we now introduce three integers $$a^{\prime}, b^{\prime}$$, and $$c^{\prime}$$ with $$a=2 a^{\prime}, b=2 b^{\prime}$$, and $$c=2 c^{\prime}$$,
    let a' := a / 2
    let b' := b / 2
    let c' := c / 2
-- then first $$ a^{\prime n-1}+a^{\prime n-2} b^{\prime}+\ldots+b^{\prime n-1}=2 c^{\prime n-1} $$
    have g8 : ∑ k ∈ Ico 0 n, a' ^ (n - 1 - k) * b' ^ k = 2 * c' ^ (n - 1) := by
      sorry
-- and secondly $$ 0 < \left|a^{\prime}\right|+\left|b^{\prime}\right|+\left|c^{\prime}\right| < |a|+|b|+|c| . $$
    have g9 : 0 < |a'| + |b'| + |c'| := by
      sorry
    have g10 : |a'| + |b'| + |c'| < |a| + |b| + |c| := by
      sorry
-- The triple $$\left(a^{\prime}, b^{\prime}, c^{\prime}\right)$$ thus contradicts the choice of $$(a, b, c)$$, and $$(\boxtimes)$$ is proved.
    have g11 := g3 a' b' c' ⟨g8, g9⟩
    omega

-- We now turn to the actual problem.
-- In the case $$n=1$$, the claim is trivial,
  have h2 (hn : n = 1) : x = y := by
    subst hn
    linarith

-- and from now on we focus only on the case $$n \geqslant 3$$.
  suffices n ≥ 3 → x = y from by
    obtain hn2 | hn2 : n = 1 ∨ n ≥ 3 := by
      rw [Nat.odd_iff] at hn
      omega
    . exact h2 hn2
    . exact this hn2
  intro hn2

-- Let $$x$$ and $$y$$ be two rational numbers such that $$x^{n}+2 x=y^{n}+2 y$$.
-- By bringing everything to one side and then factoring, we obtain
-- $$ (x-y)\left(x^{n-1}+x^{n-2} y+\ldots+y^{n-1}-2\right)=0 $$
  have h3 : x ^ n - y ^ n - 2 * x + 2 * y = 0 := by linarith [h]
  have h4 := calc
    x ^ n - y ^ n - 2 * x + 2 * y = x ^ n - y ^ n - 2 * (x - y) := by ring
    _ = (∑ k ∈ range n, x ^ k * y ^ (n - 1 - k)) * (x - y) - 2 * (x - y) := by
      congr 1
      rw [←geom_sum₂_mul]
    _ = (∑ k ∈ Ico 0 n, x ^ k * y ^ (n - 1 - k)) * (x - y) - 2 * (x - y) := by simp
    _ = (x - y) * (∑ k ∈ Ico 0 n, x ^ k * y ^ (n - 1 - k)) - 2 * (x - y) := by ring
    _ = (x - y) * (∑ k ∈ Ico 0 n, x ^ (n - 1 - k) * y ^ k) - 2 * (x - y) := by
      congr 2
      apply sum_nbij (n - 1 - .)
      . intro k hk
        simp at hk ⊢
        omega
      . intro i hi j hj
        simp at hi hj ⊢
        omega
      . intro j hj
        simp at hj ⊢
        use n - 1 - j
        omega
      . intro k hk
        congr 2
        simp at hk
        omega
    _ = (x - y) * (∑ k ∈ Ico 0 n, x ^ (n - 1 - k) * y ^ k - 2) := by
      ring
  replace h4 : (x - y) * (∑ k ∈ Ico 0 n, x ^ (n - 1 - k) * y ^ k - 2) = 0 := by simpa [h4] using h3

-- If $$x$$ and $$y$$ were different, which we will assume from now on,
-- then $$ x^{n-1}+x^{n-2} y+\ldots+y^{n-1}=2 $$ must hold.
  have h5 (hxy : x ≠ y) : ∑ k ∈ Ico 0 n, x ^ (n - 1 - k) * y ^ k = 2 := by
    simp only [mul_eq_zero] at h4
    have g1 : x - y ≠ 0 := by exact sub_ne_zero_of_ne hxy
    simp [g1] at h4
    simp
    linarith

-- Since any two rational numbers can be brought to a common denominator,
-- there exist three integers $$a, b$$, and $$c$$ with $$c \neq 0, x=a / c$$, and $$y=b / c$$.
  obtain ⟨a, b, c, hc, hac, hbc⟩ : ∃ a b c : ℤ, c ≠ 0 ∧ x = a / c ∧ y = b / c := by
    use x.num * y.den, y.num * x.den, x.den * y.den
    split_ands
    . simp
    . conv_lhs => rw [←x.num_div_den]
      field_simp
      ring
    . conv_lhs => rw [←y.num_div_den]
      field_simp
      ring

-- Substituting these fractions into (1) and then multiplying by $$c^{n-1}$$,
-- we get $$ a^{n-1}+a^{n-2} b+\ldots+b^{n-1}=2 c^{n-1} $$
  have h6 (hxy : x ≠ y) : ∑ k ∈ Ico 0 n, a ^ (n - 1 - k) * b ^ k = 2 * c ^ (n - 1) := by
    qify
    calc
    _ = ∑ k ∈ Ico 0 n, (x * c) ^ (n - 1 - k) * (y * c) ^ k := by
      apply sum_congr rfl
      intro k hk
      congr 2
      . field_simp at hac
        simp [hac]
      . field_simp at hbc
        simp [hbc]
    _ = ∑ k ∈ Ico 0 n, x ^ (n - 1 - k) * y ^ k * (c ^ (n - 1 - k) * c ^ k) := by
      apply sum_congr rfl
      intro k hk
      ring
    _ = ∑ k ∈ Ico 0 n, x ^ (n - 1 - k) * y ^ k * c ^ (n - 1) := by
      apply sum_congr rfl
      intro k hk
      congr 1
      rw [←pow_add]
      congr 1
      simp at hk
      omega
    _ = (∑ k ∈ Ico 0 n, x ^ (n - 1 - k) * y ^ k) * c ^ (n - 1) := by rw [sum_mul]
    _ = _ := by
      congr 1
      exact h5 hxy

-- From $$(\boxtimes)$$ it follows, in particular, that $$c=0$$.
  have h7 (hxy : x ≠ y) : c = 0 := by simp [h1 n hn2 a b c (h6 hxy)]

-- This contradiction shows that $$x$$ and $$y$$ must indeed be equal, thus solving the problem.
  by_contra h8
  specialize h7 h8
  contradiction
