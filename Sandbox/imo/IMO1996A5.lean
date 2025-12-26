import Mathlib

/- Let $P(x)$ be the real polynomial function $P(x)=a x^{3}+$ $b x^{2}+c x+d$. Prove that if $|P(x)| \leq 1$ for all $x$ such that $|x| \leq 1$, then  $$ |a|+|b|+|c|+|d| \leq 7 $$ -/
theorem algebra_24727
    (a b c d : ℝ)
    (P : ℝ → ℝ)
    (hP1 : ∀ x, P x = a * x ^ 3 + b * x ^ 2 + c * x + d)
    (hP2 : ∀ x, |x| ≤ 1 → |P x| ≤ 1)
    : |a| + |b| + |c| + |d| ≤ 7 := by
-- Considering the polynomials $\pm P( \pm x)$ we may assume w.l.o.g. that $a, b \geq$ 0 .
  wlog h1 : a ≥ 0 ∧ b ≥ 0
  . rcases (show a ≥ 0 ∨ a ≤ 0 from by apply le_total) with h2 | h2
    . rcases (show b ≥ 0 ∨ b ≤ 0 from by apply le_total) with h3 | h3
      . exact this a b c d P hP1 hP2 ⟨h2, h3⟩
      . specialize this a (-b) c (-d) (λ x ↦ -P (-x))
          (by
            intro x
            specialize hP1 (-x)
            apply_fun (-.) at hP1
            ring_nf at hP1 ⊢
            simpa using hP1)
          (by
            intro x hx
            specialize hP2 (-x) (by simpa using hx)
            simpa using hP2)
          (by split_ands <;> linarith)
        simpa
    . rcases (show b ≥ 0 ∨ b ≤ 0 from by apply le_total) with h3 | h3
      . specialize this (-a) b (-c) d (λ x ↦ P (-x))
          (by
            intro x
            specialize hP1 (-x)
            ring_nf at hP1 ⊢
            simpa using hP1)
          (by
            intro x hx
            specialize hP2 (-x) (by simpa using hx)
            simpa using hP2)
          (by split_ands <;> linarith)
        simpa
      . specialize this (-a) (-b) (-c) (-d) (λ x ↦ -P x)
          (by
            intro x
            specialize hP1 x
            apply_fun (-.) at hP1
            ring_nf at hP1 ⊢
            simpa using hP1)
          (by
            intro x hx
            specialize hP2 x (by simpa using hx)
            simpa using hP2)
          (by split_ands <;> linarith)
        simpa

  obtain ⟨h1, h1'⟩ := h1

-- We have four cases:
  rcases (show c ≥ 0 ∨ c < 0 from by apply le_or_lt) with h2 | h2
  . rcases (show d ≥ 0 ∨ d < 0 from by apply le_or_lt) with h3 | h3
-- (1) $c \geq 0, d \geq 0$. Then $|a|+|b|+|c|+|d|=a+b+c+d=P(1) \leq 1$.
    . rw [abs_of_nonneg h1, abs_of_nonneg h1', abs_of_nonneg h2, abs_of_nonneg h3]
      specialize hP1 1
      ring_nf at hP1
      specialize hP2 1 (by simp)
      rw [abs_le, hP1] at hP2
      linarith
-- (2) $c \geq 0, d<0$. Then $|a|+|b|+|c|+|d|=a+b+c-d=P(1)-2 P(0) \leq 3$.
    . rw [abs_of_nonneg h1, abs_of_nonneg h1', abs_of_nonneg h2, abs_of_neg h3]
      calc
        _ = P 1 - 2 * P 0 := by
          repeat rw [hP1]
          ring_nf
        _ ≤ _ := by
          have c1 := hP2 1 (by simp)
          have c2 := hP2 0 (by simp)
          rw [abs_le] at c1 c2
          linarith
  . rcases (show d ≥ 0 ∨ d < 0 from by apply le_or_lt) with h3 | h3
-- (3) $c<0, d \geq 0$. Then  $$ \begin{aligned} |a|+|b|+|c|+|d| & =a+b-c+d \\ & =\frac{4}{3} P(1)-\frac{1}{3} P(-1)-\frac{8}{3} P(1 / 2)+\frac{8}{3} P(-1 / 2) \leq 7 . \end{aligned} $$
    . rw [abs_of_nonneg h1, abs_of_nonneg h1', abs_of_neg h2, abs_of_nonneg h3]
      calc
        _ = (4 / 3) * P 1 - (1 / 3) * P (-1) - (8 / 3) * P (1 / 2) + (8 / 3) * P (-1 / 2) := by
          repeat rw [hP1]
          ring_nf
        _ ≤ _ := by
          have c1 := hP2 1 (by simp)
          have c2 := hP2 (-1) (by simp)
          have c3 := hP2 (1 / 2) (by norm_num [abs_div])
          have c4 := hP2 (-1 / 2) (by norm_num [abs_div])
          rw [abs_le] at c1 c2 c3 c4
          linarith
-- (4) $c<0, d<0$. Then  $$ \begin{aligned} |a|+|b|+|c|+|d| & =a+b-c-d \\ & =\frac{5}{3} P(1)-4 P(1 / 2)+\frac{4}{3} P(-1 / 2) \leq 7 \end{aligned} $$
    . rw [abs_of_nonneg h1, abs_of_nonneg h1', abs_of_neg h2, abs_of_neg h3]
      calc
        _ = (5 / 3) * P 1 - 4 * P (1 / 2) + (4 / 3) * P (-1 / 2) := by
          repeat rw [hP1]
          ring_nf
        _ ≤ _ := by
          have c1 := hP2 1 (by simp)
          have c2 := hP2 (1 / 2) (by norm_num [abs_div])
          have c3 := hP2 (-1 / 2) (by norm_num [abs_div])
          rw [abs_le] at c1 c2 c3
          linarith
