import Mathlib

open Finset

/- Show that if $$a, b, c$$ are the lengths of the sides of a triangle and if $$2 S=a+b+c$$, then
  $$ \frac{a^{n}}{b+c}+\frac{b^{n}}{c+a}+\frac{c^{n}}{a+b} \geq\left(\frac{2}{3}\right)^{n-2} S^{n-1}, \quad n \geq 1 $$ -/

theorem other_24099
    (a b c : ℝ)
    (ha1 : a > 0)
    (hb1 : b > 0)
    (hc1 : c > 0)
    (ha2 : a < b + c)
    (hb2 : b < a + c)
    (hc2 : c < a + b)
    (S : ℝ)
    (hS : 2 * S = a + b + c)
    (n : ℕ)
    (hn : n ≥ 1) :
    a ^ n / (b + c) + b ^ n / (c + a) + c ^ n / (a + b) ≥ (2 / 3) ^ (n - 2 : ℝ) * S ^ (n - 1) := by

-- Suppose w.l.o.g. that $$a \geq b \geq c$$.
  wlog h1 : a ≥ b ∧ b ≥ c
  . by_cases c1 : a ≤ b
    all_goals by_cases c2 : a ≤ c
    all_goals by_cases c3 : b ≤ c
    all_goals try linarith only [c1, c2, c3]
    . specialize this c b a
      specialize this (by assumption) (by assumption) (by assumption) (by linarith) (by linarith) (by linarith) S (by linarith) n hn (by split_ands <;> linarith)
      ring_nf at this ⊢
      simpa using this
    . specialize this b c a
      specialize this (by assumption) (by assumption) (by assumption) (by linarith) (by linarith) (by linarith) S (by linarith) n hn (by split_ands <;> linarith)
      ring_nf at this ⊢
      simpa using this
    . specialize this b a c
      specialize this (by assumption) (by assumption) (by assumption) (by linarith) (by linarith) (by linarith) S (by linarith) n hn (by split_ands <;> linarith)
      ring_nf at this ⊢
      simpa using this
    . specialize this c a b
      specialize this (by assumption) (by assumption) (by assumption) (by linarith) (by linarith) (by linarith) S (by linarith) n hn (by split_ands <;> linarith)
      ring_nf at this ⊢
      simpa using this
    . specialize this a c b
      specialize this (by assumption) (by assumption) (by assumption) (by linarith) (by linarith) (by linarith) S (by linarith) n hn (by split_ands <;> linarith)
      ring_nf at this ⊢
      simpa using this
    . specialize this a b c
      specialize this (by assumption) (by assumption) (by assumption) (by linarith) (by linarith) (by linarith) S (by linarith) n hn (by split_ands <;> linarith)
      ring_nf at this ⊢
      simpa using this

  replace ⟨h1, h2⟩ := h1

-- Then $$1 /(b+c) \geq 1 /(a+c) \geq 1 /(a+b)$$.
  have h3 : 1 / (b + c) ≥ 1 / (a + c) := by
    have c1 : b + c > 0 := by linarith
    have c2 : a + c > 0 := by linarith
    rw [ge_iff_le, div_le_div_iff₀ c2 c1]
    linarith

  have h4 : 1 / (a + c) ≥ 1 / (a + b) := by
    have c1 : a + c > 0 := by linarith
    have c2 : a + b > 0 := by linarith
    rw [ge_iff_le, div_le_div_iff₀ c2 c1]
    linarith

-- We will now use Chebyshev's inequality which states that if $$a_1 ≥ ... ≥ a_n$$ and $$b_1 ≥ ... ≥ b_n$$, then
-- $$\dfrac{1}{n} \sum_{k=1}^n a_k b_k ≥ \left(\dfrac{1}{n} \sum_{k=1}^n a_k\right) \left(\dfrac{1}{n} \sum_{k=1}^n b_k\right) $$

  have chebyshev_ineq (n : ℕ) (a b : ℕ → ℝ) (ha : AntitoneOn a (Icc 1 n)) (hb : AntitoneOn b (Icc 1 n)) : (1 / n : ℝ) * ∑ k ∈ Icc 1 n, a k * b k ≥ ((1 / n : ℝ) * ∑ k ∈ Icc 1 n, a k) * ((1 / n : ℝ) * ∑ k ∈ Icc 1 n, b k) := by
    sorry

-- Chebyshev's inequality yields
-- $$ \frac{a^{n}}{b+c}+\frac{b^{n}}{a+c}+\frac{c^{n}}{a+b} \geq \frac{1}{3}\left(a^{n}+b^{n}+c^{n}\right)\left(\frac{1}{b+c}+\frac{1}{a+c}+\frac{1}{a+b}\right) . $$  (1)

  have h5 : a ^ n / (b + c) + b ^ n / (a + c) + c ^ n / (a + b) ≥ (1 / 3 : ℝ) * (a ^ n + b ^ n + c ^ n) * (1 / (b + c) + 1 / (a + c) + 1 / (a + b)) := by
    have c1 := chebyshev_ineq 3
      (λ | 1 => a ^ n | 2 => b ^ n | 3 => c ^ n | 0 => 0 | _ + 3 => 0)
      (λ | 1 => 1 / (b + c) | 2 => 1 / (a + c) | 3 => 1 / (a + b) | 0 => 0 | _ + 3 => 0)
      (by
        apply antitoneOn_of_succ_le
        . simp [Set.ordConnected_Icc]
        intro k hk1 hk2 hk3
        simp at hk2 hk3
        obtain hk | hk : k = 1 ∨ k = 2 := by omega
        . subst hk; exact pow_le_pow_left₀ (by linarith) h1 n
        . subst hk; exact pow_le_pow_left₀ (by linarith) h2 n)
      (by
        apply antitoneOn_of_succ_le
        . simp [Set.ordConnected_Icc]
        intro k hk1 hk2 hk3
        simp at hk2 hk3
        obtain hk | hk : k = 1 ∨ k = 2 := by omega
        . subst hk; exact h3
        . subst hk; exact h4)
    have c2 : Icc 1 3 = {1, 2, 3} := by ext k; simp; omega
    apply_fun ((3 : ℝ) * .) at c1
    swap
    . apply monotone_mul_left_of_nonneg; norm_num
    simp [c2] at c1 ⊢
    ring_nf at c1 ⊢
    simpa using c1


-- We will now use AM-HM inequality which states that for $$n$$ positive integers $$x_1, ..., x_n$$, we have:

-- $$\dfrac{n}{\frac{1}{x_1} + ...+\frac{1}{x_n}} \le \dfrac{x_1 + ... + x_n}{n}$$

  have am_hm_ineq (n : ℕ) (x : ℕ → ℝ) (hx : ∀ i ∈ Icc 1 n, x i > 0) : n / ∑ i ∈ Icc 1 n, 1 / x i ≤ (∑ i ∈ Icc 1 n, x i) / n := by
    sorry

-- By the AM-HM inequality on $$x_1=b+c$$, $$x_2=a+c$$, and $$x_3=a+b$$ we have

-- $$ 2(a+b+c)\left(\frac{1}{b+c}+\frac{1}{a+c}+\frac{1}{a+b}\right) \geq 9 $$
  have h6 : 2 * (a + b + c) * (1 / (b + c) + 1 / (a + c) + 1 / (a + b)) ≥ 9 := by
    let x (i : ℕ) : ℝ := match i with
      | 1 => b + c | 2 => a + c | 3 => a + b | 0 => 0 | _ + 3 => 0
    have c1 := am_hm_ineq 3 x (by
      intro i hi
      simp at hi
      rcases (show i = 1 ∨ i = 2 ∨ i = 3 from by omega) with d1 | d1 | d1
      all_goals subst d1; dsimp [x]; linarith)
    have c2 : Icc 1 3 = {1, 2, 3} := by ext k; simp; omega
    simp [c2, x] at c1
    cancel_denoms at c1
    replace c1 : 9 * ((b + c)⁻¹ + (c + a)⁻¹ + (b + a)⁻¹)⁻¹ ≤ b * 2 + c * 2 + a * 2 := by
      ring_nf at c1 ⊢
      simpa using c1
    apply_fun (. * ((b + c)⁻¹ + (c + a)⁻¹ + (b + a)⁻¹)) at c1
    swap
    . apply monotone_mul_right_of_nonneg
      positivity
    have : ((b + c)⁻¹ + (c + a)⁻¹ + (b + a)⁻¹) ≠ 0 := by positivity
    simp [this] at c1
    ring_nf at c1 ⊢
    simpa using c1

-- and the mean inequality yields
-- $$\left(a^{n}+b^{n}+c^{n}\right) / 3 \geq[(a+b+c) / 3]^{n}$$.
  have h7 : (a ^ n + b ^ n + c ^ n) / 3 ≥ ((a + b + c) / 3) ^ n := by
    sorry

-- We obtain from (1) that
-- $$ \begin{aligned} \frac{a^{n}}{b+c}+\frac{b^{n}}{a+c}+\frac{c^{n}}{a+b} & \geq\left(\frac{a+b+c}{3}\right)^{n}\left(\frac{1}{b+c}+\frac{1}{a+c}+\frac{1}{a+b}\right) \ & \geq \frac{3}{2}\left(\frac{a+b+c}{3}\right)^{n-1}=\left(\frac{2}{3}\right)^{n-2} S^{n-1} . \end{aligned} $$
  calc
    _ = _ := by ring_nf
    _ ≥ _ := h5
    _ ≥ ((a + b + c) / 3) ^ n * (1 / (b + c) + 1 / (a + c) + 1 / (a + b)) := by
      gcongr
      cancel_denoms at h7 ⊢
      simpa using h7
    _ ≥ ((a + b + c) / 3) ^ n * (9 / (2 * (a + b + c))) := by
      gcongr
      have c1 : 2 * (a + b + c) ≠ 0 := by positivity
      replace h6 : 9 ≤ (1 / (b + c) + 1 / (a + c) + 1 / (a + b)) * (2 * (a + b + c)) := by
        ring_nf at h6 ⊢; simpa using h6
      apply_fun (. / (2 * (a + b + c))) at h6
      swap
      . apply monotone_mul_right_of_nonneg
        positivity
      simpa [c1] using h6
    _ = ((a + b + c) / 3) ^ (n - 1) * ((a + b + c) / 3) * (9 / (2 * (a + b + c))) := by
      congr 1
      rw [←pow_succ]
      congr 1
      omega
    _ = (((a + b + c) / 3) * (9 / (2 * (a + b + c)))) * ((a + b + c) / 3) ^ (n - 1) := by ring_nf
    _ = (3 / 2) * ((a + b + c) / 3) ^ (n - 1) := by
      congr 1
      field_simp
      ring_nf
    _ = (2 / 3) ^ (n - 1) * (3 / 2) * S ^ (n - 1) := by
      rw [←hS]
      ring_nf
    _ = _ := by
      congr 1
      obtain c1 | c1 : n = 1 ∨ n ≥ 2 := by omega
      . subst c1
        norm_num
      . norm_cast
        have c2 : n - 1 = n - 2 + 1 := by omega
        rw [c2, pow_succ]
        ring_nf
