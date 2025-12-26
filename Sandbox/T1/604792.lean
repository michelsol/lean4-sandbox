import Mathlib

open Nat Finset

/-
Let $n, k$ be given positive integers with $n>k$. Prove that

$
\frac{1}{n+1} \cdot \frac{n^{n}}{k^{k}(n-k)^{n-k}}<\frac{n!}{k!(n-k)!}<\frac{n^{n}}{k^{k}(n-k)^{n-k}} .
$
-/

theorem inequalities_604792
    (n k : ℕ)
    (hn : n > 0)
    (hk : k > 0)
    (hkn : k < n) :
    (1 / (n + 1) : ℝ) * (n ^ n / (k ^ k * (n - k) ^ (n - k)) : ℝ) < (n ! / (k ! * (n - k) !) : ℝ)
    ∧ (n ! / (k ! * (n - k) !) : ℝ) < (n ^ n / (k ^ k * (n - k) ^ (n - k)) : ℝ) := by

-- Expression of a binomial coefficient using division in ℝ.
  have choose_eq {n k : ℕ} (hk : k ≤ n) : n.choose k = (n ! / (k ! * (n - k) !) : ℝ) := by
    rw [choose_eq_factorial_div_factorial hk]
    push_cast [factorial_mul_factorial_dvd_factorial hk]
    rfl

-- #### 1. **Binomial Expansion**
-- Start with the binomial identity:
-- $ n^n = (k + (n - k))^n = \sum_{i=0}^{n} \binom{n}{i} k^{i}(n - k)^{n - i}. $

  have h1 : n ^ n = ∑ i ∈ Icc 0 n, n.choose i * k ^ i * (n - k) ^ (n - i) := by
    sorry

-- Each term in the expansion is:
-- $ T_i = \binom{n}{i} k^{i}(n - k)^{n - i}. $
  set T := λ i ↦ n.choose i * k ^ i * (n - k) ^ (n - i)

-- Note that each $T_i > 0$.
  have h1' i (hi : i ∈ Icc 0 n) : 0 < T i := by
    suffices T i > 0 * 0 * 0 from by simpa
    dsimp only [T]
    gcongr
    . simp at hi
      exact choose_pos hi
    . apply pos_pow_of_pos; omega
    . apply pos_pow_of_pos; omega

-- #### 2. **Comparing Terms**
-- Focus on the term $ T_k = \binom{n}{k} k^{k}(n - k)^{n - k} $. To show it is the **maximum term**, analyze the ratio of consecutive terms:
-- $ \frac{T_{i+1}}{T_i} = \frac{\binom{n}{i+1} k^{i+1}(n - k)^{n - (i+1)}}{\binom{n}{i} k^{i}(n - k)^{n - i}} = \frac{(n - i)k}{(i + 1)(n - k)}. $

  have h2 i (hi : i ∈ Ico 0 n) : (T (i + 1) / T i : ℝ) = (n - i) * k / ((i + 1) * (n - k)) := by
    calc
      (_ : ℝ) = n.choose (i + 1) * k ^ (i + 1) * (n - k) ^ (n - (i + 1)) / (n.choose i * k ^ i * (n - k) ^ (n - i)) := by dsimp [T]; push_cast [hkn]; rfl
      _ = _ := by
        sorry

-- - **When is $ T_{i+1} > T_i $?**
--   $  (n - i)k > (i + 1)(n - k) \implies i < k. $
--   Thus, terms **increase** for $ i < k $ and **decrease** for $ i > k $.
--   This makes $ T_k $ the **maximum term** in the expansion.
  have h3 i (hi : i ∈ Icc 0 n) : T i < T k := by
    have c1 i (hi : i ∈ Ico 0 n) : T (i + 1) > T i ↔ i < k := by
      sorry
    sorry

-- #### 3. **Lower Bound (Left Inequality)**
-- - The **average term** in the expansion is $ \frac{n^n}{n + 1} $.
-- - Since $ T_k $ is the maximum term, it must exceed the average:
-- $ \binom{n}{k} k^{k}(n - k)^{n - k} > \frac{n^n}{n + 1}. $
  have h5 : n.choose k * k ^ k * (n - k) ^ (n - k) > (n ^ n / (n + 1) : ℝ) := by
    suffices (T k : ℝ) > (n ^ n / (n + 1) : ℝ) from by
      dsimp [T] at this
      push_cast [hkn] at this
      simpa
    suffices (T k : ℝ) * (n + 1) > n ^ n  from by
      have c1 : (n + 1 : ℝ) > 0 := by linarith
      apply_fun (. / (n + 1 : ℝ)) at this
      swap
      . exact StrictMono.div_const (fun ⦃a b⦄ a => a) c1
      dsimp at this
      rw [mul_div_cancel_right₀] at this
      swap
      . linarith
      simpa
    suffices T k * (n + 1) > ∑ i ∈ Icc 0 n, T i  from by norm_cast; simpa [h1]
    sorry

-- This gives the left inequality:
-- $ \frac{n!}{k!(n - k)!} > \frac{1}{n+1} \cdot \frac{n^{n}}{k^{k}(n - k)^{n-k}}. $
  have h6 : (n ! / (k ! * (n - k) !) : ℝ) > (1 / (n + 1) : ℝ) * (n ^ n / (k ^ k * (n - k) ^ (n - k)) : ℝ) := by
    rw [choose_eq (by omega)] at h5
    sorry

-- #### 4. **Upper Bound (Right Inequality)**
-- - Since $ T_k $ is a single term in the sum $ \sum_{i=0}^n T_i = n^n $:
-- $ \binom{n}{k} k^{k}(n - k)^{n - k} < n^n. $
  have h7 : n.choose k * k ^ k * (n - k) ^ (n - k) < n ^ n := by
    suffices T k < n ^ n from by simpa
    sorry

-- This gives the right inequality:
-- $ \frac{n!}{k!(n - k)!} < \frac{n^{n}}{k^{k}(n - k)^{n-k}}. $
  have h8 : (n ! / (k ! * (n - k) !) : ℝ) < (n ^ n / (k ^ k * (n - k) ^ (n - k)) : ℝ) := by
    set m := (k ^ k * (n - k) ^ (n - k) : ℝ)
    replace h7 : n.choose k * m < n ^ n := by
      rify [hkn] at h7
      ring_nf at h7 ⊢
      simpa using h7
    rw [choose_eq (by omega)] at h7
    have c1 : (m : ℝ) > 0 := by
      suffices k ^ k * (n - k) ^ (n - k) > 0 * 0 from by rify [hkn] at this; simpa
      gcongr <;> exact pow_self_pos
    apply_fun (. / m) at h7
    swap
    . exact StrictMono.div_const (λ _ _ a => a) c1
    dsimp at h7
    rw [mul_div_cancel_right₀] at h7
    swap
    . linarith
    . exact h7

-- which concludes the proof
  exact ⟨h6, h8⟩
