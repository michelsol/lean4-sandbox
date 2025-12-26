import Mathlib

open Finset Real Function

/-
For a given positive integer $k$ denote the square of the sum of its digits
by $f_{1}(k)$ and let $f_{n+1}(k)=f_{1}\left(f_{n}(k)\right)$.
Determine the value of $f_{1991}\left(2^{1990}\right)$.
-/

theorem other_24328
    (f : ℕ → ℕ)
    (f_def : ∀ k, f k = (∑ i ∈ Icc 0 ⌊logb 10 k⌋₊, k / 10 ^ i % 10) ^ 2)
    : f^[1991] (2 ^ 1990) = 256 := by
-- Since $2^{1990}<8^{700}<10^{700}$,
  have h1 : 2 ^ 1990 < 10 ^ 700 := by norm_num

-- we have $f_{1}\left(2^{1990}\right)<(700 \cdot 9)^{2}<4 \cdot 10^{7}$.
  replace h1 : f^[1] (2 ^ 1990) < 4 * 10 ^ 7 := calc
    _ < (700 * 9) ^ 2 := by
      rw [iterate_one, f_def]
      apply Nat.pow_lt_pow_left ?_ (by norm_num)
      calc
        _ ≤ (∑ i ∈ Ico 0 700, (2 ^ 1990) / 10 ^ i % 10) := by
          apply sum_le_sum_of_subset
          suffices ⌊logb 10 (2 ^ 1990)⌋₊ < 700 from by
            intro x hx; simp at this hx ⊢; omega
          rw [Nat.floor_lt]
          . rw [logb_lt_iff_lt_rpow (by norm_num) (by norm_num)]
            exact_mod_cast h1
          . apply logb_nonneg
            . norm_num
            . norm_num
        _ < (∑ i ∈ Ico 0 700, 9) := by
          apply sum_lt_sum
          . intro i hi; omega
          . use 0
            suffices 2 ^ 1990 % 10 < 9 from by simpa
            omega
        _ = _ := by simp
    _ < _ := by norm_num

-- We then have $f_{2}\left(2^{1990}\right)<(3+9 \cdot 7)^{2}<4900$
  have h2 : f^[2] (2 ^ 1990) < 4900 := calc
    _ < (3 + 9 * 7) ^ 2 := by
      rw [iterate_succ_apply', f_def]
      apply Nat.pow_lt_pow_left ?_ (by norm_num)
      calc
        _ ≤ (∑ i ∈ Ico 0 8, (f^[1] (2 ^ 1990)) / 10 ^ i % 10) := by
          apply sum_le_sum_of_subset
          suffices ⌊logb 10 (f^[1] (2 ^ 1990))⌋₊ < 8 from by
            intro x hx; simp at this hx ⊢; omega
          rw [Nat.floor_lt]
          . rw [logb_lt_iff_lt_rpow (by norm_num)]
            . norm_cast; omega
            . norm_cast
              sorry
          . apply logb_nonneg
            . norm_num
            . norm_cast
              sorry
        _ = (∑ i ∈ Ico 0 7, (f^[1] (2 ^ 1990)) / 10 ^ i % 10) + (f^[1] (2 ^ 1990)) / 10 ^ 7 % 10 := by
          have : Ico 0 8 = Ico 0 7 ∪ {7} := by ext x; simp; omega
          rw [this, sum_union (by simp)]
          simp
        _ < (∑ i ∈ Ico 0 7, 9) + 3 := by
          suffices ∑ i ∈ Ico 0 7, f^[1] (2 ^ 1990) / 10 ^ i % 10 < (∑ i ∈ Ico 0 7, 9)
              ∧ f^[1] (2 ^ 1990) / 10 ^ 7 % 10 ≤ 3 from by omega
          split_ands
          . apply sum_lt_sum
            . intro i hi; omega
            . sorry
          . omega
        _ = _ := by simp
    _ < _ := by norm_num

-- and finally $f_{3}\left(2^{1990}\right)<(4+9 \cdot 3)^{2}=31^{2}$.
  have h3 : f^[3] (2 ^ 1990) < 31 ^ 2 := calc
    _ < 31 ^ 2 := by
      rw [iterate_succ_apply', f_def]
      apply Nat.pow_lt_pow_left ?_ (by norm_num)
      calc
        _ ≤ (∑ i ∈ Ico 0 4, (f^[2] (2 ^ 1990)) / 10 ^ i % 10) := by
          apply sum_le_sum_of_subset
          suffices ⌊logb 10 (f^[2] (2 ^ 1990))⌋₊ < 4 from by
            intro x hx; simp at this hx ⊢; omega
          rw [Nat.floor_lt]
          . rw [logb_lt_iff_lt_rpow (by norm_num)]
            . sorry
            . norm_cast
              sorry
          . apply logb_nonneg
            . norm_num
            . norm_cast
              sorry
        _ =   (f^[2] (2 ^ 1990)) / 10 ^ 0 % 10
            + (f^[2] (2 ^ 1990)) / 10 ^ 1 % 10
            + (f^[2] (2 ^ 1990)) / 10 ^ 2 % 10
            + (f^[2] (2 ^ 1990)) / 10 ^ 3 % 10 := by
          have : Ico 0 4 = {0, 1, 2, 3} := by ext x; simp; omega
          simp [this]; omega
        _ ≤ 30 := by
          have : (f^[2] (2 ^ 1990) / 10 ^ 3 % 10 = 4 ∧ f^[2] (2 ^ 1990) / 10 ^ 2 % 10 ≤ 8)
                  ∨ (f^[2] (2 ^ 1990) / 10 ^ 3 % 10 ≤ 3 ∧ f^[2] (2 ^ 1990) / 10 ^ 2 % 10 ≤ 9) := by
                  omega
          omega
        _ < _ := by norm_num
    _ = _ := by norm_num

-- All congruences in this problem will be $\bmod 9$.
-- It is easily shown that $f_{k+1}(n) \equiv f_{k}(n)^{2}(\bmod 9)$.
  have sum_logb10_div_pow_mod_mul (n : ℕ) : (∑ i ∈ Icc 0 ⌊logb 10 n⌋₊, n / 10 ^ i % 10 * 10 ^ i) = n := by
    sorry
  have h4 (k n : ℕ) : f^[k+1] n % 9 = (f^[k] n) ^ 2 % 9 := by
    rw [iterate_succ_apply']
    generalize f^[k] n = n
    rw [f_def]
    suffices (∑ i ∈ Icc 0 ⌊logb 10 n⌋₊, (n : ℤ) / 10 ^ i % 10) % 9 = (n : ℤ) % 9 from by
      norm_cast at this; rw [Nat.pow_mod, this, ←Nat.pow_mod]
    suffices (∑ i ∈ Icc 0 ⌊logb 10 n⌋₊, (n : ℤ) / 10 ^ i % 10 * 1
        - ∑ i ∈ Icc 0 ⌊logb 10 n⌋₊, (n : ℤ) / 10 ^ i % 10 * 10 ^ i) % 9 = 0 from by
      simp only [mul_one] at this
      have := sum_logb10_div_pow_mod_mul n
      zify at this
      omega
    suffices 9 ∣ ∑ i ∈ Icc 0 ⌊logb 10 n⌋₊, (n : ℤ) / 10 ^ i % 10 * (1 - 10 ^ i : ℤ) from by
      simp only [←sum_sub_distrib, ←mul_sub]
      simpa
    apply dvd_sum
    intro i hi
    suffices 9 ∣ (1 - 10 ^ i : ℤ) from by exact Dvd.dvd.mul_left this _
    suffices (1 - 10 : ℤ) ∣ (1 ^ i - 10 ^ i : ℤ) from by ring_nf at this ⊢; simpa
    exact Commute.sub_dvd_pow_sub_pow (by simp) i

-- Since $2^{6} \equiv 1(\bmod 9)$, we have $2^{1990} \equiv 2^{4} \equiv 7$
  have h5 : 2 ^ 1990 % 9 = 7 := by norm_num

-- It follows that $f_{1}\left(2^{1990}\right) \equiv 7^{2} \equiv 4$
  have h6 : f^[1] (2 ^ 1990) % 9 = 4 := by
    specialize h4 0 (2 ^ 1990)
    rw [Nat.pow_mod] at h4
    simpa [h5] using h4

-- and $f_{2}\left(2^{1990}\right) \equiv 4^{2} \equiv 7$.
  have h7 : f^[2] (2 ^ 1990) % 9 = 7 := by
    specialize h4 1 (2 ^ 1990)
    rw [Nat.pow_mod] at h4
    simp at h6
    simpa [h6] using h4

-- Indeed, it follows by induction, that $f_{2 k}\left(2^{1990}\right) \equiv 7$
-- and $f_{2 k+1}\left(2^{1990}\right) \equiv 4$ for all integer $k>0$.
  have h8 : ∀ k, f^[2 * k] (2 ^ 1990) % 9 = 7 := by
    sorry
  have h9 : ∀ k, f^[2 * k + 1] (2 ^ 1990) % 9 = 7 := by
    sorry

-- Thus $f_{3}\left(2^{1990}\right)=r^{2}$ where $r<31$ is an integer
  let r :=
    let k := f^[2] (2 ^ 1990)
    (∑ i ∈ Icc 0 ⌊logb 10 k⌋₊, k / 10 ^ i % 10)
  have h10 : f^[3] (2 ^ 1990) = r ^ 2 := by rw [iterate_succ_apply', f_def]
  have h11 : r < 31 := by rwa [h10, Nat.pow_lt_pow_iff_left (by norm_num)] at h3
-- and $r \equiv f_{2}\left(2^{1990}\right) \equiv 7$.
  have h12 : r % 9 = 7 := calc
    _ = f^[2] (2 ^ 1990) % 9 := by
      dsimp only [r]
      generalize f^[2] (2 ^ 1990) = n
      -- The sum of digits of a number divisible by 9, is divisible by 9
      sorry
    _ = _ := h7

-- It follows that $r \in\{7,16,25\}$ and
  have h13 : r = 7 ∨ r = 16 ∨ r = 25 := by omega

-- hence $f_{3}\left(2^{1990}\right) \in\{49,256,625\}$.
  have h14 : f^[3] (2 ^ 1990) = 49 ∨ f^[3] (2 ^ 1990) = 256 ∨ f^[3] (2 ^ 1990) = 625 := by
    rw [h10]
    rcases h13 with h13 | h13 | h13 <;> simp [h13]

-- It follows that $f_{4}\left(2^{1990}\right)=169,
  have h15 : f^[4] (2 ^ 1990) = 169 := by
    rw [iterate_succ_apply']
    rcases h14 with h14 | h14 | h14
    . have : ⌊logb 10 (49 : ℕ)⌋₊ = 1 := by sorry
      rw [h14, f_def, this]
      decide
    . have : ⌊logb 10 (256 : ℕ)⌋₊ = 2 := by sorry
      rw [h14, f_def, this]
      decide
    . have : ⌊logb 10 (625 : ℕ)⌋₊ = 2 := by sorry
      rw [h14, f_def, this]
      decide

-- f_{5}\left(2^{1990}\right)=256$
  have h16 : f^[5] (2 ^ 1990) = 256 := by
    have : ⌊logb 10 (169 : ℕ)⌋₊ = 2 := by sorry
    rw [iterate_succ_apply', h15, f_def, this]
    decide

-- and inductively $f_{2 k}\left(2^{1990}\right)=169$
  have h17 : ∀ k > 1, f^[2 * k] (2 ^ 1990) = 169 := sorry

-- and $f_{2 k+1}\left(2^{1990}\right)=256$ for all integer $k>1$.
  have h18 : ∀ k > 1, f^[2 * k + 1] (2 ^ 1990) = 256 := sorry

-- Hence $f_{1991}\left(2^{1990}\right)=256$.
  exact h18 995 (by norm_num)
