import Mathlib

open Finset

/-Show that the sum of the digits of $2^{2^{2 \cdot 2023}}$ is greater than 2023 .-/
theorem number_theory_605028
  : let nth_digit : ℕ → ℕ → ℕ → ℕ := fun b x k => x / b ^ k % b
    ∑ d ∈ Ico 0 (Nat.log 10 (2 ^ (2 ^ (2 * 2023))) + 1), nth_digit 10 (2 ^ (2 ^ (2 * 2023))) d > 2023 := by
  intro nth_digit

-- First we prove a lemma about the sum of digits in a given base.
  have sum_nth_digit_mul_base_pow {b : ℕ} (hb : b ≥ 2) :
      ∀ x, x = ∑ k ∈ Ico 0 (b.log x + 1), nth_digit b x k * b ^ k := by
    unfold nth_digit
    apply Nat.strongRec
    intro x ih
    obtain hx | hx : x < b ∨ x ≥ b := by omega
    · have h1 := Nat.log_of_lt hx
      have h2 := Nat.mod_eq_of_lt hx
      simp [h1, h2]
    · calc
        x = b * (x / b) + x % b := by rw [Nat.div_add_mod]
        _ = b * (∑ k ∈ Ico 0 (b.log x), x / b / b ^ k % b * b ^ k) + x % b := by
          specialize ih (x / b) (Nat.div_lt_self (by omega) hb)
          have h1 := Nat.log_pos (by omega) hx
          have h2 : b.log (x / b) + 1 = b.log x := by simp; omega
          conv_lhs => rw [ih, h2]
        _ = (∑ k ∈ Ico 0 (b.log x), (x / b ^ (k + 1) % b * b ^ (k + 1))) + x % b := by
          congr 1
          rw [mul_sum]
          apply sum_congr rfl
          intro k hk
          calc
            _ = x / b / b ^ k % b * (b ^ k * b) := by ring
            _ = _ := by congr 2; rw [Nat.div_div_eq_div_mul, Nat.mul_comm, Nat.pow_succ]
        _ = (∑ k ∈ Ico 1 (b.log x + 1), (x / b ^ k % b * b ^ k)) + x % b := by
          congr 1
          apply sum_nbij (· + 1)
          · intro k hk; simp at hk ⊢; omega
          · intro k hk k' hk' h; simpa using h
          · intro k hk
            simp only [Set.mem_image]
            use k - 1; simp at hk ⊢; omega
          · simp
        _ = ∑ k ∈ Ico 0 (b.log x + 1), x / b ^ k % b * b ^ k := by
          have h1 : {0} ⊆ Ico 0 (b.log x + 1) := by simp
          have h2 : Ico 0 (b.log x + 1) \ {0} = Ico 1 (b.log x + 1) := by ext k; simp; omega
          rw [←sum_sdiff h1, h2]
          simp

-- We will prove the more general statement that, for every positive integer $n$,
-- the sum of decimal digits of $2^{2^{2 n}}$ is greater than $n$.
  have hn : 2023 > 0 := by norm_num
  generalize 2023 = n at hn ⊢

-- Let $m=2^{2 n}=4^{n}$, so that we need to consider the digits of $2^{m}$.
  set m := 2 ^ (2 * n)

-- Let S be the set of positions of non-zero decimal digits of $2^{m}$.
  let S := {d ∈ Ico 0 (Nat.log 10 (2 ^ m) + 1) | nth_digit 10 (2 ^ m) d ≠ 0}
  let k := #S - 1
  have hS1 : #S ≥ 1 := by
    refine one_le_card.mpr ?_
    use 0
    suffices 0 < Nat.log 10 (2 ^ m) + 1 ∧ nth_digit 10 (2 ^ m) 0 ≠ 0 by simpa [S] using this
    split_ands
    · omega
    · unfold nth_digit
      sorry

-- It will suffice to prove that at least $n$ of these digits are different from 0,
-- since the last digit is at least 2.
  suffices k ≥ n by
    calc
      ∑ d ∈ Ico 0 (Nat.log 10 (2 ^ m) + 1), nth_digit 10 (2 ^ m) d
          = ∑ d ∈ Ico 0 (Nat.log 10 (2 ^ m) + 1) with nth_digit 10 (2 ^ m) d ≠ 0, nth_digit 10 (2 ^ m) d := by
        symm
        apply sum_filter_ne_zero
      _ ≥ ∑ d ∈ Ico 0 (Nat.log 10 (2 ^ m) + 1) with nth_digit 10 (2 ^ m) d ≠ 0, 1 := by
        apply sum_le_sum
        intro d hd
        simp at hd
        omega
      _ = #S := by simp [S]
      _ = k + 1 := by
        simp [k]
        omega
      _ > n := by omega

-- Let $0=e_{0} < e_{1} < \cdots < e_{k}$ be the positions of non-zero digits,
  let e i := Nat.nth (· ∈ S) i
-- and let $d_{i}$ be the corresponding digits.
  let d i := nth_digit 10 (2 ^ m) (e i)

-- so that $2^{m}=\sum_{i=0}^{k} d_{i} \cdot 10^{e_{i}}$ with $1 \leq d_{i} \leq 9$.

  have h1 := calc
    2 ^ m = ∑ d ∈ Icc 0 (Nat.log 10 (2 ^ m)), nth_digit 10 (2 ^ m) d * 10 ^ d := by
      exact sum_nth_digit_mul_base_pow (by norm_num) (2 ^ m)
    _ = ∑ d ∈ S, nth_digit 10 (2 ^ m) d * 10 ^ d := by
      symm
      apply sum_filter_of_ne
      intro i c1 c2
      contrapose! c2
      simp [c2]
    _ = ∑ i ∈ Icc 0 k, d i * 10 ^ e i := by
      symm
      apply sum_nbij e
      · sorry
      · sorry
      · sorry
      · simp

  have h2 i (hi : i ∈ Icc 0 k) : 1 ≤ d i ∧ d i ≤ 9 := by
    unfold d
    have c1 : e i ∈ S := by
      unfold e
      apply Nat.nth_mem_of_lt_card
      · simp at hi ⊢; omega
      · simp
    split_ands
    · simp [S] at c1
      unfold nth_digit at c1 ⊢
      omega
    · unfold nth_digit
      omega

-- Considering this number modulo $10^{e_{j}}$, for some $0 < j \leq k$, the residue $\sum_{i=0}^{j-1} d_{i} \cdot 10^{e_{i}}$ is a multiple of $2^{e_{j}}$,
  have h3 (j : ℕ) (hj1 : 0 < j) (hj2 : j ≤ k) : (∑ i ∈ Ico 0 j, d i * 10 ^ e i) % 2 ^ e j = 0 := calc
    _ = ((∑ i ∈ Icc 0 k, d i * 10 ^ e i) % 10 ^ e j) % 2 ^ e j := by
      congr 1
      sorry
    _ = 2 ^ m % 10 ^ e j % 2 ^ e j := by rw [h1]
    _ = 2 ^ m % (5 * 2) ^ e j % 2 ^ e j := by norm_num
    _ = 2 ^ m % (5 ^ e j * 2 ^ e j) % 2 ^ e j := by rw [Nat.mul_pow]
    _ = 2 ^ m % 2 ^ e j := by simp
    _ = _ := by
      refine Nat.mod_eq_zero_of_dvd ?_
      refine Nat.pow_dvd_pow 2 ?_
      sorry

-- hence at least $2^{e_{j}}$, but on the other hand it is bounded by $10^{e_{j-1}+1}$.
  have h4 (j : ℕ) (hj1 : 0 < j) (hj2 : j ≤ k) : (∑ i ∈ Ico 0 j, d i * 10 ^ e i) ≥ 2 ^ e j := by
    sorry

  have h5 (j : ℕ) (hj1 : 0 < j) (hj2 : j ≤ k) : (∑ i ∈ Ico 0 j, d i * 10 ^ e i) < 10 ^ (e (j - 1) + 1) := by
    sorry

-- It follows that $2^{e_{j}} < 10^{e_{j-1}+1} < 16^{e_{j-1}+1}$,
  have h6 (j : ℕ) (hj1 : 0 < j) (hj2 : j ≤ k) := calc
    2 ^ e j < 10 ^ (e (j - 1) + 1) := by
      specialize h4 j hj1 hj2
      specialize h5 j hj1 hj2
      omega
    _ < 16 ^ (e (j - 1) + 1) := by
      refine Nat.pow_lt_pow_left ?_ ?_
      norm_num
      omega
    _ = (2 ^ 4) ^ (e (j - 1) + 1) := by congr 1
    _ = 2 ^ (4 * (e (j - 1) + 1)) := by rw [Nat.pow_mul]

-- and hence $e_{j} < 4\left(e_{j-1}+1\right)$.
  have h7 (j : ℕ) (hj1 : 0 < j) (hj2 : j ≤ k) : e j < 4 * (e (j - 1) + 1) := by
    specialize h6 j hj1 hj2
    have c1 : StrictMonoOn (Real.logb 2) (Set.Ioi 0) := by
      refine Real.strictMonoOn_logb ?_
      norm_num
    rify at h6 ⊢
    specialize c1 (by simp) (by simp) h6
    simpa [Real.logb_pow] using c1

-- With $e_{0}=4^{0}-1$ and $e_{j} \leq 4\left(e_{j-1}+1\right)-1$, it follows that $e_{j} \leq 4^{j}-1$, for all $0 \leq j \leq k$.
  have h8 (j : ℕ) (hj2 : j ≤ k) : e j ≤ 4 ^ j - 1 := by
    induction' j with j ih
    · sorry
    · specialize h7 (j + 1) (by omega) (by omega)
      convert_to e (j + 1) < 4 * e j + 4 using 1 at h7
      specialize ih (by omega)
      have c2 : 4 ^ (j + 1) ≥ 1 := by
        sorry
      zify [c2]
      have c3 : 4 ^ j ≥ 1 := by
        sorry
      zify [c3] at ih
      calc
        (e (j + 1) : ℤ) ≤ 4 * e j + 3 := by
          norm_cast
          omega
        _ ≤ 4 * (4 ^ j - 1) + 3 := by omega
        _ = _ := by ring

-- In particular, $e_{k} \leq 4^{k}-1$
  have h9 : e k ≤ 4 ^ k - 1 := by exact h8 k (by omega)

-- and hence $$ 2^{m}=\sum_{i=0}^{k} d_{i} \cdot 10^{e_{i}} < 10^{4^{k}} < 16^{4^{k}}=2^{4 \cdot 4^{k}}=2^{4^{k+1}} $$

  have h10 : 2 ^ m < 2 ^ (4 ^ (k + 1)) := calc
    _ = _ := h1
    _ < 10 ^ (4 ^ k) := by
      sorry
    _ < 16 ^ (4 ^ k) := by
      refine Nat.pow_lt_pow_left ?_ ?_
      norm_num
      simp
    _ = (2 ^ 4) ^ (4 ^ k) := by congr 1
    _ = 2 ^ (4 * 4 ^ k) := by rw [Nat.pow_mul]
    _ = 2 ^ (4 ^ (k + 1)) := by ring


-- which yields $4^{n}=m < 4^{k+1}$, i.e., $n-1 < k$.
  have h11 := calc
    4 ^ n = (2 ^ 2) ^ n := by norm_num
    _ = 2 ^ (2 * n) := by rw [Nat.pow_mul]
    _ = m := by rfl
    _ < 4 ^ (k + 1) := by
      rify at h10 ⊢
      have c1 : StrictMonoOn (Real.logb 2) (Set.Ioi 0) := by
        refine Real.strictMonoOn_logb ?_
        norm_num
      specialize c1 (by simp) (by simp) h10
      simpa [Real.logb_pow] using c1

-- In other words, $2^{m}$ has $k \geq n$ non-zero decimal digits, as claimed.
  have h12 : n < k + 1 := by
    rify at h11 ⊢
    have c1 : StrictMonoOn (Real.logb 4) (Set.Ioi 0) := by
      refine Real.strictMonoOn_logb ?_
      norm_num
    specialize c1 (by simp) (by simp) h11
    simpa [Real.logb_pow] using c1

  omega





#exit

def Nat.nth_digit (b x k : ℕ) := x / b ^ k % b

theorem Nat.nth_digit_mul_base (b x k : ℕ) (hb : b > 1) :
    b.nth_digit (x * b) (k + 1) = b.nth_digit x k := by
  unfold Nat.nth_digit
  congr 1
  apply Nat.mul_div_mul_right
  omega

theorem Nat.sum_nth_digit_mul_base_pow {b : ℕ} (hb : b ≥ 2) :
    ∀ x, x = ∑ k ∈ Ico 0 (b.log x + 1), b.nth_digit x k * b ^ k := by
  unfold Nat.nth_digit
  apply Nat.strongRec
  intro x ih
  obtain hx | hx : x < b ∨ x ≥ b := by omega
  · have h1 := Nat.log_of_lt hx
    have h2 := Nat.mod_eq_of_lt hx
    simp [h1, h2]
  · calc
      x = b * (x / b) + x % b := by rw [Nat.div_add_mod]
      _ = b * (∑ k ∈ Ico 0 (b.log x), x / b / b ^ k % b * b ^ k) + x % b := by
        specialize ih (x / b) (Nat.div_lt_self (by omega) hb)
        have h1 := Nat.log_pos (by omega) hx
        have h2 : b.log (x / b) + 1 = b.log x := by simp; omega
        conv_lhs => rw [ih, h2]
      _ = (∑ k ∈ Ico 0 (b.log x), (x / b ^ (k + 1) % b * b ^ (k + 1))) + x % b := by
        congr 1
        rw [mul_sum]
        apply sum_congr rfl
        intro k hk
        calc
          _ = x / b / b ^ k % b * (b ^ k * b) := by ring
          _ = _ := by congr 2; rw [Nat.div_div_eq_div_mul, Nat.mul_comm, Nat.pow_succ]
      _ = (∑ k ∈ Ico 1 (b.log x + 1), (x / b ^ k % b * b ^ k)) + x % b := by
        congr 1
        apply sum_nbij (· + 1)
        · intro k hk; simp at hk ⊢; omega
        · intro k hk k' hk' h; simpa using h
        · intro k hk
          simp only [Set.mem_image]
          use k - 1; simp at hk ⊢; omega
        · simp
      _ = ∑ k ∈ Ico 0 (b.log x + 1), x / b ^ k % b * b ^ k := by
        have h1 : {0} ⊆ Ico 0 (b.log x + 1) := by simp
        have h2 : Ico 0 (b.log x + 1) \ {0} = Ico 1 (b.log x + 1) := by ext k; simp; omega
        rw [←sum_sdiff h1, h2]
        simp

theorem three_dvd_iff (x : ℕ) :
    3 ∣ x ↔ (∑ k ∈ Ico 0 ((10).log x + 1), (10).nth_digit x k) % 3 = 0 := calc
  3 ∣ x ↔ x % 3 = 0 := by exact Nat.dvd_iff_mod_eq_zero
  _ ↔ _ := by
    apply Eq.congr ?_ rfl
    have h1 := (10).sum_nth_digit_mul_base_pow (by norm_num) x
    conv_lhs => rw [h1, Finset.sum_nat_mod]
    conv_rhs => rw [Finset.sum_nat_mod]
    congr 2 with k
    generalize (10).nth_digit x k = d
    induction' k with k ih
    · simp
    · calc
        _ = d * (10 ^ k * 10) % 3 := by rfl
        _ = d % 3 * ((10 ^ k * 10) % 3) % 3 := by rw [Nat.mul_mod]
        _ = d % 3 * ((10 ^ k % 3) * (10 % 3) % 3) % 3 := by congr 2; rw [Nat.mul_mod]
        _ = d % 3 * (10 ^ k % 3) % 3 := by simp
        _ = d * 10 ^ k % 3 := by rw [←Nat.mul_mod]
        _ = _ := ih
