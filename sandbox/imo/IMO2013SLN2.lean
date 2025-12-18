import Mathlib

open Finset

/-
Prove that for any pair of positive integers $k$ and $n$ there exist $k$ positive integers
$m_1,m_2,...,m_k$ such that
$$1+\dfrac{2^k-1}{n}=\left(1+\dfrac{1}{m_1}\right)\left(1+\dfrac{1}{m_2}\right)...\left(1+\dfrac{1}{m_k}\right)$$
-/

theorem number_theory_24321 :
    ∀ (k : ℕ) (_ : k ≥ 1) (n : ℤ) (_ : n ≥ 1), ∃ m : ℕ → ℤ,
    1 + ((2 ^ k - 1) / n : ℚ) = ∏ i ∈ Icc 1 k, (1 + (1 / m i : ℚ))
    := by
  -- We proceed by induction on $k$. For $k=1$ the statement is trivial.
  apply Nat.le_induction
  . intro n hn
    use λ _ => n
    norm_num
  -- Assuming we have proved it for $k=j$, we now prove it for $k=j+1$.
  . intro j hj ihj
    intro n hn
    have : ∃ t, n = 2 * t - 1 ∨ n = 2 * t := by use (n + 1) / 2; omega
    obtain ⟨t, ht⟩ := this
    rcases ht with ht | ht
    -- Case 1. $n=2 t-1$ for some positive integer $t$.  Observe that
    -- $$ 1+\frac{2^{j+1}-1}{2 t-1}=\frac{2\left(t+2^{j}-1\right)}{2 t} \cdot \frac{2 t}{2 t-1}=\left(1+\frac{2^{j}-1}{t}\right)\left(1+\frac{1}{2 t-1}\right) . $$
    -- so setting $m_{j+1}=2 t-1$ and using the induction hypothesis gives the desired expression.
    . obtain ⟨m, ihm⟩ := ihj t (by omega)
      rw [ht]
      let m' i := if i = j + 1 then 2 * t - 1 else m i
      use m'
      calc
      _ = ((2 * (t + 2 ^ j - 1)) / (2 * t) : ℚ) * ((2 * t) / (2 * t - 1) : ℚ) := by
        have : (2 * t - 1 : ℚ) ≠ 0 := by norm_cast; omega
        have : (2 * t : ℚ) ≠ 0 := by norm_cast; omega
        field_simp
        ring_nf
      _ = (1 + ((2 ^ j - 1) / t : ℚ)) * (1 + (1 / (2 * t - 1) : ℚ)) := by
        congr 1
        . have : (t : ℚ) ≠ 0 := by norm_cast; omega
          field_simp
          ring_nf
        . have : (2 * t - 1 : ℚ) ≠ 0 := by norm_cast; omega
          field_simp
      _ = (∏ i ∈ Icc 1 j, (1 + (1 / m i : ℚ))) * (1 + (1 / (2 * t - 1) : ℚ)) := by rw [←ihm]
      _ = (∏ i ∈ Icc 1 j, (1 + (1 / m' i : ℚ))) * (1 + (1 / m' (j + 1) : ℚ)) := by
        congr 1
        . apply prod_congr rfl
          intro i hi
          have : ¬i = j + 1 := by simp at hi; omega
          simp [m', this]
        . simp [m']
      _ = ∏ i ∈ Icc 1 (j + 1), (1 + (1 / m' i : ℚ)) := by rw [prod_Icc_succ_top]; omega
    -- Case 2. $n=2 t$ for some positive integer $t$.  Now we have
    -- $$ 1+\frac{2^{j+1}-1}{2 t}=\frac{2 t+2^{j+1}-1}{2 t+2^{j+1}-2} \cdot \frac{2 t+2^{j+1}-2}{2 t}=\left(1+\frac{1}{2 t+2^{j+1}-2}\right)\left(1+\frac{2^{j}-1}{t}\right) $$
    -- noting that $2 t+2^{j+1}-2>0$. Setting $m_{j+1}=2 t+2^{j+1}-2$ then gives the desired expression.
    . obtain ⟨m, ihm⟩ := ihj t (by omega)
      rw [ht]
      let m' i := if i = j + 1 then 2 * t + 2 ^ (j + 1) - 2 else m i
      use m'
      have h1 : (2 * t + 2 ^ (j + 1) - 2 : ℚ) > 0 := by
        norm_cast
        push_cast
        have : 2 * t ≥ 2 := by omega
        have : 2 ^ (j + 1) ≥ 1 := by exact Nat.one_le_two_pow
        linarith
      calc
      _ = ((2 * t + 2 ^ (j + 1) - 2) / (2 * t) : ℚ)
          * ((2 * t + 2 ^ (j + 1) - 1) / (2 * t + 2 ^ (j + 1) - 2) : ℚ) := by
        have : (2 * t : ℚ) ≠ 0 := by norm_cast; omega
        field_simp
        ring_nf
      _ = (1 + ((2 ^ j - 1) / t : ℚ)) * (1 + (1 / (2 * t + 2 ^ (j + 1) - 2) : ℚ)) := by
        congr 1
        . have : (t : ℚ) ≠ 0 := by norm_cast; omega
          field_simp
          ring_nf
        . field_simp
          ring_nf
      _ = (∏ i ∈ Icc 1 j, (1 + (1 / m i : ℚ))) * (1 + (1 / (2 * t + 2 ^ (j + 1) - 2) : ℚ)) := by rw [←ihm]
      _ = (∏ i ∈ Icc 1 j, (1 + (1 / m' i : ℚ))) * (1 + (1 / m' (j + 1) : ℚ)) := by
        congr 1
        . apply prod_congr rfl
          intro i hi
          have : ¬i = j + 1 := by simp at hi; omega
          simp [m', this]
        . simp [m']
      _ = ∏ i ∈ Icc 1 (j + 1), (1 + (1 / m' i : ℚ)) := by rw [prod_Icc_succ_top]; omega
