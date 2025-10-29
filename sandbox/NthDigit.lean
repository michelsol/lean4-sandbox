import Mathlib

namespace Nat

open Finset

/-- The `n`-th digit of `x` in base `b`. -/
def nthDigit (b x n : ℕ) := x / b ^ n % b

theorem nthDigit_lt {b : ℕ} (hb : b > 0) (x n : ℕ) : nthDigit b x n < b := by
  exact mod_lt _ hb

theorem nthDigit_eq_zero_of_lt {b x n : ℕ} (h : x < b ^ n) :
    nthDigit b x n = 0 := calc
  x / b ^ n % b = 0 % b := by rw [div_eq_of_lt h]
  _ = 0 := by simp

theorem nthDigit_mul_base {b : ℕ} (hb : b > 0) (x n : ℕ) (hn : n > 0) :
    nthDigit b (x * b) n = nthDigit b x (n - 1) := by
  unfold nthDigit
  congr 1
  calc
    x * b / b ^ n = x * b / (b ^ (n - 1) * b) := by rw [Nat.pow_pred_mul hn]
    _ = _ := by exact Nat.mul_div_mul_right x (b ^ (n - 1)) hb

theorem nthDigit_div_base {b : ℕ} (x n : ℕ) :
    nthDigit b (x / b) n = nthDigit b x (n + 1) := by
  unfold nthDigit
  congr 1
  calc
    x / b / b ^ n = x / (b * b ^ n) := by exact Nat.div_div_eq_div_mul x b (b ^ n)
    _ = _ := by ring_nf

theorem sum_nthDigit_mul_base_pow {b : ℕ} (hb : b ≥ 2) :
    ∀ x, ∑ k ∈ Ico 0 (b.log x + 1), b.nthDigit x k * b ^ k = x := by
  unfold nthDigit
  apply Nat.strongRec
  intro x ih
  obtain hx | hx : x < b ∨ x ≥ b := by omega
  · have h1 := Nat.log_of_lt hx
    have h2 := Nat.mod_eq_of_lt hx
    simp [h1, h2]
  · symm
    calc
      x = b * (x / b) + x % b := by rw [Nat.div_add_mod]
      _ = b * (∑ k ∈ Ico 0 (b.log x), x / b / b ^ k % b * b ^ k) + x % b := by
        specialize ih (x / b) (Nat.div_lt_self (by omega) hb)
        have h1 := Nat.log_pos (by omega) hx
        have h2 : b.log (x / b) + 1 = b.log x := by simp; omega
        conv_lhs => rw [←ih, h2]
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

theorem sum_mul_base_pow_lt_base_pow {b : ℕ} (hb : b ≥ 2) {f : ℕ → ℕ} (hf : ∀ i, f i < b)
    (n : ℕ) : ∑ i ∈ Ico 0 n, f i * b ^ i < b ^ n := calc
    _ ≤ ∑ i ∈ Ico 0 n, b ^ i * f i := by
      apply sum_le_sum
      intro i hi
      linarith
    _ ≤ ∑ i ∈ Ico 0 n, b ^ i * (b - 1) := by
      apply sum_le_sum
      intro i hi
      apply Nat.mul_le_mul
      · omega
      · exact le_sub_one_of_lt (hf i)
    _ = (∑ i ∈ Ico 0 n, b ^ i) * (b - 1) := by
      symm
      apply sum_mul
    _ ≤ (∑ i ∈ Ico 0 n, b ^ i) * (b - 1) := by
      apply mul_le_mul_right (b - 1)
      apply sum_le_sum_of_subset
      intro i hi
      simp at hi ⊢
      omega
    _ = (b ^ n - 1) / (b - 1) * (b - 1) := by
      congr 1
      convert geomSum_eq hb n using 2
      simp
    _ ≤ b ^ n - 1 := by apply div_mul_le_self
    _ < _ := by
      apply sub_one_lt
      simp
      omega

theorem nthDigit_sum_mul_base_pow {b : ℕ} (hb : b ≥ 2) {f : ℕ → ℕ} (hf : ∀ i, f i < b)
    {n k : ℕ} : b.nthDigit (∑ i ∈ Ico 0 n, f i * b ^ i) k = if k < n then f k else 0 := by
  unfold nthDigit
  have h1 : (∑ i ∈ Ico (k + 1) n, f i * b ^ (i - k)) % b = 0 := by
    apply dvd_iff_mod_eq_zero.mp
    apply dvd_sum
    intro i hi
    simp at hi
    apply Nat.dvd_mul_left_of_dvd
    apply dvd_pow_self b
    omega
  split_ifs with hk2
  · calc
      _ = (∑ i ∈ Ico 0 k, f i * b ^ i + ∑ i ∈ Ico k n, f i * b ^ i) / b ^ k % b := by
        congr 2
        symm
        exact sum_Ico_consecutive _ (by omega) (by omega)
      _ = ((∑ i ∈ Ico 0 k, f i * b ^ i) / b ^ k +
          (∑ i ∈ Ico k n, f i * b ^ i) / b ^ k) % b := by
        congr 1
        apply Nat.add_div_of_dvd_left
        apply dvd_sum
        intro i hi
        apply Nat.dvd_mul_left_of_dvd
        apply Nat.pow_dvd_pow
        simp at hi
        omega
      _ = (0 + (∑ i ∈ Ico k n, f i * b ^ i) / b ^ k) % b := by
        congr 2
        apply div_eq_of_lt
        exact sum_mul_base_pow_lt_base_pow hb hf k
      _ = (∑ i ∈ Ico k n, f i * b ^ i) / b ^ k % b := by simp
      _ = (∑ i ∈ Ico k n, f i * b ^ i / b ^ k) % b := by
        congr 1
        have h1 : ∀ i ∈ Ico k n, b ^ k ∣ f i * b ^ i := by
          intro i hi
          apply Nat.dvd_mul_left_of_dvd
          apply Nat.pow_dvd_pow
          simp at hi
          omega
        have h2 : b ^ k ∣ ∑ i ∈ Ico k n, f i * b ^ i := dvd_sum h1
        zify at h1 h2
        qify [h2]
        rw [sum_div]
        apply sum_congr rfl
        intro i hi
        qify [h1 i hi]
      _ = (∑ i ∈ Ico k n, f i * b ^ (i - k)) % b := by
        congr 1
        apply sum_congr rfl
        intro i hi
        simp at hi
        calc
          _ = f i * (b ^ i / b ^ k) := by
            refine Nat.mul_div_assoc (f i) ?_
            refine Nat.pow_dvd_pow b ?_
            omega
          _ = _ := by
            congr 1
            refine Nat.pow_div ?_ ?_
            · omega
            · omega
      _ = (∑ i ∈ Ico (k + 1) n, f i * b ^ (i - k) + f k) % b := by
        congr 1
        have h1 : {k} ⊆ Ico k n := by
          intro i hi
          simp at hi ⊢
          subst hi
          omega
        rw [←sum_sdiff h1]
        congr 1
        · congr 1
          ext i
          simp
          omega
        · simp
      _ = (∑ i ∈ Ico (k + 1) n, f i * b ^ (i - k)) % b + f k % b := by
        refine add_mod_of_add_mod_lt ?_
        simpa [h1] using mod_lt_of_lt (hf k)
      _ = f k % b := by simp [h1]
      _ = _ := by exact mod_eq_of_lt (hf k)
  · calc
      _ = 0 % b := by
        congr 1
        refine div_eq_of_lt ?_
        calc
          _ ≤ ∑ i ∈ Ico 0 k, f i * b ^ i := by
            apply sum_le_sum_of_subset
            intro i hi
            simp at hi ⊢
            omega
          _ < _ := sum_mul_base_pow_lt_base_pow hb hf k
      _ = _ := by simp

theorem nthDigit_log_eq_zero_iff (b x : ℕ) (hb : b ≥ 2) : b.nthDigit x (b.log x) = 0 ↔ x = 0 := by
  constructor
  all_goals intro h1
  · by_contra! h2
    unfold nthDigit at h1
    replace ⟨c, h1⟩ : b ∣ x / b ^ (b.log x) := by omega
    have h3 := h1
    apply_fun log b at h3
    have h4 k : log b (x / b ^ k) = log b x - k := by
      induction k
      · simp
      · next k ih => calc
          _ = log b (x / (b ^ k * b)) := rfl
          _ = log b (x / b ^ k / b) := by rw [Nat.div_div_eq_div_mul]
          _ = log b (x / b ^ k) - 1 := by apply log_div_base
          _ = log b x - k - 1 := by rw [ih]
          _ = log b x - (k + 1) := rfl
    convert_to 0 = log b c + 1 using 1 at h3
    · simp [h4]
    · calc
        _ = log b (c * b) := by ring_nf
        _ = log b c + 1 := by
          apply log_mul_base hb
          by_contra! hc
          have hb2 : b ≠ 0 := by omega
          simp [hc, hb2] at h1
          have := Nat.pow_log_le_self b h2
          omega
    omega
  · simp [h1, nthDigit]

end Nat

namespace Nat

open Finset

def toFinDigits (b x : ℕ) : Fin (b.log x + 1) → ℕ :=
  fun ⟨n, _⟩ => nthDigit b x n

def ofFinDigits (b : ℕ) {l : ℕ} (d : Fin l → ℕ) :=
  ∑ ⟨k, hk⟩ : Ico 0 l, d ⟨k, by simpa using hk⟩ * b ^ k

theorem ofFinDigits_toFinDigits {b x : ℕ} (hb : b ≥ 2) : b.ofFinDigits (b.toFinDigits x) = x := by
  unfold ofFinDigits toFinDigits
  calc
    _ = ∑ k ∈ Ico 0 (log b x + 1), b.nthDigit x k * b ^ k := by
      apply Finset.sum_bij (fun i _ => i.val)
      all_goals simp
    _ = x := sum_nthDigit_mul_base_pow hb x

end Nat

example (s : Finset ℕ) (f : s → ℕ) :
    ∑ x : s, f x = ∑ i ∈ s, if hi : i ∈ s then f ⟨i, hi⟩ else 0 := by
  apply Finset.sum_bij (fun i _ => i.val)
  all_goals simp
