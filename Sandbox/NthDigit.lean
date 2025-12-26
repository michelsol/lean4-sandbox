import Mathlib

namespace Nat

open Finset

/-- The `k`-th digit of `n` in base `b`. -/
def digit (b n k : ℕ) := n / b ^ k % b

/-- Dividing `n` by `b` shifts the digits to the right by one. -/
theorem digit_div_base {b : ℕ} (n k : ℕ) : digit b (n / b) k = digit b n (k + 1) := by
  unfold digit
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ']

/-- The sum of the digits of `n` in base `b`, multiplied by the corresponding powers of `b`,
  equals `n`. -/
theorem sum_digit_mul_base_pow {b : ℕ} (hb : b > 1) :
    ∀ n, ∑ k ∈ Ico 0 (b.log n + 1), b.digit n k * b ^ k = n := by
  apply Nat.strongRec
  intro n ih
  obtain hn | hn : n < b ∨ n ≥ b := by omega
  · simp [digit, Nat.log_of_lt hn, Nat.mod_eq_of_lt hn]
  · symm
    calc
      n = b * (n / b) + n % b := by rw [Nat.div_add_mod]
      _ = b * ∑ k ∈ Ico 0 (b.log n), digit b (n / b) k * b ^ k + n % b := by
        rw [log_of_one_lt_of_le hb hn, ih (n / b) (Nat.div_lt_self (by omega) hb)]
      _ = ∑ k ∈ Ico 0 (b.log n), digit b n (k + 1) * b ^ (k + 1) + n % b := by
        simp_rw [mul_sum, digit_div_base]
        ring_nf
      _ = ∑ k ∈ Ico 1 (b.log n + 1), digit b n k * b ^ k + n % b := by
        congr 1
        apply sum_bij (fun k _ => k + 1)
        · simp
        · simp
        · intro k hk; use k - 1; simp at hk ⊢; omega
        · simp
      _ = ∑ k ∈ Ico 0 (b.log n + 1), digit b n k * b ^ k := by
        have h1 : {0} ⊆ Ico 0 (b.log n + 1) := by simp
        have h2 : Ico 0 (b.log n + 1) \ {0} = Ico 1 (b.log n + 1) := by ext _; simp; omega
        rw [←sum_sdiff h1, h2]
        simp [digit]

theorem digit_lt {b : ℕ} (hb : b > 0) (n k : ℕ) : digit b n k < b := mod_lt _ hb

theorem digit_eq_zero_of_lt {b n k : ℕ} (h : n < b ^ k) : digit b n k = 0 := by
  simp [digit, div_eq_of_lt h]

theorem digit_mul_base {b : ℕ} (hb : b > 0) (n k : ℕ) (hk : k > 0) :
    digit b (n * b) k = digit b n (k - 1) := by
  unfold digit
  rw [←b.pow_pred_mul hk, b.mul_div_mul_right _ _ hb]

theorem sum_mul_base_pow_lt_base_pow {b : ℕ} (hb : b > 1) {f : ℕ → ℕ} (hf : ∀ i, f i < b)
    (k : ℕ) : ∑ i ∈ Ico 0 k, f i * b ^ i < b ^ k := calc
  _ ≤ ∑ i ∈ Ico 0 k, b ^ i * f i := by gcongr 1 with i hi; linarith
  _ ≤ ∑ i ∈ Ico 0 k, b ^ i * (b - 1) := by gcongr 2 with i hi; exact le_sub_one_of_lt (hf i)
  _ = (∑ i ∈ Ico 0 k, b ^ i) * (b - 1) := by rw [sum_mul]
  _ = (b ^ k - 1) / (b - 1) * (b - 1) := by congr 1; simpa using geomSum_eq hb k
  _ ≤ b ^ k - 1 := by apply div_mul_le_self
  _ < b ^ k := by apply sub_one_lt; simp; omega

theorem digit_sum_mul_base_pow {b : ℕ} (hb : b > 1) {f : ℕ → ℕ} (hf : ∀ i, f i < b)
    {k j : ℕ} : b.digit (∑ i ∈ Ico 0 k, f i * b ^ i) j = if j < k then f j else 0 := by
  unfold digit
  split_ifs with hj
  · calc
      _ = (∑ i ∈ Ico 0 j, f i * b ^ i + ∑ i ∈ Ico j k, f i * b ^ i) / b ^ j % b := by
        rw [sum_Ico_consecutive _ (by omega) (by omega)]
      _ = ((∑ i ∈ Ico 0 j, f i * b ^ i) / b ^ j + (∑ i ∈ Ico j k, f i * b ^ i) / b ^ j) % b := by
        congr 1
        apply Nat.add_div_of_dvd_left
        apply dvd_sum
        intro i hi
        apply Nat.dvd_mul_left_of_dvd
        apply Nat.pow_dvd_pow
        simp at hi; omega
      _ = (0 + (∑ i ∈ Ico j k, f i * b ^ i) / b ^ j) % b := by
        congr 2
        apply div_eq_of_lt
        exact sum_mul_base_pow_lt_base_pow hb hf j
      _ = (∑ i ∈ Ico j k, f i * b ^ i) / b ^ j % b := by simp
      _ = (∑ i ∈ Ico j k, f i * b ^ i / b ^ j) % b := by
        congr 1
        have h1 : ∀ i ∈ Ico j k, b ^ j ∣ f i * b ^ i := by
          intro i hi
          apply Nat.dvd_mul_left_of_dvd
          apply Nat.pow_dvd_pow
          simp at hi; omega
        have h2 : b ^ j ∣ ∑ i ∈ Ico j k, f i * b ^ i := dvd_sum h1
        zify at h1 h2
        qify [h2]
        rw [sum_div]
        congr! 1 with i hi
        qify [h1 i hi]
      _ = (∑ i ∈ Ico j k, f i * b ^ (i - j)) % b := by
        congr! 2 with i hi
        calc
          _ = f i * (b ^ i / b ^ j) := by
            apply Nat.mul_div_assoc
            apply Nat.pow_dvd_pow
            simp at hi; omega
          _ = f i * b ^ (i - j) := by
            congr 1
            apply Nat.pow_div
            · simp at hi; omega
            · omega
      _ = (∑ i ∈ Ico (j + 1) k, f i * b ^ (i - j) + f j) % b := by
        have h1 : {j} ⊆ Ico j k := by intro i hi; simp at hi; simpa [hi] using hj
        rw [←sum_sdiff h1]
        congr 3
        · ext i; simp; omega
        · simp
      _ = f j % b := by
        have h1 : (∑ i ∈ Ico (j + 1) k, f i * b ^ (i - j)) % b = 0 := by
          apply dvd_iff_mod_eq_zero.mp
          apply dvd_sum
          intro i hi
          apply Nat.dvd_mul_left_of_dvd
          apply dvd_pow_self b
          simp at hi; omega
        rw [add_mod_of_add_mod_lt]
        · simp [h1]
        · simp [h1, mod_lt_of_lt (hf j)]
      _ = f j := mod_eq_of_lt (hf j)
  · calc
      _ = 0 % b := by
        congr 1
        apply div_eq_of_lt
        calc
          _ ≤ ∑ i ∈ Ico 0 j, f i * b ^ i := by
            apply sum_le_sum_of_subset
            intro i hi
            simp at hi ⊢
            omega
          _ < _ := sum_mul_base_pow_lt_base_pow hb hf j
      _ = _ := by simp

theorem digit_log_eq_zero_iff (b n : ℕ) (hb : b > 1) : b.digit n (b.log n) = 0 ↔ n = 0 := by
  constructor
  all_goals intro h1
  · by_contra! h2
    unfold digit at h1
    replace ⟨c, h1⟩ : b ∣ n / b ^ (b.log n) := by omega
    have h3 := h1
    apply_fun log b at h3
    have h4 i : log b (n / b ^ i) = log b n - i := by
      induction i
      · simp
      · next i ih => calc
          _ = log b (n / (b ^ i * b)) := rfl
          _ = log b (n / b ^ i / b) := by rw [Nat.div_div_eq_div_mul]
          _ = log b (n / b ^ i) - 1 := by apply log_div_base
          _ = log b n - i - 1 := by rw [ih]
          _ = log b n - (i + 1) := rfl
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
  · simp [h1, digit]

end Nat


example (s : Finset ℕ) (f : s → ℕ) :
    ∑ x : s, f x = ∑ i ∈ s, if hi : i ∈ s then f ⟨i, hi⟩ else 0 := by
  apply Finset.sum_bij (fun i _ => i.val)
  all_goals simp


-- def n_leading_spaces (s : String) : Nat :=
--   match hs : s.toList with
--   | [] => 0
--   | ' ' :: t => 1 + n_leading_spaces (String.ofList t)
--   | _ => 0
--   termination_by s.length
--   decreasing_by
--     simp_wf
--     convert_to t.length < s.toList.length
--     simp [hs]

def countSpaces (s : String) : Nat := Id.run do
  let mut c := 0
  for x in s.toList do
    if x = ' ' then
      c := c + 1
  return c

def countSpaces2 (s : String) : Nat := (s.toList.filter (· = ' ')).length

theorem countSpaces_eq_countSpaces2 (s : String) : countSpaces s = countSpaces2 s := by
  unfold countSpaces countSpaces2
  dsimp
  induction s.toList
  · case nil => simp
  · case cons head tail ih =>
    by_cases h : head = ' '
    · simp only [List.forIn_cons, h]
      dsimp
      apply_fun (· + 1) at ih
      convert ih using 1
      simp only [↓Char.isValue, bind_pure_comp, map_pure]
      #check List.forIn'
      sorry
    · simpa [h] using ih
