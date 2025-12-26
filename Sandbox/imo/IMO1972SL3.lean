import Mathlib

open Nat Finset

/-
Let $m$ and $n$ be nonnegative integers. Prove that $m!n!(m+$ $n)$ ! divides $(2 m)!(2 n)!$.
-/

theorem other_24954 (m n : ℕ) (hm : m ≥ 1) (hn : n ≥ 1) : m ! * n ! * (m + n) ! ∣ (2 * m) ! * (2 * n) ! := by

-- Let $f(m, n)=\frac{(2 m)!(2 n)!}{m!n!(m+n)!}$.
  let f (m n : ℕ) : ℚ := ((2 * m) ! * (2 * n) ! / (m ! * n ! * (m + n) !) : ℚ)

-- Then it is directly shown that  $$ f(m, n)=4 f(m, n-1)-f(m+1, n-1), $$
  have h1 m (hm : m ≥ 1) n (hn : n ≥ 1) : f m n = 4 * f m (n - 1) - f (m + 1) (n - 1) := by
    have : 2 * n ≥ 1 := sorry
    have : (2 * n - 1 : ℚ) ≠ 0 := sorry
    replace h1 : f m (n - 1) = f m n * (n * (m + n) / (2 * n * (2 * n - 1))) := by
      dsimp only [f]
      field_simp
      norm_cast
      sorry
    have h2 : f (m + 1) (n - 1) = f m n * ((2 * m + 1) / (2 * n - 1)) := by
      have : (2 * n - 1 : ℚ) ≠ 0 := sorry
      dsimp only [f]
      field_simp
      norm_cast
      sorry
    suffices f m n * 1 = f m n * (4 * (n * (m + n) / (2 * n * (2 * n - 1)))
        - (2 * m + 1) / (2 * n - 1)) from by linarith
    congr 1
    field_simp
    ring_nf

-- and thus $n$ may be successively reduced until one obtains
-- $f(m, n)=$ $\sum_{r} c_{r} f(r, 0)$.

  have h2 : ∀ k, ∀ m ≥ 1, ∃ (c : ℕ → ℤ) (s : ℕ), f m k = ∑ r < s, c r * f r 0 := by
    apply Nat.strongRec
    intro n ihn
    rcases (by omega : n = 0 ∨ n ≥ 1) with hn | hn
    . intro m hm
      use λ k ↦ if k = m then 1 else 0
      use m + 1
      simp [hn]
    . intro m hm
      obtain ⟨c1, s1, ih1⟩ := ihn (n - 1) (by omega) m (by omega)
      obtain ⟨c2, s2, ih2⟩ := ihn (n - 1) (by omega) (m + 1) (by omega)
      specialize h1 m hm n hn
      rw [h1, ih1, ih2]
      use λ r ↦ 4 * (if r < s1 then c1 r else 0) - (if r < s2 then c2 r else 0), max s1 s2
      simp [sub_mul, sum_add_distrib, sum_ite, mul_sum, mul_assoc]

  obtain ⟨c, s, h2⟩ := h2 n m hm


-- Now $f(r, 0)$ is a simple binomial coefficient and the $c_{r}$ 's are integers.
  have h3 m : f m 0 = choose (2 * m) m := by
    suffices (2 * m)! = (2 * m).choose m * (m ! * m !) from by
      field_simp [f]
      norm_cast
    rw [choose_eq_factorial_div_factorial (by omega)]
    rw [(by omega : 2 * m - m = m)]
    apply Eq.symm (Nat.div_mul_cancel ?_)
    sorry

  simp only [h3] at h2
  norm_cast at h2

-- So $f(m,n)$ must be an integer.
  have h4 : (f m n).isInt := by rw [h2]; rfl
  dsimp only [f] at h4
  norm_cast at h4

  have dvd_of_isInt {p q : ℤ} (h : (p / q : ℚ).isInt) (hq : q ≠ 0) : q ∣ p := by
    use (p / q : ℚ).num; qify; rw [←Rat.eq_num_of_isInt h]; field_simp

  replace h4 := dvd_of_isInt h4 sorry
  norm_cast at h4
