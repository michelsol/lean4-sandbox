import Mathlib

/-
Let $n, m, k$ and $l$ be positive integers with $n \neq 1$ such that $n^{k}+m n^{l}+1$ divides $n^{k+l}-1$.
Prove that
$m=1$ and $l=2 k$
or
$l \mid k$ and $m=\frac{n^{k-l}-1}{n^{l}-1}$.
-/
theorem number_theory_24831
    (n m k l : ℕ) (hn : n > 0) (hm : m > 0) (hk : k > 0) (hl : l > 0) (hn : n ≠ 1)
    (h0 : (n ^ k + m * n ^ l + 1 : ℤ) ∣ (n ^ (k + l) - 1 : ℤ)) :
    (m = 1 ∧ l = 2 * k) ∨ ((l : ℤ) ∣ k ∧ m = ((n ^ (k - l) - 1 : ℤ) / (n ^ l - 1 : ℤ) : ℚ)) := by

-- It is given that $ n^{k}+m n^{l}+1 \mid n^{k+l}-1 $    (1)
-- This implies $ n^{k}+m n^{l}+1 \mid\left(n^{k+l}-1\right)+\left(n^{k}+m n^{l}+1\right)=n^{k+l}+n^{k}+m n^{l} . $   (2)
  have h1 : (n ^ k + m * n ^ l + 1 : ℤ) ∣ n ^ (k + l) + n ^ k + m * n ^ l := by
    calc
      _ ∣ (n ^ (k + l) - 1 : ℤ) + (n ^ k + m * n ^ l + 1) := by exact dvd_add_self_right.mpr h0
      _ = _ := by ring

-- We have two cases to discuss. l ≥ k and l < k.
  obtain h2 | h2 : l ≥ k ∨ l < k := by omega
-- - Case 1. $l \geqslant k$.
  .
-- Since $\left(n^{k}+m n^{l}+1, n\right)=1$,(2) yields $ n^{k}+m n^{l}+1 \mid n^{l}+m n^{l-k}+1 . $
    have h3 : IsCoprime (n ^ k + m * n ^ l + 1 : ℤ) n := by
      refine Int.isCoprime_iff_gcd_eq_one.mpr ?_
      sorry
    have h4 : (n ^ k + m * n ^ l + 1 : ℤ) ∣ n ^ l + m * n ^ (l - k) + 1 := by
      have c1 : (n ^ k + m * n ^ l + 1 : ℤ) ∣ n ^ k * (n ^ l + m * n ^ (l - k) + 1) := by
        convert h1 using 1
        calc
          (_ : ℤ) = n ^ k * n ^ l + n ^ k + m * (n ^ k * n ^ (l - k)) := by ring
          _ = _ := by
            congr 2
            . ring
            . exact pow_mul_pow_sub _ h2
      have c2 : IsCoprime (n ^ k + m * n ^ l + 1 : ℤ) (n ^ k) := by exact IsCoprime.pow_right h3
      exact IsCoprime.dvd_of_dvd_mul_left c2 c1

-- In particular, we get $n^{k}+m n^{l}+1 \leqslant n^{l}+m n^{l-k}+1$.
    have h5 : n ^ k + m * n ^ l + 1 ≤ n ^ l + m * n ^ (l - k) + 1 := by
      norm_cast at h4
      exact Nat.le_of_dvd (by omega) h4

-- As $n \geqslant 2$ and $k \geqslant 1,(m-1) n^{l}$ is at least $2(m-1) n^{l-k}$.
    have hn2 : n ≥ 2 := by omega
    have h6 : (m - 1 : ℤ) * n ^ l ≥ 2 * (m - 1 : ℤ) * n ^ (l - k) := by
      sorry

-- It follows that the inequality cannot hold when $m \geqslant 2$.
    have h7 : m < 2 := by
      by_contra! h7
      sorry
    replace h7 : m = 1 := by omega

-- For $m=1$, the above divisibility becomes $ n^{k}+n^{l}+1 \mid n^{l}+n^{l-k}+1 . $
    replace h4 : (n ^ k + n ^ l + 1 : ℤ) ∣ n ^ l + n ^ (l - k) + 1 := by
      subst h7
      convert h4 using 1 <;> ring

-- Note that $n^{l}+n^{l-k}+1 < n^{l}+n^{l}+1 < 2\left(n^{k}+n^{l}+1\right)$.
    have h8 : n ^ l + n ^ (l - k) + 1 < 2 * (n ^ k + n ^ l + 1) := by
      calc
        _ < n ^ l + n ^ l + 1 := by
          sorry
        _ < _ := by
          sorry

-- Thus we must have $n^{l}+n^{l-k}+1=n^{k}+n^{l}+1$
    have h9 : n ^ l + n ^ (l - k) + 1 = n ^ k + n ^ l + 1 := by
      sorry

-- so that $l=2 k$
    have h10 : l = 2 * k := by
      sorry

-- which gives the first result.
    left
    simp [h7, h10]

-- - Case 2. $l < k$.
  .
-- This time (2) yields $ n^{k}+m n^{l}+1 \mid n^{k}+n^{k-l}+m $
    have h3 : IsCoprime (n ^ k + m * n ^ l + 1 : ℤ) n := by
      refine Int.isCoprime_iff_gcd_eq_one.mpr ?_
      sorry
    have h4 : (n ^ k + m * n ^ l + 1 : ℤ) ∣ n ^ k + n ^ (k - l) + m := by
      have c1 : (n ^ k + m * n ^ l + 1 : ℤ) ∣ n ^ l * (n ^ k + n ^ (k - l) + m) := by
        convert h1 using 1
        calc
          (_ : ℤ) = n ^ l * n ^ k + n ^ l * n ^ (k - l) + m * n ^ l := by ring
          _ = _ := by
            congr 2
            . ring
            . exact pow_mul_pow_sub _ (by omega)
      have c2 : IsCoprime (n ^ k + m * n ^ l + 1 : ℤ) (n ^ l) := by exact IsCoprime.pow_right h3
      exact IsCoprime.dvd_of_dvd_mul_left c2 c1

-- In particular, we get $n^{k}+m n^{l}+1 \leqslant n^{k}+n^{k-l}+m$,
    have h5 : n ^ k + m * n ^ l + 1 ≤ n ^ k + n ^ (k - l) + m := by
      norm_cast at h4
      exact Nat.le_of_dvd (by omega) h4

-- which implies $ m \leqslant \frac{n^{k-l}-1}{n^{l}-1} $     (3)
    have h6 : m ≤ ((n ^ (k - l) - 1 : ℤ) / (n ^ l - 1 : ℤ) : ℚ) := by
      sorry

-- On the other hand, from (1) we may let $n^{k+l}-1=\left(n^{k}+m n^{l}+1\right) t$ for some positive integer $t$.
    obtain ⟨t, h7⟩ := h0
    have ht : t > 0 := by
      sorry

-- Obviously, $t$ is less than $n^{l}$, which means $t \leqslant n^{l}-1$ as it is an integer.
    have h8 : t < n ^ l := by
      sorry
    replace h8 : t ≤ n ^ l - 1 := by omega

-- Then we have $n^{k+l}-1 \leqslant\left(n^{k}+m n^{l}+1\right)\left(n^{l}-1\right)$,
    have h9 : (n ^ (k + l) - 1 : ℤ) ≤ (n ^ k + m * n ^ l + 1) * (n ^ l - 1) := by field_simp [h7, ht, h8]

-- which implies $ m \geqslant \frac{n^{k-l}-1}{n^{l}-1} $
    have h10 : m ≥ ((n ^ (k - l) - 1 : ℤ) / (n ^ l - 1 : ℤ) : ℚ) := by
      sorry

-- Equations (3) and (4) combine to give $m=\frac{n^{k-l}-1}{n^{l}-1}$.
    have h11 : m = ((n ^ (k - l) - 1 : ℤ) / (n ^ l - 1 : ℤ) : ℚ) := by linarith

-- As this is an integer, we have $l \mid k-l$.
    have h12 : (l : ℤ) ∣ (k - l : ℤ) := by
      convert_to (l : ℤ) ∣ (k - l : ℕ) using 1
      . push_cast [h2]; rfl
      have c1 : k - l > 0 := by omega
      generalize k - l = k at h11 c1
      obtain ⟨q, r, c2, c3⟩ : ∃ (q : ℕ) (r : ℕ) (_ : r < l), k = q * l + r := by
        use k / l
        use k % l
        use by exact Nat.mod_lt k hl
        exact Eq.symm (Nat.div_add_mod' k l)
      subst c3
      suffices r = 0 by simp [this]
      replace h11 : m = n ^ r * (((n ^ l) ^ q - 1 : ℤ) / (n ^ l - 1 : ℤ) : ℚ) +
                        ((n ^ r - 1 : ℤ) / (n ^ l - 1 : ℤ) : ℚ) := by
        sorry
      obtain ⟨x, c3⟩ : ∃ x : ℤ, ((n ^ r - 1 : ℤ) / (n ^ l - 1 : ℤ) : ℚ) = x := by
        sorry
      have c4 : x = 0 := by
        have d0 : 0 ≤ (n ^ r - 1 : ℤ) := by
          suffices n ^ 0 ≤ (n ^ r : ℤ) by linarith
          refine (pow_le_pow_iff_right₀ ?_).mpr ?_
          . omega
          . omega
        have d1 : (n ^ r - 1 : ℤ) < (n ^ l - 1 : ℤ) := by
          gcongr
          omega
        have d2 : 0 ≤ (n ^ l - 1 : ℤ) := by omega
        generalize (n ^ r - 1 : ℤ) = y at c3 d0 d1 d2
        generalize (n ^ l - 1 : ℤ) = z at c3 d0 d1 d2
        obtain dz | dz : z = 0 ∨ z ≠ 0 := by tauto
        . subst dz
          qify
          simp at c3
          simp [c3]
        . have d3 : z ∣ y := by
            use x
            qify at dz ⊢
            field_simp at c3
            convert c3 using 1; ring
          replace c3 : y / z = x := by
            qify [d3]
            exact c3
          rw [←c3]
          exact Int.ediv_eq_zero_of_lt d0 d1
      subst c4
      have c4 : (n ^ l - 1 : ℚ) ≠ 0 := by
        by_contra! c4
        replace c4 : (n ^ l : ℤ) = n ^ 0 := by
          qify
          linarith
        have d1 : l = 0 := by
          norm_cast at c4
          apply Nat.pow_right_injective _ c4
          omega
        omega
      have c5 : (n ^ r - 1 : ℚ) = 0 := by
        field_simp [c4] at c3
        simpa using c3
      replace c5 : n ^ r = n ^ 0 := by
        qify
        linarith
      apply Nat.pow_right_injective _ c5
      omega

-- This means $l \mid k$ and it corresponds to the second result.
    have h13 : (l : ℤ) ∣ k := by exact dvd_sub_self_right.mp h12
    right
    simp [h11, h13]
