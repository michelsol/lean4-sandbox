import Mathlib

/-
Let $a, b$ be positive integers, and $a+b \sqrt{2}$ $=(1+\sqrt{2})^{100}$.
Then the units digit of $a b$ is 4.
-/
theorem number_theory_322477
    (a b : ℤ) (ha : a > 0) (hb : b > 0)
    (h1 : a + b * √2 = (1 + √2) ^ 100)
    : a * b % 10 = 4 := by

-- Thanks to the properties of ℤ[√2], by induction, we have $ a-b \sqrt{2}=(1-\sqrt{2})^{100} \text {. } $
  have h2 : a - b * √2 = (1 - √2) ^ 100 := by
    generalize 100 = n at h1 ⊢
    -- restate the problem in ℤ[√2]
    replace h1 : (⟨a, b⟩ : ℤ√2) = (⟨1, 1⟩ : ℤ√2) ^ n := by
      apply_fun Zsqrtd.toReal (by norm_num)
      . simpa [RingHom.map_pow] using h1
      . apply Zsqrtd.toReal_injective
        intro d
        by_contra hd
        have c1 : d ≥ -2 ∧ d ≤ 2  := by split_ands <;> nlinarith
        obtain c1 | c1 | c1 | c1 | c1 : d = -2 ∨ d = -1 ∨ d = 0 ∨ d = 1 ∨ d = 2 := by omega
        all_goals simp [c1] at hd
    suffices (⟨a, -b⟩ : ℤ√2) = (⟨1, -1⟩ : ℤ√2) ^ n by
      apply_fun Zsqrtd.toReal (by norm_num) at this
      simpa [RingHom.map_pow] using this
    clear ha hb
    induction' n with n ih generalizing a b
    . rw [Zsqrtd.ext_iff] at h1 ⊢
      simpa using h1
    . let a' := ((⟨1, 1⟩ : ℤ√2) ^ n).re
      let b' := ((⟨1, 1⟩ : ℤ√2) ^ n).im
      have c1 : (⟨a', b'⟩ : ℤ√2) = (⟨1, 1⟩ : ℤ√2) ^ n := by simp
      specialize ih a' b' c1
      have c2 : (⟨a, b⟩ : ℤ√2) = (⟨a' + 2 * b', a' + b'⟩ : ℤ√2) := by
        calc
          _ = _ := h1
          _ = ⟨1, 1⟩ ^ n * ⟨1, 1⟩ := by ring
          _ = ⟨a', b'⟩ * ⟨1, 1⟩ := by congr 1
          _ = _ := by simp [Zsqrtd.ext_iff]
      replace ⟨c2, c3⟩ : a = a' + 2 * b' ∧ b = a' + b' := by simpa using c2
      symm
      calc
        _ = ⟨1, -1⟩ ^ n * ⟨1, -1⟩ := by ring
        _ = ⟨a', -b'⟩ * ⟨1, -1⟩ := by rw [ih]
        _ = _ := by
          simp [Zsqrtd.ext_iff, c2, c3]
          ring


-- Therefore, $a=\frac{1}{2}\left((1+\sqrt{2})^{100}+(1-\sqrt{2})^{100}\right)$,

  have h3 : a = (1 / 2 : ℝ) * ((1 + √2) ^ 100 + (1 - √2) ^ 100) := by
    -- (1 + √2) ^ 100 is long to expand due to the high exponent
    -- To avoid slowdowns, we generalize the exponent to a variable
    generalize eq100 : 100 = _100 at *
    linarith

-- $ b=\frac{1}{2 \sqrt{2}}\left((1+\sqrt{2})^{100}-(1-\sqrt{2})^{100}\right) .$

  have h4 : b = (1 / (2 * √2) : ℝ) * ((1 + √2) ^ 100 - (1 - √2) ^ 100) := by
    -- (1 + √2) ^ 100 is long to expand due to the high exponent
    -- To avoid slowdowns, we generalize the exponent to a variable
    generalize eq100 : 100 = _100 at *
    calc
      _ = (1 / (2 * √2) : ℝ) * (2 * b * √2) := by
        field_simp
        ring
      _ = _ := by
        congr 1
        linarith

-- Hence $ ab =\frac{1}{4 \sqrt{2}}\left((1+\sqrt{2})^{200}-(1-\sqrt{2})^{200}\right) \ =\frac{1}{4 \sqrt{2}}\left((3+2 \sqrt{2})^{100}-(3-2 \sqrt{2})^{100}\right) . $

  have h5 : a * b = (1 / (4 * √2) : ℝ) * ((3 + 2 * √2) ^ 100 - (3 - 2 * √2) ^ 100) := by
    -- (1 + √2) ^ 100 is long to expand due to the high exponent
    -- To avoid slowdowns, we generalize the exponent to a variable
    generalize eq100 : 100 = _100 at *
    calc
      _ = 1 / (4 * √2) * ((1 + √2) ^ _100 + (1 - √2) ^ _100) * ((1 + √2) ^ _100 - (1 - √2) ^ _100) := by
        rw [h3, h4]
        ring
      _ = (1 / (4 * √2) : ℝ) * (((1 + √2) ^ _100) ^ 2 - ((1 - √2) ^ _100) ^ 2) := by ring
      _ = (1 / (4 * √2) : ℝ) * (((1 + √2) ^ 2) ^ _100 - ((1 - √2) ^ 2) ^ _100) := by
        congr 2
        all_goals
          rw [←pow_mul, ←pow_mul]
          congr 1
          subst_vars; norm_num
      _ = _ := by
        congr 3
        . ring_nf
          simp
          ring
        . ring_nf
          simp
          ring

-- Let $ x_{n}=\frac{1}{4 \sqrt{2}}\left((3+2 \sqrt{2})^{n}\right. \ \left.-(3-2 \sqrt{2})^{n}\right) $ for $ n ≥ 1 $

  let x (n : ℕ) := (1 / (4 * √2) : ℝ) * ((3 + 2 * √2) ^ n - (3 - 2 * √2) ^ n)

-- then $x_{1}=1, x_{2}=6, x_{3}=35$.
  have h6 : x 1 = 1 := by
    suffices (3 + 2 * √2) ^ 1 - (3 - 2 * √2) ^ 1 = 4 * √2 by
      field_simp [x]
      simpa using this
    ring

  have h7 : x 2 = 6 := by
    suffices (3 + 2 * √2) ^ 2 - (3 - 2 * √2) ^ 2 = 6 * (4 * √2) by
      field_simp [x]
      simpa using this
    ring

  have h8 : x 3 = 35 := by
    suffices (3 + 2 * √2) ^ 3 - (3 - 2 * √2) ^ 3 = 35 * (4 * √2) by
      field_simp [x]
      simpa using this
    suffices √2 * 108 + √2 ^ 3 * 16 = √2 * 140 by convert this using 1 <;> ring
    suffices √2 * 108 + 2 * √2 * 16 = √2 * 140 by
      have c1 : √2 ^ 3 = 2 * √2 := calc
        _ = (√2 ^ 2) * (√2 ^ 1) := by ring
        _ = 2 * √2 := by simp
      simpa [c1] using this
    ring

-- By the identity $a^{n}-b^{n}=(a+b)\left(a^{n-1}-b^{n-1}\right)-a b$ $\left(a^{n-2}-b^{n-2}\right)$,
-- we can obtain the recurrence relation $ x_{n}=6 x_{n-1}-x_{n-2} \cdot(n=3,4,5, \cdots) $
  have h9 (n : ℕ) (hn : n ≥ 3) : x n = 6 * x (n - 1) - x (n - 2) := by
    revert n
    apply Nat.le_induction
    . show x 3 = 6 * x 2 - x 1
      norm_num [h6, h7, h8]
    . intro n hn ih
      show x (n + 1) = 6 * x n - x (n - 1)
      sorry

-- Thus, all $x_n$'s are natural integers
  have h10 (n : ℕ) (hn : n ≥ 1) : ∃ x' : ℤ, x n = x' := by
    revert n
    apply Nat.strongRec
    . intro n ih hn
      obtain c1 | c1 | c1 : n = 1 ∨ n = 2 ∨ n ≥ 3 := by omega
      . subst c1
        use 1
        norm_num [h6]
      . subst c1
        use 6
        norm_num [h7]
      . obtain ⟨x1, ih1⟩ := ih (n - 1) (by omega) (by omega)
        obtain ⟨x2, ih2⟩ := ih (n - 2) (by omega) (by omega)
        use 6 * x1 - x2
        specialize h9 n c1
        simpa [ih1, ih2] using h9
  choose! x' h10 using h10

  have hx' (n : ℕ) (hn : n ≥ 1) : x' n = 1 / (4 * √2) * ((3 + 2 * √2) ^ n - (3 - 2 * √2) ^ n) := by
    specialize h10 n hn
    rw [←h10]

  replace h9 (n : ℕ) (hn : n ≥ 3) : x' n = 6 * x' (n - 1) - x' (n - 2) := by
    sorry

-- And the last digit of $x_{n}$ is
-- as follows: $ \begin{array}{l} x_{1}=1, x_{2} \equiv 6, x_{3} \equiv 5, x_{4} \equiv 4, x_{5} \equiv 9, x_{6}=0, \ x_{7}=1, x_{8} \equiv 6, x_{9}=5, x_{10} \equiv 4 (\bmod 10) . \end{array} $
-- From this, we can see that $x_{n+2}=x_{n+8}(\bmod 10)(n=1,2,3$, $\cdots$.
  have h10 (n : ℕ) (hn : n ≥ 1) : x' (n + 2) % 10 = x' (n + 8) % 10 := by
    sorry
  have h11 (n k : ℕ) (hn : n ≥ 1) : x' (6 * n + k) % 10 = x' k % 10 := by
    sorry

-- Therefore, $x_{100}=x_{6 \times 16+4} \equiv x_{4}=4(\bmod 10)$, so the last digit of $a b=x_{100}$ is 4.
  calc
    _ = x' 100 % 10 := by
      congr 1
      rify
      specialize hx' 100 (by norm_num)
      rw [h5, hx']
    _ = x' (6 * 16 + 4) % 10 := by congr 1
    _ = x' 4 % 10 := by exact h11 16 4 (by norm_num)
    _ = 4 := by
      sorry
