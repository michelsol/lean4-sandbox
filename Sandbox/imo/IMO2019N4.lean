import Mathlib

/- Let $\mathbb{Z}_{>0}$ be the set of positive integers. A positive integer constant $C$ is given.
Find all functions $f: \mathbb{Z}_{>0} \rightarrow \mathbb{Z}_{>0}$ such that,
for all positive integers $a$ and $b$ satisfying $a+b>C$,
$ a+f(b) \mid a^{2}+b f(a) $   (*)
-/
theorem number_theory_23911
    (C : ℕ) (hC : C > 0)
    (f : ℕ → ℕ)
    (hf1 : ∀ n > 0, f n > 0)
    : (∀ (a : ℕ) (_ : 0 < a) (b : ℕ) (_ : 0 < b) (_ : a + b > C),
        (a + f b : ℤ) ∣ a ^ 2 + b * f a)
      ↔ ∃ k > 0, ∀ a > 0, f a = k * a := by
  constructor
  swap
  . intro ⟨k, hk, h1⟩
    intro a ha b hb hab
    rw [h1 a ha, h1 b hb]
    use a
    push_cast
    ring

  . dsimp
    intro h1
-- First, we show that $b \mid f(b)^{2}$ for all $b$.
    have h2 (b : ℕ) (hb : b > 0) : (b : ℤ) ∣ f b ^ 2 := by
-- To do this, we choose a large positive integer $n$ so that $n b-f(b) \geqslant C$.
      obtain ⟨n, hn, c1⟩ : ∃ (n : ℕ) (_ : n > 0), (n * b - f b : ℤ) ≥ C := by
        use ⌈((C + f b) / b : ℝ)⌉₊
        use by positivity
        rify
        show _ ≤ _
        calc
          C ≤ ((C + (f b)) / b : ℝ) * b - f b := by field_simp
          _ ≤ _ := by
            gcongr
            apply Nat.le_ceil
-- Setting $a=n b-f(b)$ in (*) then shows that $ n b \mid(n b-f(b))^{2}+b f(n b-f(b)) $
      have c2 : (n * b : ℤ) ∣ ((n * b - f b) ^ 2 + b * f (n * b - f b)) := by
        convert h1 (n * b - f b) (by omega) b hb (by omega) using 1
        . omega
        . congr 2
          omega
-- so that $b \mid f(b)^{2}$ as claimed.
      replace c2 := calc
        (b : ℤ) ∣ _ := by apply Int.dvd_mul_left
        _ ∣ _ := c2
      suffices (f b : ZMod b) ^ 2 = 0 from by simpa [←ZMod.intCast_zmod_eq_zero_iff_dvd]
      calc
        _ = ((n * b - f b) ^ 2 + b * f (n * b - f b) : ZMod b) := by simp
        _ = _ := by simpa [←ZMod.intCast_zmod_eq_zero_iff_dvd] using c2

-- Now in particular we have that $p \mid f(p)$ for every prime $p$.
    have h3 (p : ℕ) (hp : p.Prime) : (p : ℤ) ∣ f p := by
      specialize h2 p (by exact Nat.Prime.pos hp)
      exact Int.Prime.dvd_pow' hp h2

-- If we write $f(p)=k(p) \cdot p$
    have h4 (p : ℕ) (hp : p.Prime) : ∃ (k : ℕ) (_ : k > 0), f p = k * p := by
      obtain ⟨k, c1⟩ := h3 p hp
      convert_to f p = k * p using 1 at c1
      . ring
      use k.natAbs
      use by
        specialize hf1 p (by exact Nat.Prime.pos hp)
        suffices k ≠ 0 from by simpa using this
        by_contra hk
        subst hk
        omega
      zify
      convert c1 using 2
      refine abs_of_nonneg ?_
      specialize hf1 p hp.pos
      nlinarith

    choose! k h5 h4 using h4

-- then the bound $f(p) \leqslant f(1) \cdot p$   (valid for $p$ sufficiently large)
    have ⟨n0, h6⟩ : ∃ n0 : ℕ, ∀ (p : ℕ) (_ : p.Prime) (_ : p ≥ n0), f p ≤ f 1 * p := by
      sorry

-- shows that some value $k_0$ of $k(p)$ must be attained for infinitely many $p$.
    have ⟨k0, h7⟩ : ∃ k0 : ℕ, { p : ℕ | p.Prime ∧ k p = k0 }.Infinite := by
      by_contra! h7
      have c1 (l : ℕ) (hl : l ≤ f 1) := (Set.not_infinite.mp (h7 l)).exists_le
      choose! M c2 using c1
      sorry

-- We will show that $f(a)=k_0 a$ for all positive integers $a$.
    use k0
    use by
      by_contra! hk0
      replace hk0 : k0 = 0 := by omega
      subst hk0
      let p0 := h7.nonempty.choose
      have c1 : p0.Prime := h7.nonempty.choose_spec.left
      have c2 : k p0 = 0 := h7.nonempty.choose_spec.right
      specialize h5 p0 c1
      omega
    intro a ha

-- To do this, we substitute $b=p$ in (*),
-- where $p$ is any sufficiently large prime for which $k(p)=k_0$, obtaining
-- $ a+k_0 p \mid\left(a^{2}+p f(a)\right)-a(a+k_0 p)=p f(a)-p k_0 a . $
    have h8 (p : ℕ) (hp : p.Prime) (hp1 : p > C) (hk : k p = k0) :
        (a + k0 * p : ℤ) ∣ p * f a - p * k0 * a := by
      specialize h1 a ha p hp.pos (by omega)
      rw [h4 p hp] at h1
      rw [hk] at h1
      sorry

-- For suitably large $p$ we have $\operatorname{gcd}(a+k_0 p, p)=1$,
-- and hence we have $ a+k_0 p \mid f(a)-k_0 a $
    have h9 (p : ℕ) (hp : p.Prime) (hp1 : p > C) (hp2 : p > a) (hk : k p = k0) :
        (a + k0 * p : ℤ) ∣ f a - k0 * a := by
      specialize h8 p hp hp1 hk
      convert_to (a + k0 * p : ℤ) ∣ p * (f a - k0 * a) using 1 at h8
      . ring
      have c1 : (a + k0 * p : ℤ).gcd p = 1 := by
        refine Int.gcd_eq_one_iff_coprime.mpr ?_
        refine IsCoprime.add_mul_right_left_iff.mpr ?_
        refine Nat.isCoprime_iff_coprime.mpr ?_
        refine Nat.Coprime.symm ?_
        exact Nat.coprime_of_lt_prime ha hp2 hp
      exact Int.dvd_of_dvd_mul_right_of_gcd_one h8 c1

-- But the only way this can hold for arbitrarily large $p$ is if $f(a)-k_0 a=0$.
    have h10 : (f a - k0 * a : ℤ) = 0 := by
      sorry

    linarith
