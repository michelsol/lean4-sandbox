import Mathlib

/-
Let $\mathbb{Q}_{>0}$ denote the set of all positive rational numbers.
Determine all functions $f: \mathbb{Q}_{>0} \rightarrow \mathbb{Q}_{>0}$
satisfying  $$ f\left(x^{2} f(y)^{2}\right)=f(x)^{2} f(y) $$
for all $x, y \in \mathbb{Q}_{>0}$.
-/

theorem algebra_23636
    (f : ℚ → ℚ)
    (hf : ∀ x > 0, f x > 0)
    : (∀ x > 0, ∀ y > 0, f (x ^ 2 * f y ^ 2) = f x ^ 2 * f y) ↔  ∀ x > 0, f x = 1 := by
  constructor
  . intro h1
-- Take any $a, b \in \mathbb{Q}_{>0}$.

-- By substituting $x=f(a), y=b$ and $x=f(b), y=a$ into $(*)$
-- we get  $$ f(f(a))^{2} f(b)=f\left(f(a)^{2} f(b)^{2}\right)=f(f(b))^{2} f(a) $$
-- which yields  $$ \frac{f(f(a))^{2}}{f(a)}=\frac{f(f(b))^{2}}{f(b)} \quad
-- \text { for all } a, b \in \mathbb{Q}_{>0} $$
    have h2 a (ha : a > 0) b (hb : b > 0) : f (f a) ^ 2 / f a = f (f b) ^ 2 / f b := by
      have c1 : f (f a) ^ 2 * f b = f (f b) ^ 2 * f a := calc
        _ = f (f a ^ 2 * f b ^ 2) := by
          symm
          exact h1 (f a) (hf a ha) b hb
        _ = _ := by
          have c2 := h1 (f b) (hf b hb) a ha
          ring_nf at c2 ⊢
          simpa using c2
      have := hf a ha
      have := hf b hb
      field_simp
      simpa using c1

-- In other words, this shows that there exists a constant $C \in \mathbb{Q}_{>0}$
-- such that $f(f(a))^{2}=C f(a)$,
-- or  $$ \left(\frac{f(f(a))}{C}\right)^{2}=\frac{f(a)}{C} \quad
-- \text { for all } a \in \mathbb{Q}_{>0} \text {. } $$   (1)
    obtain ⟨C, hC, h3⟩ : ∃ C > 0, ∀ a > 0, (f (f a) / C) ^ 2 = f a / C := by
      obtain ⟨C, hC, c1⟩ : ∃ C > 0, ∀ a > 0, f (f a) ^ 2 = C * f a := by
        replace h2 a ha := h2 a ha 1 (by norm_num)
        use f (f 1) ^ 2 / f 1
        constructor
        . have c1 := hf 1 (by norm_num)
          have c2 := hf (f 1) c1
          field_simp [c1]
        . intro a ha
          specialize h2 a ha
          specialize hf a ha
          field_simp at h2
          ring_nf at h2 ⊢
          simpa using h2
      use C, hC
      intro a ha
      specialize c1 a ha
      field_simp
      apply_fun (. * C) at c1
      linarith

-- Denote by $f^{n}(x)=\underbrace{f(f(\ldots(f}_{n}(x)) \ldots))$
-- the $n^{\text {th }}$ iteration of $f$.
-- First notice that f^{n}(a) > 0
    have h3' a (ha : a > 0) (n : ℕ) : f^[n] a > 0 := by
      induction' n with n ih
      . simpa using ha
      . rw [Function.iterate_succ_apply']
        apply hf
        simpa using ih

-- Equality (1) yields  $$ \frac{f(a)}{C}=\left(\frac{f^{2}(a)}{C}\right)^{2}
-- =\left(\frac{f^{3}(a)}{C}\right)^{4}=\cdots=\left(\frac{f^{n+1}(a)}{C}\right)^{2^{n}} $$
-- for all positive integer $n$.
    have h4 a (ha : a > 0) (n : ℕ) : f a / C = (f^[n + 1] a / C) ^ (2 ^ n) := by
      induction' n with n ih
      . simp
      . rw [Function.iterate_succ_apply']
        rw [pow_succ', pow_mul]
        specialize h3 (f^[n] a) (h3' a ha n)
        rw [Function.iterate_succ_apply']
        rw [h3]
        rw [Function.iterate_succ_apply'] at ih
        exact ih


-- So, $f(a) / C$ is the $2^{n}$-th power of a rational number for all positive integer $n$.
-- This is impossible unless $f(a) / C=1$,
-- since otherwise the exponent of some prime in the prime decomposition of $f(a) / C$
-- is not divisible by sufficiently large powers of 2 .
    have h5 a (ha : a > 0) : f a / C = 1 := by
      have c0 : f a / C > 0 := by
        field_simp
        simpa using hf a ha
      have c1 (n : ℕ) : ∃ r > 0, f a / C = r ^ (2 ^ n) := by
        use (f^[n + 1] a / C)
        constructor
        . field_simp
          simpa using h3' a ha (n + 1)
        . tauto
      choose r c0' c1 using c1
      generalize f a / C = x at c0 c1
      suffices x.num = x.den from by
        rw [←x.num_div_den]
        field_simp
        norm_cast
      replace c1 (n : ℕ) : (x.num / x.den : ℚ) = ((r n).num / (r n).den) ^ (2 ^ n) := by
        iterate 2 rw [Rat.num_div_den]
        simpa using c1 n
      replace c1 (n : ℕ) : x.num * (r n).den ^ 2 ^ n  = x.den * (r n).num ^ (2 ^ n) := by
        specialize c1 n
        field_simp at c1
        qify
        linarith
      replace c1 (n : ℕ) : x.num.natAbs * (r n).den ^ 2 ^ n  = x.den * (r n).num.natAbs ^ (2 ^ n) := by
        have d1 : 0 ≤ x.num := Rat.num_nonneg.mpr (by linarith)
        replace d1 := (Int.natAbs_of_nonneg d1).symm
        specialize c0' n
        have d2 : 0 ≤ (r n).num := Rat.num_nonneg.mpr (by linarith)
        replace d2 := (Int.natAbs_of_nonneg d2).symm
        specialize c1 n
        rw [d1, d2] at c1
        zify at c1 ⊢
        simpa
      let p := x.num.natAbs
      let q := x.den
      let y n := (r n).num.natAbs
      let z n := (r n).den
      suffices p = q from by
        dsimp [p, q] at this
        zify at this
        rw [←this]
        exact (abs_of_pos (Rat.num_pos.mpr c0)).symm
      replace c1 (n : ℕ) : p * z n ^ 2 ^ n  = q * (y n) ^ (2 ^ n) := by simpa using c1 n
      have c2 : p.Coprime q := x.reduced
      have c3 n : (y n).Coprime (z n) := (r n).reduced
      -- Using Gauss' theorem, for every n, p must be divisible by the 2-nth power of some integer $y_n$
      have c4 n : y n ^ 2 ^ n ∣ p := by
        sorry
      -- For n large enough, the prime exponents all exceed those of p, so the $y_n$ must end up being equal to 1.
      obtain ⟨N1, c5⟩ : ∃ N, ∀ n ≥ N, y n = 1 := by
        sorry
      -- The same can be said about q
      have c6 n : z n ^ 2 ^ n ∣ q := by
        sorry
      obtain ⟨N2, c7⟩ : ∃ N, ∀ n ≥ N, z n = 1 := by
        sorry
      specialize c1 (N1 ⊔ N2)
      specialize c5 (N1 ⊔ N2) (by omega)
      specialize c7 (N1 ⊔ N2) (by omega)
      simpa [c5, c7] using c1

-- Therefore, $f(a)=C$ for all $a \in \mathbb{Q}_{>0}$.
    replace h5 a (ha : a > 0) : f a = C := by
      specialize h5 a ha
      field_simp at h5
      simpa using h5

-- Finally, after substituting $f \equiv C$ into (*) we get $C=C^{3}$, whence $C=1$.
    have h6 : C = 1 := by
      specialize h1 1 (by norm_num) 1 (by norm_num)
      have c1 := h5 (C ^ 2) (by nlinarith)
      have c2 := h5 1 (by norm_num)
      simp [c1, c2] at h1
      nlinarith

-- So $f(x) \equiv 1$ is the unique function satisfying $(*)$.
    simpa [h6] using h5

-- Conversely, the function f(x) = 1 satisfies the desired condition.
  . intro h1
    intro x hx y hy
    have h2 := h1 y hy
    have h3 := h1 x hx
    have h4 := h1 (x ^ 2) (by nlinarith)
    simp [h2, h3, h4]
