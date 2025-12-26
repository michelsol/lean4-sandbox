import Mathlib

open Real

/-
Find all functions $f$ from the reals to the reals such that
$$ (f(x)+f(z))(f(y)+f(t))=f(x y-z t)+f(x t+y z) $$  for all real $x, y, z, t$.
-/

theorem algebra_25117 (f : ℝ → ℝ) :
    (∀ x y z t, (f x + f z) * (f y + f t) = f (x * y - z * t) + f (x * t + y * z))
    ↔  (∀ x, f x = 0) ∨ (∀ x, f x = 1 / 2) ∨ (∀ x, f x = x ^ 2) := by
  constructor
  . intro h1
-- Putting $x=z=0$ and $t=y$ into the given equation gives
-- $4 f(0) f(y)=$ $2 f(0)$ for all $y$.
    have h2 y : 4 * f 0 * f y = 2 * f 0 := by
      have h2 := h1 0 y 0 y
      simp at h2
      ring_nf at h2 ⊢
      simpa

-- If $f(0) \neq 0$, then we deduce $f(y)=\frac{1}{2}$, i.e.,
-- $f$ is identically equal to $\frac{1}{2}$.
    have h3 : f 0 ≠ 0 ∨ f 0 = 0 := by exact ne_or_eq (f 0) 0
    rcases h3 with h3 | h3
    . suffices ∀ x, f x = 1 / 2 from by simp [this]
      intro x
      specialize h2 x
      apply_fun (. / f 0) at h2
      ring_nf at h2
      field_simp at h2
      linarith

-- Now we suppose that $f(0)=0$.
    .
-- Setting $z=t=0$ we obtain
-- $$ f(x y)=f(x) f(y) \quad \text { for all } x, y \in \mathbb{R} $$   (1)
      have h4 x y : f (x * y) = f x * f y := by
        specialize h1 x y 0 0
        simpa [h3] using h1.symm

-- Thus if $f(y)=0$ for some $y \neq 0$, then $f$ is identically zero.
      by_cases h5 : ∃ y ≠ 0, f y = 0
      . suffices ∀ x, f x = 0 from by simp [this]
        obtain ⟨y, hy⟩ := h5
        intro x
        have := (h4 (x / y) y).symm
        field_simp [h3, hy] at this
        symm
        simpa

-- So, assume $f(y) \neq 0$ whenever $y \neq 0$.
      push_neg at h5

-- It follows from (1) that $f(x)=f(\sqrt{x})^{2} \geq 0$ for all $x \geq 0$,
      have h7 x (hx : x ≥ 0) : f x ≥ 0 := calc
        f x = f (√x * √x) := by congr 1; exact Eq.symm (Real.mul_self_sqrt hx)
        _ = f √x * f √x := by rw [h4]
        _ = f (√x) ^ 2 := by rw [pow_two]
        _ ≥ 0 := by apply sq_nonneg

-- so that the given equation for $t=x$ and $z=y$ yields
-- $f\left(x^{2}+y^{2}\right)=(f(x)+f(y))^{2} > f\left(x^{2}\right)$ for all $x, y > 0$.
      have h8 x y (hx : x > 0) (hy : y > 0) : f (x ^ 2 + y ^ 2) > f (x ^ 2) := by
        calc
        _ = (f x + f y) ^ 2 := by
          specialize h1 x y y x
          ring_nf at h1
          linarith
        _ = 2 * f x * f y + f x ^ 2 + f y ^ 2 := by ring_nf
        _ > 2 * 0 * 0 + f x ^ 2 + 0 ^ 2 := by
          have h7x := h7 x (by linarith)
          have h5x := h5 x (by linarith)
          have h7y := h7 y (by linarith)
          have h5y := h5 y (by linarith)
          have := lt_of_le_of_ne h7x (Ne.symm h5x)
          have := lt_of_le_of_ne h7y (Ne.symm h5y)
          gcongr
        _ = f x * f x := by ring_nf
        _ = _ := by rw [←h4]; ring_nf

-- We observe that $f$ is strictly increasing on the set of positive reals.
      have h6 : StrictMonoOn f (Set.Ioi 0) := by
        intro x hx y hy hxy
        simp at hx hy
        specialize h8 √x √(y-x) (by simp [hx]) (by
          have : y - x > 0 := by linarith
          simp [this])
        iterate 2 rw [sq_sqrt (by linarith)] at h8
        ring_nf at h8
        simpa

-- Using (1) it is easy to get $f(1)=1$.
      have h9 : f 1 = 1 := by
        specialize h4 1 1
        specialize h5 1 (by norm_num)
        field_simp at h4
        simpa

-- Now plugging $t=y$ into the given equation, we are led to
-- $$ 2[f(x)+f(z)]=f(x-z)+f(x+z) \quad \text { for all } x, z $$   (2)
      have h10 x z : 2 * (f x + f z) = f (x - z) + f (x + z) := by
        suffices ∀ y ≠ (0 : ℝ), _ from this 1 (by norm_num)
        intro y hy
        specialize h1 x y z y
        suffices 2 * f y * (f x + f z) = f y * (f (x - z) + f (x + z)) from by
          specialize h5 y hy
          apply_fun (. / f y) at this
          ring_nf at this
          field_simp at this
          linarith
        have g1 : (f x + f z) * (f y + f y) = 2 * f y * (f x + f z) := by ring_nf
        have g2 : f (x * y - z * y) + f (x * y + y * z) = f y * (f (x - z) + f (x + z)) := by
          rw [mul_add, ←h4, ←h4, mul_sub, mul_add]
          ring_nf
        linarith

-- In particular, $f(z)=f(-z)$.
      have h11 z : f z = f (-z) := by
        specialize h10 0 z
        simp [h3] at h10
        linarith

-- Further, it is easy to get by induction from (2) that $f(n x)=n^{2} f(x)$ for all
-- integers $n$
      have h12 : ∀ n : ℕ, ∀ x : ℝ, f (n * x) = n ^ 2 * f x := by
        apply Nat.strongRec
        . intro n ih
          rcases (by omega : n = 0 ∨ n = 1 ∨ n ≥ 2) with hn | hn | hn
          . subst hn; simp [h3]
          . subst hn; simp
          . intro x
            have g1 : 2 * f ((n - 1) * x) + 2 * f x = f ((n - 2) * x) + f (n * x) := by
              have g1 := h10 ((n - 1) * x) x
              ring_nf at g1 ⊢; simpa
            have ih1 := ih (n - 1) (by omega) x
            push_cast [(by omega : n ≥ 1)] at ih1
            have ih2 := ih (n - 2) (by omega) x
            push_cast [hn] at ih2
            linarith

      replace h12 : ∀ n : ℤ, ∀ x : ℝ, f (n * x) = n ^ 2 * f x := by
        intro n
        rcases (by omega : n ≥ 0 ∨ -n ≥ 0) with hn | hn
        . specialize h12 n.toNat
          rwa [←Int.toNat_of_nonneg hn]
        . intro x
          calc
          _ = f (- n * x) := by rw [h11]; simp
          _ = f ((-n : ℤ) * x) := by congr 2; simp
          _ = f ((-n).toNat * x) := by congr; simp [hn]
          _ = (-n).toNat ^ 2 * f x := by rw [h12]
          _ = _ := by congr 1; norm_cast; simp [hn]

-- And consequently for all rational numbers as well.
      have h13 : ∀ q : ℚ, ∀ x : ℝ, f (q * x) = q ^ 2 * f x := by
        intro r x
        rw [h4]
        suffices f r = r ^ 2 from by simp [this]
        rw [r.num_div_den.symm]
        set p := r.num
        set q := r.den
        calc
        _ = f (p / q) := by simp
        _ = f (p * (1 / q)) := by ring_nf
        _ = p ^ 2 * f (1 / q) := by rw [h12]
        _ = (p ^ 2 / q ^ 2) * q ^ 2 * f (1 / q) := by
          have : q ^ 2 ≠ 0 := by
            have : q ≠ 0 := by exact r.den_nz
            exact pow_ne_zero 2 this
          field_simp
        _ = (p ^ 2 / q ^ 2) * (q ^ 2 * f (1 / q)) := by ring_nf
        _ = (p ^ 2 / q ^ 2) * f (q * (1 / q)) := by
          have := h12 q (1 / q)
          push_cast at this
          rw [←this]
        _ = (p ^ 2 / q ^ 2) * f 1 := by field_simp
        _ = _ := by simp [h9]

-- Therefore $f(q)=q^{2}$ for all $q \in \mathbb{Q}$.
      have h14 : ∀ q : ℚ, f q = q ^ 2 := by
        intro q
        specialize h13 q 1
        simpa [h9] using h13

-- But $f$ is increasing for $x>0$, so we must have $f(x)=x^{2}$ for all $x$.
      have h15 : ∀ x : ℝ, f x = x ^ 2 := by
        sorry

      simp [h15]

-- It is easy to verify that $f(x)=0, f(x)=\frac{1}{2}$ and $f(x)=x^{2}$ are indeed solutions.
  . intro h1
    intro x y z t
    rcases h1 with h1 | h1 | h1
    . norm_num [h1]
    . norm_num [h1]
    . simp [h1]
      ring_nf
