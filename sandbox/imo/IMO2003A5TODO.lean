import Mathlib

open Set Topology Filter Real

/-
Let $\mathbb{R}^{+}$ be the set of all positive real numbers.
Find all functions $f: \mathbb{R}^{+} \rightarrow \mathbb{R}^{+}$that satisfy
the following conditions:
(i) $f(x y z)+f(x)+f(y)+f(z)=f(\sqrt{x y}) f(\sqrt{y z}) f(\sqrt{z x})$
for all $x, y, z \in$ $\mathbb{R}^{+}$.
(ii) $f(x) < f(y)$ for all $1 \leq x < y$.
-/

theorem algebra_25157
    (f : ℝ → ℝ)
    (hf : ∀ x > 0, f x > 0)
    :
    -- condition (i)
    ((∀ x > 0, ∀ y > 0, ∀ z > 0,
      f (x * y * z) + f x + f y + f z = f √(x * y) * f √(y * z) * f √(z * x))
    -- condition (ii)
    ∧ (∀ x ≥ 1, ∀ y > x, f x < f y))
    ↔ ∃ (k : ℝ) (_ : k > 0), ∀ x > 0, f x = x ^ k + x ^ (-k)
    := by
  constructor

-- We will first show that a function satisfying (i) and (ii) must be of the form
-- $f(x)=x^{k}+x^{-k}$ with k > 0
  . intro ⟨h1, h2⟩

-- Placing $x=y=z=1$ in (i) leads to $4 f(1)=f(1)^{3}$,
    have h3 : 4 * f 1 = f 1 ^ 3 := by
      specialize h1 1 (by norm_num) 1 (by norm_num) 1 (by norm_num)
      norm_num at h1 ⊢
      ring_nf at h1 ⊢
      simpa

-- so by the condition $f(1)>0$ we get $f(1)=2$.
    have h4 : f 1 = 2 := by
      specialize hf 1 (by norm_num)
      have c1 : f 1 ^ 2 = 2 ^ 2 := calc
        _ = f 1 ^ 3 / f 1 ^ 1 := by field_simp; ring_nf
        _ = 4 := by field_simp [←h3]
        _ = _ := by norm_num
      apply_fun (√.) at c1
      iterate 2 rw [sqrt_sq (by linarith)] at c1
      exact c1

-- Also putting $x=t s, y=\frac{t}{s}, z=\frac{s}{t}$ in (i)
-- gives  $$ f(t) f(s)=f(t s)+f(t / s) $$       (1)
    have h5 t (ht : t > 0) s (hs : s > 0) : f t * f s = f (t * s) + f (t / s) := by
      specialize h1 (t * s) (by positivity) (t / s) (by positivity) (s / t) (by positivity)
      sorry

-- In particular, for $t=1$ and $s=t$ the last equality yields $f(t)=f(1 / t)$;
    have h6 t (ht : t > 0) : f t = f (1 / t) := by
      specialize h5 1 (by norm_num) t ht
      rw [h4] at h5
      ring_nf at h5 ⊢
      linarith

-- hence using (ii), $f(t) \geq f(1)=2$ for each $t$.
    have h7 t (ht : t > 0) : f t ≥ 2 := by
      rcases (by apply lt_trichotomy : t < 1 ∨ t = 1 ∨ t > 1) with ht2 | ht2 | ht2
      . rw [h6 t ht]
        set t := 1 / t
        replace ht2 : t > 1 := by
          suffices 1 / 1 < t from by simpa [t]
          rw [div_lt_div_iff₀ (by norm_num) ht]
          linarith
        have := h2 1 (by norm_num) t ht2
        linarith
      . subst ht2
        linarith
      . have := h2 1 (by norm_num) t ht2
        linarith

-- It follows that there exists $g(t) \geq 1$ such that $\bar{f}(t)=g(t)+\frac{1}{g(t)}$.
    let g t := (f t) / 2 + √((f t / 2) ^ 2 - 1)
    have h8 t (ht : t > 0) : f t = g t + 1 / g t := by
      sorry
    have h9 t (ht : t > 0) : g t ≥ 1 := by
      sorry

--  Show that g(xy) = g(x) g(y)
    have h10 x (hx : x > 0) y (hy : y > 0) : g (x * y) = g x * g y := by
      sorry

-- Now it follows by induction from (1) that $g\left(t^{n}\right)=$ $g(t)^{n}$ for every integer $n$,
    -- have h10 t (ht : t > 0) (n : ℕ) : g (t ^ n) = g t ^ n := by
    --   induction' n with n ih
    --   . sorry
    --   . sorry

    sorry
-- and therefore $g\left(t^{q}\right)=g(t)^{q}$ for every rational $q$.
-- Consequently, if $t>1$ is fixed, we have $f\left(t^{q}\right)=a^{q}+a^{-q}$, where $a=g(t)$.
-- But since the set of $a^{q}(q \in \mathbb{Q})$ is dense in $\mathbb{R}^{+}$
-- and $f$ is monotone on $(0,1]$ and $[1, \infty)$,
-- it follows that $f\left(t^{r}\right)=a^{r}+a^{-r}$ for every real $r$.
-- Therefore, if $k$ is such that $t^{k}=a$, we have
-- $$ f(x)=x^{k}+x^{-k} \quad \text { for every } x \in \mathbb{R} $$

  . sorry #exit
-- Conversely, any function of the form $f(x)=x^{k}+x^{-k}$ with k > 0 satisfies (i) and (ii).
  . intro ⟨k, hk0, hk1⟩
    split_ands
-- Show that f satisfies (i)
    . intro x hx y hy z hz
      conv_rhs =>
        repeat rw [hk1 _ (by positivity)]
        repeat rw [add_mul]
        repeat rw [mul_add]
        repeat rw [sqrt_mul (by positivity)]
        repeat rw [mul_rpow (by positivity) (by positivity)]
        ring_nf
        repeat rw [←rpow_mul_natCast (by positivity), mul_comm (_ : ℝ) (2 : ℕ),
            rpow_natCast_mul (by positivity), sq_sqrt (by positivity)]
        repeat rw [rpow_neg (by positivity)]
      set sxk := √x ^ k
      set syk := √y ^ k
      set szk := √z ^ k
      set xk := x ^ k
      set yk := y ^ k
      set zk := z ^ k
      rw [show sxk * syk * zk * syk⁻¹ * sxk⁻¹ = zk from by field_simp; ring_nf]
      rw [show sxk * syk * syk⁻¹ * zk⁻¹ * sxk⁻¹ = zk⁻¹ from by field_simp; ring_nf]
      rw [show sxk * yk * szk * szk⁻¹ * sxk⁻¹ = yk from by field_simp]
      rw [show sxk * szk * yk⁻¹ * szk⁻¹ * sxk⁻¹  = yk⁻¹ from by field_simp; ring_nf]
      rw [show xk * syk * szk * syk⁻¹ * szk⁻¹ = xk from by field_simp; ring_nf]
      rw [show syk * szk * syk⁻¹ * szk⁻¹ * xk⁻¹ = xk⁻¹ from by field_simp]
      suffices f (x * y * z) + f x + f y + f z =
          (xk * yk * zk + xk⁻¹ * yk⁻¹ * zk⁻¹) + (xk + xk⁻¹) + (yk + yk⁻¹) + (zk + zk⁻¹) from by
        ring_nf at this ⊢
        simpa
      conv_lhs =>
        repeat rw [hk1 _ (by positivity)]
        repeat rw [mul_rpow (by positivity) (by positivity)]
        repeat rw [rpow_neg (by positivity)]
-- Show that f satisfies (ii)
-- Which means f is strictly monotone on [1, ∞)
    . let g (x : ℝ) := x ^ k + x ^ (-k)
      suffices StrictMonoOn g (Ici 1) from by
        intro x hx y hy
        rw [hk1 x (by linarith), hk1 y (by linarith)]
        exact this hx (by simp; linarith) hy
-- Which we show by showing that its derivative is positive on [1, ∞)
      apply strictMonoOn_of_deriv_pos
      . apply convex_Ici
      . apply ContinuousOn.add
        all_goals
        . apply ContinuousOn.rpow_const
          . apply continuousOn_id'
          . intro x hx
            simp at hx
            left
            linarith
      . intro x hx
        simp at hx
        rw [deriv_add]
        . iterate 2 rw [deriv_rpow_const (by left; linarith)]
          suffices k * x ^ (-k - 1) < k * x ^ (k - 1) from by linarith
          suffices x ^ (-k - 1) < x ^ (k - 1) from by exact (mul_lt_mul_left hk0).mpr this
          have c1 : x ^ (-k - 1) > 0 := by
            refine rpow_pos_of_pos ?_ (-k - 1)
            linarith
          suffices x ^ (-k - 1) / x ^ (-k - 1) < x ^ (k - 1) / x ^ (-k - 1) from
            (div_lt_div_iff_of_pos_right c1).mp this
          suffices 1 < x ^ (k - 1) / x ^ (-k - 1) from by field_simp; simpa
          suffices 1 < x ^ (2 * k) from by
            rw [←rpow_sub (by linarith)]
            ring_nf at this ⊢
            simpa
          apply one_lt_rpow hx
          linarith
        . apply differentiableAt_rpow_const_of_ne; linarith
        . apply differentiableAt_rpow_const_of_ne; linarith
