import Mathlib

open Set

/-
Find all functions $f: \mathbb{R}^{+} \rightarrow \mathbb{R}^{+}$such that
$$ f(x+f(y))=f(x+y)+f(y) $$  for all $x, y \in \mathbb{R}^{+}$.
(Symbol $\mathbb{R}^{+}$denotes the set of all positive real numbers.)
-/

theorem algebra_23631
    (f : ℝ → ℝ)
    (hf1 : ∀ x > 0, f x > 0)
    : (∀ x > 0, ∀ y > 0, f (x + f y) = f (x + y) + f y)  -- (1)
      ↔ (∀ x > 0, f x = 2 * x) := by
  constructor
  . intro h1

-- First we show that $f(y)>y$ for all $y \in \mathbb{R}^{+}$.
    have h2 : ∀ y > 0, f y > y := by
      intro y hy
-- Functional equation (1) yields $f(x+f(y))>f(x+y)$
      have a1 : ∀ x > 0, f (x + f y) > f (x + y) := by
        intro x hx
        specialize h1 x hx y hy
        specialize hf1 y hy
        linarith
-- and hence $f(y) \neq y$ immediately.
      have a2 : f y ≠ y := by
        intro b1
        specialize a1 1 (by norm_num)
        rw [b1] at a1
        linarith
-- If $f(y) < y$
      have a3 : ¬ f y < y := by
-- then setting $x=y-f(y)$ we get
-- $$ f(y)=f((y-f(y))+f(y))=f((y-f(y))+y)+f(y)>f(y) $$  contradiction.
        intro b1
        have b2 : f y > f y := calc
          _ = _ := by ring_nf
          _ = _ := h1 (y - f y) (by linarith) y hy
          _ > 0 + f y := by
            gcongr
            exact hf1 (y - f y + y) (by linarith)
          _ = f y := by ring_nf
        linarith

-- Therefore $f(y)>y$ for all $y \in \mathbb{R}^{+}$.
      have a4 : f y < y ∨ f y = y ∨ f y > y := lt_trichotomy (f y) y
      simpa [a3, a2] using a4

-- For $x \in \mathbb{R}^{+}$define $g(x)=f(x)-x$; then $f(x)=g(x)+x$
    let g x := f x - x
    have h3 : ∀ x > 0, f x = g x + x := by intro x hx; ring_nf
-- and, as we have seen, $g(x)>0$.
    have h4 : ∀ x > 0, g x > 0 := by
      intro x hx
      specialize h2 x hx
      dsimp [g]
      linarith

-- Transforming (1) for function $g(x)$ and setting $t=x+y$,
-- $$ \begin{aligned} f(t+g(y)) & =f(t)+f(y) \\
-- g(t+g(y))+t+g(y) & =(g(t)+t)+(g(y)+y) \end{aligned} $$
-- and therefore  $$ g(t+g(y))=g(t)+y \quad \text { for all } t>y>0 $$   (2)
    have h5 : ∀ y > 0, ∀ t > y, g (t + g y) = g t + y := by
      intro y hy t ht
      let x := t - y
      have a1 : f (t + g y) = f t + f y := by
        specialize h1 (t - y) (by linarith) y hy
        dsimp [g]
        ring_nf at h1 ⊢
        simpa
      have a2 : g (t + g y) + t + g y = (g t + t) + (g y + y) := by
        dsimp [g] at a1 ⊢
        ring_nf at a1 ⊢
        simpa
      linarith

-- Next we prove that function $g(x)$ is injective.
    have h6 : InjOn g (Ioi 0) := by
-- Suppose that $g\left(y_{1}\right)=g\left(y_{2}\right)$ for some numbers
-- $y_{1}, y_{2} \in \mathbb{R}^{+}$.
      intro y1 hy1 y2 hy2 a1
-- Then by $(2)$,
-- $$ g(t)+y_{1}=g\left(t+g\left(y_{1}\right)\right)=g\left(t+g\left(y_{2}\right)\right)=g(t)+y_{2} $$
-- for all $t>\max \left\{y_{1}, y_{2}\right\}$.
      have a2 t (ht : t > max y1 y2) : g t + y1 = g t + y2 := calc
        _ = g (t + g y1) := by rw [h5 y1 hy1 t (by sorry)]
        _ = g (t + g y2) := by rw [a1]
        _ = _ := by rw [h5 y2 hy2 t (by sorry)]
-- Hence, $g\left(y_{1}\right)=g\left(y_{2}\right)$ is possible only if $y_{1}=y_{2}$.
      specialize a2 (max y1 y2 + 1) (by linarith)
      linarith

-- We will now show that $ g(u) + g(v) = g(u + v) $
    have h7 : ∀ u > 0, ∀ v > 0, g u + g v = g (u + v) := by
-- Now let $u, v$ be arbitrary positive numbers and $t>u+v$.
      intro u hu v hv
      have a1 : ∀ t > u + v, t + g u + g v = t + g (u + v) := by
        intro t ht
-- Applying (2) three times,  $$ g(t+g(u)+g(v))=g(t+g(u))+v=g(t)+u+v=g(t+g(u+v)) \text {. } $$
        have b1 : g (t + g u + g v) = g (t + g (u + v)) := calc
          _ = g (t + g u) + v := h5 v hv (t + g u) (by dsimp [g]; specialize h2 u hu; linarith)
          _ = g t + u + v := by rw [h5 u hu t (by linarith)]
          _ = _ := by rw [h5 (u + v) (by linarith) t ht]; ring_nf
-- By the injective property we conclude that $t+g(u)+g(v)=t+g(u+v)$
        have b2 : t + g u + g v > 0 := by
          sorry
        have b3 : t + g (u + v) > 0 := by
          sorry
        exact h6 b2 b3 b1
-- hence  $$ g(u)+g(v)=g(u+v) . $$   (3)
      specialize a1 (u + v + 1) (by linarith)
      linarith

-- Since function $g(v)$ is positive, equation (3) also shows that $g$ is an increasing function.
    have h8 : StrictMonoOn g (Ioi 0) := by
      intro x hx y hy hxy
      let z := y - x
      rw [show y = z + x from by simp [z]]
      rw [←h7 z (by simp [z]; linarith) x hx]
      specialize h4 z (by simp [z]; linarith)
      linarith

-- Finally we prove that $g(x)=x$.
    have h9 : ∀ x > 0, g x = x := by
-- Combining (2) and (3), we obtain
-- $$ g(t)+y=g(t+g(y))=g(t)+g(g(y)) $$
      have a1 y (hy : y > 0) t (ht : t > y)  : g t + y = g t + g (g y) := calc
        _ = g (t + g y) := (h5 y hy t ht).symm
        _ = _ := (h7 t (by linarith) (g y) (h4 y hy)).symm
-- and hence  $$ g(g(y))=y $$
      have a2 y (hy : y > 0) : g (g y) = y := by
        specialize a1 y (by linarith) (y + 1) (by linarith)
        linarith

-- Suppose that there exists an $x \in \mathbb{R}^{+}$such that $g(x) \neq x$.
      by_contra h9
      push_neg at h9
      obtain ⟨x, hx, h9⟩ := h9

-- By the monotonicity of $g$, if $x>g(x)$ then $g(x)>g(g(x))=x$.
      have a3 (hx2 : x > g x) : g x > x := calc
        _ > g (g x) := h8 (by have := h4 x hx; simp; linarith) (by simp; linarith) hx2
        _ = _ := a2 x hx

-- Similarly, if $x < g(x)$ then $g(x) < g(g(x))=x$.
      have a4 (hx2 : x < g x) : g x < x := calc
        _ < g (g x) := h8 (by have := h4 x hx; simp; linarith) (by simp; linarith) hx2
        _ = _ := a2 x hx

-- Both cases lead to contradiction, so there exists no such $x$.
      have a5 : g x < x ∨ g x = x ∨ g x > x := by apply lt_trichotomy
      rcases a5 with a5 | a5 | a5
      . specialize a3 a5; linarith
      . contradiction
      . specialize a4 a5; linarith

-- We have proved that $g(x)=x$ and therefore $f(x)=g(x)+x=2 x$ for all $x \in \mathbb{R}^{+}$.
    intro x hx
    specialize h9 x hx
    dsimp only [g] at h9
    linarith

-- This function indeed satisfies the functional equation (1).
  . intro h1
    intro x hx y hy
    have := hf1 y hy
    rw [h1 (x + f y) (by linarith)]
    rw [h1 (x + y) (by linarith)]
    rw [h1 y (by linarith)]
    ring_nf
