import Mathlib

open Finset

/- Let $a, b, c$ be integers and $p$ an odd prime number.
Prove that if $f(x)=a x^{2}+b x+c$ is a perfect square
for $2 p-1$ consecutive integer values of $x$, then $p$ divides $b^{2}-4 a c$. -/
theorem number_theory_24345
    (a b c : ℤ)
    (p : ℕ)
    (hp1 : Nat.Prime p)
    (hp2 : Odd p)
    (hp3 : p ≥ 3)
    (f : ℤ → ℤ) (hf : ∀ x, f x = a * x ^ 2 + b * x + c)
-- Suppose that $f\left(x_{0}\right), f\left(x_{0}+1\right), \ldots, f\left(x_{0}+2 p-2\right)$ are squares.
    (x0 : ℤ)
    (h1 : ∀ x ∈ Icc x0 (x0 + 2 * p - 2), IsSquare (f x)) :
    (p : ℤ) ∣ b ^ 2 - 4 * a * c := by

  have hp4 : NeZero p := by sorry

-- If $p \mid a$ and $p \nmid b$, then $f(x) \equiv b x+c(\bmod p)$ for $x=x_{0}, \ldots, x_{0}+p-1$
-- form a complete system of residues modulo $p$.
  have h2 (hpa : (p : ℤ) ∣ a) (hpb : ¬(p : ℤ) ∣ b) :
      (Icc x0 (x0 + 2 * p - 2)).image (λ x ↦ (f x : ZMod p)) = univ := by
    sorry

-- However, a square is always congruent to exactly one of
-- the $\frac{p+1}{2}$ numbers $0,1^{2}, 2^{2}, \ldots,\left(\frac{p-1}{2}\right)^{2}$
  have h3 : (Icc (0 : ℤ) (p - 1)).image (λ k : ℤ ↦ (k ^ 2 : ZMod p))
        = (Icc (0 : ℤ) ((p - 1) / 2)).image (λ k : ℤ ↦ (k ^ 2 : ZMod p)) := by
    sorry

-- and thus cannot give every residue modulo $p$.
  have h4 (hpa : (p : ℤ) ∣ a) (hpb : ¬(p : ℤ) ∣ b) : False := by
    set X := (Icc x0 (x0 + 2 * p - 2)).image (λ x ↦ (f x : ZMod p))
    set Y := (Icc (0 : ℤ) (p - 1)).image (λ k : ℤ ↦ (k ^ 2 : ZMod p))
    set Z := (Icc (0 : ℤ) ((p - 1) / 2)).image (λ k : ℤ ↦ (k ^ 2 : ZMod p))
    have c1 : X ⊆ Z := calc
      X ⊆ Y := by
        dsimp [X, Y]
        intro y hy
        simp only [mem_image] at hy ⊢
        obtain ⟨x, d1, d2⟩ := hy
        obtain ⟨k, d3⟩ := h1 x d1
        use k % p
        constructor
        . sorry
        . simp [d3] at d2
          ring_nf at d2
          simpa using d2
      Y = Z := h3
    rw [h2 hpa hpb] at c1
    replace c1 := card_le_card c1
    sorry

-- Also, if $p \mid a$ and $p \mid b$, then $p \mid b^{2}-4 a c$.
  have h5 (hpa : (p : ℤ) ∣ a) (hpb : (p : ℤ) ∣ b) : (p : ℤ) ∣ b ^ 2 - 4 * a * c := by
    sorry

-- We can now assume $p \nmid a$.
  by_cases hpa : (p : ℤ) ∣ a
  . by_cases hpb : (p : ℤ) ∣ b
    . exact h5 hpa hpb
    . exfalso; exact h4 hpa hpb

-- The following identities hold for any quadric polynomial:
-- $ 4 a \cdot f(x)=(2 a x+b)^{2}-\left(b^{2}-4 a c\right) $ (1)  and $ f(x+p)-f(x)=p(2 a x+b)+p^{2} a .$ (2)
  have h6 (x : ℤ) : 4 * a * f x = (2 * a * x + b) ^ 2 - (b ^ 2 - 4 * a * c) := by
    rw [hf]
    ring
  have h7 (x : ℤ) : f (x + p) - f x = p * (2 * a * x + b) + p ^ 2 * a := by
    iterate 2 rw [hf]
    ring_nf

-- Suppose that there is an $y, x_{0} \leq y \leq x_{0}+p-2$, for which $f(y)$ is divisible by $p$.
-- Then both $f(y)$ and $f(y+p)$ are squares divisible by $p$, and therefore both are divisible by $p^{2}$.
-- But relation (2) implies that $p \mid 2 a y+b$, and hence by (1) $b^{2}-4 a c$ is divisible by $p$ as well.
  have h8 (y : ℤ) (hy : x0 ≤ y ∧ y ≤ x0 + p - 2) (c1 : (p : ℤ) ∣ f y) :
      (p : ℤ) ∣ b ^ 2 - 4 * a * c := by
    sorry

-- Therefore it suffices to show that such an $y$ exists,
  suffices (p : ℤ) ∣ b ^ 2 - 4 * a * c ∨ ∃ y : ℤ, x0 ≤ y ∧ y ≤ x0 + p - 2 ∧ (p : ℤ) ∣ f y from by
    obtain this | this := this
    . exact this
    obtain ⟨y, hy1, hy2, hy3⟩ := this
    exact h8 y ⟨hy1, hy2⟩ hy3
-- Assume the opposite.
  by_contra! h9
  obtain ⟨h9', h9⟩ := h9

-- Since for $x=x_{0}, x_{0}+1, \ldots, x_{0}+p-1 $ , $f(x)$ is congruent modulo $p$ to

-- one of the $\frac{p-1}{2}$ numbers $1^{2}, 2^{2}, \ldots,\left(\frac{p-1}{2}\right)^{2}$,
-- it follows by the pigeon-hole principle that
-- for some mutually distinct $u, v, w \in\left\{x_{0}, \ldots, x_{0}+p-1\right\}$ we have $f(u) \equiv f(v) \equiv f(w)(\bmod p)$.
  have ⟨u, v, w, hu, hv, hw, ⟨huv, hvw, huw⟩, h10, h11⟩ : ∃ u v w : ℤ,
      (x0 ≤ u ∧ u ≤ x0 + p - 1) ∧
        (x0 ≤ v ∧ v ≤ x0 + p - 1) ∧
          (x0 ≤ w ∧ w ≤ x0 + p - 1) ∧
            (u ≠ v ∧ v ≠ w ∧ u ≠ w) ∧
            (f u : ZMod p) = f v ∧
            (f v : ZMod p) = f w := by
    sorry

-- Consequently the difference $f(u)-f(v)=$ $(u-v)(a(u+v)+b)$ is divisible by $p$,
  have h12 : (p : ℤ) ∣ (u - v) * (a * (u + v) + b) := by
    sorry

-- but it is clear that $p \nmid u-v$, hence $a(u+v) \equiv-b(\bmod p)$.
  have h13 : (a * (u + v) : ZMod p) = -b := by
    sorry

-- Similarly $a(u+w) \equiv-b(\bmod p)$,
  have h14 : (a * (u + w) : ZMod p) = -b := by
    sorry

-- which together with the previous congruence yields $p|a(v-w) \Rightarrow p| v-w$  which is clearly impossible.
  have h15 : ¬(p : ℤ) ∣ a * (v - w) := by
    by_contra! h15
    sorry

-- It follows that $p \mid f\left(y_{1}\right)$ for at least one $y_{1}$, $x_{0} \leq y_{1} < x_{0}+p$.
  have ⟨y1, h16, h16'⟩ : ∃ y1 : ℤ, (x0 ≤ y1 ∧ y1 < x0 + p) ∧ (p : ℤ) ∣ f y1 := by
    sorry

-- Choose $y_{2}, x_{0} \leq y_{2} < x_{0}+p$ such that $a\left(y_{1}+y_{2}\right)+b \equiv 0(\bmod p)$
  have ⟨y2, h17, h17'⟩ : ∃ y2 : ℤ,
      (x0 ≤ y2 ∧ y2 < x0 + p) ∧ ((a * (y1 + y2)  + b : ZMod p) = 0) := by
    sorry
-- We have  $p | f\left(y_{1}\right)-f\left(y_{2}\right) $ thus $ p | f\left(y_{2}\right)$.
  have h18 : (p : ℤ) ∣ f y2 := by
    sorry

-- If $y_{1}=y_{2}$, then by (1) $p \mid b^{2}-4 a c$.
  by_cases h19 : y1 = y2
  . subst h19
    specialize h6 y1
    set Δ := b ^ 2 - 4 * a * c
    apply_fun (λ x ↦ (x : ZMod p)) at h6
    push_cast at h6
    have c1 : (2 * a * y1 + b : ZMod p) = 0 := by
      ring_nf at h17' ⊢
      simpa using h17'
    have c2 : (f y1 : ZMod p) = 0 := by simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using h16'
    have c3 : (Δ : ZMod p) = 0 := by simpa [c1, c2] using h6
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at c3
    contradiction
-- Otherwise, among $y_{1}, y_{2}$ one belongs to $\left[x_{0}, x_{0}+p-2\right]$ as required.
  . have h20 : y1 ≤ x0 + p - 2 ∨ y2 ≤ x0 + p - 2 := by omega
    obtain h20 | h20 := h20
    . specialize h9 y1 h16.left h20
      contradiction
    . specialize h9 y2 h17.left h20
      contradiction
