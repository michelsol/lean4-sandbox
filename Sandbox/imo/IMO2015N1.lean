import Mathlib

/-
Determine all positive integers $$M$$ for which the sequence $$a_{0}, a_{1}, a_{2}, \ldots$$, defined by

$$a_{0}=\frac{2 M+1}{2}$$ and $$a_{k+1}=a_{k}\left\lfloor a_{k}\right\rfloor$$ for $$k=0,1,2, \ldots$$, contains at least one integer term.
-/
theorem number_theory_24637 :
    {M : ℕ | M > 0 ∧
      ∀ (a : ℕ → ℝ) (_ : a 0 = (2 * M + 1) / 2) (_ : ∀ k : ℕ, a (k + 1) = a k * ⌊a k⌋),
        ∃ (k : ℕ) (y : ℤ), a k = y} = {M : ℕ | M ≥ 2} := by
  ext M
  dsimp
  constructor
  swap
  . intro h1
    constructor
    . omega

    intro a ha0 ha1

-- Define $$b_{k}=2 a_{k}$$ for all $$k \geqslant 0$$.
    let b k := 2 * a k

-- Then $$ b_{k+1}=2 a_{k+1}=2 a_{k}\left\lfloor a_{k}\right\rfloor=b_{k}\left\lfloor\frac{b_{k}}{2}\right\rfloor . $$
    have h2 k : b (k + 1) = b k * ⌊(b k : ℝ) / 2⌋ := calc
        _ = 2 * a (k + 1) := by dsimp [ha1]
        _ = 2 * (a k * ⌊a k⌋) := by
          congr 1
          exact ha1 k
        _ = (2 * a k) * ⌊a k⌋ := by ring
        _ = _ := by
          congr 2
          simp [b]

-- Since $$b_{0}$$ is an integer, it follows that $$b_{k}$$ is an integer for all $$k \geqslant 0$$.
    have h3 k : ∃ (y : ℤ), b k = y := by
      induction' k with k ih
      . use 2 * M + 1
        field_simp [b, ha0]
      . obtain ⟨z, ih⟩ := ih
        dsimp [b] at ih ⊢
        specialize ha1 k
        use z * ⌊a k⌋
        calc
          2 * a (k + 1) = (2 * a k) * ⌊a k⌋ := by rw [ha1]; ring
          _ = _ := by simp [ih]
    choose b' h3' using h3

-- Suppose that the sequence $$a_{0}, a_{1}, a_{2}, \ldots$$ does not contain any integer term.
    by_contra! h4

-- Then $$b_{k}$$ must be an odd integer for all $$k \geqslant 0$$,
    have h5 k : b' k % 2 = 1 := by
      by_contra! h5
      obtain ⟨l, c1⟩ : 2 ∣ b' k := by omega
      have c2 : a k = l := calc
        _ = b k / 2 := by ring
        _ = _ := by simp [h3', c1]
      specialize h4 k l
      contradiction

-- so that $$ b_{k+1}=b_{k}\left\lfloor\frac{b_{k}}{2}\right\rfloor=\frac{b_{k}\left(b_{k}-1\right)}{2} $$    (1)

    have h6 k : b' (k + 1) = (b' k * (b' k - 1) / 2 : ℝ) := by
      sorry

-- Hence $$ b_{k+1}-3=\frac{b_{k}\left(b_{k}-1\right)}{2}-3=\frac{\left(b_{k}-3\right)\left(b_{k}+2\right)}{2} $$ for all $$k \geqslant 0$$.   (2)

    have h7 k : b' (k + 1) - 3 = ((b' k - 3) * (b' k + 2) / 2 : ℝ) := by
      sorry

-- Suppose that $$b_{0}-3 > 0$$.

-- Then equation (2) yields $$b_{k}-3 > 0$$ for all $$k \geqslant 0$$.
    have h8 k (c1 : b' 0 - 3 > 0): b' k - 3 > 0 := by
      induction' k with k ih
      . rify at h1 ⊢
        rw [←h3']
        dsimp [b]
        rw [ha0]
        nlinarith
      . rify at ih ⊢
        rw [h7]
        nlinarith

-- For each $$k \geqslant 0$$, define $$c_{k}$$ to be the highest power of 2 that divides $$b_{k}-3$$.
    let c k := multiplicity 2 (b' k - 3)

-- Since $$b_{k}-3$$ is even for all $$k \geqslant 0$$,
-- the number $$c_{k}$$ is positive for every $$k \geqslant 0$$.
    have h9 k (c1 : b' 0 - 3 > 0) : c k > 0 := by
      sorry

-- Note that $$b_{k}+2$$ is an odd integer.
-- Therefore, from equation (2), we have that $$c_{k+1}=c_{k}-1$$ .
    have h10 k (c1 : b' 0 - 3 > 0) : c (k + 1) < c k := by
      sorry

-- so that $$c_{k}$$ is strictly decreasing which is a contradiction. So, $$b_{0}-3 \leqslant 0$$,
    have h11 : b' 0 - 3 ≤ 0 := by
      by_contra! h11
      replace h10 k := h10 k h11
      have c1 (k : ℕ) : c k ≤ (c 0 - k : ℤ) := by
        induction' k with k ih
        . omega
        . specialize h10 k
          zify at h10
          omega
      specialize c1 (c 0 + 1)
      omega

-- which implies $$M ≤ 1$$.
    have h12 : M ≤ 1 := by
      rify at h11
      rw [←h3'] at h11
      dsimp [b] at h11
      rw [ha0] at h11
      cancel_denoms at h11
      norm_cast at h11
      omega

-- which contradicts $$M ≥ 2$$.
    omega

  . intro h1
    obtain ⟨hM, h2⟩ := h1

-- For $$M=1$$, we can check that the sequence is constant with $$a_{k}=\frac{3}{2}$$ for all $$k \geqslant 0$$.
    have h3 : ¬M = 1 := by
      by_contra! h3
      subst h3
      let a (k : ℕ) := (3 : ℝ) / 2
      obtain ⟨k, y, c1⟩ := h2 a (by norm_num [a]) (by intro k; norm_num [a])
      replace c1 : 3 = 2 * y := by
        dsimp [a] at c1
        cancel_denoms at c1
        norm_cast at c1
      apply_fun (. % 2) at c1
      omega

-- Therefore, the answer is $$M \geqslant 2$$.
    omega
