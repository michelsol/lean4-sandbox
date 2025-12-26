import Mathlib


example
    (ipow : {n : ℕ} → (Fin n → ℕ) → ℕ → ℕ → ℕ)
    (hf : ∀ {n} (d : Fin n → ℕ) i j,
      ipow d i j = if hk : i < n ∧ i < j then d ⟨i, hk.left⟩ ^ ipow d (i + 1) j else 1)

    (d : Fin n → ℕ)
    :
    (∀ j (hj : j < n), ipow d 0 n =
      ipow (λ i : Fin n ↦ if _ : i < j then d ⟨i, by omega⟩ else ipow d j n) 0 j)
    := by
  intro j hj
  induction' j with j ih
  . sorry
  . specialize ih (by omega)
    conv_lhs => rw [hf]
    sorry

#exit
/-
In a game, participants choose a nine-digit positive integer $$\overline{ABCDEFGHI}$$ composed
of different non-zero digits, and their score is $$A^{B^{C^{D^{E^{F^{G^{H^{I}}}}}}}}$$.
To achieve the maximum score, which nine-digit number should the participant choose?
-/
theorem number_theory_623793
    :
    let f (d : Fin 9 → ℕ) := d 0 ^ d 1 ^ d 2 ^ d 3 ^ d 4 ^ d 5 ^ d 6 ^ d 7 ^ d 8
    let s := { d : Fin 9 → ℕ | Set.BijOn d .univ (Set.Icc 1 9) }
    -- The question assumes that the digits form a non-empty finite set
    have hs1 : s.Nonempty := sorry
    have hs2 : Fintype s := sorry
    let M := (s.toFinset.image f).max' (by simpa using hs1)
    let v : Fin 9 → ℕ := ![2, 3, 4, 5, 6, 7, 8, 9, 1]
    M = f v := by
  intro f s hs1 hs2 M v

  obtain ⟨h1, h2⟩ := (s.toFinset.image f).isGreatest_max' sorry
  replace ⟨u, hu, h1⟩ : ∃ u ∈ s, f u = M := by simpa using h1
  replace h2 : ∀ d ∈ s, f d ≤ f u := by
    rw [h1]
    intro d hd
    apply h2
    simp
    use d
  suffices u = v by simp [←this, h1]

-- Clearly I should be $$1$$ (if another letter is $$1$$,
-- then one can easily check that swapping the value of this letter with I
-- leads to a lower score).
  dsimp [s] at hu
  sorry

-- Note that for integers $$x, y, z$$ greater than $$1$$, we have
-- $$x < y$$ implies $$x^{y^{z}} > y^{x^{z}}$$.
-- (This is intuitively obvious by trying a few small cases,
-- and a technical proof is given in the remark below.)


-- It follows that one should choose $$234567891$$,
-- for otherwise one can swap a digit with
-- a smaller one on its right (except the ending $$1$$) to get a higher score.

-- **Remark.** To show that $$x^{y^{z}}>y^{x^{z}}$$ whenever $$x < y$$, we consider two cases:
-- ●Suppose $$x = 2$$.
-- When $$y ≥ 5$$, it follows from a simple induction (on $$y$$) that $$x^{y} > y^{x}$$ and so
-- $$x^{y^{z}} = (x^{y})^{y^{z-1}} > (x^{y})^{x^{z-1}} > (y^{x})^{x^{z-1}} = y^{x^{z}}$$.

-- If $$y = 3$$ or $$y = 4$$ we can also use induction (on $$z$$) to show $$x^{y^{z}}> y^{x^{z}}$$ for all integers $$z > 1$$.

-- ●Suppose $$x≥3$$.
-- We shall prove that we must have $$x^{y} > y^{x}$$, or equivalently, $$x^{1/x}\gt y^{1/y}$$,
-- and so the same argument above (in case $$x = 2$$ and $$y ≥5$$) would work.

-- We present two different proofs here:
-- (1) Using calculus — the function $$f(x) = x^{1/x}$$ is decreasing when $$x ≥ 3$$
-- since $$f'(x) = x^{\frac{1}{x}-2}(1-\ln x) < 0$$ whenever $$x > e$$.

-- (2) Without calculus — using binomial theorem, we have, for integer $$k ≥ 3$$,

-- $$​​​​k^{k+1}=\underbrace{k^{k}+k^{k}+\cdots+k^{k}}_{k \text{ terms}} > \underbrace{k^{k}+k^{k}+\cdots+k^{k}}_{k-1 \text{ terms}} + k^{2} + 1 > k^{k} + \left( \begin{matrix}k \ 1\end{matrix}\right)k^{k-1} + \left( \begin{matrix}k \ 2\end{matrix}\right)k^{k-2} + \cdots + \left( \begin{matrix}k \ k-2\end{matrix}\right)k^{2} + k^{2} + 1 = (k+1)^{k}$$

-- and so $$k^{1/k} > (k+1)^{1/(k+1)}$$. Recurring this inequality eventually gives $$x^{y} > y^{x}$$.
