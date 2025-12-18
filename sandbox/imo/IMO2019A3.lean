import Mathlib

open Finset Real

/- Let $n \geqslant 3$ be a positive integer and let $\left(a_{1}, a_{2}, \ldots, a_{n}\right)$ be a strictly increasing sequence of $n$ positive real numbers with sum equal to 2 . Let $X$ be a subset of $\{1,2, \ldots, n\}$ such that the value of  $$ \left|1-\sum_{i \in X} a_{i}\right| $$  is minimised. Prove that there exists a strictly increasing sequence of $n$ positive real numbers $\left(b_{1}, b_{2}, \ldots, b_{n}\right)$ with sum equal to 2 such that  $$ \sum_{i \in X} b_{i}=1 $$  (New Zealand) -/
theorem algebra_23695
    (n : ℕ) (hn : 3 ≤ n)
    (a : ℕ → ℝ)
    (ha1 : StrictMonoOn a (Icc 1 n))
    (ha2 : ∀ i ∈ Icc 1 n, a i > 0)
    (ha3 : ∑ i ∈ Icc 1 n, a i = 2)
    (X : Finset ℕ) (hX1 : X ⊆ Icc 1 n)
    (hX2 : ∀ Y ⊆ Icc 1 n, |1 - ∑ i ∈ X, a i| ≤ |1 - ∑ i ∈ Y, a i|)
    : ∃ (b : ℕ → ℝ) (_ : StrictMonoOn b (Icc 1 n)) (_ : ∀ i ∈ Icc 1 n, b i > 0) (_ : ∑ i ∈ Icc 1 n, b i = 2), ∑ i ∈ X, b i = 1 := by

  -- Note that |1 - ∑ i ∈ X, a i| = |1 - ∑ i ∈ Icc 1 n \ X, a i|
  have h1 X (hX : X ⊆ Icc 1 n) : |1 - ∑ i ∈ X, a i| = |1 - ∑ i ∈ Icc 1 n \ X, a i| := calc
      _ = |2 - ∑ i ∈ X, a i - 1| := by congr 1; linarith
      _ = |∑ i ∈ Icc 1 n, a i - ∑ i ∈ X, a i - 1| := by rw [ha3]
      _ = |∑ i ∈ Icc 1 n \ X, a i - 1| := by congr 1; rw [←sum_sdiff hX]; linarith
      _ = _ := by rw [←abs_neg]; simp

  let Δ X := ∑ i ∈ Icc 1 n \ X, a i - ∑ i ∈ X, a i

  -- Note that X is (a_i) minimizing iff X minimizes |Δ|
  have h2 X (hX : X ⊆ Icc 1 n) :
      (∀ Y ⊆ Icc 1 n, |1 - ∑ i ∈ X, a i| ≤ |1 - ∑ i ∈ Y, a i|) ↔ (∀ Y ⊆ Icc 1 n, |Δ X| ≤ |Δ Y|) := by
    sorry

  -- And that ∑ i ∈ X, a_i = 1 iff Δ = 0
  have h3 X (hX : X ⊆ Icc 1 n) : ∑ i ∈ X, a i = 1 ↔ Δ X = 0 := by
    sorry

  -- Thanks to h1 we may assume that $∑ i ∈ X, a i ≤ 1$
  wlog h4 : ∑ i ∈ X, a i ≤ 1
  . push_neg at h4
    let X' := Icc 1 n \ X
    have c1 : ∑ i ∈ X', a i ≤ 1 := by
      sorry
    specialize this n hn a ha1 ha2 ha3 X' sorry sorry h1 h2 h3
    sorry

  -- we may assume strict inequality as otherwise $b_{i}=a_{i}$ works.
  replace h4 : ∑ i ∈ X, a i = 1 ∨ ∑ i ∈ X, a i < 1 := eq_or_lt_of_le h4
  obtain h4 | h4 := h4
  . use a

  -- Also, $X$ clearly cannot be empty.
  have h5 : X ≠ ∅ := by
    intro h5
    subst h5
    sorry

  -- A scaling process might be used. It suffices to construct a strictly increasing sequence of positive real numbers c_i (typically obtained by perturbing the a_i in some way) such that $∑ i ∈ X, c i = ∑ i ∈ Icc 1 n \ X, c i$, as we may put $b_i = 2 c_i / ∑ j ∈ Icc 1 n, c_j$
  have h6 (h : ∃ (c : ℕ → ℝ) (_ : StrictMonoOn c (Icc 1 n)) (_ : ∀ i ∈ Icc 1 n, c i > 0), ∑ i ∈ X, c i = ∑ i ∈ Icc 1 n \ X, c i) : (∃ (b : ℕ → ℝ) (_ : StrictMonoOn b (Icc 1 n)) (_ : ∀ i ∈ Icc 1 n, b i > 0) (_ : ∑ i ∈ Icc 1 n, b i = 2), ∑ i ∈ X, b i = 1) := by
    obtain ⟨c, hc1, hc2, hc3⟩ := h
    use λ i ↦ 2 * c i / ∑ j ∈ Icc 1 n, c j
    use by
      sorry
    use by
      sorry
    use by
      sorry
    sorry

  by_cases h7 : n ∈ X
  .
  -- If $n \in X$, add $\Delta$ to $a_{n}$, producing a sequence of $c_{i}$ with $\sum_{i \in X} c_{i}=\sum_{i \in X^{c}} c_{i}$
    let c i := if i = n then a n + Δ X else a i
  -- and then scale as described above to make the sum equal to 2
    apply h6
    use c
    use by sorry
    use by sorry
    use by sorry

-- Otherwise, there is some $k$ with $k \in X$ and $k+1 \in X^{c}$.
  . obtain ⟨k, h8⟩ : ∃ k ∈ X, k + 1 ∈ Icc 1 n \ X := by
      sorry

 -- Let $\delta=a_{k+1}-a_{k}$.
    let δ := a (k + 1) - a k

 -- - If $\delta > \Delta$, add $\Delta$ to $a_{k}$ and then scale.
    by_cases h9 : δ > Δ X
    . let c i := if i = k then a k + Δ X else a i
      apply h6
      use c
      use by sorry
      use by sorry
      use by sorry

 -- - If $\delta < \Delta$, then considering $X \cup{k+1} \backslash{k}$ contradicts $X$ being $\left(a_{i}\right)$-minimising.
    by_cases h9' : δ < Δ X
    . let X' := X ∪ {k + 1} \ {k}
      have h10 : X' ⊆ Icc 1 n := sorry
      have h11 : |1 - ∑ i ∈ X', a i| < |1 - ∑ i ∈ X, a i| := by
        sorry
      specialize hX2 X' h10
      linarith

-- - If $\delta=\Delta$,
    replace h9 : δ = Δ X := by linarith

-- choose any $j \neq k, k+1$ (possible since $n \geqslant 3$ ),
    obtain ⟨j, h10⟩ : ∃ j ∈ Icc 1 n, j ≠ k ∧ j ≠ k + 1 := sorry

-- and choose any $\epsilon$ less than the least of $a_{1}$ and all the differences $a_{i+1}-a_{i}$.
    obtain ⟨ε, h11⟩ : ∃ ε > 0, ε < a 1 ∧ ∀ i ∈ Ico 1 n, ε < a (i + 1) - a i := by
      sorry

    by_cases h12 : j ∈ X
-- If $j \in X$ then add $\Delta-\epsilon$ to $a_{k}$ and $\epsilon$ to $a_{j}$, then scale;
    . let c i := if i = k then a k + Δ X - ε else if i = j then a j + ε else a i
      apply h6
      use c
      use by sorry
      use by sorry
      use by sorry
-- otherwise, add $\Delta$ to $a_{k}$ and $\epsilon / 2$ to $a_{k+1}$, and subtract $\epsilon / 2$ from $a_{j}$, then scale.
    . let c i := if i = k then a k + Δ X
          else if i = k + 1 then a (k + 1) + ε / 2
          else if i = j then a j - ε / 2
          else a i
      apply h6
      use c
      use by sorry
      use by sorry
      use by sorry
