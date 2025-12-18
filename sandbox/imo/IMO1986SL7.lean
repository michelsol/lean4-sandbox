import Mathlib

open Finset Real Polynomial

/-
Let real numbers $x_{1}, x_{2}, \ldots, x_{n}$ satisfy
$0 < x_{1} < x_{2}<\cdots<$ $x_{n}<1$ and set $x_{0}=0, x_{n+1}=1$.
Suppose that these numbers satisfy the following system of equations:
$$ \sum_{j=0, j \neq i}^{n+1} \frac{1}{x_{i}-x_{j}}=0 \quad \text { where } i=1,2, \ldots, n $$
Prove that $x_{n+1-i}=1-x_{i}$ for $i=1,2, \ldots, n$.
-/

theorem other_24047
    (n : ℕ)
    (hn : n ≥ 1)
    (x : ℕ → ℝ)
    (hx1 : x 0 = 0)
    (hx2 : x (n + 1) = 1)
    (hx3 : ∀ i ∈ Icc 0 n, x i < x (i + 1))
    (h : ∀ i ∈ Icc 1 n, ∑ j ∈ Icc 0 (n + 1) \ {i}, 1 / (x i - x j) = 0)
    : ∀ i ∈ Icc 1 n, x (n + 1 - i) = 1 - x i := by
-- Formula for the derivative of a product.
  have derivative_prod' {ι : Type} [DecidableEq ι] (P : ι → ℝ[X]) (s : Finset ι)
    : derivative (∏ j ∈ s, P j) = ∑ i ∈ s, (∏ j ∈ s \ {i}, P j) * derivative (P i) := by
      sorry

-- Let $P(x)=\left(x-x_{0}\right)\left(x-x_{1}\right) \cdots
-- \left(x-x_{n}\right)\left(x-x_{n+1}\right)$.
  let P : ℝ[X] := ∏ j ∈ Icc 0 (n + 1), (X - C (x j))
-- Then  $$ P^{\prime}(x)=\sum_{j=0}^{n+1} \frac{P(x)}{x-x_{j}} \quad
  let P' := derivative P
  have h1 : P' =
      ∑ j ∈ Icc 0 (n + 1), ∏ l ∈ Icc 0 (n + 1) \ {j}, (X - C (x l)) := by
    simp [P', derivative_prod']

-- \text { and } \quad P^{\prime \prime}(x)=
-- \sum_{j=0}^{n+1} \sum_{k \neq j} \frac{P(x)}{\left(x-x_{j}\right)\left(x-x_{k}\right)} . $$
  let P'' := derivative P'
  have h2 : P'' =
      ∑ k ∈ Icc 0 (n + 1), ∑ j ∈ Icc 0 (n + 1) \ {k}, ∏ l ∈ Icc 0 (n + 1) \ {k, j}, (X - C (x l)) := by
    simp [P'', P', derivative_prod']
    have (a b i j : ℕ) : (Icc a b \ {i}) \ {j} = Icc a b \ {i, j} := by ext k; simp; omega
    simp only [this]

-- Therefore  $$ P^{\prime \prime}\left(x_{i}\right)=
-- 2 P^{\prime}\left(x_{i}\right) \sum_{j \neq i} \frac{1}{\left(x_{i}-x_{j}\right)} $$
-- for $i=0,1, \ldots, n+1$,
  have h3 i (hi : i ∈ Icc 0 (n + 1)) : eval (x i) P'' =
      2 * eval (x i) P' * ∑ j ∈ Icc 0 (n + 1) \ {i}, 1 / (x i - x j) := by
    simp [h2, h1, eval_finset_sum, eval_prod]
    sorry

-- and the given condition implies $P^{\prime \prime}\left(x_{i}\right)=0$
-- for $i=1,2, \ldots, n$.
  replace h4 i (hi : i ∈ Icc 1 n) : eval (x i) P'' = 0 := by
    specialize h3 i (by simp at hi ⊢; omega)
    simp only [h i hi] at h3
    simpa using h3

-- Consequently,  $$ x(x-1) P^{\prime \prime}(x)=(n+2)(n+1) P(x) . $$   (1)
  have h5 : X * (X - 1) * P'' = C ((n + 2) * (n + 1) : ℝ) * P := by
    -- the roots of $P''$ are $x_1, ..., x_n$
    have c1 : P''.roots = Multiset.map x (Multiset.Icc 1 n) := by
      sorry
    have c2 : P''.leadingCoeff = (n + 2) * (n + 1) := by
      dsimp [P'', P']
      sorry
    have c3 : P'' = _ := eq_prod_roots_of_splits_id sorry
    replace c3 : P'' = C ((n + 2) * (n + 1) : ℝ) * ∏ i ∈ Icc 1 n, (X - C (x i)) := by
      simpa [c1, c2, Multiset.Icc] using c3
    suffices C ((n + 2) * (n + 1) : ℝ) * ((∏ i ∈ Icc 1 n, (X - C (x i))) * X * (X - 1)) =
      C ((n + 2) * (n + 1) : ℝ) * P from by rw [c3]; ring_nf at this ⊢; simpa
    dsimp [P]
    congr 1
    sorry

  have hp1 : P.natDegree = n + 2 := by simp [P, natDegree_prod']
  have hp2 : P.Monic := by
    apply monic_prod_of_monic
    intro i hi
    apply monic_X_sub_C

-- It is easy to observe that there is a unique monic polynomial of degree $n+2$
-- satisfying differential equation (1).
  have h6 : ∃! P : ℝ[X], P.natDegree = n + 2 ∧ P.Monic
    ∧ X * (X - 1) * P.derivative.derivative = C ((n + 2) * (n + 1) : ℝ) * P := by
    apply ExistsUnique.intro P
    . simp [hp1, hp2, h5]
-- Use the equation satisfied by P, to show that its coefficients are uniquely determined.
    . intro R ⟨hr1, hr2, hr3⟩
      suffices ∀ k, R.coeff k = P.coeff k from by
        apply coeff_inj.mp; ext k; exact this k
      suffices ∀ k ≤ n + 2, R.coeff k = P.coeff k from by
        intro k
        rcases (by omega : k ≤ n + 2 ∨ k > n + 2) with hk | hk
        . exact this k hk
        . have : R.coeff k = 0 := by apply coeff_eq_zero_of_natDegree_lt; omega
          have : P.coeff k = 0 := by apply coeff_eq_zero_of_natDegree_lt; omega
          linarith
      sorry

-- On the other hand, the polynomial $Q(x)=(-1)^{n} P(1-x)$ also satisfies this equation,
-- is monic, and $\operatorname{deg} Q=$ $n+2$.
  let Q := C ((-1) ^ n : ℝ) * P.comp (1 - X)
-- Therefore $(-1)^{n} P(1-x)=P(x)$
  have h7 : P = Q := by
    apply h6.unique
    . simp [hp1, hp2, h5]
    . split_ands
      . rw [natDegree_mul (by simp) (by sorry) , natDegree_comp]
        rw [show (1 - X : ℝ[X]) = -(X - C 1) from by simp]
        rw [natDegree_neg, natDegree_X_sub_C]
        simp [P, natDegree_prod']
      . sorry
      . sorry

-- and the result follows.
-- as the roots of $P(1-x)$, and hence of Q, are $1 - x_{n+1} < 1 - x_n < ... < 1 - x_0$
  have h8 : P.roots = (Multiset.Icc 0 (n + 1)).map x := by
    sorry
  have h9 : (Multiset.Icc 0 (n + 1)).map (λ k => 1 - x k) = (Multiset.Icc 0 (n + 1)).map x := by
    rw [h7] at h8
    dsimp [Q] at h8
    rw [roots_C_mul _ (by simp)] at h8
    sorry
  replace h9 : (Icc 0 (n + 1)).image (λ k => 1 - x k) = (Icc 0 (n + 1)).image x := by
    sorry
  sorry
