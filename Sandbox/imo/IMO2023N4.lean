import Mathlib

open Finset Nat

/- Let $a_{1}, a_{2}, \ldots, a_{n}, b_{1}, b_{2}, \ldots, b_{n}$ be $2 n$ positive integers  uch that the $n+1$ products
$ a_{1} a_{2} a_{3} \cdots a_{n} \hspace{1cm} b_{1} a_{2} a_{3} \cdots a_{n} \hspace{1cm} b_{1} b_{2} a_{3} \cdots a_{n} \hspace{1cm} \cdots \hspace{1cm} b_{1} b_{2} b_{3} \cdots b_{n} $
form a strictly increasing arithmetic progression in that order.
Determine the smallest positive integer that could be the common difference
of such an arithmetic progression.
Answer: The smallest common difference is $n!$.
-/
theorem number_theory_607782
    (n : ℕ)
    (hn : n ≥ 1)
    : let S := { d : ℕ |
        d > 0 ∧
        ∃ (a : ℕ → ℕ) (_ : ∀ i ∈ Icc 1 n, 0 < a i)
          (b : ℕ → ℕ) (_ : ∀ i ∈ Icc 1 n, 0 < b i)
          (p : ℕ → ℕ)
          (hp : ∀ i ∈ Icc 0 n, p i = (∏ j ∈ Icc 1 i, b j) * ∏ j ∈ Icc (i + 1) n, a j),
          ∀ i ∈ Icc 0 n, p i = p 0 + d * i }
      IsLeast S (n !) := by
  intro S
  constructor

-- Equality is achieved when $b_{i}-a_{i}=1$ for $1 \leqslant i \leqslant n$ and $a_{1}=1$,
-- i.e. $a_{i}=i$ and $b_{i}=i+1$ for every $1 \leqslant i \leqslant n$.
-- Indeed, it is straightforward to check that these integers
-- produce an arithmetic progression with common difference $n!$.
  . constructor
    . exact Nat.factorial_pos n
    . use λ i ↦ i
      use by intro i hi; simp at hi; omega
      use λ i ↦ i + 1
      use by intro i hi; simp at hi; omega
      use λ i ↦ (∏ j ∈ Icc 1 i, (j + 1)) * ∏ j ∈ Icc (i + 1) n, j
      use by simp
      intro i hi
      simp at hi
      calc
        (∏ j ∈ Icc 1 i, (j + 1)) * ∏ j ∈ Icc (i + 1) n, j =
        (∏ j ∈ Icc 2 (i + 1), j) * ∏ j ∈ Icc (i + 1) n, j := by
          congr 1
          apply prod_nbij (. + 1)
          . intro j hj
            simp at hj ⊢
            omega
          . intro i hi j hj c1
            simp at hi hj c1 ⊢
            omega
          . intro j hj
            simp at hj ⊢
            omega
          . simp
        _ = (∏ j ∈ Icc 2 i, j) * (i + 1) * ∏ j ∈ Icc (i + 1) n, j := by
          congr 1
          obtain c1 | c1 : i = 0 ∨ 1 ≤ i := by omega
          . simp [c1]
          . exact prod_Icc_succ_top (by omega) id
        _ = (∏ j ∈ Icc 2 i, j) * (∏ j ∈ Icc (i + 1) n, j) * (i + 1) := by ring
        _ = (∏ j ∈ Icc 2 i ∪ Icc (i + 1) n, j) * (i + 1) := by
          congr 1
          symm
          apply prod_union
          intro s hs1 hs2 j hjs
          specialize hs1 hjs
          specialize hs2 hjs
          simp at hs1 hs2
          omega
        _ = (∏ j ∈ Icc 2 n, j) * (i + 1) := by
          obtain c1 | c1 : i = 0 ∨ 1 ≤ i := by omega
          . suffices ∏ j ∈ Icc 1 n, j = ∏ j ∈ Icc 2 n, j from by simpa [c1] using this
            calc
              _ = ∏ j ∈ {1} ∪ Icc 2 n, j := by congr 1; ext j; simp; omega
              _ = (∏ j ∈ {1}, j) * ∏ j ∈ Icc 2 n, j := by apply prod_union; simp
              _ = _ := by simp
          . congr 2
            ext j
            simp
            omega
        _ = (∏ j ∈ Ico 1 (n + 1), j) * (i + 1) := by
          congr 1
          symm
          calc
            _ = ∏ j ∈ Icc 1 n, j := rfl
            _ = ∏ j ∈ {1} ∪ Icc 2 n, j := by congr 1; ext j; simp; omega
            _ = (∏ j ∈ {1}, j) * ∏ j ∈ Icc 2 n, j := by apply prod_union; simp
            _ = _ := by simp
        _ = n ! * (i + 1) := by
          congr 1
          exact prod_Ico_id_eq_factorial n
        _ = n ! + n ! * i := by ring
        _ = ∏ x ∈ Ico 1 (n + 1), x + n ! * i := by
          congr 1
          symm
          exact prod_Ico_id_eq_factorial n
        _ = ∏ x ∈ Icc 1 n, x + n ! * i := by congr 1
        _ = _ := by simp


  . intro D ⟨hD, a, ha, b, hb, p, hp, h1⟩
-- The condition in the problem
-- is equivalent to $ D=\left(b_{1}-a_{1}\right) a_{2} a_{3} \cdots a_{n}=b_{1}\left(b_{2}-a_{2}\right) a_{3} a_{4} \cdots a_{n}=\cdots=b_{1} b_{2} \cdots b_{n-1}\left(b_{n}-a_{n}\right), $
-- where $D$ is the common difference.

    have h2 (i : ℕ) (hi : i ∈ Ico 0 n) :
        D = (∏ j ∈ Icc 1 i, (b j : ℤ)) * (b (i + 1) - a (i + 1) : ℤ) *
            (∏ j ∈ Icc (i + 2) n, (a j : ℤ)) := by
      simp at hi
      have h1i := h1 i (by simp; omega)
      have h1i' := h1 (i + 1) (by simp; omega)
      have hpi := hp i (by simp; omega)
      have hpi' := hp (i + 1) (by simp; omega)
      zify at h1i h1i' hpi hpi'
      calc
        (D : ℤ) = p (i + 1) - p i := by linarith
        _ = (∏ i ∈ Icc 1 (i + 1), (b i : ℤ)) * ∏ i ∈ Icc (i + 2) n, (a i : ℤ)
            - (∏ i ∈ Icc 1 i, (b i : ℤ)) * ∏ i ∈ Icc (i + 1) n, (a i : ℤ) := by congr 1
        _ = ((∏ i ∈ Icc 1 i, (b i : ℤ)) * b (i + 1)) * ∏ i ∈ Icc (i + 2) n, (a i : ℤ)
            - (∏ i ∈ Icc 1 i, (b i : ℤ)) * (a (i + 1) * ∏ i ∈ Icc (i + 2) n, (a i : ℤ)) := by
          congr 2
          . sorry
          . sorry
        _ = _ := by linarith

-- Since the progression is strictly increasing, $D > 0$, hence $b_{i} > a_{i}$ for every $1 \leqslant i \leqslant n$.
    have h3 (i : ℕ) (hi : i ∈ Icc 1 n) : b i > a i := by
      simp at hi
      specialize h2 (i - 1) (by simp; omega)
      zify at hD ha hb
      have c1 : ∏ j ∈ Icc 1 (i - 1), (b j : ℤ) > 0 := by
        apply prod_pos
        intro j hj
        simp at hj
        exact hb j (by simp; omega)
      have c2 : ∏ j ∈ Icc (i - 1 + 2) n, (a j : ℤ) > 0 := by
        apply prod_pos
        intro j hj
        simp at hj
        exact ha j (by simp; omega)
      set x1 := ∏ j ∈ Icc 1 (i - 1), (b j : ℤ)
      set x2 := ∏ j ∈ Icc (i - 1 + 2) n, (a j : ℤ)
      set x3 := (b (i - 1 + 1) : ℤ) - a (i - 1 + 1)
      have c3 : x3 > 0 := by
        by_contra! c3
        sorry
      replace c3 : (b i : ℤ) - (a i : ℤ) > 0 := by convert c3 using 4 <;> omega
      zify
      linarith

-- Individually, these equalities simplify
-- to $ \left(b_{i}-a_{i}\right) a_{i+1}=b_{i}\left(b_{i+1}-a_{i+1}\right) \text { for every } 1 \leqslant i \leqslant n-1 $      (1)
    have h4 (i : ℕ) (hi : i ∈ Ico 1 n) :
        (b i - a i : ℤ) * a (i + 1) = b i * (b (i + 1) - a (i + 1) : ℤ) := by
      sorry

-- If $g_{i}:=\operatorname{gcd}\left(a_{i}, b_{i}\right) > 1$ for some $1 \leqslant i \leqslant n$,
-- then we can replace $a_{i}$ with $\frac{a_{i}}{g_{i}}$ and $b_{i}$ with $\frac{b_{i}}{g_{i}}$ to get a smaller common difference.
-- Hence we may assume $\operatorname{gcd}\left(a_{i}, b_{i}\right)=1$ for every $1 \leqslant i \leqslant n$.
    clear S
    wlog h5 : ∀ i ∈ Icc 1 n, (a i).gcd (b i) = 1
    . specialize @this n hn (D / (∏ i ∈ Icc 1 n, (a i).gcd (b i))) sorry
      let g i := (a i).gcd (b i)
      let a' i := a i / g i
      let b' i := b i / g i
      specialize this a' sorry
      specialize this b' sorry
      specialize this (λ i ↦ (∏ j ∈ Icc 1 i, b' j) * ∏ j ∈ Icc (i + 1) n, a' j) (by simp)
      specialize this (by
        sorry)
      specialize this (by
        sorry)
      specialize this (by
        sorry)
      specialize this (by
        sorry)
      specialize this (by
        sorry)
      calc
        _ ≤ _ := this
        _ ≤ _ := by
          sorry

-- Then, we have $\operatorname{gcd}\left(b_{i}-a_{i}, b_{i}\right)=\operatorname{gcd}\left(a_{i}, b_{i}\right)=1$ and $\operatorname{gcd}\left(a_{i+1}, b_{i+1}-a_{i+1}\right)=\operatorname{gcd}\left(a_{i+1}, b_{i+1}\right)=1$ for
-- every $1 \leqslant i \leqslant n-1$.
    have h6 (i : ℕ) (hi : i ∈ Ico 1 n) : (a i : ℤ).gcd (b i : ℤ) = 1 := by
      simp at hi
      specialize h5 i (by simp; omega)
      simpa using h5
    have h7 (i : ℕ) (hi : i ∈ Ico 1 n) : (b i - a i : ℤ).gcd (b i : ℤ) = 1 := by
      specialize h6 i hi
      sorry

    have h8 (i : ℕ) (hi : i ∈ Ico 1 n) : (a (i + 1) : ℤ).gcd (b (i + 1) : ℤ) = 1 := by
      simp at hi
      specialize h5 (i + 1) (by simp; omega)
      simpa using h5
    have h9 (i : ℕ) (hi : i ∈ Ico 1 n) :
        (a (i + 1) : ℤ).gcd ((b (i + 1) : ℤ) - (a (i + 1) : ℤ)) = 1 := by
      specialize h8 i hi
      sorry

-- The equality (1) implies $a_{i+1}=b_{i}$
    have h10 (i : ℕ) (hi : i ∈ Ico 1 n) : a (i + 1) = b i := by
      sorry

-- and $b_{i}-a_{i}=b_{i+1}-a_{i+1}$.
    have h11 (i : ℕ) (hi : i ∈ Ico 1 n) : b i - a i = b (i + 1) - a (i + 1) := by
      sorry

-- Thus, $ a_{1}, \quad b_{1}=a_{2}, \quad b_{2}=a_{3}, \quad \ldots, \quad b_{n-1}=a_{n}, \quad b_{n} $ is an arithmetic progression with
-- positive common difference.
    have ⟨d, hd, h12⟩ : ∃ (d : ℕ) (_ : d > 0), ∀ i ∈ Icc 1 n, a i = a 1 + d * (i - 1) := by
      sorry

-- Since $a_{1} \geqslant 1$, we have $a_{i} \geqslant i$ for every $1 \leqslant i \leqslant n$,
    have h13 (i : ℕ) (hi : i ∈ Icc 1 n) : a i ≥ i := by
      simp at hi
      specialize ha 1 (by simp; omega)
      specialize h12 i (by simp; omega)
      calc
        a i = a 1 + d * (i - 1) := h12
        _ ≥ 1 + 1 * (i - 1) := by gcongr <;> omega
        _ = _ := by omega

-- so $ D=\left(b_{1}-a_{1}\right) a_{2} a_{3} \cdots a_{n} \geqslant 1 \cdot 2 \cdot 3 \cdots n=n! $
    calc
      D = (b 1 - a 1) * ∏ j ∈ Icc 2 n, a j := by
        specialize h2 0 (by simp; omega)
        specialize h3 1 (by simp; omega)
        zify [h3]
        simpa using h2
      _ ≥ 1 * ∏ j ∈ Icc 2 n, a j := by
        specialize h3 1 (by simp; omega)
        gcongr
        . omega
      _ ≥ 1 * ∏ j ∈ Icc 2 n, j := by
        gcongr with j hj
        simp at hj
        specialize h13 j (by simp; omega)
        exact h13
      _ = ∏ j ∈ Ico 1 (n + 1), j := by
        sorry
      _ = n ! := by exact prod_Ico_id_eq_factorial n
