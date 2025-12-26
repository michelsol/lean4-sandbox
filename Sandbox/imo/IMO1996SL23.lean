import Mathlib

/-
Let $$\mathbb{N}_{0}$$ denote the set of nonnegative integers.
Find a bijective function $$f$$ from $$\mathbb{N}_{0}$$ into $$\mathbb{N}_{0}$$ such that
for all $$m, n \in \mathbb{N}_{0}$$,  $$ f(3 m n+m+n)=4 f(m) f(n)+f(m)+f(n) . $$
-/
theorem number_theory_24701 :
    ∃ (f : ℕ → ℕ) (_ : f.Bijective), ∀ m n : ℕ, f (3 * m * n + m + n) = 4 * f m * f n + f m + f n
    := by
-- We first observe that the given functional equation is equivalent

-- to $$ 4 f\left(\frac{(3 m+1)(3 n+1)-1}{3}\right)+1=(4 f(m)+1)(4 f(n)+1) . $$

  have h1 (f : ℕ → ℕ) (m n : ℕ) :
      (f (3 * m * n + m + n) = 4 * f m * f n + f m + f n) ↔
        (4 * f (((3 * m + 1) * (3 * n + 1) - 1) / 3) + 1 = (4 * f m + 1) * (4 * f n + 1)) := by
    calc
      _ ↔ 4 * f (3 * m * n + m + n) + 1 = 4 * (4 * f m * f n + f m + f n) + 1 := by omega
      _ ↔ _ := by
        congr! 1
        . congr 3
          set x1 := ((3 * m + 1) * (3 * n + 1) - 1 : ℤ)
          have c1 : (3 : ℤ) ∣ x1 := by
            dsimp [x1]
            ring_nf
            omega
          qify [c1]
          field_simp [x1]
          ring
        . ring
-- This gives us the idea of introducing a function $$g: 3 \mathbb{N}_{0}+1 \rightarrow 4 \mathbb{N}_{0}+1$$

-- defined as $$g(x)=4 f\left(\frac{x-1}{3}\right)+1$$.

-- By the above equality, $$g$$ will be multiplicative, i.e., $$ g(x y)=g(x) g(y) \quad \text { for all } x, y \in 3 \mathbb{N}_{0}+1 $$
-- Conversely, any multiplicative bijection $$g$$ from $$3 \mathbb{N}_{0}+1$$ onto $$4 \mathbb{N}_{0}+1$$ gives us

-- a function $$f$$ with the required property: $$f(x)=\frac{g(3 x+1)-1}{4}$$.

-- It remains to give an example of such a function $$g$$.
  suffices ∃ (g : ℕ → ℕ) (_ : Set.BijOn g { 3 * n + 1 | n } { 4 * n + 1 | n }),
      ∀ x ∈ { 3 * n + 1 | n }, ∀ y ∈ { 3 * n + 1 | n }, g (x * y) = g x * g y by
    obtain ⟨g, hg1, hg2⟩ := this
    let f x := (g (3 * x + 1) - 1) / 4
    use f
    use by
      apply Set.bijective_iff_bijOn_univ.mpr
      let φ (x : ℕ) := (x - 1) / 4
      have hφ : Set.BijOn φ { 4 * n + 1 | n } .univ := by sorry
      let ψ (x : ℕ) := 3 * x + 1
      have hψ : Set.BijOn ψ .univ { 3 * n + 1 | n } := by sorry
      have c1 : f = φ ∘ g ∘ ψ := by ext x; rfl
      rw [c1]
      apply Set.BijOn.comp hφ
      apply Set.BijOn.comp hg1
      exact hψ
    sorry

-- Let $$P_{1}, P_{2}, Q_{1}, Q_{2}$$ be the sets of primes of the forms $$3 k+1,3 k+2,4 k+1$$, and $$4 k+3$$, respectively.
  let P1 := {p : ℕ | p.Prime ∧ ∃ k : ℕ, p = 3 * k + 1}
  let P2 := {p : ℕ | p.Prime ∧ ∃ k : ℕ, p = 3 * k + 2}
  let Q1 := {p : ℕ | p.Prime ∧ ∃ k : ℕ, p = 4 * k + 1}
  let Q2 := {p : ℕ | p.Prime ∧ ∃ k : ℕ, p = 4 * k + 3}
-- It is well known that these sets are infinite.
  have hP1 : P1.Infinite := by
    convert Nat.infinite_setOf_prime_modEq_one (by norm_num : 3 ≠ 0) using 4 with p
    sorry
  have hP2 : P2.Infinite := by
    sorry
  have hQ1 : Q1.Infinite := by
    convert Nat.infinite_setOf_prime_modEq_one (by norm_num : 4 ≠ 0) using 4 with p
    sorry
  have hQ2 : Q2.Infinite := by
    sorry

-- $$P_{1} \cup P_{2}$$ and $$Q_{1} \cup Q_{2}$$ are countably infinite.
-- Therefore we can choose a bijection $$h$$ from $$P_{1} \cup P_{2}$$ onto $$Q_{1} \cup Q_{2}$$ that maps $$P_{1}$$ bijectively onto $$Q_{1}$$
-- and $$P_{2}$$ bijectively onto $$Q_{2}$$.
  obtain ⟨h, hh1, hh2, hh3⟩ : ∃ (h : ℕ → ℕ) (_ : Set.BijOn h P1 Q1) (_ : Set.BijOn h P2 Q2),
      Set.BijOn h (P1 ∪ P2) (Q1 ∪ Q2) := by
    sorry

-- Now define $$g$$ as follows: $$g(1)=1$$
-- and for $$n=p_{1} p_{2} \cdots p_{m}\left(p_{i}\right.$$ 's need not be different)
-- define $$g(n)=h\left(p_{1}\right) h\left(p_{2}\right) \cdots h\left(p_{m}\right)$$.
  let g (n : ℕ) := ∏ p ∈ n.primeFactors, h p ^ n.factorization p
  use g

-- We now show that $$g: 3 \mathbb{N}_{0}+1 \rightarrow 4 \mathbb{N}_{0}+1$$ is bijective
  use by
    split_ands
-- Let $$n=p_{1} p_{2} \cdots p_{m} \in 3 \mathbb{N}_{0}+1 $$
-- Among the $$p_{i}$$ 's an even number are of the form $$3 k+2$$,
-- and consequently an even number of $$h\left(p_{i}\right) \mathrm{s}$$ are of the form $$4 k+3$$.
-- Hence the product of the $$h\left(p_{i}\right)$$ 's is of the form $$4 k+1$$.
    . intro n ⟨k, hn⟩
      let p := n.primeFactorsList.toFinsupp
      let m := n.primeFactorsList.length
      have c1 : n = p.support.prod id := by
        dsimp [p]
        simp
        sorry
      sorry
    . sorry
    . sorry

-- Also, it is obvious that $$g$$ is multiplicative.
  intro x ⟨n, hx⟩
  intro y ⟨m, hy⟩
  -- subst hx hy
  dsimp [g]
  calc
    _ = ∏ p ∈ x.primeFactors ∪ y.primeFactors, h p ^ (x * y).factorization p := by
      rw [Nat.primeFactors_mul]
      . omega
      . omega
    _ = ∏ p ∈ x.primeFactors ∪ y.primeFactors, h p ^ (x.factorization p + y.factorization p) := by
      rw [Nat.factorization_mul]
      . simp
      . omega
      . omega
    _ = ∏ p ∈ x.primeFactors ∪ y.primeFactors, h p ^ x.factorization p * h p ^ y.factorization p := by
      congr 2 with p
      rw [Nat.pow_add]
    _ = (∏ p ∈ x.primeFactors ∪ y.primeFactors, h p ^ x.factorization p) *
        (∏ p ∈ x.primeFactors ∪ y.primeFactors, h p ^ y.factorization p) := Finset.prod_mul_distrib
    _ = _ := by
      congr 1
      . refine Finset.prod_union_eq_left ?_
        intro p hp1 hp2
        suffices x.factorization p = 0 by simp [this]
        exact Finsupp.not_mem_support_iff.mp hp2
      . refine Finset.prod_union_eq_right ?_
        intro p hp1 hp2
        suffices y.factorization p = 0 by simp [this]
        exact Finsupp.not_mem_support_iff.mp hp2

-- Thus, the defined $$g$$ satisfies all the required properties.
theorem List.prod_support_toFinsupp [AddZeroClass α] [CommMonoid α] [DecidableEq α] (l : List α) :
    l.toFinsupp.support.prod l.toFinsupp = (l.filter (. ≠ 0)).prod := by
  induction' l with a l ih
  . simp
  . calc
      _ = ∏ x ∈ (a :: l).toFinsupp.support, (a :: l).getD x 0 := by simp
      _ = (if a ≠ 0 then a else 1) * (l.filter (. ≠ 0)).prod := by
        rw [List.toFinsupp_cons_eq_single_add_embDomain]
        rw [Finsupp.support_add_eq]
        rw [Finset.prod_union]
        congr 1
        . obtain ha | ha : a ≠ 0 ∨ a = 0 := by tauto
          . simp [Finsupp.support_single_ne_zero 0 ha, ha]
          . simp [ha]
        . simp at ih
          simp [ih]
        iterate 2
        . intro s hs1 hs2 x hx
          specialize hs1 hx
          specialize hs2 hx
          obtain ⟨c1, c2⟩ : 0 = x ∧ a ≠ 0 := by simpa [Finsupp.single_apply] using hs1
          obtain ⟨y, hy1, hy2⟩ : ∃ y, ¬l.getD y 0 = 0 ∧ y + 1 = x := by simpa using hs2
          omega
      _ = _ := by
        obtain ha | ha : a ≠ 0 ∨ a = 0 := by tauto
        . simp [ha]
        . simp [ha]

example (n : ℕ) (hn : n ≠ 0) : n.primeFactorsList.toFinsupp.support.prod n.primeFactorsList.toFinsupp = n := by
  rw [List.prod_support_toFinsupp]
  rw [List.filter_eq_self.mpr]
  . exact Nat.prod_primeFactorsList hn
  . intro p hp
    obtain ⟨hp1, hp2, hp3⟩ : Nat.Prime p ∧ p ∣ n ∧ ¬n = 0 := by simpa using hp
    simp [hp1.ne_zero]
