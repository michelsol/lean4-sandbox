import Mathlib

open Real Finset

/-
Let $a_{1} \geq \cdots \geq a_{n} \geq a_{n+1}=0$ be a sequence of real numbers.
Prove that  $$ \sqrt{\sum_{k=1}^{n} a_{k}} \leq
  \sum_{k=1}^{n} \sqrt{k}\left(\sqrt{a_{k}}-\sqrt{a_{k+1}}\right) $$
-/

theorem other_24768
    (n : ℕ)
    (hn : n ≥ 1)
    (a : ℕ → ℝ)
    (ha1 : ∀ k ∈ Icc 1 n, a k ≥ a (k + 1))
    (ha2 : a (n + 1) = 0)
    :
    √(∑ k ∈ Icc 1 n, a k) ≤ ∑ k ∈ Icc 1 n, √k * (√(a k) - √(a (k + 1))) := by
-- We need the following lemmas about sums.
  have sum_Icc_Icc_comm' {M : Type} [AddCommMonoid M] (a b : ℕ) (f : ℕ → ℕ → M) :
    (∑ i ∈ Icc a b, ∑ j ∈ Icc (i + 1) b, f i j) =
      ∑ j ∈ Icc a b, ∑ i ∈ Ico a j, f i j := sum_Ico_Ico_comm' a (b + 1) f
  have sum_Icc_Icc_comm {M : Type} [AddCommMonoid M] (a b : ℕ) (f : ℕ → ℕ → M) :
    (∑ i ∈ Icc a b, ∑ j ∈ Icc i b, f i j) =
      ∑ j ∈ Icc a b, ∑ i ∈ Icc a j, f i j := sum_Ico_Ico_comm a (b + 1) f
  have sq_sum_eq_sum_sq_add (x : ℕ → ℝ) (a b : ℕ) : (∑ i ∈ Icc a b, x i) ^ 2 =
      (∑ i ∈ Icc a b, x i ^ 2) + 2 * ∑ i ∈ Icc a b, ∑ j ∈ Icc (i + 1) b, x i * x j := calc
      _ = ∑ i ∈ Icc a b, ∑ j ∈ Icc a b, x i * x j := by rw [sq, sum_mul_sum]
      _ = ∑ i ∈ Icc a b, (∑ j ∈ Ico a i, x i * x j + x i * x i + ∑ j ∈ Icc (i + 1) b, x i * x j) := by
        apply sum_congr rfl
        intro i hi
        have : Icc a b = Ico a i ∪ {i} ∪ Icc (i + 1) b := by ext x; simp at hi ⊢; omega
        rw [this]
        iterate 2 rw [sum_union (by
          intro s hs1 hs2 t hts; specialize hs1 hts; specialize hs2 hts; simp at hs1 hs2 ⊢; omega)]
        simp
      _ = ∑ i ∈ Icc a b, ∑ j ∈ Ico a i, x i * x j
          + ∑ i ∈ Icc a b, x i * x i + ∑ i ∈ Icc a b, ∑ j ∈ Icc (i + 1) b, x i * x j := by
        simp [sum_add_distrib]
      _ = _ := by
        have : ∑ i ∈ Icc a b, x i * x i = ∑ i ∈ Icc a b, x i ^ 2 := by
          apply sum_congr rfl; intro i hi; ring_nf
        rw [this]
        have : ∑ i ∈ Icc a b, ∑ j ∈ Ico a i, x i * x j
            = ∑ j ∈ Icc a b, ∑ i ∈ Icc (j + 1) b, x j * x i := calc
          _ = ∑ j ∈ Icc a b, ∑ i ∈ Icc (j + 1) b, x i * x j := by
            exact Eq.symm (sum_Icc_Icc_comm' a b fun i j => x j * x i)
          _ = _ := by apply sum_congr rfl; intro j hj; apply sum_congr rfl; intro i hi; ring_nf
        rw [this]
        linarith

-- First check that all $a_i$'s are nonnegative.
  have a_pos : ∀ k ∈ Icc 1 n, a k ≥ 0 := by
    suffices ∀ k, k ≤ n → 1 ≤ k → 0 ≤ a k from by intro k hk; simp at hk; apply this <;> omega
    apply Nat.decreasingInduction
    . intro k hk ihk hk'
      specialize ihk (by omega)
      specialize ha1 k (by simp; omega)
      linarith
    . intro hn
      specialize ha1 n (by simp; omega)
      linarith

-- Set $b_{k}=\sqrt{a_{k}}-\sqrt{a_{k+1}}$ for $k=1, \ldots, n$
  let b k := √(a k) - √(a (k + 1))

-- All $b_i$'s are nonnegative.
  have b_pos : ∀ k ∈ Icc 1 n, b k ≥ 0 := by
    intro k hk
    specialize ha1 k hk
    simp only [ge_iff_le, sub_nonneg, b, sqrt_le_sqrt ha1]

-- We have $a_{i}=\left(b_{i}+\cdots+b_{n}\right)^{2}$,
  have h1 : ∀ k ∈ Icc 1 n, a k = (∑ l ∈ Icc k n, b l) ^ 2 := by
    intro k hk
    rw [sum_sub_distrib]
    have : ∑ x ∈ Icc k n, √(a (x + 1)) = ∑ x ∈ Icc (k + 1) (n + 1), √(a x) := by
      apply sum_nbij (. + 1)
      . intro a ha; simp at ha ⊢; omega
      . intro i hi j hj hij; simp at hij; omega
      . intro i hi; simp at hi ⊢; omega
      . simp
    rw [this]
    have : Icc k n = {k} ∪ Icc (k + 1) n := by ext x; simp at hk ⊢; omega
    rw [this, sum_union (by simp)]
    have : Icc (k + 1) (n + 1) = Icc (k + 1) n ∪ {n + 1} := by ext x; simp at hk ⊢; omega
    rw [this, sum_union (by simp)]
    specialize a_pos k (by simp at hk ⊢; omega)
    simp [ha2, a_pos]

  replace h1 : ∀ k ∈ Icc 1 n, a k =
      (∑ l ∈ Icc k n, b l ^ 2) + 2 * ∑ i ∈ Icc k n, ∑ j ∈ Icc (i + 1) n, b i * b j := by
    intro k hk
    rw [h1 k hk, sq_sum_eq_sum_sq_add]

-- so the desired inequality after squaring becomes
-- $$ \sum_{k=1}^{n} k b_{k}^{2}+2 \sum_{1 \leq k < l \leq n} k b_{k} b_{l} \leq
--   \sum_{k=1}^{n} k b_{k}^{2}+2 \sum_{1 \leq k < l \leq n} \sqrt{k l} b_{k} b_{l}, $$
  suffices √(∑ k ∈ Icc 1 n, a k) ≤ ∑ k ∈ Icc 1 n, √k * b k from by simpa
  suffices √(∑ k ∈ Icc 1 n, a k) ≤ √((∑ k ∈ Icc 1 n, √k * b k) ^ 2) from by
    suffices √((∑ k ∈ Icc 1 n, √k * b k) ^ 2) = ∑ k ∈ Icc 1 n, √k * b k from by rwa [←this]
    apply sqrt_sq
    apply sum_nonneg
    intro i hi
    specialize b_pos i hi
    have : √i ≥ 0 := by exact sqrt_nonneg ↑i
    exact Left.mul_nonneg this b_pos
  suffices ∑ k ∈ Icc 1 n, a k ≤ (∑ k ∈ Icc 1 n, √k * b k) ^ 2 from sqrt_le_sqrt this
  have h2 :
      ∑ k ∈ Icc 1 n, a k =
      ∑ k ∈ Icc 1 n, k * b k ^ 2 + 2 * ∑ k ∈ Icc 1 n, ∑ l ∈ Icc (k + 1) n, k * b k * b l := by
    trans ∑ k ∈ Icc 1 n, ((∑ l ∈ Icc k n, b l ^ 2) + 2 * ∑ i ∈ Icc k n, ∑ j ∈ Icc (i + 1) n, b i * b j)
    . exact sum_congr rfl h1
    rw [sum_add_distrib]
    rw [←mul_sum]
    congr 1
    . simp [sum_Icc_Icc_comm]
    congr 1
    simp [sum_Icc_Icc_comm, mul_sum, mul_assoc]
  rw [h2]
  have h3 :
      (∑ k ∈ Icc 1 n, √k * b k) ^ 2 =
      ∑ k ∈ Icc 1 n, k * b k ^ 2 + 2 * ∑ k ∈ Icc 1 n, ∑ l ∈ Icc (k + 1) n, √(k * l) * b k * b l := by
    rw [sq_sum_eq_sum_sq_add]
    congr 1
    . apply sum_congr rfl
      intro k hk
      simp [mul_pow]
    . congr 1
      apply sum_congr rfl
      intro k hk
      apply sum_congr rfl
      intro l hl
      rw [sqrt_mul (by norm_cast; simp at hk; omega)]
      ring_nf
  rw [h3]

-- which clearly holds.
  suffices ∑ k ∈ Icc 1 n, ∑ l ∈ Icc (k + 1) n, k * b k * b l
      ≤ ∑ k ∈ Icc 1 n, ∑ l ∈ Icc (k + 1) n, √(k * l) * b k * b l from by simpa
  apply sum_le_sum
  intro k hk
  apply sum_le_sum
  intro l hl
  have := b_pos l (by simp at hl ⊢; omega)
  have := b_pos k (by simp at hk ⊢; omega)
  gcongr
  have : (k : ℝ) ≤ l := by norm_cast; simp at hl; omega
  trans √(k * k)
  . simp
  . gcongr


-- #check norm_sum_le
-- #check bilinsum
-- #check multinomi

/-
  have sq_sum_eq_sum_sq_add (x : ℕ → ℝ) (I : Finset ℕ) : (∑ i ∈ I, x i) ^ 2 =
      (∑ i ∈ I, x i ^ 2) + 2 * ((I ×ˢ I).filter λ (i, j) ↦ i < j).sum λ (i, j) ↦ x i * x j := calc
      _ = ∑ i ∈ I, ∑ j ∈ I, x i * x j := by rw [sq, sum_mul_sum]
      _ = (I ×ˢ I).sum λ (i, j) ↦ x i * x j := by rw [sum_product]
      _ = (∑ i ∈ I, x i ^ 2)
          + (((I ×ˢ I).filter λ (i, j) ↦ i < j).sum λ (i, j) ↦ x i * x j)
          + (((I ×ˢ I).filter λ (i, j) ↦ i < j).sum λ (i, j) ↦ x i * x j) := by
        have : (I ×ˢ I) = ((I ×ˢ I).filter λ (i, j) ↦ i = j)
                        ∪ ((I ×ˢ I).filter λ (i, j) ↦ i < j)
                        ∪ ((I ×ˢ I).filter λ (i, j) ↦ i > j)
                         := by
          ext x
          constructor
          . simp; intro h1 h2; simp [h1, h2]; omega
          . simp; intro h; rcases h with h | h | h <;> simp [h]
        conv_lhs => rw [this]
        dsimp at this ⊢
        rw [sum_union (by
          simp only [disjoint_union_left]
          split_ands
          all_goals
          . intro s hs1 hs2 t hts
            specialize hs1 hts
            specialize hs2 hts
            simp at hs1 hs2 ⊢
            omega)]
        rw [sum_union (by
          intro s hs1 hs2 t hts
          specialize hs1 hts
          specialize hs2 hts
          simp at hs1 hs2 ⊢
          omega)]
        congr 1
        . simp [sum_filter, sum_product, sq]
        . apply sum_nbij (λ (i, j) ↦ (j, i))
          . intro a ha
            simp at ha
            simp [ha]
          . intro a ha b hb hab
            simp at ha hb hab
            simp [Prod.eq_iff_fst_eq_snd_eq, hab]
          . intro (i, j) ha
            simp at ha ⊢
            use j, i
            simp [ha]
          . intro i hi; ring_nf
      _ = _ := by linarith
  dsimp at sq_sum_eq_sum_sq_add

-/
