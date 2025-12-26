import Mathlib

open Finset
open Filter

/-
Determine all sequences $(x_1, x_2, . . . , x_{2011})$ of positive integers such that for every positive integer $n$ there is an integer $a$ with
$$x_1^n + 2x_2^n + · · · + 2011x_{2011}^n = a^{n+1} + 1$$
-/

theorem algebra_24008
  (x : ℕ → ℕ) (pos_x : ∀ k, x k > 0)
  : (∀ n ≥ 1, ∃ a, ∑ i ∈ Icc 1 2011, i * (x i) ^ n = a ^ (n + 1) + 1)
    ↔ x 1 = 1 ∧ ∀ i ∈ Icc 2 2011, x i = ∑ i ∈ Icc 2 2011, i := by
  constructor
  swap
  -- Check that sequence $(x_1,..., x_{2011}) = (1, m,..., m)$ with $m=2+3+...+2011$ is valid.
  . intro ⟨h1, h2⟩
    intro n hn
    use ∑ i ∈ Icc 2 2011, i
    have : Icc 1 2011 = Icc 1 1 ∪ Icc 2 2011 := by ext x; simp; omega
    rw [this]
    have : Disjoint (Icc 1 1) (Icc 2 2011) := by
      intro x h1 h2; intro k hk; specialize h1 hk; specialize h2 hk; simp at h1 h2 ⊢; omega
    rw [sum_union this]
    have : ∀ i ∈ Icc 2 2011, i * x i ^ n = i * (∑ i ∈ Icc 2 2011, i) ^ n := by
      intro i hi; specialize h2 i hi; simp [h2]
    rw [sum_congr rfl this]
    rw [←sum_mul]
    simp [h1]
    ring_nf
  -- Let a valid sequence  $(x_1,..., x_{2011})$ be given.
  -- We will show it must be $(1, m,..., m)$ with $m=2+3+...+2011$.
  . intro h
    -- For each $n \in \mathbb{N}$, call $y_n$ the integer such that
    -- $x_1^n + 2x_2^n + · · · + 2011x_{2011}^n = y_n^{n+1} + 1$
    let y (n : ℕ) := if hn : n ≥ 1 then (h n hn).choose else 0
    replace hy : ∀ n ≥ 1, ∑ i ∈ Icc 1 2011, i * x i ^ n = y n ^ (n + 1) + 1 := by
      intro n hn
      dsimp [y]
      split_ifs
      exact (h n hn).choose_spec
    -- Show that $(y_n)$ is bounded using the fact that
    -- $x_1^n + 2x_2^n + · · · + 2011x_{2011}^n \le \left(x_1 + 2x_2 + · · · + 2011x_{2011}\right)^n$
    have y_mem : ∀ n ≥ 1, y n ∈ Set.Icc 0 (∑ i ∈ Icc 1 2011, i * x i) := by
      intro n hn
      specialize hy n hn
      have : y n ^ (n + 1) + 1 ≤ (∑ i ∈ Icc 1 2011, i * x i) ^ n := by
        calc
          _ = ∑ i ∈ Icc 1 2011, i * x i ^ n := hy.symm
          _ ≤ ∑ i ∈ Icc 1 2011, (i * x i) ^ n := by
            gcongr with i hi
            . suffices i * x i ^ n ≤ i ^ n * x i ^ n from by ring_nf; simpa
              gcongr
              . have : n ≠ 0 := by omega
                exact Nat.le_self_pow this i
          _ ≤ (∑ i ∈ Icc 1 2011, i * x i) ^ n := by
            rw [show (λ i => (i * x i) ^ n) = (λ i => i * x i)^n from by ext i; simp]
            generalize (λ i => i * x i) = x
            have hm : 2011 ≥ 1 := by omega
            generalize 2011 = m at hm ⊢
            induction' m, hm using Nat.le_induction with m hm ihm
            . simp
            . calc
                _ = (Icc 1 m).sum (x ^ n) + x (m + 1) ^ n := by rw [sum_Icc_succ_top (by simp)]; rfl
                _ ≤ (Icc 1 m).sum x ^ n + x (m + 1) ^ n := by gcongr
                _ ≤ ((Icc 1 m).sum x + x (m + 1)) ^ n := by apply pow_add_pow_le <;> omega
                _ = _ := by rw [sum_Icc_succ_top (by simp)]
      replace : y n ^ (n + 1) ≤ (∑ i ∈ Icc 1 2011, i * x i) ^ (n + 1) := by
        calc
        _ ≤ (∑ i ∈ Icc 1 2011, i * x i) ^ n * 1 := by omega
        _ ≤ _ := by
          rw [pow_succ]
          gcongr
          have : Icc 1 2011 = Icc 1 1 ∪ Icc 2 2011 := by ext x; simp; omega
          rw [this]
          have : Disjoint (Icc 1 1) (Icc 2 2011) := by
            intro x h1 h2; intro k hk; specialize h1 hk; specialize h2 hk; simp at h1 h2 ⊢; omega
          rw [sum_union this]
          have := pos_x 1
          simp; omega
      replace : y n ≤ (∑ i ∈ Icc 1 2011, i * x i) := by
        have : n + 1 ≠ 0 := by omega
        apply le_of_pow_le_pow_left this <;> omega
      simpa
    replace y_mem : ∀ n, y n ∈ Set.Icc 0 (∑ i ∈ Icc 1 2011, i * x i) := by
      intro n
      rcases (show n = 0 ∨ n ≥ 1 from by omega) with hn | hn
      . subst hn; dsimp [y]; norm_num
      . specialize y_mem n hn; exact y_mem
    -- As $y$ is bounded, a subsequence $y ∘ φ$ converges to some integer $z$
    -- and ends up being equal to $z$, as $y$ is integer valued.
    obtain ⟨z, hz, ⟨φ, hφ, hyz⟩⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc 0 _) y_mem
    replace hyz : ∃ n₀, ∀ n ≥ n₀, y (φ n) = z := by simpa using hyz
    replace hyz : ∃ n₀ ≥ 1, ∀ n ≥ n₀, y (φ n) = z := by
      obtain ⟨n₀, hyz⟩ := hyz
      use max n₀ 1; split_ands; omega; intro n hn; exact hyz n (by omega)
    obtain ⟨n₀, hn₀, hyz⟩ := hyz
    -- The main equation now simplifies to
    -- $\forall n \ge n_0,  x_1^{\phi_n} + 2x_2^{\phi_n} + ... + 2011x_{2011}^{\phi_n} = z \cdot z^{\phi_n} +1$
    replace hy' : ∀ n ≥ n₀, ∑ i ∈ Icc 1 2011, i * x i ^ φ n = z ^ (φ n) * z + 1 := by
      intro n hn
      specialize hy (φ n) (by have := hφ (by omega : 0 < n); omega)
      specialize hyz n hn
      rw [hyz] at hy
      exact hy
    -- Let $m$ be the maximum of $x_i$'s.
    have hm1 := (((Icc 1 2011).image x).isGreatest_max' (by simp)).1
    have hm2 : ∀ _, _ := (((Icc 1 2011).image x).isGreatest_max' (by simp)).2
    set m := ((Icc 1 2011).image x).max' (by simp)
    -- Grouping terms with equal $x_i$ together, we will now rewrite
    -- $x_1^n+2x_2^n+...+2011x_{2011}^n=a_{m}m^n+a_{m-1}(m-1)^n+...+a_1$
    let a (j : ℕ) := ∑ k ∈ { k ∈ Icc 1 2011 | x k = j }, k
    -- z cannot be 0 nor 1 because  z ^ φ n * z + 1 ≥ ∑ i ∈ Icc 1 2011, i > 2
    have z_ne_0 : z ≠ 0 := sorry
    have z_ne_1 : z ≠ 1 := sorry
    -- m is not 0 because xi's are > 0
    have m_ne_0 : m ≠ 0 := sorry
    -- m is not 1 because otherwise, all xi's would be = 1, and
    -- lhs would be constant, while rhs would increase with n in the main equation
    have m_ne_1 : m ≠ 1 := sorry
    -- a(m) ≠ 0 by definition of a, and by definition of m
    have am_ne_0 : a m ≠ 0 := sorry
    have ha : ∀ n ≥ 1, ∑ i ∈ Icc 1 2011, i * x i ^ n = ∑ j ∈ Icc 1 m, a j * j ^ n := by
      intro n hn
      have h1 : Icc 1 2011 = (Icc 1 m).biUnion λ j => { k ∈ Icc 1 2011 | x k = j } := by
        ext i
        constructor
        . intro hi
          specialize pos_x i
          specialize hm2 (x i) (by simp at hi ⊢; use i)
          simp at hi ⊢; omega
        . simp
      rw [h1]
      rw [Finset.sum_biUnion]
      congr
      . ext j
        rw [sum_mul]
        apply sum_congr rfl
        intro i hi
        replace hi : (1 ≤ i ∧ i ≤ 2011) ∧ x i = j := by simpa using hi
        simp [hi.2]
      . intro i hi j hj hij s hsi hsj c hc
        specialize hsi hc; specialize hsj hc
        simp at hsi hsj ⊢; omega
    -- We now define $b_i = a_i$ if $i\notin\{1,z\}$, and $b_1=a_1$, $b_z=a_z-z$
    -- So that we can rewrite the main equation as :
    --  $\forall n \ge n_0, b_{M}M^{\phi_n}+b_{M-1}(M-1)^{\phi_n}+...+b_1 = 0$ with $M=max(z,m)$
    let b (j : ℕ) : ℤ := if j = z then a j - z else if j = 1 then a 1 - 1 else a j
    have hb : ∀ n ≥ n₀, ∑ j ∈ Icc 1 (max z m), b j * j ^ φ n = 0 := by
      intro n hn
      have hb : ∑ j ∈ Icc 1 m, a j * j ^ φ n = z * z ^ (φ n) + 1 := calc
        _ = ∑ i ∈ Icc 1 2011, i * x i ^ φ n := by
          specialize ha (φ n) (by have := hφ (by omega : 0 < n); omega)
          exact ha.symm
        _ = _ := by rw [hy' _ hn]; ring_nf
      have : ∑ j ∈ Icc 1 (max z m), b j * j ^ φ n + 1 + z * z ^ φ n = ∑ j ∈ Icc 1 m, a j * j ^ φ n := by
        have : ∑ j ∈ Icc 1 m, a j * j ^ φ n = ∑ j ∈ Icc 1 (max z m), a j * j ^ φ n := by
          have : Icc 1 (max z m) = Icc 1 m ∪ Icc (m + 1) (max z m) := by ext i; simp; omega
          rw [this, sum_union_eq_left]
          intro j hj1 hj2
          suffices a j = 0 from by simp [this]
          have hmj : m < j := by simp at hj1; omega
          rw [sum_eq_zero_iff]
          intro k hk
          simp at hk
          specialize hm2 (x k) (by simp; use k; omega)
          omega
        rw [this]
        replace : {1, z} ⊆ Icc 1 (max z m) := by
          intro k hk
          rcases (show k = 1 ∨ k = z from by simpa using hk) with hk | hk <;> (simp; omega)
        iterate 2 rw [←sum_sdiff this]
        replace : ∑ j ∈ Icc 1 (max z m) \ {1, z}, b j * j ^ φ n = ∑ j ∈ Icc 1 (max z m) \ {1, z}, a j * j ^ φ n := by
          zify
          apply sum_congr rfl
          intro j hj
          replace hj : (1 ≤ j ∧ (j ≤ z ∨ j ≤ m)) ∧ ¬j = 1 ∧ ¬j = z := by simpa using hj
          simp [b, hj.2.1, hj.2.2]
        rw [this]
        suffices ∑ x ∈ {1, z}, b x * x ^ φ n + 1 + z * z ^ φ n = ∑ x ∈ {1, z}, a x * x ^ φ n from by omega
        iterate 2 rw [sum_pair z_ne_1.symm]
        dsimp [b]
        simp [z_ne_1.symm]
        ring_nf
      rw [hb] at this
      push_cast at this
      omega
    -- We now show that  $\forall n \ge n_0, b_{M}M^{\phi_n}+b_{M-1}(M-1)^{\phi_n}+...+b_1 = 0$
    -- implies that all $b_i$'s are zero.
    have : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ n₀ ≥ 1, ∀ (b : ℕ → ℤ) (N : ℕ), (∀ n ≥ n₀, ∑ j ∈ Icc 1 N, b j * j ^ φ n = 0) → ∀ j ∈ Icc 1 N, b j = 0 := by
      clear * -
      intro φ hφ n₀ hn₀ b N hb
      rcases (show N = 0 ∨ N ≥ 1 from by omega) with hN | hN; simp [hN]
      -- Suppose that not all $b_i$'s are zero.
      by_contra h
      push_neg at h
      -- wlog, we can assume $b_N$ is not equal to zero.
      wlog bN_ne_0 : b N ≠ 0
      . specialize this φ hφ _ hn₀
        have he : { j ∈ Icc 1 N | b j ≠ 0 }.Nonempty := (by use h.choose; simpa using h.choose_spec)
        have hm1 := ({ j ∈ Icc 1 N | b j ≠ 0 }.isGreatest_max' he).1
        have hm2 : ∀ _, _ := ({ j ∈ Icc 1 N | b j ≠ 0 }.isGreatest_max' he).2
        set m := { j ∈ Icc 1 N | b j ≠ 0 }.max' he
        let b' (j : ℕ) := if j ≤ m then b j else 0
        specialize this b' m
        apply this
        . intro n hn
          specialize hb n hn
          have : Icc 1 N = Icc 1 m ∪ Icc (m + 1) N := by ext i; simp at hm1 ⊢; omega
          rw [this] at hb
          rw [sum_union_eq_left] at hb
          . suffices ∑ j ∈ Icc 1 m, b' j * j ^ φ n = ∑ j ∈ Icc 1 m, b j * j ^ φ n from by omega
            rw [sum_congr rfl]
            intro j hj
            simp at hj; simp [b']; omega
          . intro j hj1 hj2
            by_cases hbj : b j = 0; simp [hbj]
            specialize hm2 j (by simp at hj1 ⊢; omega)
            simp at hj1
            omega
        . simp at hm1; omega
        . obtain ⟨j, hj1, hj2⟩ := h
          use j
          specialize hm2 j (by simp at hj1 ⊢; omega)
          split_ands
          . simp at hj1 ⊢; omega
          . simp [b']; omega
        . simp at hm1; simp [b']; omega
      -- We will derive a contradiction, showing that $b_N$ is 0.
      suffices b N = 0 from by omega
      -- We show that $|b_N|\le K \cdot \left(1-\dfrac{1}{N}\right)^{\phi_n}$
      have bN_lt : ∀ n ≥ n₀, |b N| ≤ (∑ i ∈ Icc 1 (N - 1), |b i|) * (1 - (1 / N : ℝ)) ^ φ n := by
        intro n hn₀
        specialize hb n hn₀
        replace hb : b N * N ^ φ n = -∑ i ∈ Icc 1 (N - 1), b i * i ^ φ n := by
          have : {N} ⊆ Icc 1 N := by intro i; simp; omega
          rw [←sum_sdiff this] at hb
          have : Icc 1 N \ {N} = Icc 1 (N - 1) := by ext i; simp; omega
          rw [this] at hb
          simp at hb
          omega
        have : |b N| * N ^ φ n ≤ (∑ i ∈ Icc 1 (N - 1), |b i|) * (N - 1) ^ φ n := calc
          |b N| * N ^ φ n = |b N * N ^ φ n| := by simp [abs_mul]
          _ = |-∑ i ∈ Icc 1 (N - 1), b i * i ^ φ n| := by rw [hb]
          _ = |∑ i ∈ Icc 1 (N - 1), b i * i ^ φ n| := by simp
          _ ≤ ∑ i ∈ Icc 1 (N - 1), |b i * i ^ φ n| := by exact abs_sum_le_sum_abs _ _
          _ ≤ ∑ i ∈ Icc 1 (N - 1), |b i| * (N - 1) ^ φ n := by
            gcongr with i hi
            rw [abs_mul]
            gcongr
            suffices i ^ φ n ≤ (N - 1) ^ φ n from by norm_cast
            exact Nat.pow_le_pow_of_le_left (by simp at hi; omega) (φ n)
          _ = _ := by rw [sum_mul]
        set K := ∑ i ∈ Icc 1 (N - 1), |b i|
        rify at this
        calc
          _ = |(b N : ℝ)| := by simp
          _ ≤ K * (N - 1) ^ φ n / N ^ φ n := by
            have h2 : (N ^ φ n : ℝ) > 0 := by norm_cast; exact Nat.pos_pow_of_pos (φ n) hN
            exact (le_div_iff₀ h2).mpr this
          _ = K * ((N - 1) ^ φ n / N ^ φ n) := by rw [mul_div_assoc]
          _ = K * ((N - 1) / N) ^ φ n := by congr; rw [div_pow]
          _ = _ := by field_simp
      set K := ∑ i ∈ Icc 1 (N - 1), |b i|
      -- Show that rhs tends to 0 as n grows to infinity
      suffices (Tendsto (λ n : ℕ ↦ K * (1 - (1 / N : ℝ)) ^ φ n) atTop (nhds 0)) from by
        suffices |b N| ≤ (0 : ℝ) from by simpa
        apply ge_of_tendsto this
        simp only [eventually_atTop]
        use n₀
      suffices (Tendsto (λ n : ℕ ↦ (1 - (1 / N : ℝ)) ^ φ n) atTop (nhds 0)) from by
        have := Tendsto.const_mul (K : ℝ) this
        simpa
      have hφ' : Tendsto φ atTop atTop := StrictMono.tendsto_atTop hφ
      suffices (Tendsto (λ n : ℕ ↦ (1 - (1 / N : ℝ)) ^ n) atTop (nhds 0)) from by
        set f := (λ n : ℕ ↦ (1 - (1 / N : ℝ)) ^ n)
        set g := (λ n : ℕ ↦ (1 - (1 / N : ℝ)) ^ φ n)
        rw [show g = f ∘ φ from by ext n; simp]
        exact Tendsto.comp this hφ'
      apply tendsto_pow_atTop_nhds_zero_of_lt_one
      . suffices (1 / N : ℝ) ≤ 1 from by linarith
        apply (div_le_one₀ (by norm_cast)).mpr (by norm_cast)
      . suffices  (1 / N : ℝ) > 0 from by linarith
        apply one_div_pos.mpr (by norm_cast)
    -- Now that all $b_{i}$'s are 0, show that all $a_i$'s are 0 except $a_1=1$ and $a_m=m=z$.
    replace hb : ∀ j ∈ Icc 1 (max z m), b j = 0 := this φ hφ n₀ hn₀ b _ hb
    have hbm := hb m (by simp; omega)
    have m_eq_z : m = z := by
      by_contra this; simp [b, this, show m ≠ 1 from by omega, am_ne_0] at hbm
    simp [b, m_eq_z, show m ≠ 1 from by omega] at hbm
    replace hbm : a z = z := by omega
    replace hb : ∀ j ∈ Icc 1 m, b j = 0 := by rwa [show max z m = m from by omega] at hb
    -- This will imply that $x_i=m$ for $i\ge 2$ and $x_1=1$ concluding the proof.
    have hb2 : ∀ i ∈ Icc 1 2011, ∀ j ∈ Icc 2 (m - 1), x i ≠ j := by
      intro i hi
      intro j hj
      specialize hb j (by simp at hj ⊢; omega)
      simp at hj
      have j_ne_z : j ≠ z := by omega
      have j_ne_1 : j ≠ 1 := by omega
      replace hb : a j = 0 := by simpa [b, j_ne_z, j_ne_1] using hb
      replace hb : ∀ i ∈ Icc 1 2011, x i = j → i = 0 := by simpa [a] using hb
      intro hij
      specialize hb i hi hij
      simp at hi; omega
    have hb1 : x 1 = 1 ∧ ∀ i ∈ Icc 2 2011, x i ≠ 1 := by
      specialize hb 1 (by simp; omega)
      simp [b, z_ne_1.symm] at hb
      replace hb : a 1 = 1 := by omega
      replace hb : ∑ k ∈ { k ∈ Icc 1 2011 | x k = 1 }, k = 1 := hb
      have h2 : ∀ i ∈ Icc 2 2011, x i ≠ 1 := by
        by_contra h2
        push_neg at h2
        obtain ⟨k₀, hk₀⟩ := h2
        have : {k₀} ⊆ { k ∈ Icc 1 2011 | x k = 1 } := by
          intro k hk
          simp at hk; subst hk
          simp at hk₀ ⊢; omega
        rw [←sum_sdiff this] at hb
        have : ∑ k ∈ {k₀}, k ≤ 1 := by omega
        simp at hk₀ this
        omega
      have : { k ∈ Icc 1 2011 | x k = 1 } = { k ∈ Icc 1 1 | x k = 1 } ∪ { k ∈ Icc 2 2011 | x k = 1 } := by
        ext k; simp; omega
      rw [this, sum_union (by
        intro s hs ht k hk; specialize hs hk; specialize ht hk; simp at hs ht ⊢; omega)] at hb
      have : ∑ k ∈ { k ∈ Icc 2 2011 | x k = 1 }, k = 0 := by
        apply sum_eq_zero
        intro k hk
        specialize h2 k (by simp at hk ⊢; omega) (by simp at hk ⊢; omega)
        exact h2.elim
      rw [this] at hb
      replace hb : ∑ k ∈ { k ∈ {1} | x k = 1 }, k = 1 := by simpa using hb
      have h3 : x 1 = 1 := by
        by_contra h3
        have : { k ∈ ({1} : Finset ℕ) | x k = 1 } = ∅ := by
          ext k
          constructor
          . intro hk
            have hk : k = 1 ∧ x k = 1 := by simpa using hk
            obtain ⟨hk1, hk2⟩ := hk; subst hk1; omega
          . simp
        simp [this] at hb
      exact ⟨h3, h2⟩
    split_ands
    . exact hb1.1
    . replace hb : ∀ i ∈ Icc 2 2011, x i = m := by
        intro i hi
        have : ¬ x i < m := by
          intro h
          specialize hb2 i (by simp at hi ⊢; omega)
          replace hb1 := hb1.2 i (by simp at hi ⊢; omega)
          specialize pos_x i
          specialize hb2 (x i) (by simp; omega)
          omega
        specialize hm2 (x i) (by simp at hi ⊢; use i; omega)
        omega
      suffices ∑ i ∈ Icc 2 2011, i = m from by rwa [←this] at hb
      specialize hy' n₀ (by omega)
      have : Icc 1 2011 = Icc 1 1 ∪ Icc 2 2011 := by ext x; simp; omega
      rw [this] at hy'
      have : Disjoint (Icc 1 1) (Icc 2 2011) := by
        intro x h1 h2; intro k hk; specialize h1 hk; specialize h2 hk; simp at h1 h2 ⊢; omega
      rw [sum_union this] at hy'
      replace hy' : ∑ i ∈ Icc 2 2011, i * x i ^ φ n₀ = m * m ^ φ n₀ := by
        simp [hb1.1, ←m_eq_z] at hy'
        linarith
      have : ∑ i ∈ Icc 2 2011, i * x i ^ φ n₀ = ∑ i ∈ Icc 2 2011, i * m ^ φ n₀ := by
        apply sum_congr rfl
        . intro i hi
          specialize hb i hi
          rw [hb]
      rw [this, ←sum_mul] at hy'
      suffices m ^ φ n₀ ≠ 0 from by simpa [this] using hy'
      apply (pow_ne_zero_iff _).mpr _
      . have := hφ (by omega : 0 < n₀); omega
      . omega
