import Mathlib

open List Finset Real

/-
Let $f$ be a non-constant function from the set of positive integers
into the set of positive integers,
such that $a-b$ divides $f(a)-f(b)$ for all distinct positive integers $a, b$.
Prove that there exist infinitely many primes $p$
such that $p$ divides $f(c)$ for some positive integer $c$.
-/

theorem number_theory_23878
    (f : ℤ → ℤ)
    (b : ℤ) (hb : b > 0)
    (b' : ℤ) (hb' : b' > 0)
    (hf1 : f b ≠ f b')
    (hf2 : ∀ n > 0, f n > 0)
    (hf3 : ∀ a > 0, ∀ b > 0, a ≠ b → a - b ∣ f a - f b) :
    { p : ℤ | p ≥ 0 ∧ Prime p ∧ ∃ c > 0, p ∣ f c }.Infinite := by
  let fintype_of_finite := Fintype.ofFinite

-- Denote by $v_{p}(a)$ the exponent of the prime $p$ in the prime decomposition of $a$.
  let v (p : ℤ) (a : ℤ) := multiplicity p a

-- Assume that there are only finitely many primes $p_{1}, p_{2}, \ldots, p_{m}$
-- that divide some function value produced of $f$.
  by_contra h1
  replace h1 : Finite { p : ℤ | p ≥ 0 ∧ Prime p ∧ ∃ c > 0, p ∣ f c } := by simpa using h1

  let s := { p : ℤ | p ≥ 0 ∧ Prime p ∧ ∃ c > 0, p ∣ f c }.toFinset
  have hs1 : #s ≥ 1 := by
    apply one_le_card.mpr
    have c1 : f b ≠ 1 ∨ f b' ≠ 1 := by omega
    rcases c1 with c1 | c1
    . obtain ⟨p, hp1, hp2⟩ := (f b).exists_prime_and_dvd (by
        have := hf2 b hb
        intro d1
        rw [Int.natAbs_eq_iff] at d1
        omega)
      rw [Int.prime_iff_natAbs_prime, Nat.prime_iff_prime_int, Int.natCast_natAbs] at hp1
      use |p|
      simp [s]
      tauto
    . obtain ⟨p, hp1, hp2⟩ := (f b').exists_prime_and_dvd (by
        have := hf2 b' hb'
        intro d1
        rw [Int.natAbs_eq_iff] at d1
        omega)
      rw [Int.prime_iff_natAbs_prime, Nat.prime_iff_prime_int, Int.natCast_natAbs] at hp1
      use |p|
      simp [s]
      tauto

  let p k := (s.sort (. ≤ .)).getD (k - 1) 0

  have hp1 : s = (Icc 1 #s).image p := by
    symm
    apply eq_of_subset_of_card_le
    . intro x hx
      obtain ⟨k, hk, hk2⟩ : ∃ k, (1 ≤ k ∧ k ≤ #s) ∧ p k = x := by simpa using hx
      subst hk2
      suffices p k ∈ (s.sort (. ≤ .)) from by simpa [s]
      apply mem_iff_get.mpr
      use ⟨k - 1, by simp at hk ⊢; omega⟩
      exact (getD_eq_getElem _ 0 (by simp at hk ⊢; omega)).symm
    . rw [card_image_of_injOn]
      . simp
      . intro i hi j hj hij
        simp at hi hj
        suffices i - 1 = j - 1 from by omega
        have c1 := ((s.sort (. ≤ .)).getElem?_eq_some_getElem_iff (i - 1) (by simp; omega)).mpr trivial
        have c2 := ((s.sort (. ≤ .)).getElem?_eq_some_getElem_iff (j - 1) (by simp; omega)).mpr trivial
        apply (s.sort_nodup (. ≤ .)).getElem_inj_iff.mp
        simpa [p, c1, c2] using hij

  have hp2 : StrictMonoOn p (Icc 1 #s) := by
    intro i hi j hj hij
    simp at hi hj
    dsimp [p]
    have c0 := (s.sort_sorted (. ≤ .))
    have c1 := ((s.sort (. ≤ .)).getElem?_eq_some_getElem_iff (i - 1) (by simp; omega)).mpr trivial
    have c2 := ((s.sort (. ≤ .)).getElem?_eq_some_getElem_iff (j - 1) (by simp; omega)).mpr trivial
    simp only [getD_eq_getElem?_getD, Option.getD_some, c1, c2]
    apply lt_of_le_of_ne
    . exact pairwise_iff_getElem.mp c0 (i - 1) (j - 1) (by simp; omega) (by simp; omega) (by omega)
    . intro h
      have := (s.sort_nodup (. ≤ .)).getElem_inj_iff.mp h
      omega

  have hp3 k (hk : k ∈ Icc 1 #s) : p k ∈ s := by
    simp at hk
    rw [hp1]
    simp only [mem_image, mem_Icc]
    use k

  have hp3' k (hk : k ∈ Icc 1 #s) : p k ≥ 0 := by
    specialize hp3 k hk
    simp [s] at hp3
    tauto

  have hp4 k (hk : k ∈ Icc 1 #s) : Prime (p k) := by
    specialize hp3 k hk
    simp [s] at hp3
    tauto

  have hp5 k (hk : k ∈ Icc 1 #s) : ∃ c > 0, p k ∣ f c := by
    specialize hp3 k hk
    simp [s] at hp3
    tauto

  set m := #s

-- There are infinitely many positive integers $a$ such that $v_{p_{i}}(a)>v_{p_{i}}(f(1))$
-- for all $i=1,2, \ldots, m$,
  have h2 : { a : ℤ | a > 0 ∧ ∀ i ∈ Icc 1 m, v (p i) a > v (p i) (f 1) }.Infinite := by
-- e.g. $a=\left(p_{1} p_{2} \ldots p_{m}\right)^{\alpha}$
-- with $\alpha$ sufficiently large.
    let y1 := (Icc 1 m).image λ i => v (p i) (f 1)
    obtain ⟨c1, c2⟩ : _ ∧ ∀ _, _ := y1.isGreatest_max' (by use v (p 1) (f 1); simp [y1]; use 1)
    let α n := y1.max' (by use v (p 1) (f 1); simp [y1]; use 1) + 1 + n
    have c3 n i (hi : i ∈ Icc 1 m) : α n > v (p i) (f 1) := by
      specialize c2 (v (p i) (f 1)) (by simp [y1]; use i; simp at hi ⊢; omega)
      dsimp only [α]
      omega
    let a n := ∏ i ∈ Icc 1 m, p i ^ α n
    have c4 : a.Injective := by
      intro i j hij
      dsimp [a] at hij
      iterate 2 rw [prod_pow] at hij
      have d1 : α i = α j := by
        have e1 : ∏ i ∈ Icc 1 m, p i > 1 := calc
            ∏ i ∈ Icc 1 m, p i > ∏ i ∈ Icc 1 m, 1 := by
              apply prod_lt_prod_of_nonempty
              . simp
              . intro k hk
                specialize hp4 k hk
                have := hp4.ne_one
                have := hp4.ne_zero
                specialize hp3' k hk
                omega
              . use 1; simp; omega
            _ = 1 := by simp
        generalize ∏ x ∈ Icc 1 m, p x = n at hij e1
        replace hij : (n ^ (α i : ℝ) : ℝ) = (n ^ (α j : ℝ) : ℝ) := by norm_cast
        rify
        generalize (α i : ℝ) = u, (α j : ℝ) = v at hij
        have e2 : (n ^ (u - v) : ℝ) = 1 := by
          rw [Real.rpow_sub (by norm_cast; omega)]
          field_simp [hij]
        suffices u - v = 0 from by linarith
        generalize u - v = k at e2
        rw [rpow_def_of_pos (by norm_cast; omega)] at e2
        rw [exp_eq_one_iff] at e2
        suffices log n > 0 from by
          apply_fun (. / log n) at e2
          field_simp at e2
          simpa
        apply log_pos
        norm_cast
      dsimp [α] at d1
      omega
    apply Set.infinite_of_injective_forall_mem c4
    intro n
    have c5 : a n > 0 := by
      dsimp [a]
      rw [prod_pow]
      apply pow_pos
      apply Finset.prod_pos
      intro i hi
      specialize hp4 i hi
      specialize hp3' i hi
      have := hp4.ne_zero
      omega
    split_ands
    . exact c5
    intro i hi
    have c6 : FiniteMultiplicity (p i) (a n) := by
      . rw [Int.finiteMultiplicity_iff]
        split_ands
        . specialize hp4 i hi
          specialize hp3' i hi
          zify
          simp [abs_of_nonneg hp3', hp4.ne_one]
        . omega
    specialize c3 n i hi
    suffices v (p i) (a n) = α n from by omega
    dsimp [v, a]
    suffices emultiplicity (p i) (a n) = α n from by
      rw [FiniteMultiplicity.emultiplicity_eq_multiplicity] at this
      . norm_cast at this
      . rw [Int.finiteMultiplicity_iff]
        split_ands
        . specialize hp4 i hi
          specialize hp3' i hi
          zify
          simp [abs_of_nonneg hp3', hp4.ne_one]
        . omega
    simp only [emultiplicity_prod (hp4 i hi), emultiplicity_pow (hp4 i hi), ←mul_sum]
    suffices ∑ k ∈ Icc 1 m, emultiplicity (p i) (p k) = 1 from by
      apply_fun ((α n : ℕ∞) * .) at this
      simpa
    calc
      ∑ k ∈ Icc 1 m, emultiplicity (p i) (p k) = ∑ k ∈ Icc 1 m, multiplicity (p i) (p k) := by
        push_cast
        apply sum_congr rfl
        intro j hj
        apply FiniteMultiplicity.emultiplicity_eq_multiplicity
        rw [Int.finiteMultiplicity_iff]
        split_ands
        . specialize hp4 i hi
          specialize hp3' i hi
          zify
          simp [abs_of_nonneg hp3', hp4.ne_one]
        . specialize hp4 j hj
          exact hp4.ne_zero
      _ = 1 := by
        norm_cast
        calc
          _ = ∑ k ∈ Icc 1 m, if k = i then 1 else 0 := by
            apply sum_congr rfl
            intro k hk
            have d1 := hp4 i hi
            have d2 := hp4 k hk
            have d3 := hp3' i hi
            have d4 := hp3' k hk
            split_ifs with hki
            . subst hki
              apply multiplicity_self
            . rw [multiplicity_eq_zero]
              rw [Prime.dvd_prime_iff_associated d1 d2]
              rw [Int.associated_iff_natAbs, Int.natAbs_eq_natAbs_iff]
              suffices p k ≠ p i from by omega
              intro d5
              apply hki
              apply hp2.injOn hk hi d5
          _ = _ := by simp at hi ⊢; omega

  set x1 := { a : ℤ | a > 0 ∧ ∀ i ∈ Icc 1 m, v (p i) a > v (p i) (f 1) }

-- Pick any such $a$.

-- The condition of the problem then yields $a \mid(f(a+1)-f(1))$.
  have h4 a (ha : a ∈ x1) : a ∣ f (a + 1) - f 1 := by
    dsimp [x1] at ha
    specialize hf3 (a + 1) (by omega) 1 (by omega) (by omega)
    simpa using hf3

-- Assume $f(a+1) \neq f(1)$.
-- Then we must have $v_{p_{i}}(f(a+1)) \neq$ $v_{p_{i}}(f(1))$ for at least one $i$.
  have h5 a (ha : a ∈ x1) (ha2 : f (a + 1) ≠ f 1) :
      ∃ i ∈ Icc 1 m, v (p i) (f (a + 1)) ≠ v (p i) (f 1) := by
    by_contra c1
    push_neg at c1
    dsimp [v] at c1
    apply ha2
    sorry

-- We show that $a$ does not divide $f(a+1)-f(1)$.
  have h6 a (ha : a ∈ x1) (ha2 : f (a + 1) ≠ f 1) : ¬a ∣ f (a + 1) - f 1 := by
-- Previous inequality yields $v_{p_{i}}(f(a+1)-f(1))
-- =\min \left\{v_{p_{i}}(f(a+1)), v_{p_{i}}(f(1))\right\} \leq$ $v_{p_{i}}(f(1)) < v_{p_{i}}(a)$.
    obtain ⟨i, hi, c1⟩ := h5 a ha ha2
    have c2 : v (p i) (f (a + 1) - f 1) < v (p i) a := by
      calc
        _ = v (p i) (f (a + 1)) ⊓ v (p i) (f 1) := sorry
        _ ≤ v (p i) (f 1) := by omega
        _ < _ := ha.2 i hi
    intro c3
    dsimp [v] at c2
    have c4 : multiplicity (p i) a ≤ multiplicity (p i) (f (a + 1) - f 1) := by
      have d1 := emultiplicity_le_emultiplicity_of_dvd_right (a := p i) c3
      have d2 : FiniteMultiplicity (p i) a := by
        apply Int.finiteMultiplicity_iff.mpr
        sorry
      have d3 : FiniteMultiplicity (p i) (f (a + 1) - f 1) := by
        apply Int.finiteMultiplicity_iff.mpr
        sorry
      rw [d2.emultiplicity_eq_multiplicity, d3.emultiplicity_eq_multiplicity] at d1
      norm_cast at d1
    omega

-- But this contradicts the fact that $a \mid(f(a+1)-f(1))$.
-- Hence we must have $f(a+1)=f(1)$ for all such $a$.
  have h7 a (ha : a ∈ x1) : f (a + 1) = f 1 := by
    by_contra c1
    apply h6 a ha c1
    exact h4 a ha

-- Now, for any positive integer $b$ and all such $a$,
-- we have $(a+1-b) \mid(f(a+1)-f(b))$
-- i.e., $(a+1-b) \mid(f(1)-f(b))$.
  have h8 b (hb : b > 0) a (ha : a ∈ x1) : a + 1 - b ∣ f 1 - f b := by
    have c1 : a + 1 - b ∣ f (a + 1) - f b := by
      by_cases hb2 : b = a + 1
      . subst hb2; simp
      . dsimp [x1] at ha
        apply hf3 <;> omega
    simpa [h7 a ha] using c1

-- Since this is true for infinitely many positive integers $a$ we must have $f(b)=f(1)$.
  have h9 b (hb : b > 0) : f b = f 1 := by
    suffices f 1 - f b = 0 from by omega
    obtain ⟨a, ha, ha2⟩ := h2.exists_not_mem_finset (Icc 0 (|f 1 - f b| + b - 1))
    replace ha2 : a + 1 - b > |f 1 - f b| := by
      dsimp [x1] at ha
      simp at ha2
      omega
    specialize h8 _ hb a ha
    exact Int.eq_zero_of_abs_lt_dvd h8 ha2

-- Hence $f$ is a constant function, a contradiction.
  have h10 := h9 b hb
  have h11 := h9 b' hb'
  omega
-- Therefore, our initial assumption was false
-- and there are indeed infinitely many primes $p$ dividing $f(c)$ for some positive integer c.
