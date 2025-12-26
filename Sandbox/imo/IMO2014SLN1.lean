import Mathlib

open Finset

/-
Let $n ≥ 2$ be an integer, and let $A_n$ be the set $$A_n = \{2^n - 2^k | k ∈ ℤ, 0 ≤ k < n\}$$
Determine the largest positive integer that cannot be written as the sum
of one or more (not necessarily distinct) elements of $A_n$.
-/

theorem number_theory_24536 (n : ℕ) (n_ge_2 : n ≥ 2) :
    let R := {x : ℤ | x > 0 ∧ ∃ (t : ℕ) (l : ℕ → ℕ) (_ : ∀ i < t, 0 ≤ l i ∧ l i < n),
      ∑ i < t, (2 ^ n - 2 ^ l i : ℤ) = x}
    IsGreatest Rᶜ ((n - 2) * 2 ^ n + 1) := by
  intro R
  constructor
  -- First we show that every integer greater than $(n-2)2^n + 1$ can be represented
  -- as such a sum. This is achieved by induction on $n$.
  swap
  . revert n
    apply Nat.le_induction
    -- For $n=2$, the set $A_n$ consists of the two elements $2$ and $3$.
    -- Every positive integer $m$ except for $1$ can be represented as the sum of elements of
    -- $A_n$ in this case: as $m=2+2+...+2$ if $m$ is even, and as $m=3+2+2+...+2$ if $m$ is odd.
    . dsimp [upperBounds]
      intro m
      contrapose!
      intro m_gt_1
      have m_gt_0 : m > 0 := by omega
      simp only [Set.mem_compl_iff]; push_neg; dsimp
      split_ands; omega
      obtain ⟨m', hm'⟩ := Int.even_or_odd' m
      have m'_ge_0 : m' ≥ 0 := by omega
      rcases hm' with hm' | hm'
      . use m'.toNat
        use λ _ => 1
        use by intro k hk; omega
        simp [m'_ge_0]
        omega
      . use m'.toNat
        use λ i => if i = 0 then 0 else 1
        use by intro k hk; by_cases hk' : k = 0 <;> simp [hk']
        have : (Iio m'.toNat).filter (. = 0) = {0} := by ext i; simp; omega
        have : (Iio m'.toNat).filter (¬. = 0) = Ioo 0 m'.toNat := by ext i; simp; omega
        have : m' ≥ 1 := by omega
        simp [sum_ite, *]
        omega
    -- Now consider some $n≥2$, and take an integer $m>(n-1)2^(n+1)+1$.
    . intro n n_ge_2 ihn
      dsimp [upperBounds] at ihn ⊢
      replace ihn : ∀ m : ℤ, (n - 2) * 2 ^ n + 1 < m →
          m > 0 ∧ ∃ (t : ℕ) (l : ℕ → ℕ) (_ : ∀ i < t, 0 ≤ l i ∧ l i < n),
            ∑ i < t, (2 ^ n - 2 ^ l i : ℤ) = m := by
        intro m; contrapose; intro h; specialize ihn h; omega
      intro m
      contrapose!
      intro hm
      have m_gt_0 : m > 0 := by
        push_cast at hm
        calc
          m > _ := hm
          _ ≥ 0 * 0 + 1 := by
            gcongr
            . omega
            . omega
            . norm_cast; exact Nat.zero_le ..
          _ ≥ _ := by norm_num
      simp only [Set.mem_compl_iff]; push_neg; dsimp
      split_ands; omega
      obtain ⟨m', hm'⟩ := Int.even_or_odd' m
      rcases hm' with hm' | hm'
      -- If $m$ is even, then consider
      -- $$\dfrac{m}{2} \ge \dfrac{(n-1)2^{n+1}+2}{2}=(n-1)2^n+1>(n-2)2^n+1$$.
      -- By the induction hypothesis, there is a representation of the form
      -- $$\dfrac{m}{2}=(2^n-2^{l_1})+(2^n-2^{l_2})+...+(2^n-2^{l_t})$$.
      -- Multiplying by $2$ shows that $m$ has a representation as a sum of terms in $A_{n+1}$.
      . specialize ihn m' ?_
        . qify at hm ⊢
          have : n + 1 ≥ 2 := by omega
          have : n ≥ 1 := by omega
          push_cast [*] at hm ⊢
          calc
          _ ≥ (((n - 1) * 2 ^ (n + 1) + 2) / 2 : ℚ) := by cancel_denoms; norm_cast at hm ⊢
          _ = (n - 1) * 2 ^ n + 1 := by ring_nf
          _ > _ := by gcongr; norm_num
        obtain ⟨m'_pos, t, l, l_subset, hl⟩ := ihn
        use t
        use λ i => l i + 1
        use by
          intro k hk
          specialize l_subset _ hk
          omega
        push_cast [hm']
        rw [←hl, mul_sum]
        rw [sum_congr rfl]
        intro i hi
        omega
      -- If $m$ is odd, we consider $\dfrac{m-(2^n-1)}{2}>(n-2)2^n+1$.
      -- By the induction hypothesis, there is a representation for $\dfrac{m-(2^n-1)}{2}$.
      -- We multiply that representation by $2$ and add $2^n-1$ to show that $m$ again
      -- has the desired representation as a sum of terms in $A_{n+1}$.
      . specialize ihn (m' + 1 - 2 ^ n) ?_
        . push_cast at hm ⊢
          rw [hm'] at hm
          have : m' + 1 ≥ 2 ^ n := by
            replace hm : (n - 1) * 2 ^ (n + 1) ≤ (2 * m' : ℤ) := by
              ring_nf at hm ⊢; omega
            suffices 2 ^ (n + 1) ≤ 2 * m' from by  omega
            calc
              _ = 1 * 2 ^ (n + 1) := by omega
              _ ≤ (n - 1 : ℤ) * 2 ^ (n + 1) := by gcongr; omega
              _ ≤ _ := hm
          ring_nf at hm ⊢
          omega
        obtain ⟨m'_pos, t, l, l_subset, hl⟩ := ihn
        use t + 1
        use λ i => if i = t then 0 else l i + 1
        use by
          intro k hk
          split_ifs with hkt
          . omega
          . replace hk : k < t := by omega
            specialize l_subset _ hk
            omega
        have : (Iio (t + 1)).filter (. = t) = {t} := by ext i; simp; omega
        have : (Iio (t + 1)).filter (¬. = t) = Iio t := by ext i; simp; omega
        simp [sum_ite, *]
        ring_nf
        apply congrArg (2 * .) at hl
        simp [mul_sum, Int.mul_sub] at hl
        have : m' + 1 ≥ 2 ^ n := by
          push_cast [hm'] at hm
          suffices 2 * (m' + 1) ≥ 2 * 2 ^ n from Int.le_of_mul_le_mul_left this (by norm_num)
          calc
            _ ≥ 2 * m' + 1 := by omega
            _ ≥ (n + 1 - 2 : ℤ) * 2 ^ (n + 1) := by omega
            _ ≥ 1 * 2 ^ (n + 1) := by
              gcongr; omega
            _ = _ := by ring_nf
        ring_nf at hl
        rw [hl]
        omega
  -- It remains to show that there is no representation for $(n-1)2^{n+1}+1$.
  -- Let $N$ be the smallest positive integer that satisfies
  -- $N \equiv 1 \mod n$ and that can be represented as a sum of elements of $A_n$.
  . let S := {x ∈ R | x ≡ 1 [ZMOD 2 ^ n]}
    let N := sInf S
    have bddbelow_s : ∀ x ∈ S, 0 ≤ x := by intro x hx; have := hx.1.1; omega
    have nonempty_s : ∃ x, x ∈ S := by
      use (2 ^ n - 1) * (2 ^ n - 1)
      split_ands
      . suffices (2 ^ n - 1 : ℤ) > 0 from Int.mul_pos this this
        suffices (2 ^ n : ℤ) ≥ 2 ^ 2 from by omega
        norm_cast
        exact Nat.pow_le_pow_of_le_right (by norm_num) n_ge_2
      . dsimp [R]
        use 2 ^ n - 1
        use λ _ => 0
        use by intro k hk; omega
        simp
      . have : 2 ^ n ≡ 0 [ZMOD 2 ^ n] := by rw [Int.modEq_zero_iff_dvd]
        have : 2 ^ n - 1 ≡ -1 [ZMOD 2 ^ n] := Int.ModEq.sub this rfl
        have : (2 ^ n - 1) * (2 ^ n - 1) ≡ 1 [ZMOD 2 ^ n] := Int.ModEq.mul this this
        simpa
    have N_le : ∀ x ∈ S, N ≤ x  := by
      classical
      dsimp [N]
      rw [Int.csInf_eq_least_of_bdd _ bddbelow_s nonempty_s]
      exact (Int.leastOfBdd _ bddbelow_s nonempty_s).2.2
    have N_mem : N ∈ S  := by
      classical
      dsimp [N]
      rw [Int.csInf_eq_least_of_bdd _ bddbelow_s nonempty_s]
      exact (Int.leastOfBdd _ bddbelow_s nonempty_s).2.1
    -- To conclude it suffices to show that $N = (n - 1)2^n + 1$
    suffices (n - 2 : ℤ) * 2 ^ n + 1 ∉ S from by
      suffices h : (n - 2 : ℤ) * 2 ^ n + 1 ≡ 1 [ZMOD 2 ^ n] from by simpa [S, R, h]
      replace : 2 ^ n ≡ 0 [ZMOD 2 ^ n] := by rw [Int.modEq_zero_iff_dvd]
      replace : (n - 2) * 2 ^ n ≡ (n - 2) * 0 [ZMOD 2 ^ n] := Int.ModEq.mul_left _ this
      replace : (n - 2) * 2 ^ n ≡ 0 [ZMOD 2 ^ n] := by ring_nf at this ⊢; assumption
      replace : (n - 2) * 2 ^ n + 1 ≡ 0 + 1 [ZMOD 2 ^ n] := Int.ModEq.add this rfl
      exact this
    suffices N = (n - 1) * 2 ^ n + 1 from by
      intro h
      specialize N_le _ h
      rw [this] at N_le
      replace N_le : (n - 1 : ℤ) * 2 ^ n ≤ (n - 2) * 2 ^ n := by omega
      replace N_le : (n - 1 : ℤ) ≤ n - 2 := Int.le_of_mul_le_mul_right N_le
        (by norm_cast; exact Nat.two_pow_pos n)
      omega
    -- Consider a representation $N=(2^n-2^{l_1})+(2^n-2^{l_2})+...+(2^n-2^{l_t})$ with
    -- $0 \le l_1, l_2, ..., l_t \lt n$.
    obtain ⟨N_pos, t, l, l_subset, hl⟩ := N_mem.1
    -- We show that the $l_i$'s are distinct by contradiction.
    -- Suppose $l_i=l_j=k$ with $i \ne j$. Replace the two terms by
    -- $2^n-2^{k+1}\in A_n$ to get a representation for $N-2(2^n - 2^k) + (2^n-2^{k+1})=N-2^n$.
    -- This is a contradiction as $N$ is supposed to be minimal.
    have inj_l : Set.InjOn l (Iio t) := by
      by_contra h
      dsimp [Set.InjOn] at h
      push_neg at h
      obtain ⟨i, i_lt, j, j_lt, li_eq_lj, i_ne_j⟩ := h
      let k := l i
      have hki : l i = k := by omega
      have hkj : l j = k := by omega
      have : {i, j} ⊆ Iio t := by intro x hx; simp at hx i_lt j_lt ⊢; omega
      rw [←sum_sdiff this] at hl
      rw [sum_pair i_ne_j] at hl
      rw [hki, hkj] at hl
      replace hl : N - 2 ^ n = ∑ x ∈ Iio t \ {i, j}, (2 ^ n - 2 ^ l x) + (2 ^ n - 2 ^ (k + 1)) := by
        omega
      have : N - 2 ^ n ∉ S := by
        intro hs
        specialize N_le _ hs
        have : 2 ^ n ≥ 2 ^ 2 := Nat.pow_le_pow_of_le_right (by norm_num) n_ge_2
        linarith
      apply this
      split_ands
      . rw [hl]
        sorry
      . rw [hl]
        sorry
      . have h1 := N_mem.2
        sorry
    -- $2^{l_1} + ... + 2^{l_t} = t2^n - N \equiv N \equiv -1 \equiv 2^n-1 \mod 2^n$
    -- Furthermore $2^{l_1} + ... + 2^{l_t} \le 2^0 +2^1+...+2^{n-1}=2^n-1<2^n$
    replace hl : ∑ i < t, 2 ^ l i = (t * 2 ^ n - N : ℤ) := by simp at hl; omega
    have h1 : 2 ^ n ≡ 0 [ZMOD 2 ^ n] := by rw [Int.modEq_zero_iff_dvd]
    replace h1 : t * 2 ^ n ≡ 0 [ZMOD 2 ^ n] := Int.ModEq.mul_left t h1
    replace h1 : t * 2 ^ n - N ≡ 0 - N [ZMOD 2 ^ n] := Int.ModEq.sub h1 rfl
    replace h1 : t * 2 ^ n - N ≡ -N [ZMOD 2 ^ n] := by simpa using h1
    replace h1 : t * 2 ^ n - N ≡ -1 [ZMOD 2 ^ n] := by
      have : -N ≡ -1 [ZMOD 2 ^ n] := Int.neg_modEq_neg.mpr N_mem.2
      exact h1.trans this
    replace h1 : ∑ i < t, 2 ^ l i ≡ -1 [ZMOD 2 ^ n] := by rwa [hl]
    replace h1 : ∑ i < t, 2 ^ l i ≡ 2 ^ n - 1 [ZMOD 2 ^ n] := by
      have : -1 ≡ -1 + 2 ^ n [ZMOD 2 ^ n] := Int.ModEq.symm Int.add_modEq_right
      replace : -1 ≡ 2 ^ n - 1 [ZMOD 2 ^ n] := by ring_nf at this ⊢; assumption
      exact Int.ModEq.trans h1 this
    have h2 : ∑ i < t, 2 ^ l i ≤ (2 ^ n : ℤ) := calc
      _ = ∑ k ∈ (Iio t).image l, 2 ^ k := by rw [sum_image inj_l]
      _ ≤ ∑ k ∈ Ico 0 n, (2 ^ k : ℤ) := by
        norm_cast
        suffices (Iio t).image l ⊆ Ico 0 n from sum_le_sum_of_ne_zero fun x a _ => this a
        intro k hk
        have : ∃ i < t, l i = k := by simpa using hk
        obtain ⟨i, hi1, hi2⟩ := this
        specialize l_subset _ hi1
        simp; omega
      _ = 2 ^ n - 1 := by
        qify
        rw [geom_sum_Ico (by norm_num) (by omega)]
        ring_nf
      _ ≤ _ := by omega
    -- Therefore $2^{l_1} + ... + 2^{l_t}=2^n-1$
    replace h2 : ∑ i < t, 2 ^ l i = (2 ^ n - 1 : ℤ) := sorry
    -- This is only possible if each element of $\{0,1,...,n-1\}$ occurs as one of the $l_i$'s.
    -- This gives us $N=n2^n-(2^0+2^1+...+2^{n-1})=(n-1)2^n+1$
    replace hl : N = (t * 2 ^ n - ∑ i < t, (2 ^ l i) : ℤ) := by omega
    replace hl : N = ((t - 1) * 2 ^ n + 1 : ℤ) := by rw [h2] at hl; ring_nf; omega
    suffices t = n from by rwa [this] at hl
    have : (2 ^ n - 1 : ℤ) = (∑ k ∈ Ico 0 n, 2 ^ k) := by
      qify; rw [geom_sum_Ico (by norm_num) (by omega)]; ring_nf
    rw [this] at h2
    norm_cast at h2
    rw [←sum_image inj_l] at h2
    suffices (Iio t).image l = Ico 0 n from by
      apply congrArg card at this
      simpa [card_image_of_injOn inj_l]
    have h3 : (Iio t).image l ⊆ Ico 0 n := by
      intro k hk
      have : ∃ i < t, l i = k := by simpa using hk
      obtain ⟨i, hi1, hi2⟩ := this
      specialize l_subset _ hi1
      simp; omega
    generalize (Iio t).image l = a at h2 h3
    generalize Ico 0 n = b at h2 h3
    rw [←sum_sdiff h3] at h2
    replace h2 : ∑ x ∈ b \ a, 2 ^ x = 0 := by omega
    replace h2 : b ⊆ a := by simpa using h2
    exact Subset.antisymm h3 h2
