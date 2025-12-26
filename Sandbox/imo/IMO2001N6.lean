import Mathlib

open Finset

/-
Is it possible to find 100 positive integers not exceeding 25,000 such that all pairwise sums of them are different?
-/

theorem number_theory_25086 :
    -- Yes.
    ∃ (S : Finset ℕ) (_ : #S = 100)
    (_ : ∀ x ∈ S, x > 0) (_ : ∀ x ∈ S, x ≤ 25000),
      ∀ i ∈ S, ∀ j ∈ S, ∀ i' ∈ S, ∀ j' ∈ S,
        ({i, j} : Set _) ≠ {i', j'} → i + j ≠ i' + j' := by
  -- The desired result is an immediate consequence of the following fact applied on $p=101$.
  -- Lemma. For any prime number $p ≥ 3$, there exist $p$ nonnegative integers  $ ≤ 2 p^{2}$ with all pairwise sums mutually distinct.
  suffices h1 : ∀ p ≥ 3, Prime p → ∃ (S : Finset ℕ) (_ : #S = p) (_ : ∀ x ∈ S, x ≤ 2 * p ^ 2), ∀ i ∈ S, ∀ j ∈ S, ∀ i' ∈ S, ∀ j' ∈ S,
        ({i, j} : Set ℕ) ≠ {i', j'} → i + j ≠ i' + j' from by
    obtain ⟨S, h2, h3, h4⟩ := h1 101 (by norm_num) (by sorry)
    have h5 : S.Nonempty := by
      apply nonempty_of_ne_empty
      intro h5
      apply_fun (#.) at h5
      conv_rhs at h5 => simp
      omega
    have ⟨h6, h7⟩ := S.isLeast_min' h5
    set m := S.min' h5
    use S \ {m}
    use by rw [card_sdiff (by simpa using h6)]; simp; omega
    use by
      intro x hx
      simp at hx
      specialize h7 hx.left
      omega
    use by
      intro x hx
      simp at hx
      specialize h3 x hx.left
      omega
    intro i hi j hj i' hi' j' hj' h8
    simp at hi hj hi' hj'
    exact h4 _ hi.left _ hj.left _ hi'.left _ hj'.left h8

  -- Proof of the lemma.
  intro p hp2 hp

  -- We claim that the numbers $a_{n}=2 n p+\left(n^{2}\right)$ have the desired property, where $(x)$ denotes the remainder of $x$ upon division by $p$.
  let a n := 2 * n * p + n ^ 2 % p

  -- a is injective as it is a strictly increasing sequence
  have h1 : Set.InjOn a (Icc 1 p) := by
    apply StrictMonoOn.injOn
    intro i hi j hj hij
    simp at hi hj
    dsimp [a]
    suffices (i ^ 2 % p - j ^ 2 % p : ℤ) < 2 * j * p - 2 * i * p from by
      zify
      omega
    have c1 : (i ^ 2 % p - j ^ 2 % p : ℤ) < 2 * p := by
      have d2 : i ^ 2 % p ≥ 0 := by omega
      have d2' : i ^ 2 % p < p := Nat.mod_lt _ (by omega)
      have d3 : j ^ 2 % p ≥ 0 := by omega
      have d3' : j ^ 2 % p < p := Nat.mod_lt _ (by omega)
      zify at d2 d2' d3 d3'
      omega
    have c2 : (2 * j * p - 2 * i * p : ℤ) ≥ 2 * p := calc
      _ = (2 * p) * (j - i : ℤ) := by ring_nf
      _ ≥ (2 * p) * 1 := by gcongr; omega
      _ = _ := by simp
    omega

  use (Icc 1 p).image a
  -- S has 100 elements as a is injective.
  use by simp [card_image_iff.mpr h1]
  use by
    intro x hx
    obtain ⟨i, hi, hi2⟩ := by simpa using hx
    subst hi2
    dsimp [a]
    have d1 : i ^ 2 % p < p := Nat.mod_lt _ (by omega)
    have d2 : i = p ∨ i < p := by omega
    obtain d2 | d2 := d2
    . subst d2
      calc
        _ = 2 * i * i + 0 := by
          congr 1
          apply Nat.dvd_iff_mod_eq_zero.mp
          use i
          ring_nf
        _ ≤ _ := by ring_nf; omega
    . sorry

  -- Suppose that $a_{k}+a_{l}=a_{m}+a_{n}$.
  intro ak hak al hal am ham an han
  obtain ⟨k, hak1, hak2⟩ := by simpa using hak
  obtain ⟨l, hal1, hal2⟩ := by simpa using hal
  obtain ⟨m, ham1, ham2⟩ := by simpa using ham
  obtain ⟨n, han1, han2⟩ := by simpa using han
  clear hak hal ham han
  subst hak2 hal2 ham2 han2
  contrapose!
  intro h2

  -- By the construction of $a_{i}$, we have
  -- $ 2 p(k+l) \leq a_{k}+a_{l} < 2 p(k+l+1) $ and
  -- $ 2 p(m+n) \leq a_{k}+a_{l} < 2 p(m+n+1) $.
  have h3 : 2 * p * (k + l) ≤ a k + a l := by ring_nf; omega
  have h3' : a k + a l < 2 * p * (k + l + 1) := by sorry
  have h4 : 2 * p * (m + n) ≤ a k + a l := by rw [h2]; ring_nf; omega
  have h4' : a k + a l < 2 * p * (m + n + 1) := by sorry

  have h5 : k + l < m + n + 1 := by
    have c1 : 2 * p * (k + l) < 2 * p * (m + n + 1) := by omega
    exact Nat.lt_of_mul_lt_mul_left c1
  have h6 : m + n < k + l + 1 := by
    have c1 : 2 * p * (m + n) < 2 * p * (k + l + 1) := by omega
    exact Nat.lt_of_mul_lt_mul_left c1

  -- Hence we must have $k+l=m+n$,
  have h7 : k + l = m + n := by omega

  -- and therefore also $\left(k^{2}\right)+\left(l^{2}\right)=\left(m^{2}\right)+\left(n^{2}\right)$.
  have h8 : k ^ 2 % p + l ^ 2 % p = m ^ 2 % p + n ^ 2 % p := by
    dsimp [a] at h2
    zify at h2 h7 ⊢
    sorry

  -- Thus $ k+l \equiv m+n \quad \text { and } \quad k^{2}+l^{2} \equiv m^{2}+n^{2} \quad(\bmod p) . $$
  have h9 : (k + l : ZMod p) = m + n := by
    sorry

  have h10 : (k ^ 2 + l ^ 2 : ZMod p) = m ^ 2 + n ^ 2 := by
    sorry

  -- But then it holds that $(k-l)^{2}=2\left(k^{2}+l^{2}\right)-(k+l)^{2} \equiv(m-n)^{2}(\bmod$ $p)$,
  have h11 : ((k - l) ^ 2 : ZMod p) = (m - n) ^ 2 := calc
      _ = (2 * (k ^ 2 + l ^ 2) - (k + l) ^ 2 : ZMod p) := by
        sorry
      _ = _ := by
        sorry

  -- so $k-l \equiv \pm(m-n)$,
  have h12 : (k - l : ZMod p) = m - n ∨ (k - l : ZMod p) = -(m - n) := by
    sorry

  -- which leads to $(k, l)=(m, n)$.
  have h13 : k = m ∧ l = n := by
    obtain h12 | h12 := h12
    . have c1 : ((2 * (k - m) : ℤ) : ZMod p) = 0 := by
        push_cast
        calc
        (_ : ZMod p) = k - l + (k + l) - 2 * m := by ring_nf
        _ = _ := by rw [h9, h12]; ring_nf
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at c1
      rw [Prime.dvd_mul (by sorry)] at c1
      obtain c1 | c1 := c1
      . obtain ⟨q, hq⟩ := c1
        have hq2 := hp2
        zify at hq2
        apply_fun (. * q) at hq2
        swap
        . intro i j hij
          dsimp
          gcongr
          sorry
        dsimp at hq2
        rw [←hq] at hq2
        have : (p : ℤ) * q ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
        omega
      . sorry
    . sorry

  -- This proves the lemma.
  rw [h13.left, h13.right]
