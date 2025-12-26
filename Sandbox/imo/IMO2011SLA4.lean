import Mathlib

open Set

/-
Determine all pairs $(f, g)$ of functions from the set of positive integers to itself that satisfy
$ f^{g(n)+1}(n) + g^{f (n)}(n) = f (n + 1) - g(n + 1) + 1 $
-/

theorem algebra_24013
    {f g : ℕ → ℕ}
    (f_ge_1 : ∀ n ∈ Ici 1, f n ≥ 1)
    (g_ge_1 : ∀ n ∈ Ici 1, g n ≥ 1)
    : (∀ n ∈ Ici 1, f^[g n + 1] n + g^[f n] n = (f (n + 1) - g (n + 1) : ℤ) + 1)
      ↔ (∀ n ∈ Ici 1, f n = n) ∧ (∀ n ∈ Ici 1, g n = 1) := by
  constructor
  swap
  -- Check that f = n ↦ n and g = n ↦ 1 satisfy the equation
  . intro ⟨h1, h2⟩
    intro n hn
    -- The equation reduces to g^{n}(n) = 1
    suffices g^[n] n = 1 from by
      have := h2 n hn
      have := h2 (n + 1) (by simp)
      have := h1 n hn
      have := h1 (n + 1) (by simp)
      simp [*]
    suffices ∀ k ≥ 1, g^[k] n = 1 from this n hn
    intro k hk
    induction' k, hk using Nat.le_induction with k hk ihk
    . apply h2 n hn
    . specialize h2 1 (by simp)
      simpa [Function.iterate_succ_apply', ihk]
  . intro h
    have f_iter_ge_1 : ∀ n ∈ Ici 1, ∀ k ≥ 1, f^[k] n ≥ 1 := by
      intro n hn k hk
      induction' k, hk using Nat.le_induction with k hk ihk
      . apply f_ge_1; simpa
      . rw [Function.iterate_succ_apply']; apply f_ge_1 _ ihk
    have g_iter_ge_1 : ∀ n ∈ Ici 1, ∀ k ≥ 1, g^[k] n ≥ 1 := by
      intro n hn k hk
      induction' k, hk using Nat.le_induction with k hk ihk
      . apply g_ge_1; simpa
      . rw [Function.iterate_succ_apply']; apply g_ge_1 _ ihk
    -- Show that g can be easily derived from f
    suffices h2 : ∀ n ∈ Ici 1, f n = n from by
      have h2' : ∀ k ≥ 1, ∀ n ∈ Ici 1, f^[k] n = n := by
        intro k _ n hn
        specialize h2 n hn
        exact Function.iterate_fixed h2 k
      split_ands
      . exact h2
      . replace h : ∀ n ∈ Ici 1, g (n + 1) = (2 - g^[n] n : ℤ) := by
          intro n hn
          specialize h n hn
          have : g n + 1 ≥ 1 := by have := g_ge_1 n hn; omega
          simp [h2' (g n + 1) this n hn, h2 n hn, h2 (n + 1) (by simp)] at h
          omega
        intro n (hn : n ≥ 1)
        rcases (show n = 1 ∨ n ≥ 2 from by omega) with hn | hn
        . subst hn
          specialize h 1 (by simp)
          have := g_ge_1 2 (by norm_num)
          have := g_ge_1 1 (by norm_num)
          norm_num at h
          omega
        . specialize h (n - 1) (by simp; omega)
          replace h : g n + g^[n - 1] (n - 1) = 2 := by
            have : n ≥ 1 := by omega
            simp only [this, Nat.sub_add_cancel] at h
            omega
          have hg1 := g_ge_1 n (by simp; omega)
          have hg2 := g_iter_ge_1 (n - 1) (by simp; omega) (n - 1) (by simp; omega)
          omega
    -- Replace the problem's equation with the following inequality ∀ n ≥ 1, f^{g(n) + 1} n < f(n + 1)
    -- which will turn out to be enough to determine f
    replace h : ∀ n ∈ Ici 1, f^[g n + 1] n < f (n + 1) := by
      intro n hn
      specialize h n hn
      have := g_iter_ge_1 n hn (f n) (f_ge_1 n (by simpa))
      have := g_ge_1 (n + 1) (by simp)
      omega
    -- It remains to show that ∀ n ≥ 1, f n = n
    -- It suffices to show that f is strictly increasing
    suffices strictmono_f : StrictMonoOn f (Ici 1) from by
      -- First, we obviously have n ≤ f n
      have n_le_f_n : ∀ n ∈ Ici 1, n ≤ f n := by
        intro n hn
        induction' n, hn using Nat.le_induction with n hn ihn
        . apply f_ge_1 1; norm_num
        . have : n < n + 1 := by omega
          have := strictmono_f hn (by simp) this
          omega
      -- Assume that the result is not true, then there is a n ≥ 1 such that n < f(n)
      by_contra h
      push_neg at h
      obtain ⟨n₀, hn₀, hn₀'⟩ := h
      replace hn₀' : n₀ < f n₀ := by specialize n_le_f_n n₀ hn₀; omega
      -- Let us derive a contradiction by showing f(n₀) < f^{g(n₀) + 1}(n₀) < f(n₀ + 1)
      have h2 : ∀ k ≥ 2, f n₀ < f^[k] n₀ := by
        intro k hk
        induction' k, hk using Nat.le_induction with k hk ihk
        . exact strictmono_f hn₀ (f_ge_1 _ hn₀) hn₀'
        . rw [Function.iterate_succ_apply']
          apply strictmono_f hn₀
          . exact f_iter_ge_1 _ hn₀ _ (by omega)
          . omega
      specialize h n₀ hn₀
      specialize h2 (g n₀ + 1) (by have := g_ge_1 n₀ hn₀; omega)
      rw [Function.iterate_succ_apply'] at h h2
      set j := f^[g n₀] n₀
      have : j ∈ Ici 1 := (f_iter_ge_1 n₀ hn₀ _ (g_ge_1 _ hn₀))
      rw [strictmono_f.lt_iff_lt this (by simp)] at h
      rw [strictmono_f.lt_iff_lt hn₀ this] at h2
      omega
    -- It remains to prove that f is strictly increasing
    -- which follow from ∀ n ≥ 1, f is strictly increasing over {1, ..., n}
    suffices ∀ n ≥ 1, StrictMonoOn f (Icc 1 n) from by
      intro i hi j hj h
      have hi' : i ∈ Icc 1 (j + 1) := by simp at hi ⊢; omega
      have hj' : j ∈ Icc 1 (j + 1) := by simp at hj ⊢; omega
      exact this (j + 1) (by simp) hi' hj' h
    intro n hn
    -- Show that f is strictly increasing over {1, ..., n} by induction on n ≥ 1
    induction' n, hn using Nat.le_induction with n hn ihn
    . simp
    -- Assuming f is strictly increasing over {1, ..., n}
    -- It suffices to show f(n) < f(n + 1)
    . suffices f_lt_succ : f n < f (n + 1) from by
        intro i hi j hj i_lt_j
        have : (i ∈ Icc 1 n ∧ j ∈ Icc 1 n) ∨ (i = n + 1 ∧ j ∈ Icc 1 n)
            ∨  (i ∈ Icc 1 n ∧ j = n + 1) ∨ (i = n + 1 ∧ j = n + 1) := by
          simp at hi hj ⊢; omega
        rcases this with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
        . exact ihn hi hj i_lt_j
        . simp at hj; omega
        . subst hj
          have :=  (ihn.le_iff_le hi (by simp; omega)).mpr hi.2
          omega
        . omega
      -- It remains to show that f(n) < f(n + 1)
      -- Let us call f(k + 1) = min { f i | i ≥ n + 1 }
      have : sInf { f i | i ≥ n + 1 } ∈ { f i | i ≥ n + 1 } := by
        apply Nat.sInf_mem
        use f (n + 1), n + 1
      obtain ⟨k', hkn, fk_def⟩ := this
      let k := k' - 1
      replace hkn : k ≥ n := by omega
      replace fk_def : f (k + 1) = sInf { f i | i ≥ n + 1 } := by
        simpa [k, show k' ≥ 1 from by omega] using fk_def
      -- It suffices to show that f(k) < f(k + 1), as it will turn out that k = n.
      suffices fk_lt : f k < f (k + 1) from by
        have : f k ∉ { f i | i ≥ n + 1 } := by
          rw [fk_def] at fk_lt
          exact Nat.not_mem_of_lt_sInf fk_lt
        replace : ¬k ≥ n + 1 := by intro hk; apply this; use k
        replace : k = n := by omega
        subst this
        assumption
      -- It suffices to show that ∀ j in {0, ..., g k}, f^{g k - j + 1}(k) < f(k+1)
      suffices ∀ j ∈ Icc 0 (g k), f^[g k - j + 1] k < f (k + 1) from by
        specialize this (g k) (by simp)
        simpa
      -- Which we show by induction on j
      intro j hj
      induction' j with j ih
      . specialize h k (by simp; omega)
        simpa
      . replace hj : j + 1 ≤ g k := by simpa using hj
        rw [show g k - (j + 1) + 1 = g k - j from by omega]
        specialize ih (by simp; omega)
        have h2 : f^[g k - j + 1] k ∉ { f i | i ≥ n + 1 } := by
          rw [fk_def] at ih
          exact Nat.not_mem_of_lt_sInf ih
        rw [Function.iterate_succ_apply'] at h2 ih
        replace h2 : ¬f^[g k - j] k ≥ n + 1 := by intro hk; apply h2; use f^[g k - j] k
        replace h2 : f^[g k - j] k ≤ n := by omega
        replace h2 : f^[g k - j] k ∈ Icc 1 n := by
          split_ands
          . apply f_iter_ge_1; simp; omega; omega
          . simpa
        -- As ∀ k ∈ {1, ..., n}, k ≤ f(k), we have f^[g k - j] k ≤ f^[g k - j + 1] k
        -- And f^[g k - j + 1] k < f(k + 1) so we conclude that f^[g k - j] k < f(k + 1)
        have k_le_f_k : ∀ k ∈ Icc 1 n, k ≤ f k := by
          intro k hk
          induction' k, hk.1 using Nat.le_induction with k hk ihk
          . apply f_ge_1 1; norm_num
          . have : k < k + 1 := by omega
            specialize ihk (by simp at hk ⊢; omega)
            have : f k < f (k + 1) := ihn (by simp at hk ⊢; omega) (by simp at hk ⊢; omega) (by omega)
            omega
        specialize k_le_f_k (f^[g k - j] k) h2
        omega
