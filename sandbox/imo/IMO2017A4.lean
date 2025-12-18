import Mathlib

open Finset

/- A sequence of real numbers $ a_{1}, a_{2}, \ldots$  satisfies the relation  $  a_{n}=-\max _{i+j=n}\left(a_{i}+a_{j}\right) \quad \text { for all } n>2017 $
  Prove that this sequence is bounded,
  i.e., there is a constant $ M$  such that $ \left|a_{n}\right| \leqslant M$  for all positive integers $ n$ .
-/

theorem algebra_25036
    {a : ℕ → ℝ}
    (ha : ∀ n (hn : n > 2017), a n = -((Ico 1 n).image λ i ↦ a i + a (n - i)).max' (by simp; omega))
    : ∃ M, ∀ n > 0, |a n| ≤ M := by

-- First we introduce some auxiliary lemmas to talk about argmin's, and argmax's.
-- These lemmas will allow us to extract the indices of maxima or minima in an image set.
  let argmin {α β : Type} [LinearOrder β] (f : α → β) (s : Finset α) (H : s.Nonempty) : α :=
    have h := (image f s).isLeast_min' (by simp [H])
    (Finset.mem_image.mp h.1).choose

  have argmin_mem {α β : Type _} [LinearOrder β] (f : α → β) (s : Finset α) (H : s.Nonempty) :
      argmin f s H ∈ s := by
    have h := (image f s).isLeast_min' (by simp [H])
    exact (Finset.mem_image.mp h.1).choose_spec.1

  have apply_argmin {α β : Type _} [LinearOrder β] (f : α → β) (s : Finset α) (H : s.Nonempty) :
      f (argmin f s H) = (s.image f).min' (by simp [H]) := by
    have h := (image f s).isLeast_min' (by simp [H])
    exact (Finset.mem_image.mp h.1).choose_spec.2

  have apply_argmin_le {α β : Type _} [LinearOrder β] (f : α → β) (s : Finset α) (H : s.Nonempty) :
      ∀ a ∈ s, f (argmin f s H) ≤ f a := by
    have h := (image f s).isLeast_min' (by simp [H])
    simpa [lowerBounds, apply_argmin f s H] using h.2

  let argmax {α β : Type} [LinearOrder β] (f : α → β) (s : Finset α) (H : s.Nonempty) : α :=
    have h := (image f s).isGreatest_max' (by simp [H])
    (Finset.mem_image.mp h.1).choose

  have argmax_mem {α β : Type _} [LinearOrder β] (f : α → β) (s : Finset α) (H : s.Nonempty) :
      argmax f s H ∈ s := by
    have h := (image f s).isGreatest_max' (by simp [H])
    exact (Finset.mem_image.mp h.1).choose_spec.1

  have apply_argmax {α β : Type _} [LinearOrder β] (f : α → β) (s : Finset α) (H : s.Nonempty) :
      f (argmax f s H) = (s.image f).max' (by simp [H]) := by
    have h := (image f s).isGreatest_max' (by simp [H])
    exact (Finset.mem_image.mp h.1).choose_spec.2

  have apply_argmax_le {α β : Type _} [LinearOrder β] (f : α → β) (s : Finset α) (H : s.Nonempty) :
      ∀ a ∈ s, f a ≤ f (argmax f s H) := by
    have h := (image f s).isGreatest_max' (by simp [H])
    simpa [upperBounds, apply_argmax f s H] using h.2


  let ia n := if hn : n > 1 then argmax (λ i ↦ a i + a (n - i)) (Ico 1 n) (by simp; omega) else 0
  let A n := a (ia n) + a (n - ia n)
  have hia0 n (hn : n > 1) : A n = ((Ico 1 n).image λ i ↦ a i + a (n - i)).max' (by simp; omega) := by rw [←apply_argmax _ _ (by simp; omega)]; simp [A, ia, hn]
  have hia1 n (hn : n > 1) : ia n ∈ Ico 1 n := by simpa [ia, hn] using argmax_mem (λ i ↦ a i + a (n - i)) (Ico 1 n) (by simp; omega)
  have hia2 n (hn : n > 1) : ∀ i ∈ Ico 1 n, a i + a (n - i) ≤ A n := by simpa [A, ia, hn] using apply_argmax_le (λ i ↦ a i + a (n - i)) (Ico 1 n) (by simp; omega)
  replace ha n (hn : n > 2017) : a n = -A n := by rw [hia0 n (by omega), ha n hn]

-- Set $ D=2017$ .
  set D := 2017

-- Denote $  M_{n}=\max _{k < n} a_{k} \quad \text { and } \quad m_{n}=-\min _{k < n} a_{k}=\max _{k < n}\left(-a_{k}\right) . $
  let iM n := if hn : n > 1 then argmax a (Ico 1 n) (by simp; omega) else 0
  let M n := a (iM n)
  have hiM0 n (hn : n > 1) : M n = ((Ico 1 n).image a).max' (by simp; omega) := by rw [←apply_argmax _ _ (by simp; omega)]; simp [M, iM, hn]
  have hiM1 n (hn : n > 1) : iM n ∈ Ico 1 n := by simpa [iM, hn] using argmax_mem a (Ico 1 n) (by simp; omega)
  have hiM2 n (hn : n > 1) : ∀ k ∈ Ico 1 n, a k ≤ M n := by simpa [M, iM, hn] using apply_argmax_le a (Ico 1 n) (by simp; omega)
  let im n := if hn : n > 1 then argmin a (Ico 1 n) (by simp; omega) else 0
  let m n := - a (im n)
  have him0 n (hn : n > 1) : m n = -((Ico 1 n).image a).min' (by simp; omega) := by rw [←apply_argmin _ _ (by simp; omega)]; simp [m, im, hn]
  have him1 n (hn : n > 1) : im n ∈ Ico 1 n := by simpa [im, hn] using argmin_mem a (Ico 1 n) (by simp; omega)
  have him2 n (hn : n > 1) : ∀ k ∈ Ico 1 n, -m n ≤ a k := by simpa [m, im, hn] using apply_argmin_le a (Ico 1 n) (by simp; omega)


-- Clearly, the sequences $ \left(m_{n}\right)$  and $ \left(M_{n}\right)$  are nondecreasing.
  have h1 : MonotoneOn m (Set.Ici 1) := by
    sorry
  have h2 : MonotoneOn M (Set.Ici 1) := by
    sorry

-- We need to prove that both are bounded.
  suffices (∃ K > 0, ∀ n > 0, |M n| ≤ K) ∧ ∃ K > 0, ∀ n > 0, |m n| ≤ K from by
    sorry

-- Consider an arbitrary $ n > D$ ;
-- our first aim is to bound $ a_{n}$  in terms of $ m_{n}$  and $ M_{n}$ .

-- (i) There exist indices $ p$  and $ q$  such that $ a_{n}=-\left(a_{p}+a_{q}\right)$  and $ p+q=n$ .
-- Since $ a_{p}, a_{q} \leqslant M_{n}$ , we have $ a_{n} \geqslant-2 M_{n}$ .
  have h3 n (hn : n > D) : a n ≥ -2 * M n := by
    have ⟨p, hp, q, hq, c1, c2⟩ : ∃ p > 0, ∃ q > 0, a n = -(a p + a q) ∧ p + q = n := sorry
    have c3 : a p ≤ M n := hiM2 n (by omega) p (by simp; omega)
    have c4 : a q ≤ M n := hiM2 n (by omega) q (by simp; omega)
    linarith

-- (ii) On the other hand, choose an index $ k < n$  such that $ a_{k}=M_{n}$ .
-- Then, we have $  a_{n}=-\max _{\ell < n}\left(a_{n-\ell}+a_{\ell}\right) \leqslant-\left(a_{n-k}+a_{k}\right)=-a_{n-k}-M_{n} \leqslant m_{n}-M_{n} $
  have h4 n (hn : n > D) : a n ≤ m n - M n := by
    have ⟨k, hk1, hk2⟩ : ∃ k ∈ Ico 1 n, a k = M n := by
      use iM n
      use hiM1 n (by omega)
    calc
      a n ≤ -(a (n - k) + a k) := by
        specialize ha n (by omega)
        specialize hia2 n (by omega) k hk1
        rw [ha]
        linarith only [hia2]
      _ ≤ -a (n - k) - M n := by
        suffices a k ≤ M n by linarith
        exact hiM2 n (by omega) k hk1
      _ ≤ m n - M n := by
        specialize him2 n (by omega) (n - k) (by simp at hk1 ⊢; omega)
        gcongr
        linarith only [him2]

-- Summarizing (i) and (ii), $  -2 M_{n} \leqslant a_{n} \leqslant m_{n}-M_{n}, $
-- whence $  m_{n} \leqslant m_{n+1} \leqslant \max \left\{m_{n}, 2 M_{n}\right\} \quad \text { and } \quad M_{n} \leqslant M_{n+1} \leqslant \max \left\{M_{n}, m_{n}-M_{n}\right\} $   (1)
  have h5 n (hn : n > D) : m n ≤ m (n + 1) := sorry
  have h5' n (hn : n > D) : m (n + 1) ≤ m n ⊔ (2 * M n) := sorry
  have h6 n (hn : n > D) : M n ≤ M (n + 1) := sorry
  have h6' n (hn : n > D) : M (n + 1) ≤ M n ⊔ (m n - M n) := sorry

-- Now, say that an index $ n > D$  is lucky if $ m_{n} \leqslant 2 M_{n}$ .
-- Two cases are possible: There is a lucky index, or there is no lucky index.
-- Case 1. Assume that there exists a lucky index $ n$ .
  by_cases h7 : ∃ n > D, m n ≤ 2 * M n
  . obtain ⟨n, hn, hn'⟩ := h7
    replace h7 : ∀ k ≥ n, m k ≤ 2 * M k ∧ M k = M n := by
      apply Nat.le_induction
      . simpa using hn'
      . intro n hn ⟨ih1, ih2⟩
    -- In this case we will show by induction, that all indices $ k > n$  are also lucky and $ M_k = M_n $.
    -- (1) yields $ m_{n+1} \leqslant 2 M_{n}$
        have h8 : m (n + 1) ≤ 2 * M n := by
          specialize h5' n (by omega)
          have c1 : m n ⊔ 2 * M n ≤ 2 * M n := by apply sup_le ih1 (by simp)
          linarith

    -- and (1) yields $ M_{n} \leqslant M_{n+1} \leqslant M_{n}$ .
        have h9 : M n ≤ M (n + 1) := h6 n (by omega)

        have h9' : M (n + 1) ≤ M n := by
          specialize h6' n (by omega)
          sorry

    -- Therefore, $ M_{n+1}=M_{n}$  and $ m_{n+1} \leqslant 2 M_{n}=2 M_{n+1}$ .
        have h10 : M (n + 1) = M n := by linarith

        have h11 : m (n + 1) ≤ 2 * M (n + 1) := by
          sorry
    -- So, the index $ n+1$  is also lucky, and $ M_{n+1}=M_{n}$ .
        simpa [h10, ih2] using h11

-- Thus, all of the $ m_{k}$  and $ M_{k}$  are bounded by $ 2 M_{n}$ .
    sorry
-- Case 2. Assume now that there is no lucky index, i.e., $ 2 M_{n} < m_{n}$  for all $ n > D$ .
  . replace h7 n (hn : n > D) : 2 * M n < m n := by push_neg at h7; exact h7 n hn

-- Then (1) shows that for all $ n > D$  we have $ m_{n} \leqslant m_{n+1} \leqslant m_{n}$ ,
    have h8 n (hn : n > D) : m n ≤ m (n + 1) := by
      sorry
    have h8' n (hn : n > D) : m (n + 1) ≤ m n := by
      sorry

-- so $ m_{n}=m_{D+1}$  for all $ n > D$ .
    have h9 n (hn : n > D) : m n = m (D + 1) := by
      revert n
      apply Nat.le_induction
      . simp
      . intro n hn ih
        specialize h8 n hn
        specialize h8' n hn
        linarith

-- Since $ M_{n} < m_{n} / 2$  for all such indices,
    have h10 n (hn : n > D) : M n < m n / 2 := by
      sorry

-- all of the $ m_{n}$  and $ M_{n}$  are bounded by $ m_{D+1}$ .
    have h11 n (hn : n > D) : |m n| ≤ m (D + 1) := by
      sorry

    have h12 n (hn : n > D) : |M n| ≤ m (D + 1) := by
      sorry

-- Thus, in both cases the sequences $ \left(m_{n}\right)$  and $ \left(M_{n}\right)$  are bounded, as desired.
    have h13 : ∃ K > 0, ∀ n > 0, |m n| ≤ K := by
      let K := ((Icc 1 (D + 1)).image |m|).max' (by simp)
      sorry

    have h14 : ∃ K > 0, ∀ n > 0, |M n| ≤ K := by
      let K := ((Icc 1 (D + 1)).image |M|).max' (by simp)
      sorry

    exact ⟨h14, h13⟩
