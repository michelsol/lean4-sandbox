import Mathlib

open Finset

-- Examples where using Fin / Subtype makes proofs harder
-- typically situations where the index inside the Fin is moving

  -- Proof is easy
example (n : ℕ) (x : ℕ → ℕ) (hx : ∀ k ∈ Icc 0 n, x k = k) :
    2 * ∑ k ∈ Icc 0 n, x k = n * (n + 1) := by
  induction n
  · simp [hx 0 (by simp)]
  · next n ih =>
    rw [sum_Icc_succ_top (by omega), mul_add]
    specialize ih (by intro k hk; apply hx; simp at hk ⊢; omega)
    rw [ih]
    rw [hx (n + 1) (by simp)]
    ring

-- not so bad using omega
example (n : ℕ) (x : Fin (n + 1) → ℕ) (hx : ∀ k, x k = k.val) : 2 * ∑ k, x k = n * (n + 1) := by
  induction n
  · simpa using hx 0
  · next n ih => calc
      2 * ∑ k, x k = 2 * (∑ k : Fin (n + 1), x ⟨k.1, by omega⟩ + x ⟨n + 1, by omega⟩) := by
        congr 1
        exact Fin.sum_univ_castSucc x
      _ = 2 * ∑ k : Fin (n + 1), x ⟨k.1, by omega⟩ + 2 * x ⟨n + 1, by omega⟩ := by ring
      _ = n * (n + 1) + 2 * (n + 1) := by
        congr 1
        · exact ih _ fun ⟨k, hk⟩ => hx ⟨k, by omega⟩
        · congr 1
          exact hx ⟨n + 1, by omega⟩
      _ = _ := by ring


example (n : ℕ) (x : Icc 0 n → ℕ) (hx : ∀ k, x k = k.val) :
    2 * ∑ k ∈ (Icc 0 n).attach, x k = n * (n + 1) := by
  induction n
  · simp; grind
  · next n ih => calc
      2 * ∑ k ∈ (Icc 0 (n + 1)).attach, x k =
      2 * ∑ ⟨k, hk⟩ ∈ (insert (n + 1) (Icc 0 n)).attach, x ⟨k, by simp at hk ⊢; omega⟩ := by
        congr 1
        apply sum_bij (fun ⟨k, hk⟩ _ => ⟨k, by simp at hk ⊢; omega⟩)
        all_goals try simp; try omega
      _ = 2 * (x ⟨n + 1, by simp⟩ +
        ∑ ⟨k, hk⟩ ∈ (Icc 0 n).attach, x ⟨k, by simp at hk ⊢; omega⟩) := by
          simp
          sorry
      _ = 2 * x ⟨n + 1, by simp⟩ +
        2 * ∑ ⟨k, hk⟩ ∈ (Icc 0 n).attach, x ⟨k, by simp at hk ⊢; omega⟩ := by ring
      _ = 2 * (n + 1) + n * (n + 1) := by
        congr 1
        · congr 1; apply hx
        · apply ih _ fun ⟨k, hk⟩ => hx ⟨k, by simp at hk ⊢; omega⟩
      _ = _ := by ring



example (n : ℕ) : 2 * ∑ ⟨k, hk⟩ : Fin (n + 1), k = n * (n + 1) := by
  calc
    _ = 2 * ∑ k ∈ Ico 0 (n + 1), k := by
      congr 1
      apply Finset.sum_bij (fun ⟨k, hk⟩ _ => k)
      all_goals try simp; try omega
      intro b hb; use ⟨b, by omega⟩
    _ = n * (n + 1) := by
      sorry


theorem Finset.attach_union {α} [DecidableEq α] {s t : Finset α} : (s ∪ t).attach =
    s.attach.image (fun ⟨x, hx⟩ => ⟨x, mem_union_left t hx⟩)
    ∪ t.attach.image (fun ⟨x, hx⟩ => ⟨x, mem_union_right s hx⟩)
    := by ext ⟨k, hk⟩; simpa using hk

theorem Finset.sum_attach_union {α β} [DecidableEq α] [AddCommMonoid β] (s t : Finset α)
    (hs : Disjoint s t) (f : (s ∪ t : Finset α) → β) :
    ∑ x ∈ (s ∪ t).attach, f x =
      ∑ x ∈ s.attach, f ⟨x.1, mem_union_left t x.2⟩ +
      ∑ x ∈ t.attach, f ⟨x.1, mem_union_right s x.2⟩ := by
  rw [attach_union, sum_union]
  · simp [Function.Injective]
  · intro r hr1 hr2 x hx
    obtain ⟨a, ha1, hr1⟩ := by simpa using hr1 hx
    obtain ⟨b, hb1, hr2⟩ := by simpa using hr2 hx
    replace ha1 : {x.1} ⊆ s := by simpa [←hr1] using ha1
    replace hb1 : {x.1} ⊆ t := by simpa [←hr2] using hb1
    specialize hs ha1 hb1
    simp at hs

open Finset in
example (n : ℕ) : 2 * ∑ k : Icc 0 n, k.1 = n * (n + 1) := by
  induction n
  · simp
  · next n ih =>
    calc
      _ = 2 * ∑ k ∈ (Icc 0 (n + 1)).attach, k.1 := rfl
      _ = 2 * ∑ k ∈ (Icc 0 n ∪ {n + 1}).attach, k.1 := by congr! 6 <;> (ext k; simp; omega)
      _ = 2 * (∑ k ∈ (Icc 0 n).attach, k.1 + (n + 1)) := by congr 1; apply sum_attach_union; simp
      _ = 2 * ∑ k ∈ (Icc 0 n).attach, k.1 + 2 * (n + 1) := by ring
      _ = 2 * ∑ k : Icc 0 n, k.1 + 2 * (n + 1) := rfl
      _ = n * (n + 1) + 2 * (n + 1) := by rw [ih]
      _ = _ := by ring

theorem Finset.sum_union' {α β} [DecidableEq α] [AddCommMonoid β] (s t : Finset α)
    (hs : Disjoint s t) (f : (s ∪ t : Finset α) → β) :
    ∑ x : (s ∪ t : Finset _), f x =
      ∑ x : s, f ⟨x.1, mem_union_left t x.2⟩ + ∑ x : t, f ⟨x.1, mem_union_right s x.2⟩ := by
  simpa using sum_attach_union s t hs f

theorem Finset.sum_union'' {α β} [DecidableEq α] [AddCommMonoid β]
    (s t : Set α) [Fintype s] [Fintype t]
    (hs : Disjoint s t) (f : (s ∪ t : Set α) → β) :
    ∑ x : (s ∪ t : Set α), f x = ∑ x : s, f ⟨x.1, by simp⟩ + ∑ x : t, f ⟨x.1, by simp⟩ := by
  calc
    _ = ∑ x : (s.toFinset ∪ t.toFinset : Finset α), f ⟨x.1, by grind⟩ := by
      apply sum_bij (fun x _ => ⟨x.1, by grind⟩) <;> simp
    _ = ∑ x : s.toFinset, f ⟨x.1, by grind⟩ + ∑ x : t.toFinset, f ⟨x.1, by grind⟩ := by
      rw [sum_union']
      exact Set.disjoint_toFinset.mpr hs
    _ = _ := by congr 1 <;> apply sum_bij (fun x _ => ⟨x.1, by grind⟩) <;> simp

-- #eval (∑ x : ({1, 3, 5} : Set ℕ), x.1)

open Finset in
example (n : ℕ) : 2 * ∑ k : Icc 0 n, k.1 = n * (n + 1) := by
  induction n
  · rfl
  · next n ih =>
    calc
      _ = 2 * ∑ k : (Icc 0 n ∪ {n + 1} : Finset _), k.1 := by congr! 6 <;> (ext k; simp; omega)
      _ = 2 * (∑ k : Icc 0 n, k.1 + (n + 1)) := by congr 1; apply sum_union'; simp
      _ = 2 * ∑ k : Icc 0 n, k.1 + 2 * (n + 1) := by ring
      _ = n * (n + 1) + 2 * (n + 1) := by rw [ih]
      _ = _ := by ring

example (n : ℕ) (x : Icc 0 n → ℕ) (hx : ∀ k, x k = k.val) :
    2 * ∑ k ∈ (Icc 0 n).attach, x k = n * (n + 1) := by
  induction n
  · simp; grind
  · next n ih => calc
      2 * ∑ k ∈ (Icc 0 (n + 1)).attach, x k =
      2 * ∑ k ∈ (Icc 0 n ∪ {n + 1}).attach, x ⟨k.1, by grind⟩ := by
        congr 1
        apply sum_bij (fun k _ => ⟨k.1, by grind⟩)
        all_goals try simp; try omega
      _ = 2 * (∑ k ∈ (Icc 0 n).attach, x ⟨k.1, by grind⟩ + x ⟨n + 1, by simp⟩) := by
        congr 1
        rw [sum_attach_union]
        · congr 1
        · simp
      _ = 2 * ∑ k ∈ (Icc 0 n).attach, x ⟨k.1, by grind⟩
        + 2 * x ⟨n + 1, by simp⟩ := by ring
      _ = n * (n + 1) + 2 * (n + 1) := by
        congr 1
        · apply ih _ fun ⟨k, hk⟩ => hx ⟨k, by grind⟩
        · congr 1; apply hx
      _ = _ := by ring
