import Mathlib

theorem Nat.nth_surjOn {p : ℕ → Prop} (hs : (setOf p).Finite) :
    Set.SurjOn (Nat.nth p) (Set.Ico 0 (setOf p).ncard) (setOf p) := by
  convert_to Set.SurjOn (Nat.nth (setOf p)) (Finset.Ico 0 (setOf p).ncard) hs.toFinset using 1
  · exact Eq.symm (Finset.coe_Ico 0 (setOf p).ncard)
  · exact Eq.symm (Set.Finite.coe_toFinset hs)
  apply Finset.surjOn_of_injOn_of_card_le
  · intro k hk
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    apply Nat.nth_mem
    intro hf
    simp at hk
    convert hk using 1
    rw [Set.ncard_eq_toFinset_card (setOf p) hf]
  · convert Nat.nth_injOn hs using 1
    · simp [Set.ncard_eq_toFinset_card (setOf p) hs]
  · simp [Set.ncard_eq_toFinset_card (setOf p) hs]

def Tuple α := Σ n, Fin n → α

namespace Tuple

def empty α : Tuple α := ⟨0, (nomatch ·)⟩

def length {α} (t : Tuple α) := t.1

def toFun {α} (t : Tuple α) : Fin t.length → α := t.2

@[ext (iff := false)] protected theorem ext {α} {t s : Tuple α}
    (h1 : t.length = s.length) (h2 : ∀ k, t.toFun k = s.toFun ⟨k.1, h1 ▸ k.2⟩) : t = s := by
  obtain ⟨n, f⟩ := t
  obtain ⟨m, g⟩ := s
  apply Sigma.ext
  · simpa using h1
  · rw [Fin.heq_fun_iff]
    · simpa [toFun, length] using h2
    · simpa using h1

theorem eq_empty_of_length_zero {α} (t : Tuple α) (h : t.length = 0) : t = empty α := by
  obtain ⟨k, f⟩ := t
  convert_to k = 0 using 1 at h
  subst h
  ext ⟨k, hk⟩
  · simp [length, empty]
  · simp [length] at hk

def append {α} (t1 t2 : Tuple α) : Tuple α :=
  ⟨t1.length + t2.length, fun i =>
    if h : i < t1.length then t1.toFun ⟨i, h⟩ else t2.toFun ⟨i - t1.length, by omega⟩⟩

@[simp]
theorem append_empty {α} (t : Tuple α) : append t (empty α) = t := by
  obtain ⟨n, f⟩ := t
  simp [append, empty, length, toFun]

@[simp]
theorem length_append {α} (t1 t2 : Tuple α) : length (append t1 t2) = length t1 + length t2 := by
  simp [append, length, toFun]

theorem append_assoc {α} (t1 t2 t3 : Tuple α) :
    append (append t1 t2) t3 = append t1 (append t2 t3) := by
  ext ⟨k, hk⟩
  · simp
    omega
  · simp [append, toFun, length]
    grind

def reverse {α} (t : Tuple α) : Tuple α :=
  ⟨t.length, fun i => t.toFun ⟨t.length - 1 - i, by omega⟩⟩

theorem reverse_reverse {α} (t : Tuple α) : reverse (reverse t) = t := by
  ext ⟨k, hk⟩
  · simp [reverse, toFun, length]
  · simp [reverse, toFun, length]
    simp [reverse, length] at hk
    grind

theorem length_reverse {α} (t : Tuple α) : length (reverse t) = length t := by
  simp [reverse, length]

def Mem {α} (x : α) (t : Tuple α) : Prop := ∃ i, t.toFun i = x

instance {α} : Membership α (Tuple α) where
  mem x t := Mem t x

def take {α} (t : Tuple α) (n : ℕ) (hn : n ≤ t.length) : Tuple α :=
  ⟨n, fun ⟨i, hi⟩ => t.toFun ⟨i, by omega⟩⟩

def drop {α} (t : Tuple α) (n : ℕ) (hn : n ≤ t.length) : Tuple α :=
  ⟨t.length - n, fun ⟨i, hi⟩ => t.toFun ⟨i + n, by omega⟩⟩

theorem append_take_drop {α} (t : Tuple α) (n : ℕ) (hn : n ≤ t.length) :
    append (take t n hn) (drop t n hn) = t := by
  ext ⟨k, hk⟩
  · simp [length] at hn
    simp [take, drop, append, toFun, length]
    omega
  · simp [take, drop, append, length] at hk
    simp [take, drop, append, toFun, length]
    grind


theorem take_append {α} (t1 t2 : Tuple α) (n : ℕ) (hn : n ≤ t1.length + t2.length) :
    take (append t1 t2) n hn =
      append (take t1 (min n t1.length) (by omega)) (take t2 (n - t1.length) (by omega)) := by
  ext ⟨k, hk⟩
  · simp [length] at hn
    simp [take, append, toFun, length]
    omega
  · simp [take, append, length] at hk
    simp [take, append, toFun, length]
    grind

theorem mem_append {α} (x : α) (t1 t2 : Tuple α) :
    x ∈ append t1 t2 ↔ x ∈ t1 ∨ x ∈ t2 := by
  constructor
  · intro ⟨⟨i, hi⟩, h1⟩
    simp [append, length, toFun] at h1 hi
    split_ifs at h1 with h2
    · left
      use ⟨i, h2⟩, h1
    · right
      use ⟨i - t1.length, by unfold length; omega⟩, h1
  · intro h1
    obtain ⟨⟨i, hi⟩, h1⟩ | ⟨⟨i, hi⟩, h1⟩ := h1
    · use ⟨i, by simp; omega⟩
      simpa [append, toFun, hi] using h1
    · use ⟨i + t1.length, by simp; omega⟩
      simpa [append, toFun] using h1


def natPred {α} (p : α → Prop) [DecidablePred p] (t : Tuple α) (k : ℕ) : Prop :=
  if hk : k < t.length then p (t.toFun ⟨k, hk⟩) else False

noncomputable def countP {α} (p : α → Prop) [DecidablePred p] (t : Tuple α) : ℕ :=
  (setOf (natPred p t)).ncard

theorem natPred_nth {α} (p : α → Prop) [DecidablePred p] (t : Tuple α)
    (k : ℕ) (hk : k < countP p t) : (natPred p t) (Nat.nth (natPred p t) k) := by
  apply Nat.nth_mem k
  intro hf
  rw [←Set.ncard_eq_toFinset_card (setOf (natPred p t)) hf]
  exact hk

noncomputable def filter {α} (p : α → Prop) [DecidablePred p] (t : Tuple α) : Tuple α :=
  ⟨countP p t, fun ⟨i, hi⟩ => t.toFun ⟨Nat.nth (natPred p t) i, by
    have h1 : dite .. := natPred_nth p t i hi
    split_ifs at h1 with h2
    exact h2⟩⟩

theorem mem_filter {α} (p : α → Prop) [DecidablePred p] (x : α) (t : Tuple α) :
    x ∈ filter p t ↔ x ∈ t ∧ p x := by
  constructor
  · intro ⟨⟨i, hi⟩, h0⟩
    have h1 : dite .. := natPred_nth p t i hi
    split_ifs at h1 with h2
    constructor
    · use ⟨Nat.nth (natPred p t) i, h2⟩
      exact h0
    · convert h1 using 1
      exact h0.symm
  · intro ⟨⟨⟨i, hi⟩, h1⟩, h2⟩
    subst h1
    have h3 : (setOf (natPred p t)).Finite := (by
      apply Set.Finite.subset (by apply (Finset.Ico 0 t.length).finite_toSet)
      intro k (hk : dite ..)
      split_ifs at hk with hk2
      simpa using hk2)
    have h4 : Set.SurjOn (Nat.nth (natPred p t))
        (Finset.Ico 0 (countP p t)) (setOf (natPred p t)) := by
      convert Nat.nth_surjOn h3 using 1
      ext k
      simp
      rfl
    have h5 : i ∈ setOf (natPred p t) := by change dite ..; split_ifs; exact h2
    obtain ⟨j, h6, h7⟩ := h4 h5
    use ⟨j, by simpa using h6⟩
    simp [filter, toFun, h7]

end Tuple
