import Mathlib

def hello := "world"

variable {α : Type _} [AddCommMonoid α]

def sum : List α → α
  | [] => 0
  | x :: xs => x + sum xs

def sum2 (l : List α) : α := Id.run <| do
    let mut s := 0
    for x in l do
      s := s + x
    return s

example (l : List α) : sum2 l = sum l := by
  convert_to l.foldl (· + ·) 0 = sum l
  · simp [sum2]
  induction l
  · simp [sum]
  · next n l ih => simp [l.foldl_eq_of_comm_of_assoc, ih, sum]
#exit
def sum3 (l : List α) : α := ∑ i ∈ Finset.Ico 0 l.length, l.getD i 0

open Finset in
example (l : List α) : sum3 l = sum l := by
  unfold sum3
  induction' l with n l ih
  · simp [sum]
  · calc
      _ = ∑ i ∈ Ico 0 (l.length + 1), (n :: l).getD i 0 := by rfl
      _ = ∑ i ∈ Ico (0 + 1) (l.length + 1), (n :: l).getD i 0 + n := by
        have h1 : {0} ⊆ Ico 0 (l.length + 1) := by intro k; simp; omega
        rw [←sum_sdiff h1]
        congr 1
        simp
      _ = ∑ i ∈ Ico 0 l.length, (n :: l).getD (i + 1) 0 + n := by
        rw [←sum_nbij (· + 1)]
        · simp
        · simp
        · intro y hy
          simp only [Set.mem_image]
          use y - 1
          simp at hy ⊢
          omega
        · simp
      _ = ∑ i ∈ Ico 0 l.length, l.getD i 0 + n := by congr 1
      _ = _ := by rw [ih, add_comm, sum]


theorem List.length_erase_lt_of_minimum_eq_some {α} [LinearOrder α] {l : List α} {a : α}
    (hm : l.minimum = some a) : (l.erase a).length < l.length := by
  rw [length_erase_of_mem]
  · suffices l.length > 0 by simpa using this
    apply length_pos_iff_exists_mem.mpr
    use a
    exact minimum_mem hm
  · exact minimum_mem hm


def List.selection_sort {α} [LinearOrder α] (l : List α) : List α :=
  match hm : l.minimum with
  | none => []
  | some m => m :: (l.erase m).selection_sort
termination_by l.length
decreasing_by exact l.length_erase_lt_of_minimum_eq_some hm

theorem List.mem_of_mem_selection_sort {α} [LinearOrder α] {l : List α} {a : α}
    (ha : a ∈ l.selection_sort) :
  a ∈ l := by
  unfold selection_sort at ha
  match hm : l.minimum with
  | none =>
    rw [hm] at ha
    simp at ha
  | some m =>
    rw [hm] at ha
    obtain ha | ha := by simpa only [mem_cons] using ha
    · subst ha
      exact minimum_mem hm
    · have h1 := (l.erase m).mem_of_mem_selection_sort ha
      apply mem_of_mem_erase h1
termination_by l.length
decreasing_by exact l.length_erase_lt_of_minimum_eq_some hm

theorem List.sorted_selection_sort {α} [LinearOrder α] (l : List α) :
    l.selection_sort.SortedLE := by
  unfold selection_sort
  match hm : l.minimum with
  | none => simp [SortedLE, Monotone]
  | some m =>
    dsimp
    constructor
    · intro a ha
      apply l.minimum_le_of_mem ?_ hm
      have h1 := (l.erase m).mem_of_mem_selection_sort ha
      apply mem_of_mem_erase h1
    · apply sorted_selection_sort
termination_by l.length
decreasing_by exact l.length_erase_lt_of_minimum_eq_some hm


def List.insertion_sort {α} [LinearOrder α] (l : List α) : List α :=
  match l with
  | [] => []
  | a :: as =>
    let p := as.insertion_sort.filter (· ≤ a)
    let q := as.insertion_sort.filter (¬· ≤ a)
    p ++ a :: q

theorem List.sorted_insertion_sort {α} [LinearOrder α] (l : List α) :
    l.insertion_sort.Sorted (· ≤ ·) := by
  unfold insertion_sort
  match l with
  | [] => simp
  | a :: as =>
    let p := as.insertion_sort.filter (· ≤ a)
    let q := as.insertion_sort.filter (¬· ≤ a)
    change (p ++ a :: q).Sorted (· ≤ ·)
    sorry





def Or.toPSum {p q : Prop} [Decidable p] [Decidable q] (h : p ∨ q) : p ⊕' q :=
  if hp : p then PSum.inl hp
  else if hq : q then PSum.inr hq
  else by grind
    -- apply False.elim; apply not_or_intro hp hq h


structure BitString where
  size : Nat
  bits : Fin size → Bool

def BitString.append (b1 b2 : BitString) : BitString := {
    size := b1.size + b2.size
    bits := fun ⟨i, hi⟩ =>
      if h1 : i < b1.size
      then b1.bits ⟨i, h1⟩
      else b2.bits ⟨i - b1.size, by omega⟩
      -- have h1 : i < b1.size ⊕' i ≥ b1.size := by apply Or.toPSum; omega
      -- match h1 with
      -- | .inl h1 => b1.bits ⟨i, by omega⟩
      -- | .inr h1 => b2.bits ⟨i - b1.size, by omega⟩
  }

instance : Append BitString where append := BitString.append

theorem BitString.append_assoc (b1 b2 b3 : BitString) : b1 ++ (b2 ++ b3) = (b1 ++ b2) ++ b3 := by
  change b1.append (b2.append b3) = (b1.append b2).append b3
  rw [mk.injEq]
  dsimp only [append]
  split_ands
  · rw [Nat.add_assoc]
  · apply (Fin.heq_fun_iff ?_).mpr ?_
    · rw [Nat.add_assoc]
    · grind

def BitString.or (b1 b2 : BitString) : BitString := {
    size := max b1.size b2.size
    bits := fun ⟨i, _⟩ =>
      (if h1 : i < b1.size then b1.bits ⟨i, h1⟩ else false)
      || (if h2 : i < b2.size then b2.bits ⟨i, h2⟩ else false)
  }

instance : HOr BitString BitString BitString where hOr := BitString.or

theorem BitString.or_assoc (b1 b2 b3 : BitString) : b1 ||| (b2 ||| b3) = (b1 ||| b2) ||| b3 := by
  change b1.or (b2.or b3) = (b1.or b2).or b3
  rw [mk.injEq]
  dsimp only [or]
  split_ands
  · grind
  · apply (Fin.heq_fun_iff ?_).mpr ?_
    all_goals grind

#exit

def BitString.shiftLeft (b : BitString) (n : Nat) : BitString := {
    size := b.size + n
    bits := fun i => if h1 : i < n then false else b.bits (i - n)
    prop := by
      intro i hi
      split_ifs with h1
      · rfl
      · exact b.prop (i - n) (by omega)
  }

theorem BitString.or_shiftLeft (n : Nat) (b1 b2 : BitString) :
    (b1 ||| b2).shiftLeft n = b1.shiftLeft n ||| b2.shiftLeft n := by
  change (b1.or b2).shiftLeft n = (b1.shiftLeft n).or (b2.shiftLeft n)
  rw [mk.injEq]
  dsimp only [or, shiftLeft]
  split_ands
  · simp
  · ext i
    split_ifs with h1
    all_goals rfl

#check ite
