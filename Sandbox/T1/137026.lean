import Mathlib


/-
A seven-digit natural number $N$ is called interesting if:

- it consists of non-zero digits;
- it is divisible by 4;
- any number obtained from the number $N$ by permuting its digits is divisible by 4.

How many interesting numbers exist?
-/

theorem number_theory_137026
    (S : Set (Fin 7 → ℕ))
    (hS : S = { d : Fin 7 → ℕ |
      (∀ i, d i ≥ 1 ∧ d i ≤ 9) ∧
      (∑ i, d i * 10 ^ (i : ℕ)) % 4 = 0 ∧
      ∀ p : Equiv.Perm (Fin 7), (∑ i, (d ∘ p) i * 10 ^ (i : ℕ)) % 4 = 0})
    : S.ncard = 2 ^ 7 := by

  -- A number is divisible by 4 if and only if the number formed by its last two digits is divisible by 4.
  have h1 (d : Fin 7 → ℕ) : (∑ i, d i * 10 ^ (i : ℕ)) % 4 = (d 0 + d 1 * 10) % 4 := calc
      _ = (∑ i, if i < 2 then d i * 10 ^ (i : ℕ) else d i * 10 ^ (i : ℕ)) % 4 := by simp
      _ = (∑ i with i < 2, d i * 10 ^ (i : ℕ) + ∑ i with ¬i < 2, d i * 10 ^ (i : ℕ)) % 4 := by rw [Finset.sum_ite]
      _ = ((∑ i with i < 2, d i * 10 ^ (i : ℕ)) % 4 + (∑ i with ¬i < 2, d i * 10 ^ (i : ℕ)) % 4) % 4 := by rw [Nat.add_mod]
      _ = ((d 0 + d 1 * 10) % 4 + 0) % 4 := by
        congr 2
        . have c1 : {i ∈ (.univ : Finset (Fin 7)) | i < 2} = {0, 1} := by
            ext i; simp; omega
          simp [c1]
        . have c1 : {i ∈ (.univ : Finset (Fin 7)) | ¬i < 2} = {2, 3, 4, 5, 6} := by
            ext i; simp; omega
          rw [c1]
          sorry
      _ = _ := by simp

-- For any two digits a and b in N, both 10a+b and 10b+a must be divisible by 4.
  have h2 (d : Fin 7 → ℕ) :
      (∀ p : Equiv.Perm (Fin 7), (∑ i, (d ∘ p) i * 10 ^ (i : ℕ)) % 4 = 0) ↔
      (∀ i j : Fin 7, i ≠ j → (d i + d j * 10) % 4 = 0) :=
    let r (i j : Fin 7) := (d i + d j * 10) % 4 = 0
    calc
    _ ↔ (∀ p : Equiv.Perm (Fin 7), (d (p 0) + d (p 1) * 10) % 4 = 0) := by simp [h1]
    (∀ p : Equiv.Perm (Fin 7), r (p 0) (p 1)) ↔ (∀ i j : Fin 7, i ≠ j → r i j) := by
      constructor <;> intro c1
      . intro i j hij
        let p : Equiv.Perm (Fin 7) := Equiv.ofBijective (
          λ k ↦ if k = 0 then i else if k = 1 then j else k) (by
          constructor
          . sorry
          . sorry
        )
        convert c1 p using 1
      . intro p
        apply c1 (p 0) (p 1)
        by_contra! c2
        have c3 := p.injective c2
        omega

-- Simplify the form of the set of interesting numbers S.
  convert_to S = { d : Fin 7 → ℕ | (∀ i, d i ≥ 1 ∧ d i ≤ 9) ∧
      ∀ i j : Fin 7, i ≠ j → (d i + d j * 10) % 4 = 0} using 3 with d at hS
  . rw [h1, h2]
    constructor
    . intro ⟨c1, c2, c3⟩
      split_ands
      . exact c1
      . exact c3
    . intro ⟨c1, c2⟩
      split_ands
      . exact c1
      . exact c2 0 1 (by norm_num)
      . exact c2

-- If a + 10b % 4 = 0 and b + 10a % 4 = 0 then a,b ∈ {4, 8}
  have h3 (a b : ℕ) (ha : a ≥ 1 ∧ a ≤ 9) (hb : b ≥ 1 ∧ b ≤ 9)
      (c1 : (a + b * 10) % 4 = 0) (c2 : (b + a * 10) % 4 = 0) :
      a = 4 ∨ a = 8 := by omega

-- Thus, only the digits 4 and 8  can appear in the number N.
  have h4 : S ⊆ { d : Fin 7 → ℕ | (∀ i, d i = 4 ∨ d i = 8) } := by
    rw [hS]
    intro d ⟨c1, c2⟩ i
    obtain ⟨j, hj⟩ : ∃ j : Fin 7, j ≠ i := by
      obtain d1 | d1 : i < 6 ∨ i = 6 := by omega
      . use i + 1; omega
      . use 0; omega
    have c3 := c2 i j (by omega)
    have c4 := c2 j i (by omega)
    exact h3 (d i) (d j) (c1 i) (c1 j) c3 c4

-- Conversely, if N is only composed of the digits 4 and 8, then it is interesting.
  have h5 : { d : Fin 7 → ℕ | (∀ i, d i = 4 ∨ d i = 8) } ⊆ S := by
    intro d c1
    rw [hS]
    dsimp at c1 ⊢
    split_ands
    . intro i
      specialize c1 i
      omega
    . intro i j
      have c1i := c1 i
      have c1j := c1 j
      omega

  have h6 : S = { d : Fin 7 → ℕ | (∀ i, d i = 4 ∨ d i = 8) } := by
    exact Set.Subset.antisymm h4 h5

  have h7 : S ≃ (Fin 7 → Fin 2) := by
    rw [h6]
    simp only [Set.coe_setOf]
    apply Equiv.mk
      (λ ⟨d, hd⟩ i ↦
          have hr1 : ∃ r : Fin 2, match r with | 0 => d i = 4 | 1 => d i = 8 := by
            obtain hdi | hdi := hd i
            . use 0
            . use 1
          hr1.choose
        )
      (λ e ↦ ⟨λ i ↦ match e i with | 0 => 4 | 1 => 8, by
        intro i
        obtain he | he : e i = 0 ∨ e i = 1 := by omega
        all_goals simp [he]⟩)
    . intro ⟨d, hd⟩
      ext i
      dsimp
      have hr1 : ∃ r : Fin 2, match r with | 0 => d i = 4 | 1 => d i = 8 := by
        obtain hdi | hdi := hd i
        . use 0
        . use 1
      have hr2 := hr1.choose_spec
      set r := hr1.choose
      obtain hr3 | hr3 : r = 0 ∨ r = 1 := by omega
      . simp [hr3] at hr2
        simp [hr3, hr2]
      . simp [hr3] at hr2
        simp [hr3, hr2]
    . intro e
      ext i
      dsimp
      obtain he | he : e i = 0 ∨ e i = 1 := by omega
      . sorry
      . sorry

  calc
    S.ncard = Nat.card S := by rfl
    _ = Nat.card (Fin 7 → Fin 2) := by exact Nat.card_congr h7
    _ = Nat.card (Fin 2) ^ Nat.card (Fin 7) := by rw [Nat.card_fun]
    _ = 2 ^ 7 := by
      congr 1
      . simp
      . simp
