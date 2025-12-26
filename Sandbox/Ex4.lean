import Sandbox.fincomb

inductive Letter
| A | B | C | D | E | F | G | H | I | J | K | L | M
| N | O | P | Q | R | S | T | U | V | W | X | Y | Z
deriving DecidableEq

/-
Example: Counting permutations of ABC
-/
open Letter Nat in
example :
    let f := fun p : Fin 3 ↪ Fin 3 => ![A, B, C] ∘ p
    (Finset.univ.image f).card = 6 := by
  intro f
  rw [Finset.card_image_of_injective]
  · rw [Finset.card_univ, ←card_eq_fintype_card]
    rw [card_finEmbeddingFin]
    · decide
    · decide
  · intro ⟨p, hp⟩ ⟨q, hq⟩ hpq
    dsimp [f] at hpq
    set w : Fin 3 → Letter := ![A, B, C]
    let v : Letter → Fin 3 := fun | A => 0 | B => 1 | C => 2 | _ => 0
    apply_fun (v ∘ ·) at hpq
    simpa using calc
      id ∘ p = (v ∘ w) ∘ p := by
        congr 1
        ext k
        fin_cases k <;> simp [v, w]
      _ = (v ∘ w) ∘ q := hpq
      _ = id ∘ q := by
        congr 1
        ext k
        fin_cases k <;> simp [v, w]


open Letter Nat in
example :
    let f := fun p : Fin 4 ↪ Fin 4 => ![T, R, E, E] ∘ p
    (Finset.univ.image f).card = 12 := by
  intro f
  have h1 : Finset.univ.image f × (Fin 2 ↪ Fin 2) ≃ (Fin 4 ↪ Fin 4) := {
    toFun := fun ⟨⟨x, hx⟩, q⟩ => by
      -- let ⟨p, hp⟩ := by simpa using hx
      sorry
    invFun := sorry
    left_inv := sorry
    right_inv := sorry
  }
  replace h1 : Nat.card (Finset.univ.image f) * 2 = 24 := by simpa using Nat.card_congr h1
  rw [←card_eq_finsetCard]
  omega
