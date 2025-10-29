import Mathlib


open Finset Nat

def finSuccEquivProd (k n : ℕ) : (Fin (k + 1) → Fin n) ≃ (Fin k → Fin n) × Fin n where
  toFun f := (fun x ↦ f ⟨x.val, by omega⟩, f ⟨k, by omega⟩)
  invFun := fun (f, fk) x ↦ if hx : x.val < k then f ⟨x.val, hx⟩ else fk
  left_inv f := by
    ext ⟨x, hx0⟩
    grind
  right_inv := by
    intro ⟨f, fk⟩
    ext x
    all_goals simp

theorem card_finMapFin (k n : ℕ) : Nat.card (Fin k → Fin n) = n ^ k := by
  induction k
  · simp
  · next k ih => calc
      _ = Nat.card ((Fin k → Fin n) × Fin n) := by
        apply Nat.card_congr
        apply finSuccEquivProd
      _ = Nat.card (Fin k → Fin n) * Nat.card (Fin n) := by apply Nat.card_prod
      _ = n ^ k * n := by
        congr 1
        apply Nat.card_fin
      _ = _ := by ring

def finSuccEmbeddingEquivSigma (n : ℕ) :
    (Fin (n + 1) ↪ Fin (n + 1)) ≃ Σ y0, Fin n ↪ {y : Fin (n + 1) // y ≠ y0} := {
      toFun := fun ⟨f, hf⟩ =>
        ⟨f ⟨n, by omega⟩,
          ⟨fun ⟨k, hk⟩ => ⟨f ⟨k, by omega⟩, by intro h; specialize hf h; grind⟩, by
            intro ⟨i, hi⟩ ⟨j, hj⟩ hij
            simp at hij
            simpa using hf hij⟩⟩,
      invFun := fun ⟨fn, ⟨f', hf'⟩⟩ => ⟨
        fun ⟨k, _⟩ => if hk' : k < n then (f' ⟨k, hk'⟩).1 else fn, by
        intro ⟨i, hi⟩ ⟨j, hj⟩ hij
        dsimp at hij
        by_cases hi' : i < n
        all_goals by_cases hj' : j < n
        · replace hij : f' ⟨i, hi'⟩ = f' ⟨j, hj'⟩ := by grind
          simpa using hf' hij
        · grind
        · grind
        · grind
        ⟩,
      left_inv := by
        intro f
        ext ⟨x, hx⟩
        dsimp
        grind
      right_inv := by
        intro y
        dsimp
        ext
        · simp
        · symm
          apply heq_of_eqRec_eq
          · ext k
            simp
            congr 4
            all_goals simp
            all_goals tauto
          · simp
    }

noncomputable def finSuccPermEquivSigma (n : ℕ) :
    (Fin (n + 1) ≃ Fin (n + 1)) ≃ Σ y0, Fin n ≃ {y : Fin (n + 1) // y ≠ y0} :=
  sorry

#exit
    calc
  _ ≃ (Fin (n + 1) ↪ Fin (n + 1)) := by symm; apply Equiv.embeddingEquivOfFinite
  _ ≃ _ := finSuccEmbeddingEquivSigma n
  _ ≃ _ := by
    apply Equiv.sigmaCongrRight
    intro k
    exact {
      toFun := fun ⟨f, hf⟩ => Equiv.ofBijective f (by
        rw [Fintype.bijective_iff_injective_and_card]
        use hf
        simp)
      invFun := fun ⟨f, g, hf, hg⟩ => Function.Embedding.mk f hf.injective
      left_inv := by tauto
      right_inv := by intro f; ext x; simp
    }

#exit

theorem card_finEquivFin (n : ℕ) : Nat.card (Fin n ≃ Fin n) = n ! := by
  induction n
  · simp
  · next n ih => calc
      _ = Nat.card (Σ y0, Fin n ≃ {y : Fin (n + 1) // y ≠ y0}) := by
        apply Nat.card_congr
        apply finSuccPermEquivSigma
      _ = ∑ y0, Nat.card (Fin n ≃ {y : Fin (n + 1) // y ≠ y0}) := by apply Nat.card_sigma
      _ = ∑ _ : Fin (n + 1), Nat.card (Fin n ≃ Fin n) := by
        congr 1 with y0
        apply Nat.card_congr
        apply Equiv.equivCongr
        · exact finCongr rfl
        · symm
          exact finSuccAboveEquiv y0
      _ = ∑ _ : Fin (n + 1), n ! := by rw [ih]
      _ = (n + 1) * n ! := by simp
      _ = (n + 1) ! := by exact rfl


example (α : Type) [Finite α] : Nat.card (α ≃ α) = (Nat.card α) ! := by
  let n := Nat.card α
  calc
    _ = Nat.card (Fin n ≃ Fin n) := by
      apply Nat.card_congr
      apply Equiv.permCongr
      apply Finite.equivFin
    _ = n ! := by apply card_finEquivFin
    _ = _ := rfl
