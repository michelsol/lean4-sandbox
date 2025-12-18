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

def finSuccEmbeddingEquivSigma (n m : ℕ) :
    (Fin (n + 1) ↪ Fin m) ≃ Σ y0, Fin n ↪ {y : Fin m // y ≠ y0} := {
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

def finSuccPermEquivSigma (n : ℕ) :
    (Fin (n + 1) ≃ Fin (n + 1)) ≃ Σ y0, Fin n ≃ {y : Fin (n + 1) // y ≠ y0} :=

  let F : (Fin (n + 1) ≃ Fin (n + 1)) → Σ y0, Fin n ≃ {y : Fin (n + 1) // y ≠ y0} :=
    fun ⟨f, g, gof, fog⟩ ↦
    ⟨f ⟨n, by omega⟩,
      let a : Fin n → { y // y ≠ f ⟨n, by omega⟩ } :=
        fun ⟨k, hk⟩ ↦ ⟨f ⟨k, by omega⟩, by grind⟩
      let b : { y // y ≠ f ⟨n, by omega⟩ } → Fin n :=
          fun ⟨⟨y, hy0⟩, hy⟩ ↦ ⟨(g ⟨y, hy0⟩).val, by
            contrapose! hy
            apply_fun g
            swap
            · exact fog.injective
            rw [gof]
            ext; simp; omega
            ⟩
      ⟨a, b, by
        intro ⟨k, hk⟩
        ext
        unfold a b
        unfold Function.LeftInverse at gof
        simp [gof]
        , by
        intro ⟨y, hy⟩
        ext
        unfold a b
        unfold Function.RightInverse Function.LeftInverse at fog
        simp [fog]
        ⟩⟩

  let G : (Σ y0, Fin n ≃ {y : Fin (n + 1) // y ≠ y0}) → (Fin (n + 1) ≃ Fin (n + 1)) :=
    fun ⟨fn, ⟨f', g', g'of', f'og'⟩⟩ ↦ ⟨
    fun k ↦ if hk : k.val < n then (f' ⟨k.val, hk⟩).1 else fn,
    fun y ↦ if hy : y ≠ fn then ⟨(g' ⟨y, hy⟩).1, by omega⟩ else ⟨n, by omega⟩, by
    intro k
    dsimp
    split_ifs with h1 h2 h2
    · have := (f' ⟨k, h1⟩).2; contradiction
    · ext
      simp only [Subtype.coe_eta]
      rw [g'of']
    · ext; simp; omega
    · simp at h2, by
    intro y
    dsimp
    split_ifs with h1 h2 h2
    all_goals
      try simp at *
      try grind
    ⟩

  have hGF : Function.LeftInverse G F := by
    intro f
    unfold F G
    ext ⟨x, hx⟩
    dsimp
    grind

  have hFG : Function.RightInverse G F := by
    intro f
    ext
    · unfold F G
      simp
    · symm
      apply heq_of_eqRec_eq
      swap
      · grind
      ext k
      unfold F G
      conv_rhs => simp
      congr 5
      all_goals simp
      all_goals tauto

  ⟨F, G, hGF, hFG⟩

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

theorem card_finEmbeddingFin {n m : ℕ} (h : n ≤ m) :
    Nat.card (Fin n ↪ Fin m) = m ! / (m - n) ! := by
  revert m
  induction n
  · intro m hm
    symm
    simpa using Nat.div_self (Nat.factorial_pos _)
  · next n ih =>
    intro m hm
    cases m
    · omega
    · next m => calc
      _ = Nat.card (Σ k, Fin n ↪ {y // y ≠ k}) := by
        apply Nat.card_congr
        apply finSuccEmbeddingEquivSigma
      _ = ∑ k, Nat.card (Fin n ↪ {y // y ≠ k}) := by apply Nat.card_sigma
      _ = ∑ k, Nat.card (Fin n ↪ Fin m) := by
        congr 1 with y0
        apply Nat.card_congr
        apply Equiv.embeddingCongr
        · exact Equiv.refl _
        · symm
          apply finSuccAboveEquiv
      _ = (m + 1) * Nat.card (Fin n ↪ Fin m) := by simp
      _ = (m + 1) * (m ! / (m - n) !) := by rw [ih (by omega)]
      _ = (m + 1) ! / (m - n) ! := by
        symm
        apply Nat.mul_div_assoc
        apply factorial_dvd_factorial
        omega
      _ = _ := by
        congr 2
        omega
