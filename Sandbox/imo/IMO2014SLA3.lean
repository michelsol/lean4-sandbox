import Mathlib


open Finset
open Classical


noncomputable def price (n : ℕ) (x : ℕ → ℝ) :=
  if hn : n ≥ 1 then ((Icc 1 n).image λ i => |∑ k ∈ Icc 1 i, x k|).max' (by simp [hn]) else 0

def perms (n : ℕ) := { φ : ℕ → ℕ | Set.BijOn φ (Set.Icc 1 n) (Set.Icc 1 n) ∧ ∀ k ∉ Icc 1 n, φ k = 0 }

noncomputable instance [Finite α] : Fintype α := Fintype.ofFinite α
instance : Finite (perms n) := by
  let f (φ : perms n) : Icc 1 n → Icc 1 n :=  λ ⟨i, hi⟩ ↦
    ⟨φ.1 i, by simpa using φ.2.1.1 (by simpa using hi)⟩
  apply Finite.of_injective f
  intro ⟨φ, hφ⟩ ⟨φ', hφ'⟩ h
  ext i
  by_cases hi : i ∈ Icc 1 n
  . simpa [f] using congrFun h ⟨i, hi⟩
  . have := hφ.2 i hi
    have := hφ'.2 i hi
    simp; omega

instance (n : ℕ) (x : ℕ → ℝ) : Finite { x ∘ φ | φ ∈ perms n } := Finite.Set.finite_image _ _

noncomputable def D (n : ℕ) (x : ℕ → ℝ) := ({ x ∘ φ | φ ∈ perms n }.toFinset.image (price n)).min' sorry

noncomputable def Finset.argmax' [LinearOrder β] (f : α → β) (s : Finset α) (H : s.Nonempty) : α :=
  have h := (image f s).isGreatest_max' (by simp [H])
  (Finset.mem_image.mp h.1).choose

variable (n : ℕ) (x : ℕ → ℝ) in
noncomputable def gφ (i : ℕ) : ℕ :=
  if i ∈ Icc 1 n then
    let unused := { j ∈ Icc 1 n | ∀ k ∈ Ico 1 i, j ≠ gφ k }
    if unused_ne : unused.Nonempty then
      let f := λ j => |(∑ k ∈ Ico 1 i, if k ∈ Ico 1 i then x (gφ k) else 0) + x j|
      argmax' f unused unused_ne
    else 0
  else 0
decreasing_by all_goals (simp_wf; simp at *; omega)

noncomputable def G (n : ℕ) (x : ℕ → ℝ) := price n (x ∘ gφ n x)



theorem algebra_ : IsLeast { c : ℝ | ∀ n ≥ 1, ∀ x, G n x ≤ c * D n x } 2 := by
  constructor
  swap
  . intro c h
    let n := 4
    let x' : ℕ → ℤ := λ | 1 => 1 | 2 => -1 | 3 => 2 | 4 => -2 | 0 => 0 | c + 5 => 0
    let x (k : ℕ) : ℝ := x' k
    replace h := h n (by norm_num) x
    set G := G n x
    set D := D n x
    suffices D = 1 ∧ G = 2 from by simpa [this] using h
    split_ands
    . have := (({ x ∘ φ | φ ∈ perms n }.toFinset.image (price n)).isLeast_min' sorry)
      apply IsLeast.unique this
      constructor
      . suffices ∃ φ ∈ perms 4, price 4 (x ∘ φ) = 1 from by simpa
        let φ : ℕ → ℕ := λ | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 0 => 0 | c + 5 => 0
        use φ
        split_ands
        . simp [Set.MapsTo, φ]; decide
        . simp [Set.InjOn, φ]; decide
        .
          -- have := Finset.surj_on_of_inj_on_of_card_le sorry sorry this
          sorry
        . intro k hk
          simp only [mem_Icc, not_and] at hk
          by_cases hk' : k = 0
          . simp [hk']
          . obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le' (by omega : k ≥ 5)
            simp [hj]
        . simp [price]
          have := ((image (fun i => |∑ k ∈ Icc 1 i, x (φ k)|) (Icc 1 4)).isGreatest_max' sorry)
          apply IsGreatest.unique this
          split_ands
          . simp only [coe_image, coe_Icc, Set.mem_image, Set.mem_Icc]
            use 1
            norm_cast
          . simp only [upperBounds, coe_image, Set.mem_image, forall_exists_index, and_imp]
            intro m
            intro i hi h
            subst h
            revert i
            norm_cast
            dsimp [φ, x']
            decide
      . suffices ∀ φ ∈ perms 4, 1 ≤ price n (x ∘ φ) from by simpa [lowerBounds]
        intro φ hφ
        simp [price]
        sorry
      -- have h1 := (({ x ∘ φ | φ ∈ perms n }.toFinset.image (price n)).isLeast_min' sorry)
      -- have h1 := (({ x ∘ φ | φ ∈ perms n }.toFinset.image (price n)).isLeast_min' sorry).1
      -- have h2 := (({ x ∘ φ | φ ∈ perms n }.toFinset.image (price n)).isLeast_min' sorry).2
      -- set m := ({ x ∘ φ | φ ∈ perms n }.toFinset.image (price n)).min' sorry
      -- simp at h1
      -- simp [lowerBounds] at h2
    . sorry
  . intro n n_ge_1 x
    sorry
