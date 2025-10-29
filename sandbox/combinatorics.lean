import Mathlib


open Nat Function

namespace Set

variable {α β} (s : Set α) [DecidablePred (· ∈ s)] (t : Set β) [Zero β]

def funOn := {f : α → β | ∀ x, if x ∈ s then f x ∈ t else f x = 0}

def equivFunOn : funOn s t ≃ (s → t) where
  toFun := fun ⟨f, hf⟩ ⟨x, hx⟩ ↦ ⟨f x, by simpa [hx] using hf x⟩
  invFun := fun f ↦ ⟨fun x ↦ if hx : x ∈ s then (f ⟨x, hx⟩).1 else 0, by intro x; grind⟩
  left_inv := by intro ⟨f, hf⟩; ext x; specialize hf x; grind
  right_inv := by intro f; simp

end Set


namespace Finset

variable {α β} [DecidableEq α] [Zero β] (s : Finset α) (t : Finset β)

instance : Fintype (s.toSet.funOn t.toSet) := .ofEquiv (s → t) (s.toSet.equivFunOn t.toSet).symm

def funOn := (s.toSet.funOn t.toSet).toFinset

theorem mem_funOn_iff (f : α → β) : f ∈ funOn s t ↔ ∀ x, if x ∈ s then f x ∈ t else f x = 0 := by
  simp [funOn, Set.funOn]

theorem mem_funOn_iff' (f : α → β) : f ∈ funOn s t ↔ (∀ x ∈ s, f x ∈ t) ∧ ∀ x ∉ s, f x = 0 := by
  grind [mem_funOn_iff]



-- Given finite sets s t, and x0 ∈ s,
-- Choosing a function from s → t, is equivalent to
-- Choosing a function from s \ {x0} → t, and an element of t to assign to x0
def funOnEquivSProdSDiff {x0 : α} (hx0 : x0 ∈ s) :
  funOn s t ≃ funOn (s \ {x0}) t ×ˢ t where
      toFun := fun ⟨f, hf⟩ ↦ ⟨⟨fun x ↦ if x = x0 then 0 else f x, f x0⟩, by
        replace hf := by simpa [funOn] using hf
        simp only [mem_product, mem_funOn_iff]
        split_ands
        · intro x
          specialize hf x
          simp at *; grind
        · specialize hf x0
          simp at *; grind
          ⟩
      invFun := fun ⟨⟨g, y0⟩, hg⟩ =>
        ⟨fun x ↦ if x = x0 then y0 else g x, by
          obtain ⟨hg, hy0⟩ := by simpa [funOn] using hg
          simp only [mem_funOn_iff]
          intro x
          specialize hg x
          simp at *; grind⟩
      left_inv := by
        intro ⟨f, hf⟩
        ext x
        grind
      right_inv := by
        intro ⟨⟨g, y0⟩, hg⟩
        obtain ⟨hg, hy0⟩ := by simpa [funOn] using hg
        ext x
        · specialize hg x
          simp at *; grind
        · simp


-- The number of s → t functions is #t ^ #s
theorem card_funOn : #(funOn s t) = #t ^ #s := by
  suffices ∀ n, #s = n → #(funOn s t) = #t ^ n from this #s rfl
  intro n
  induction' n with n ih generalizing s t
  all_goals intro hs
  · replace hs : s = ∅ := by simpa using hs
    suffices ∃ f, funOn s t = {f} from by simpa [hs, card_eq_one]
    use fun _ ↦ 0
    ext f
    simp [hs, mem_funOn_iff, funext_iff]
  · obtain ⟨x0, hx0⟩ : s.Nonempty := by
      apply nonempty_of_ne_empty
      apply_fun (#·)
      simp [hs]
    calc
      _ = #((s \ {x0}).funOn t ×ˢ t) := card_eq_of_equiv (funOnEquivSProdSDiff s t hx0)
      _ = #((s \ {x0}).funOn t) * #t := by simp
      _ = #t ^ n * #t := by
        congr 1
        apply ih
        rw [card_sdiff (by simpa using hx0)]
        simp [hs]
      _ = _ := by ring


end Finset



namespace Finset

variable {α β} [DecidableEq α] [DecidableEq β] [Zero β] (s : Finset α) (t : Finset β)

def bijOn := {f ∈ funOn s t | Set.BijOn f s t}


-- Given x0 ∈ s,
-- choosing a bijection from s → t, is equivalent to
-- choosing an element y ∈ t to assign to x0, together with a bijection from s \ {x0} → t \ {y}
def bijOnEquivSigma {x0 : α} (hx0 : x0 ∈ s) :
  bijOn s t ≃ t.sigma fun y ↦ bijOn (s \ {x0}) (t \ {y}) := {
      toFun := fun ⟨f, hf⟩ ↦ ⟨⟨f x0, fun x ↦ if x = x0 then 0 else f x⟩, by
        obtain ⟨hf1, hf2⟩ := by simpa [bijOn, funOn] using hf
        simp only [mem_sigma, bijOn, funOn]
        simp only [mem_filter, Set.mem_toFinset, Set.BijOn]
        split_ands
        · simpa [hx0] using hf1 x0
        · intro x
          specialize hf1 x
          by_cases hx : x ∈ s <;> by_cases hx2 : x = x0
          all_goals simp [hx, hx2] at hf1 ⊢
          all_goals simp [hf1]
          contrapose! hx2
          exact hf2.right.left hx hx0 hx2
        · intro x hx
          obtain ⟨hx, hx2⟩ := by simpa using hx
          specialize hf1 x
          simp [hx] at hf1
          simp [hx2, hf1]
          contrapose! hx2
          exact hf2.right.left hx hx0 hx2
        · intro x hx x' hx'
          obtain ⟨hx, hx2⟩ := by simpa using hx
          obtain ⟨hx', hx2'⟩ := by simpa using hx'
          intro h
          simp [hx2, hx2'] at h
          exact hf2.right.left (by simpa using hx) (by simpa using hx') h
        · intro y hy
          obtain ⟨hy, hy2⟩ := by simpa using hy
          obtain ⟨x, hx, hx2⟩ := hf2.right.right hy
          use x
          have hxx0 : x ≠ x0 := by
            contrapose! hy2
            subst hy2
            simp [hx2]
          split_ands
          · simp at hx
            simp [hx, hxx0]
          · simp [hxx0, hx2]⟩
      invFun := fun ⟨⟨y0, f⟩, hyf⟩ ↦ ⟨fun x ↦ if x = x0 then y0 else f x, by
        obtain ⟨hy0, hf⟩ := by simpa using hyf
        obtain ⟨hf, hf2⟩ := by simpa [bijOn, funOn] using hf
        simp only [bijOn, funOn]
        simp only [mem_filter, Set.mem_toFinset, Set.BijOn]
        split_ands
        · intro x
          specialize hf x
          by_cases hx : x ∈ s <;> by_cases hx2 : x = x0
          all_goals simp [hx, hx2, hx0, hy0] at hf ⊢ <;> simp [hf]
        · intro x hx
          simp at hx
          specialize hf x
          by_cases hx2 : x = x0
          all_goals simp [hx2, hy0, hx] at hf ⊢ <;> simp [hf]
        · intro x hx x' hx' h
          simp at hx hx'
          simp at h
          have hfx := hf x
          have hfx' := hf x'
          by_cases hx2 : x = x0 <;> by_cases hx2' : x' = x0
          all_goals simp [hx, hx2, hx', hx2'] at hfx hfx' h
          · simp [hx2, hx2']
          · tauto
          · tauto
          · exact hf2.right.left (by simp [hx, hx2]) (by simp [hx', hx2']) h
        · intro y hy
          by_cases hy2 : y = y0
          · use x0
            simp [hx0, hy2]
          · obtain ⟨x, hx, hx2⟩ : ∃ x, (x ∈ s ∧ ¬x = x0) ∧ f x = y := by
              simpa using hf2.right.right (by simp [hy, hy2])
            use x
            simp [hx, hx2]⟩
      left_inv := by
        simp [Function.LeftInverse]
        intro f hf
        ext x
        by_cases hx : x = x0
        all_goals simp [hx]
      right_inv := by
        intro ⟨⟨y, f⟩, hyf⟩
        obtain ⟨hy0, hf⟩ := by simpa using hyf
        obtain ⟨hf, hf2⟩ := by simpa [bijOn, funOn] using hf
        simp
        ext x
        specialize hf x
        by_cases hx : x ∈ s <;> by_cases hx2 : x = x0
        all_goals simp [hx, hx2] at hf ⊢ <;> simp [hf]
    }


-- The number of bijections between two finite sets of same size n is n!.
theorem equivBijOn {n : ℕ} (hs : #s = n) (ht : #t = n) : #(bijOn s t) = n ! := by
  induction' n with n ih generalizing s t
  · suffices ∃ y, bijOn s t = {y} by simpa [card_eq_one]
    replace hs : s = ∅ := card_eq_zero.mp hs
    subst hs
    replace ht : t = ∅ := card_eq_zero.mp ht
    subst ht
    use fun _ ↦ 0
    ext f
    simp [bijOn, funOn, Set.funOn, funext_iff]
  · have hs : s.Nonempty := by apply Finset.card_ne_zero.mp; omega
    let x0 := hs.choose
    have hx0 : x0 ∈ s := hs.choose_spec
    calc
      #(bijOn s t) = #(t.sigma fun y0 ↦ bijOn (s \ {x0}) (t \ {y0})) := by
        apply card_eq_of_equiv
        exact bijOnEquivSigma s t hx0
      _ = ∑ y0 ∈ t, #(bijOn (s \ {x0}) (t \ {y0})) := by apply card_sigma
      _ = ∑ y0 ∈ t, n ! := by
        apply sum_congr rfl
        intro y0 hy0
        exact ih (s \ {x0}) (t \ {y0})
          (by rw [card_sdiff (by simpa using hx0)]; simp; omega)
          (by rw [card_sdiff (by simpa using hy0)]; simp; omega)
      _ = (n + 1) ! := by simp only [sum_const, smul_eq_mul, ht, Nat.factorial_succ]




end Finset
