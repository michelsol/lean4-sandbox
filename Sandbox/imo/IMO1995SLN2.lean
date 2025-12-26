import Mathlib

/-
Let $\mathbb{Z}$ denote the set of all integers. Prove that for any integers $A$ and $B$,
one can find an integer $C$ for which $M_1=\{x^2+Ax+B : x \in \mathbb{Z}\}$
and $M_2=\{2x^2+2x+C : x \in \mathbb{Z}\}$ do not intersect.
-/

theorem algebra_24606 (A B : ℤ) : ∃ C : ℤ,
    let M1 := { x ^ 2 + A * x + B | x : ℤ }
    let M2 := { 2 * x ^ 2 + 2 * x + C | x : ℤ }
    M1 ∩ M2 = ∅ := by
  have : ∃ A' : ℤ, A = 2 * A' ∨ A = 2 * A' + 1 := Int.even_or_odd' A
  obtain ⟨A', hA'⟩ := this
  rcases hA' with hA' | hA'
  swap
/-
If $A$ is odd, then every number in $M_{1}$ is of the form $x(x+A)+B \equiv B$ $(\bmod 2)$,
-/
  . let M1 := { x ^ 2 + A * x + B | x : ℤ }
    have h1 : ∀ y ∈ M1, y ≡ B [ZMOD 2] := by
      intro y hy
      obtain ⟨x, hx⟩ := hy
      subst hx
      suffices (x ^ 2 + A * x + B) - B ≡ B - B [ZMOD 2] from
        (Int.ModEq.add_right_cancel' (-B) this.symm).symm
      suffices x * (x + A) ≡ 0 [ZMOD 2] from by ring_nf at this ⊢; assumption
      suffices x * (x + A) % 2 = 0 from by simpa [Int.ModEq]
      have hA : A % 2 = 1 := by omega
      rcases (show x % 2 = 0 ∨ x % 2 = 1 from by omega) with hx | hx
      . simp [Int.mul_emod, hx]
      . simp [Int.mul_emod, Int.add_emod, hA, hx]
/-
while numbers in $M_{2}$ are congruent to $C$ modulo 2 .
-/
    let M2 (C : ℤ) := { 2 * x ^ 2 + 2 * x + C | x : ℤ }
    have h2 C : ∀ y ∈ M2 C, y ≡ C [ZMOD 2] := by
      intro y hy
      obtain ⟨x, hx⟩ := hy
      subst hx
      simp [Int.ModEq]
      omega
/-
Thus it is enough to take $C \equiv B+1(\bmod 2)$. We use B + 1.
-/
    use B + 1
    suffices M1 ∩ M2 (B + 1) = ∅ from by simpa
    ext y
    suffices y ∈ M1 → y ∉ M2 (B + 1) from by simpa
    intro hy1 hy2
    specialize h1 y hy1
    specialize h2 _ y hy2
    have := h1.symm.trans h2
    simp [Int.ModEq] at this
    omega
/-
If $A$ is even
-/
  . let M1 := { x ^ 2 + A * x + B | x : ℤ }
    have h1 : ∀ y ∈ M1, y ≡ 0 + (B - A' ^ 2) [ZMOD 4] ∨ y ≡ 1 + (B - A' ^ 2) [ZMOD 4] := by
      intro y hy
      obtain ⟨x, hx⟩ := hy
      /-
      then all numbers in $M_{1}$ have the form
      $\left(X+\frac{A}{2}\right)^{2}+B-\frac{A^{2}}{4}$
      -/
      replace hx : (x + A') ^ 2 + (B - A' ^ 2) = y := by rw [hA'] at hx; ring_nf at hx ⊢; assumption
      subst hx
      /-
      and are congruent to
      $B-\frac{A^{2}}{4}$ or $1 + B-\frac{A^{2}}{4}$ modulo 4 ,
      -/
      suffices (x + A') ^ 2 ≡ 0 [ZMOD 4] ∨ (x + A') ^ 2 ≡ 1 [ZMOD 4] from by
        rcases this with this | this
        . left; exact Int.ModEq.add this rfl
        . right; exact Int.ModEq.add this rfl
      generalize x + A' = x
      iterate 2 rw [Int.ModEq]
      rw [pow_two, Int.mul_emod]
      have h : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
      rcases h with h | h | h | h <;> norm_num [h]
/-
while numbers in $M_{2}$ are congruent to $C$ modulo 4 .
-/
    let M2 (C : ℤ) := { 2 * x ^ 2 + 2 * x + C | x : ℤ }
    have h2 C : ∀ y ∈ M2 C, y ≡ C [ZMOD 4] := by
      intro y hy
      obtain ⟨x, hx⟩ := hy
      subst hx
      suffices 2 * x ^ 2 + 2 * x + C ≡ 0 + C [ZMOD 4] from by ring_nf at this ⊢; assumption
      suffices 2 * x ^ 2 + 2 * x ≡ 0 [ZMOD 4] from Int.ModEq.add this rfl
      suffices x * (x + 1) + x * (x + 1) ≡ 0 [ZMOD 4] from by ring_nf at this ⊢; assumption
      rw [Int.ModEq, Int.add_emod, Int.mul_emod, Int.add_emod x 1]
      have h : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
      rcases h with h | h | h | h <;> norm_num [h]
/-
So one can choose any $C \equiv 2+B-\frac{A^{2}}{4}$ $(\bmod 4)$.
-/
    use 2 + (B - A' ^ 2)
    suffices M1 ∩ M2 _ = ∅ from by simpa
    ext y
    suffices y ∈ M1 → y ∉ M2 _ from by simpa
    intro hy1 hy2
    specialize h1 y hy1
    specialize h2 _ y hy2
    rcases h1 with h1 | h1
    all_goals
    . have := h1.symm.trans h2
      simp [Int.ModEq] at this
      omega
