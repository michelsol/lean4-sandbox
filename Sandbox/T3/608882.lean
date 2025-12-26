import Mathlib

open ComplexConjugate

/- # Problem:
 Let $$a, b$$, and $$c$$ be complex numbers such that $$|a|=|b|=|c|=1$$. If

$$\frac{a^{2}}{b c}+\frac{b^{2}}{c a}+\frac{c^{2}}{a b}=1$$

as well, determine the product of all possible values of $$|a+b+c|$$.
-/

theorem algebra_608882
  (S : Set (ℂ × ℂ × ℂ))
  (hS : S = {(a, b, c) : ℂ × ℂ × ℂ | ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ ‖c‖ = 1 ∧
    a ^ 2 / (b * c) + b ^ 2 / (c * a) + c ^ 2 / (a * b) = 1})
  (V : Finset ℝ) (hV : V.toSet = (λ (a, b, c) => ‖a + b + c‖) '' S)
  : ∏ x ∈ V, x = 2 := by
-- Let $$s=a+b+c$$.





-- Then $$ \begin{aligned} s^{3} & =a^{3}+b^{3}+c^{3}+3\left(a^{2} b+a b^{2}+b^{2} c+b c^{2}+c^{2} a+c a^{2}\right)+6 a b c \\ & =a b c\left(\frac{a^{2}}{b c}+\frac{b^{2}}{c a}+\frac{c^{2}}{a b}+3\left(\frac{a}{b}+\frac{b}{a}+\frac{b}{c}+\frac{c}{b}+\frac{c}{a}+\frac{a}{c}\right)+6\right) \\ & =a b c\left(1+\left(3(a+b+c)\left(\frac{1}{a}+\frac{1}{b}+\frac{1}{c}\right)-9\right)+6\right) \\ & =a b c\left(3 s\left(\frac{1}{a}+\frac{1}{b}+\frac{1}{c}\right)-2\right) \\ & =a b c(3 s \bar{s}-2) \quad(\text { because } \bar{s}=\bar{a}+\bar{b}+\bar{c}=1 / a+1 / b+1 / c) \\ & =a b c\left(3|s|^{2}-2\right) \end{aligned} $$





  have h1 : S = {(a, b, c) : ℂ × ℂ × ℂ | ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ ‖c‖ = 1 ∧
      let s := a + b + c
      s ^ 3 = a * b * c * (3 * ‖s‖ ^ 2 - 2)} := by
    rw [hS]
    ext x
    obtain ⟨a, b, c⟩ := x
    dsimp only [Set.mem_setOf_eq]
    set s := a + b + c
    constructor
    all_goals
      intro ⟨ha, hb, hc, c1⟩
      have ha2 : a ≠ 0 := by
        suffices ‖a‖ ≠ 0 by simpa using this
        simp [ha]
      have hb2 : b ≠ 0 := by
        suffices ‖b‖ ≠ 0 by simpa using this
        simp [hb]
      have hc2 : c ≠ 0 := by
        suffices ‖c‖ ≠ 0 by simpa using this
        simp [hc]
      split_ands
      . exact ha
      . exact hb
      . exact hc
    . calc
        s ^ 3 = a ^ 3 + b ^ 3 + c ^ 3
                + 3 * (a ^ 2 * b + a * b ^ 2 + b ^ 2 * c + b * c ^ 2 + c ^ 2 * a + c * a ^ 2)
                + 6 * a * b * c := by
          ring
        _ = a * b * c * (a ^ 2 / (b * c) + b ^ 2 / (c * a) + c ^ 2 / (a * b)
                + 3 * (a / b + b / a + b / c + c / b + c / a + a / c) + 6) := by
          iterate 4 conv_rhs => rw [mul_add]
          iterate 4 congr 1
          . field_simp
            ring
          . field_simp
            ring
          . field_simp
            ring
          . ring_nf
            field_simp
            ring
          . ring
        _ = a * b * c * (1 + (3 * (a + b + c) * (1 / a + 1 / b + 1 / c) - 9) + 6) := by
          congr 1
          rw [c1]
          congr 2
          ring_nf
          simp [ha2, hb2, hc2]
          ring
        _ = a * b * c * (1 + (3 * s * (1 / a + 1 / b + 1 / c) - 9) + 6) := by congr 3
        _ = a * b * c * (3 * (s * (1 / a + 1 / b + 1 / c)) - 2) := by ring
        _ = a * b * c * (3 * (s * conj s) - 2) := by
          congr 4
          unfold s
          iterate 2 rw [map_add]
          congr 2
          . simpa using Complex.inv_eq_conj ha
          . simpa using Complex.inv_eq_conj hb
          . simpa using Complex.inv_eq_conj hc
        _ = a * b * c * (3 * ‖s‖ ^ 2 - 2) := by
          congr 3
          exact Complex.mul_conj' s
    . have c2 := calc
        _ = _ := c1
        _ = a * b * c * (3 * (s * conj s) - 2) := by
          congr 3
          symm
          exact Complex.mul_conj' s
        _ = a * b * c * (3 * (s * (1 / a + 1 / b + 1 / c)) - 2) := by
          congr 4
          unfold s
          iterate 2 rw [map_add]
          symm
          congr 2
          . simpa using Complex.inv_eq_conj ha
          . simpa using Complex.inv_eq_conj hb
          . simpa using Complex.inv_eq_conj hc
        _ = a * b * c * (1 + (3 * s * (1 / a + 1 / b + 1 / c) - 9) + 6) := by ring
        _ = a * b * c * (1 + (3 * (a + b + c) * (1 / a + 1 / b + 1 / c) - 9) + 6) := by congr 3
        _ = a * b * c * (1 + 3 * (a / b + b / a + b / c + c / b + c / a + a / c) + 6) := by
          congr 1
          congr 2
          ring_nf
          simp [ha2, hb2, hc2]
          ring
      have c3 := calc
        s ^ 3 = a ^ 3 + b ^ 3 + c ^ 3
                + 3 * (a ^ 2 * b + a * b ^ 2 + b ^ 2 * c + b * c ^ 2 + c ^ 2 * a + c * a ^ 2)
                + 6 * a * b * c := by
          ring
        _ = a * b * c * (a ^ 2 / (b * c) + b ^ 2 / (c * a) + c ^ 2 / (a * b)
                + 3 * (a / b + b / a + b / c + c / b + c / a + a / c) + 6) := by
          iterate 4 conv_rhs => rw [mul_add]
          iterate 4 congr 1
          . field_simp
            ring
          . field_simp
            ring
          . field_simp
            ring
          . ring_nf
            field_simp
            ring
          . ring
      set A := 3 * (a / b + b / a + b / c + c / b + c / a + a / c)
      have c4 : a * b * c * (1 + A + 6) =
                a * b * c * (a ^ 2 / (b * c) + b ^ 2 / (c * a) + c ^ 2 / (a * b) + A + 6) := by
        rw [←c2, c3]
      simp [ha2, hb2, hc2] at c4
      simp [c4]

  subst h1

-- Taking absolute values, we find $$|s|^{3}=\left.|3| s\right|^{2}-2 \mid$$.
  have h2 : V.toSet ⊆ {s : ℝ | s ^ 3 = |3 * s ^ 2 - 2|} := by
    rw [hV]
    intro s
    simp only [Set.mem_image, Set.mem_setOf_eq, Prod.exists]
    intro ⟨a, b, c, ⟨ha, hb, hc, c1⟩, c2⟩
    subst c2
    set s := a + b + c
    calc
      ‖s‖ ^ 3 = ‖s ^ 3‖ := by simp
      _ = ‖a * b * c * (3 * ‖s‖ ^ 2 - 2)‖ := by rw [c1]
      _ = ‖a * b * c‖ * ‖(3 * ‖s‖ ^ 2 - 2 : ℂ)‖ := by apply NormedField.norm_mul'
      _ = 1 * ‖(3 * ‖s‖ ^ 2 - 2 : ℂ)‖ := by simp [ha, hb, hc]
      _ = ‖(3 * ‖s‖ ^ 2 - 2 : ℂ)‖ := by ring
      _ = |3 * ‖s‖ ^ 2 - 2| := by norm_cast

-- It follows that $$|s|$$ must be a positive real root of $$x^{3}-3 x^{2}+2=0$$ or $$x^{3}+3 x^{2}-2=0$$.
  have h3 : V.toSet ⊆ {s : ℝ | s > 0 ∧ (s ^ 3 - 3 * s ^ 2 + 2 = 0 ∨ s ^ 3 + 3 * s ^ 2 - 2 = 0)} := by
    intro s hs
    specialize h2 hs
    dsimp at h2 ⊢
    constructor
    . apply lt_of_le_of_ne
      . by_contra! c1
        replace c1 : s ^ 3 < 0 := calc
            s ^ 3 < 0 ^ 3 := by
              sorry
            _ = _ := by norm_num
        rw [h2] at c1
        have c2 : |3 * s ^ 2 - 2| ≥ 0 := by apply abs_nonneg
        linarith
      . by_contra! c1
        subst c1
        simp at h2
    . obtain c1 | c1 := eq_or_eq_neg_of_abs_eq h2.symm
      . left
        linarith
      . right
        linarith

-- First $$x^3-3x^2+2=(x-1)(x^2-2x-2)=(x-1)(x-(1+\sqrt{3}))(x-(1-\sqrt{3}))$$
-- Now considering $$f(x)=x^3-3x^2-2$$, we have $$f'(x)=3x^2-6x=3x(x-2)$$
-- Hence $$f$$ decreases from $$f(0)=-2$$ to $$f(2)=-6$$ and then increases to $$+\infty$$
-- By the intermediate value theorem, $$f$$ has exactly one positive real root which is in $$(2, +\infty)$$
  sorry
