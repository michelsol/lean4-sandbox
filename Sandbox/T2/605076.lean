import Mathlib

open Real
/-
Let $(a, b, c)$ be a Pythagorean triple, i.e., a triplet of positive integers with $a^{2}+b^{2}=c^{2}$.
Prove that $(c / a+c / b)^{2}>8$.
-/

theorem inequalities_605076
    (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h1 : a ^ 2 + b ^ 2 = c ^ 2) :
    (c / a + c / b : ℝ) ^ 2 > 8 := by
-- Let $(a, b, c)$ be a Pythagorean triple.

-- View $a, b$ as lengths of the legs of a right angled triangle with hypotenuse of length $c$;
-- let $\theta$ be the angle determined by the sides with lengths $a$ and $c$.
  let θ := arccos (a / c)


-- Note that $0<\theta<90^{\circ}$
  have h3 : 0 < θ ∧ θ < π / 2 := by
    constructor
    . apply arccos_pos.mpr
      suffices 0 < (1 - a / c : ℝ) from by linarith
      suffices a < c from by field_simp; simpa
      nlinarith
    . apply arccos_lt_pi_div_two.mpr
      field_simp [hc]
  have h3' : 0 < sin θ := by apply sin_pos_of_mem_Ioo; constructor <;> linarith
  have h3'' : 0 < cos θ := by apply cos_pos_of_mem_Ioo; constructor <;> linarith

-- Then


-- $ \begin{aligned} \left(\frac{c}{a}+\frac{c}{b}\right)^{2} & =\left(\frac{1}{\cos \theta}+\frac{1}{\sin \theta}\right)^{2}=\frac{\sin ^{2} \theta+\cos ^{2} \theta+2 \sin \theta \cos \theta}{(\sin \theta \cos \theta)^{2}} \\ & =4\left(\frac{1+\sin 2 \theta}{\sin ^{2} 2 \theta}\right)=\frac{4}{\sin ^{2} 2 \theta}+\frac{4}{\sin 2 \theta} \end{aligned} $


  have h2 : (c / a + c / b : ℝ) ^ 2 = 4 / sin (2 * θ) ^ 2 + 4 / sin (2 * θ) := by
    calc
      _ = (1 / cos θ + 1 / sin θ) ^ 2 := by
        congr 2
        . rw [cos_arccos]
          . field_simp
          . calc _ ≤ (0 : ℝ) := by norm_num
              _ ≤ _ := by positivity
          . suffices (a : ℝ) ≤ 1 * (c : ℝ) from (div_le_one₀ (by norm_cast)).mpr (by nlinarith)
            norm_cast
            nlinarith
        . rw [sin_arccos]
          have c1 : (c ^ 2 - a ^ 2 : ℝ) = b ^ 2 := by rify at h1; linarith
          field_simp [c1]
      _ = (sin θ / (sin θ * cos θ) + cos θ / (sin θ * cos θ)) ^ 2 := by
        congr 2
        . field_simp
        . field_simp
      _ = 4 * (sin θ ^ 2 + cos θ ^ 2 + 2 * sin θ * cos θ) / (2 * sin θ * cos θ) ^ 2 := by ring
      _ = 4 * (1 + sin (2 * θ)) / sin (2 * θ) ^ 2 := by rw [sin_sq_add_cos_sq, sin_two_mul]
      _ = 4 / sin (2 * θ) ^ 2 + 4 * (sin (2 * θ) / sin (2 * θ) ^ 2) := by ring
      _ = 4 / sin (2 * θ) ^ 2 + 4 * (1 / sin (2 * θ)) := by
        congr 2
        by_cases c1 : sin (2 * θ) = 0
        . simp [c1]
        . field_simp
          ring
      _ = 4 / sin (2 * θ) ^ 2 + 4 / sin (2 * θ) := by ring

  rw [h2]

-- we have $0<\sin 2 \theta \leq 1$,
  have h4 : 0 < sin (2 * θ) := by apply sin_pos_of_pos_of_lt_pi <;> linarith
  have h5 : sin (2 * θ) ≤ 1 := by apply sin_le_one

-- with equality only if $\theta=45^{\circ}$.
-- But then $a=b$ and we obtain $\sqrt{2}=c / a$
-- contradicting $a, c$ both being integers.
-- Thus, $0<\sin 2 \theta<1$
  have h6 : sin (2 * θ) < 1 := by
      suffices sin (2 * θ) ≠ 1 from by
        apply lt_of_le_of_ne
        . apply sin_le_one
        . simpa
      intro c1
      rw [sin_eq_one_iff] at c1
      obtain ⟨k, hk⟩ := c1
      have c2 : k = θ / π - 1 / 4 := by field_simp at hk ⊢; nlinarith
      have c3 : k > (-1 : ℝ) := by nlinarith
      have c4 : k < (1 : ℝ) := by nlinarith
      have c5 : k = 0 := by norm_cast at c3 c4; simp at c3 c4; omega
      subst c5
      replace hk : θ = π / 4 := by linarith
      dsimp [θ] at hk
      apply_fun cos at hk
      rw [cos_arccos] at hk
      . replace hk : a * 2 = √2 * c := by field_simp at hk; simpa using hk
        replace hk : a ^ 2 * (2 ^ 2) = 2 * c ^ 2 := by
          apply_fun (. ^ 2) at hk
          iterate 2 rw [mul_pow] at hk
          norm_num at hk
          norm_cast at hk
        have d1 : Prime 2 := by apply Nat.prime_iff.mp; decide
        apply_fun emultiplicity 2 at hk
        iterate 2 rw [emultiplicity_mul] at hk
        iterate 3 rw [emultiplicity_pow] at hk
        rw [Nat.Prime.emultiplicity_self] at hk
        iterate 2 rw [FiniteMultiplicity.emultiplicity_eq_multiplicity] at hk
        . norm_cast at hk
          omega
        . apply Nat.finiteMultiplicity_iff.mpr
          simpa using hc
        . apply Nat.finiteMultiplicity_iff.mpr
          simpa using ha
        . decide
        . exact d1
        . exact d1
        . exact d1
        . exact d1
        . exact d1
      . suffices 0 ≤ (a / c + 1 : ℝ) from by linarith
        positivity
      . suffices a ≤ c from by
          rify at this
          apply div_le_one_of_le₀ this
          simp
        nlinarith

-- which gives $(c / a+c / b)^{2}>8$.
  calc
    (_ : ℝ) > 4 / 1 ^ 2 + 4 / 1 := by gcongr
    _ = 8 := by ring
