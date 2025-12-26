import Mathlib

open Real

/-
Given that $x, y, z$ are distinct real numbers. Prove:
$
\left|\frac{1+x y}{x-y}+\frac{1+y z}{y-z}+\frac{1+z x}{z-x}\right| \geqslant \sqrt{3} .
$
-/
theorem inequalities_328413
    (x y z : ℝ) (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
    : |(1 + x * y) / (x - y) + (1 + y * z) / (y - z) + (1 + z * x) / (z - x)| ≥ √3 := by

-- Let $a=\frac{1+x y}{x-y}, b=\frac{1+y z}{y-z}, c=\frac{1+z x}{z-x}$, $ x=\tan \alpha, y=\tan \beta, z=\tan \gamma \text {. } $

  set a := (1 + x * y) / (x - y)
  set b := (1 + y * z) / (y - z)
  set c := (1 + z * x) / (z - x)

  set α := arctan x
  set β := arctan y
  set γ := arctan z

-- First we handle the case where $a = 0$ or $b = 0$ or $c = 0$.
  by_cases ha : a = 0
  . have h1 : c = 1 / b := by
      have c2 : x * y = -1 := by
        replace hxy : x - y ≠ 0 := by intro h; apply hxy; linarith
        replace ha : 1 + x * y = 0 := by simpa [a, hxy] using ha
        linarith
      have c3 : y ≠ 0 := by
        by_contra! d1
        subst d1
        linarith
      have c4 : x = -1 / y := by field_simp [c2]
      calc
        c = (1 + z * x) / (z - x) := by simp [c]
        _ = (1 + z * (-1 / y)) / (z - (-1 / y)) := by rw [c4]
        _ = y * (1 + z * (-1 / y)) / (y * (z - (-1 / y))) := by
          symm
          apply mul_div_mul_left _ _ c3
        _ = (y - z) / (1 + y * z) := by
          congr 1
          . field_simp
            ring
          . field_simp
            ring
        _ = _ := by field_simp [b]
    have h2 : b ≠ 0 := by
      have c2 : x * y = -1 := by
        replace hxy : x - y ≠ 0 := by intro h; apply hxy; linarith
        replace ha : 1 + x * y = 0 := by simpa [a, hxy] using ha
        linarith
      have c3 : y ≠ 0 := by
        by_contra! d1
        subst d1
        linarith
      have c4 : x = -1 / y := by field_simp [c2]
      by_contra! h2
      have c5 : z * y = -1 := by
        replace hyz : y - z ≠ 0 := by intro h; apply hyz; linarith
        replace h2 : 1 + y * z = 0 := by simpa [b, hyz] using h2
        linarith
      have c6 : z ≠ 0 := by
        by_contra! d1
        subst d1
        linarith
      have c7 : z = -1 / y := by field_simp [c5]
      have c8 : z = x := by linarith
      contradiction
    calc
      _ = |b + 1 / b| := by simp [ha, h1]
      _ = √((b + 1 / b) ^ 2) := by rw [sqrt_sq_eq_abs]
      _ = √(b ^ 2 + 2 * b * (1 / b) + (1 / b) ^ 2) := by ring_nf
      _ = √(b ^ 2 + 2 + (1 / b) ^ 2) := by congr 3; field_simp
      _ = √(b ^ 2 + 2 + 1 / b ^ 2) := by congr 2; simp
      _ ≥ √3 := by
        gcongr
        by_cases c1 : b ^ 2 ≥ 1
        . calc
            b ^ 2 + 2 + 1 / b ^ 2 ≥ 1 + 2 + 1 / b ^ 2 := by gcongr
            _ = 3 + 1 / b ^ 2 := by ring
            _ ≥ 3 + 0 := by gcongr; positivity
            _ = 3 := by ring
        . replace c1 : b ^ 2 ≤ 1 := by linarith
          calc
            b ^ 2 + 2 + 1 / b ^ 2 ≥ b ^ 2 + 2 + 1 / 1 := by gcongr
            _ = 3 + b ^ 2 := by ring
            _ ≥ 3 + 0 := by gcongr; positivity
            _ = 3 := by ring

  by_cases hb : b = 0
  . sorry

  by_cases hc : c = 0
  . sorry

-- Now we'll assume that $a, b, c \neq 0$.
-- As $x, y, z$ are distinct, $\alpha, \beta, \gamma$ are also distinct real numbers.
  have hαβ : α ≠ β := by
    by_contra! hαβ
    unfold α β at hαβ
    have c1 := arctan_injective hαβ
    contradiction
  have hβγ : β ≠ γ := by
    by_contra! hβγ
    unfold β γ at hβγ
    have c1 := arctan_injective hβγ
    contradiction
  have hγα : γ ≠ α := by
    by_contra! hγα
    unfold γ α at hγα
    have c1 := arctan_injective hγα
    contradiction

-- And $ tan(\alpha - \beta) = \frac{1}{a}, tan(\beta - \gamma) = \frac{1}{b}, tan(\gamma - \alpha) = \frac{1}{c} $.
  have h1 : tan (α - β) = 1 / a := calc
      tan (α - β) = tan (α + -β) := by ring_nf
      _ = (tan α + tan (-β)) / (1 - tan α * tan (-β)) := by
        rw [tan_add]
        left
        split_ands
        . intro k
          unfold α
          have c1 := arctan_lt_pi_div_two x
          have c2 := neg_pi_div_two_lt_arctan x
          by_contra! c3
          obtain c4 | c4 : (k : ℝ) ≥ 0 ∨ (k : ℝ) ≤ -1 := by sorry
          . replace c3 : arctan x ≥ π / 2 := calc
              _ = _ := c3
              _ ≥ 1 * π / 2 := by
                gcongr
                linarith
              _ = _ := by ring
            linarith
          . replace c3 : arctan x ≤ -π / 2 := calc
              _ = _ := c3
              _ ≤ -1 * π / 2 := by
                gcongr
                linarith
              _ = _ := by ring
            linarith
        . intro l
          unfold β
          have c1 := arctan_lt_pi_div_two y
          have c2 := neg_pi_div_two_lt_arctan y
          by_contra! c3
          obtain c4 | c4 : (l : ℝ) ≥ 0 ∨ (l : ℝ) ≤ -1 := by sorry
          . replace c3 : -arctan y ≥ π / 2 := calc
              _ = _ := c3
              _ ≥ 1 * π / 2 := by
                gcongr
                linarith
              _ = _ := by ring
            linarith
          . replace c3 : -arctan y ≤ -π / 2 := calc
              _ = _ := c3
              _ ≤ -1 * π / 2 := by
                gcongr
                linarith
              _ = _ := by ring
            linarith
      _ = (tan α - tan β) / (1 + tan α * tan β) := by
        rw [tan_neg]
        congr 1
        all_goals ring
      _ = (x - y) / (1 + x * y) := by simp [α, β]
      _ = _ := by field_simp [a]

  have h2 : tan (β - γ) = 1 / b := calc
      tan (β - γ) = tan (β + -γ) := by ring_nf
      _ = (tan β + tan (-γ)) / (1 - tan β * tan (-γ)) := by
        rw [tan_add]
        left
        split_ands
        . intro k
          unfold β
          have c1 := arctan_lt_pi_div_two y
          have c2 := neg_pi_div_two_lt_arctan y
          by_contra! c3
          obtain c4 | c4 : (k : ℝ) ≥ 0 ∨ (k : ℝ) ≤ -1 := by sorry
          . replace c3 : arctan y ≥ π / 2 := calc
              _ = _ := c3
              _ ≥ 1 * π / 2 := by
                gcongr
                linarith
              _ = _ := by ring
            linarith
          . replace c3 : arctan y ≤ -π / 2 := calc
              _ = _ := c3
              _ ≤ -1 * π / 2 := by
                gcongr
                linarith
              _ = _ := by ring
            linarith
        . intro l
          unfold γ
          have c1 := arctan_lt_pi_div_two z
          have c2 := neg_pi_div_two_lt_arctan z
          by_contra! c3
          obtain c4 | c4 : (l : ℝ) ≥ 0 ∨ (l : ℝ) ≤ -1 := by sorry
          . replace c3 : -arctan z ≥ π / 2 := calc
              _ = _ := c3
              _ ≥ 1 * π / 2 := by
                gcongr
                linarith
              _ = _ := by ring
            linarith
          . replace c3 : -arctan z ≤ -π / 2 := calc
              _ = _ := c3
              _ ≤ -1 * π / 2 := by
                gcongr
                linarith
              _ = _ := by ring
            linarith
      _ = (tan β - tan γ) / (1 + tan β * tan γ) := by
        rw [tan_neg]
        congr 1
        all_goals ring
      _ = (y - z) / (1 + y * z) := by simp [β, γ]
      _ = _ := by field_simp [b]

  have h3 : tan (γ - α) = 1 / c := calc
      tan (γ - α) = tan (γ + -α) := by ring_nf
      _ = (tan γ + tan (-α)) / (1 - tan γ * tan (-α)) := by
        rw [tan_add]
        left
        split_ands
        . intro k
          unfold γ
          have c1 := arctan_lt_pi_div_two z
          have c2 := neg_pi_div_two_lt_arctan z
          by_contra! c3
          obtain c4 | c4 : (k : ℝ) ≥ 0 ∨ (k : ℝ) ≤ -1 := by sorry
          . replace c3 : arctan z ≥ π / 2 := calc
              _ = _ := c3
              _ ≥ 1 * π / 2 := by
                gcongr
                linarith
              _ = _ := by ring
            linarith
          . replace c3 : arctan z ≤ -π / 2 := calc
              _ = _ := c3
              _ ≤ -1 * π / 2 := by
                gcongr
                linarith
              _ = _ := by ring
            linarith
        . intro l
          unfold α
          have c1 := arctan_lt_pi_div_two x
          have c2 := neg_pi_div_two_lt_arctan x
          by_contra! c3
          obtain c4 | c4 : (l : ℝ) ≥ 0 ∨ (l : ℝ) ≤ -1 := by sorry
          . replace c3 : -arctan x ≥ π / 2 := calc
              _ = _ := c3
              _ ≥ 1 * π / 2 := by
                gcongr
                linarith
              _ = _ := by ring
            linarith
          . replace c3 : -arctan x ≤ -π / 2 := calc
              _ = _ := c3
              _ ≤ -1 * π / 2 := by
                gcongr
                linarith
              _ = _ := by ring
            linarith
      _ = (tan γ - tan α) / (1 + tan γ * tan α) := by
        rw [tan_neg]
        congr 1
        all_goals ring
      _ = (z - x) / (1 + z * x) := by simp [γ, α]
      _ = _ := by field_simp [c]


-- Notice that, $\tan (\gamma-\alpha)=-\tan [(\alpha-\beta)+(\beta-\gamma)]$.
  have h4 : tan (γ - α) = -tan ((α - β) + (β - γ)) := calc
    _ = -tan (α - γ) := by
      rw [←tan_neg]
      ring_nf
    _ = _ := by ring_nf



-- Thus, $\frac{1}{c}=-\frac{\frac{1}{a}+\frac{1}{b}}{1-\frac{1}{a b}}$

  have h5 : 1 / c = -((1 / a + 1 / b) / (1 - 1 / a * (1 / b))) := calc
    _ = tan (γ - α) := by rw [h3]
    _ = -tan ((α - β) + (β - γ)) := by rw [h4]
    _ = -((tan (α - β) + tan (β - γ)) / (1 - tan (α - β) * tan (β - γ))) := by
      congr 1
      rw [tan_add]
      . sorry
    _ = _ := by congr 4

-- Thus, $ a b+b c+c a=1$.
  have h6 : a * b + b * c + c * a = 1 := by
    have c1 : a * b - 1 ≠ 0 := by
      sorry
    field_simp at h5
    linarith


-- Also, $(a+b+c)^{2} \geqslant 3(a b+b c+c a)=3$,
-- hence, $|a+b+c| \geqslant \sqrt{3}$.
  calc
    |a + b + c| = √((a + b + c) ^ 2) := by rw [sqrt_sq_eq_abs]
    _ ≥ √(3 * (a * b + b * c + c * a)) := by
      gcongr
      generalize a = a, b = b, c = c
      suffices a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a by linarith
      suffices (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ 0 by linarith
      positivity
    _ = √3 := by
      congr 1
      rw [h6]
      norm_num
