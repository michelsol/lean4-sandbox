import Mathlib

/-
Determine all pairs $(x, y)$ of positive integers such that $x^{2} y+$ $x+y$ is divisible
by $x y^{2}+y+7$.
-/

theorem other_24823 :
    { (x, y) : ℤ × ℤ | x > 0 ∧ y > 0 ∧ x * y ^ 2 + y + 7 ∣ x ^ 2 * y + x + y }
    = ({ t | t > 0 }.image λ t => (7 * t ^ 2, 7 * t)) ∪ {(11, 1)} ∪ {(49, 1)} := by
  ext ⟨x, y⟩
  constructor
  . intro ⟨hx, hy, h1⟩
    suffices x = 49 ∧ y = 1 ∨ x = 11 ∧ y = 1 ∨ ∃ t > 0, 7 * t ^ 2 = x ∧ 7 * t = y from by simpa

-- If $x^{2} y+x+y$ is divisible by $x y^{2}+y+7$,
-- then so is the number $y\left(x^{2} y+x+y)-x\left(x y^{2}+y+7\right)=y^{2}-7 x$.
    have h2 : x * y ^ 2 + y + 7 ∣ y ^ 2 - 7 * x := by
      have c1 : y ^ 2 - 7 * x = y * (x ^ 2 * y + x + y) - x * (x * y ^ 2 + y + 7) := by ring_nf
      rw [c1]
      apply dvd_sub
      . apply dvd_mul_of_dvd_right h1
      . apply dvd_mul_of_dvd_right
        apply dvd_refl

-- Now we split the proof depending on the sign of $y^2 - 7x$.
    obtain h3 | h3 : y ^ 2 - 7 * x ≥ 0 ∨ y ^ 2 - 7 * x < 0 := by omega

-- If $y^{2}-7 x \geq 0$,
-- then since $y^{2}-7 x < x y^{2}+y+7$ it follows that $y^{2}-7 x=0$.
    . have h4 : y ^ 2 - 7 * x = 0 := by
        have c1 : y ^ 2 - 7 * x < x * y ^ 2 + y + 7 := by nlinarith
        by_contra c2
        have c3 := Int.le_of_dvd (by positivity) h2
        linarith

-- Hence $(x, y)=\left(7 t^{2}, 7 t\right)$ for some $t \in \mathbb{N}$.
      right
      right
-- As 7 divides y, we can pick t = y/7
      obtain ⟨t, h5⟩ : 7 ∣ y := by
        have c1 : y ^ 2 = 7 * x := by omega
        have c2 : 7 ∣ y ^ 2 := by
          rw [c1]
          apply dvd_mul_of_dvd_left
          apply dvd_refl
        have c3 : Prime (7 : ℤ) := by norm_num
        rwa [c3.dvd_pow_iff_dvd (by norm_num)] at c2
      use t
      split_ands
      . omega
      . nlinarith
      . omega

-- If $y^{2}-7 x < 0$, then $7 x-y^{2}>0$ is divisible by $x y^{2}+y+7$.
    . have h4 : x * y ^ 2 + y + 7 ∣ 7 * x - y ^ 2 := by
        have c1 : 7 * x - y ^ 2 > 0 := by linarith
        rw [←dvd_neg]
        ring_nf at h2 ⊢
        simpa using h2

-- But then $x y^{2}+y+7 \leq 7 x-y^{2} < 7 x$, from which we obtain $y \leq 2$.
      have h5 : x * y ^ 2 + y + 7 < 7 * x := calc
        _ ≤ 7 * x - y ^ 2 := by exact Int.le_of_dvd (by linarith) h4
        _ < _ := by nlinarith
      have h6 : y ≤ 2 := by
        have c1 : y ^ 2 ≤ 7 := by nlinarith
        nlinarith

      obtain h7 | h7 : y = 1 ∨ y = 2 := by omega
-- For $y=1$, we are led to $x+8 \mid 7 x-1$,
      . subst h7
        have h7 : x + 8 ∣ 7 * x - 1 := by
          ring_nf at h4 ⊢
          simpa using h4

-- and hence $x+8 \mid 7(x+8)-(7 x-1)=57$.
        replace ⟨z, h7⟩ : x + 8 ∣ 57 := by
          have c1 : 57 = 7 * (x + 8) - (7 * x - 1) := by omega
          rw [c1]
          apply dvd_sub
          . apply dvd_mul_of_dvd_right
            apply dvd_refl
          . exact h7

-- Thus the only possibilities are $x=11$ and $x=49$,
-- and the obtained pairs are $(11,1),(49,1)$.
        replace h7 : x = 11 ∨ x = 49 := by
          have c1 : z ≥ 1 := by nlinarith
          have c2 : z ≤ 6 := by nlinarith
          interval_cases z
          all_goals omega

        obtain h7 | h7 := h7
        all_goals simp [h7]

-- For $y=2$, we have $4 x+9 \mid 7 x-4$,
      . subst h7
        have h7 : 4 * x + 9 ∣ 7 * x - 4 := by
          ring_nf at h4 ⊢
          simpa using h4

-- so that $7(4 x+9)-4(7 x-4)=79$ is divisible by $4 x+9$.
        replace ⟨z, h7⟩ : 4 * x + 9 ∣ 79 := by
          have c1 : 79 = 7 * (4 * x + 9) - 4 * (7 * x - 4) := by omega
          rw [c1]
          apply dvd_sub
          . apply dvd_mul_of_dvd_right
            apply dvd_refl
          . apply dvd_mul_of_dvd_right h7

-- We do not get any new solutions in this case.
        have c1 : z ≥ 1 := by nlinarith
        have c2 : z ≤ 3 := by nlinarith
        interval_cases z
        all_goals omega

-- Therefore all required pairs $(x, y)$ are
-- $\left(7 t^{2}, 7 t\right)(t \in \mathbb{N}),(11,1)$, and $(49,1)$.

-- Conversely these solutions satisfy the desired condition.
  . intro h1
    replace h1 : x = 49 ∧ y = 1 ∨ x = 11 ∧ y = 1 ∨ ∃ t > 0, 7 * t ^ 2 = x ∧ 7 * t = y := by
      simpa using h1
    dsimp
    obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨t, ht, h1, h2⟩ := h1
    . norm_num [h1, h2]
    . norm_num [h1, h2]
    . rw [←h1, ←h2]
      split_ands
      . positivity
      . positivity
      . use t
        ring_nf
