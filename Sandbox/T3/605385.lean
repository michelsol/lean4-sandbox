import Mathlib

open Real

/- A triple of positive integers $(a, b, c)$ is called quasi-Pythagorean if
there exists a triangle with lengths of the sides $a, b, c$ and the angle opposite
to the side $c$ equal to $120^{\circ}$.
Prove that if $(a, b, c)$ is a quasi-Pythagorean triple then $c$ has a prime divisor greater than 5 . -/
theorem number_theory_605385
    (quasiPythagorean : ℕ → ℕ → ℕ → Prop)
    (quasiPythagorean_def : ∀ a > 0, ∀ b > 0, ∀ c > 0, quasiPythagorean a b c ↔
      a + b > c ∧ a + c > b ∧ b + c > a ∧ a ^ 2 + b ^ 2 - c ^ 2 = 2 * a * b * cos (120 * π / 180))
    : ∀ a > 0, ∀ b > 0, ∀ c > 0, quasiPythagorean a b c → ∃ p, p.Prime ∧ p > 5 ∧ p ∣ c := by

-- By the cosine law, a triple of positive integers $(a, b, c)$ is quasi-Pythagorean if and only if
-- $$ c^{2}=a^{2}+a b+b^{2} $$    (1)
  have h1 a (ha : a > 0) b (hb : b > 0) c (hc : c > 0) :
      quasiPythagorean a b c ↔ c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
    rw [quasiPythagorean_def a ha b hb c hc]
    constructor
    · intro ⟨c1, c2, c3, c4⟩
      replace c4 : c ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b * cos (120 * π / 180) := by linarith
      rify
      suffices a * b = - 2 * a * b * cos (120 * π / 180) by linarith
      suffices cos (120 * π / 180) = -1 / 2 by
        apply_fun (fun x : ℝ => a * b * x) at this
        linarith
      calc
        cos (120 * π / 180) = cos (2 * (π / 3)) := by
          congr 1
          ring
        _ = -1 / 2 := by
          rw [cos_two_mul, cos_pi_div_three]
          norm_num
    · intro c1
      split_ands
      · nlinarith
      · nlinarith
      · nlinarith
      · sorry

-- If a triple $(a, b, c)$ with a common divisor $d > 0$ satisfies (1),
-- then so does the reduced triple $\left(\frac{a}{d}, \frac{b}{d}, \frac{c}{d}\right)$.
  have h2 a (ha : a > 0) b (hb : b > 0) c (hc : c > 0) (d : ℕ) (hd : d > 0)
      (ha2 : d ∣ a) (hb2 : d ∣ b) (hc2 : d ∣ c) (c1 : quasiPythagorean a b c) :
      quasiPythagorean (a / d) (b / d) (c / d) := by
    rw [h1 a ha b hb c hc] at c1
    rw [h1 (a / d) (by rify [ha2]; positivity) (b / d) (by rify [hb2]; positivity)
        (c / d) (by rify [hc2]; positivity)]
    rify at c1
    rify [ha2, hb2, hc2]
    field_simp [c1]
    ring

-- Hence it suffices to prove that in every irreducible quasi-Pythagorean triple
-- the greatest term $c$ has a prime divisor greater than 5.
  suffices
  ∀ a > 0, ∀ b > 0, ∀ c > 0, ∀ (c1 : quasiPythagorean a b c) (c2 : (a.gcd b).gcd c = 1),
      ∃ p, p.Prime ∧ p > 5 ∧ p ∣ c by
    intro a ha b hb c hc c1
    set d := (a.gcd b).gcd c
    have hd : d > 0 := by exact Nat.gcd_pos_of_pos_right (a.gcd b) hc
    let a' := a / d
    let b' := b / d
    let c' := c / d
    have ha2 : d ∣ a  := by
      sorry
    have hb2 : d ∣ b  := by
      sorry
    have hc2 : d ∣ c  := by
      sorry
    have ha' : a' > 0 := by rify [a', ha2]; positivity
    have hb' : b' > 0 := by rify [b', hb2]; positivity
    have hc' : c' > 0 := by rify [c', hc2]; positivity
    specialize h2 a ha b hb c hc d hd ha2 hb2 hc2 c1
    obtain ⟨p, c2, c3, c4⟩ := this a' ha' b' hb' c' hc' h2 sorry
    use p, c2, c3
    calc
      p ∣ c' := c4
      _ ∣ c := by exact Nat.div_dvd_of_dvd hc2

-- Actually, we will show that in that case every prime divisor of $c$ is greater than 5.

-- Let $(a, b, c)$ be an irreducible triple satisfying (1).
  intro a ha b hb c hc h3 h4

-- Note that then $a, b$ and $c$ are pairwise coprime.
  have h5 : a.Coprime b := by
    sorry
  have h6 : b.Coprime c := by
    sorry
  have h7 : c.Coprime a := by
    sorry

-- We have to show that $c$ is not divisible by 2, 3, or 5.
  suffices ¬2 ∣ c ∧ ¬3 ∣ c ∧ ¬5 ∣ c by
    obtain ⟨c1, c2, c3⟩ := this
    obtain ⟨p, c4, c5⟩ := c.exists_prime_and_dvd sorry
    use p
    use c4
    use by
      by_contra! c6
      have c7 := c4.ne_one
      have c8 := c4.ne_zero
      interval_cases p
      all_goals omega

-- If $c$ were even, then $a$ and $b$ (coprime to $c$) should be odd, and (1) would not hold.
  have h8 : ¬2 ∣ c := by
    by_contra! h8
    sorry

-- Suppose now that $c$ is divisible by 3
-- and rewrite (1) as $$ 4 c^{2}=(a+2 b)^{2}+3 a^{2} $$   (2)
-- Then $a+2 b$ must be divisible by 3.
-- Since $a$ is coprime to $c$, the number $3 a^{2}$ is not divisible by 9.
-- This yields a contradiction since the remaining terms in (2) are divisible by 9.
  have h9 : ¬3 ∣ c := by
    by_contra! h9
    specialize h1 a ha b hb c hc
    rw [h1] at h3
    replace h3 : 4 * c ^ 2 = (a + 2 * b) ^ 2 + 3 * a ^ 2 := by linarith

    have c1 : 3 ∣ (a + 2 * b) := by
      suffices 3 ∣ (a + 2 * b) ^ 2 by
        apply Nat.Prime.dvd_of_dvd_pow ?_ this
        decide
      suffices (3 : ℤ) ∣ (a + 2 * b) ^ 2 by zify; simpa using this
      zify at h3 h9
      calc
        (3 : ℤ) ∣ (4 * c ^ 2 - 3 * a ^ 2) := by
          refine Int.dvd_sub ?_ ?_
          · apply Dvd.dvd.mul_left
            refine Dvd.dvd.pow h9 ?_
            norm_num
          · apply Dvd.dvd.mul_right
            norm_num
        _ = (a + 2 * b) ^ 2 := by omega
    replace c1 : 9 ∣ (a + 2 * b) ^ 2 := by simpa using pow_dvd_pow_of_dvd c1 2

    have c2 : 9 ∣ 3 * a ^ 2 := by
      zify at h3 h9 c1 ⊢
      calc
        (9 : ℤ) ∣ 4 * c ^ 2 - (a + 2 * b) ^ 2 := by
          refine Int.dvd_sub ?_ c1
          apply Dvd.dvd.mul_left
          suffices (3 ^ 2 : ℤ) ∣ c ^ 2 by simpa using this
          exact pow_dvd_pow_of_dvd h9 2
        _ = 3 * a ^ 2 := by omega
    replace c2 : 3 * 3 ∣ 3 * a ^ 2 := by simpa using c2
    replace c2 : 3 ∣ a ^ 2 := by
      obtain ⟨k, c2⟩ := c2
      use k
      omega
    replace c2 : 3 ∣ a := by
      apply Nat.Prime.dvd_of_dvd_pow ?_ c2
      decide

    have c3 : 3 ∣ c.gcd a := by exact Nat.dvd_gcd h9 c2
    unfold Nat.Coprime at h7
    omega

-- Finally, suppose $c$ is divisible by 5 (and hence $a$ is not).
-- Again we get a contradiction with (2) since the square of every integer
-- is congruent to 0, 1, or -1 modulo 5; so $4 c^{2}-3 a^{2} \equiv \pm 2(\bmod 5)$
-- and it cannot be equal to $(a+2 b)^{2}$.
  have h10 : ¬5 ∣ c := by
    by_contra! h10

    have c1 : ¬5 ∣ a := by
      by_contra! c1
      have c2 : 5 ∣ c.gcd a := by exact Nat.dvd_gcd h10 c1
      unfold Nat.Coprime at h7
      omega

    specialize h1 a ha b hb c hc
    rw [h1] at h3
    replace h3 : 4 * c ^ 2 = (a + 2 * b) ^ 2 + 3 * a ^ 2 := by linarith
    zify at h3 h10 c1

    have c2 (k : ZMod 5) : k ^ 2 ∈ ({0, 1, -1} : Set _) := by
      fin_cases k
      all_goals decide

    have c3 : (4 * c ^ 2 - 3 * a ^ 2 : ZMod 5) ∈ ({2, -2} : Set _) := by
      sorry

    have c4 : (4 * c ^ 2 - 3 * a ^ 2 : ZMod 5) ∈ ({0, 1, -1} : Set _) := by
      convert_to (a + 2 * b : ZMod 5) ^ 2 ∈ ({0, 1, -1} : Set _) using 1
      · replace h3 : (4 * c ^ 2 - 3 * a ^ 2 : ℤ) = (a + 2 * b) ^ 2 := by omega
        apply_fun (fun x : ℤ  => (x : ZMod 5)) at h3
        simpa using h3
      apply c2

    obtain c3 | c3 := c3
    all_goals
      rw [c3] at c4
      tauto

-- This completes the proof.
  exact ⟨h8, h9, h10⟩
