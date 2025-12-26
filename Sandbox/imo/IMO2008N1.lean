import Mathlib

open Finset

/- Let $$n$$ be a positive integer and let $$p$$ be a prime number.
Prove that if $$a, b, c$$ are integers (not necessarily positive)
satisfying the equations  $$ a^{n}+p b=b^{n}+p c=c^{n}+p a, $$  then $$a=b=c$$.
-/
theorem number_theory_23777
    (n : ℕ) (hn : n > 0)
    (p : ℕ) (hp : Prime (p : ℤ))
    (a b c : ℤ)
    (h1 : a ^ n + p * b = b ^ n + p * c)
    (h2 : b ^ n + p * c = c ^ n + p * a) :
    a = b ∧ b = c := by

-- If two of $$a, b, c$$ are equal, it is immediate that all the three are equal.
-- So we may assume that $$a \neq b \neq c \neq a$$.
  obtain h3 | h3 | h3 | ⟨hab, hbc, hca⟩ :
    a = b ∨ b = c ∨ c = a ∨ (a - b ≠ 0 ∧ b - c ≠ 0 ∧ c - a ≠ 0) := by omega
  . subst h3
    have c1 : p * (a - c) = 0 := by linarith
    simp [hp.ne_zero] at c1
    constructor <;> linarith
  . subst h3
    have c1 : p * (a - b) = 0 := by linarith
    simp [hp.ne_zero] at c1
    constructor <;> linarith
  . subst h3
    have c1 : p * (b - c) = 0 := by linarith
    simp [hp.ne_zero] at c1
    constructor <;> linarith

-- Subtracting the equations we get $$a^{n}-b^{n}=-p(b-c)$$ and
  have h3 : a ^ n - b ^ n = -p * (b - c) := by linarith
-- two cyclic copies of this equation,
  have h4 : b ^ n - c ^ n = -p * (c - a) := by linarith
  have h5 : c ^ n - a ^ n = -p * (a - b) := by linarith

-- which upon multiplication yield $$ \frac{a^{n}-b^{n}}{a-b} \cdot \frac{b^{n}-c^{n}}{b-c} \cdot \frac{c^{n}-a^{n}}{c-a}=-p^{3} . $$ (1)

  have h6 : ((a ^ n - b ^ n) / (a - b) : ℝ) * ((b ^ n - c ^ n) / (b - c) : ℝ) * ((c ^ n - a ^ n) / (c - a) : ℝ) = -p ^ 3 := by
    rify at h3 h4 h5
    rw [h3, h4, h5]
    rify at hab hbc hca
    field_simp
    ring

-- If $$n$$ is odd then the differences $$a^{n}-b^{n}$$ and $$a-b$$ have the same sign
-- and the product on the left is positive, while $$-p^{3}$$ is negative.
-- So $$n$$ must be even.
  have ⟨k, h7⟩ := n.even_or_odd'
  obtain h7 | h7 := h7
  swap
  . have c1 : ((a ^ n - b ^ n) / (a - b) : ℝ) > 0 := by
      sorry
    have c2 : ((b ^ n - c ^ n) / (b - c) : ℝ) > 0 := by
      sorry
    have c3 : ((c ^ n - a ^ n) / (c - a) : ℝ) > 0 := by
      sorry
    have c4 : ((a ^ n - b ^ n) / (a - b) : ℝ) * ((b ^ n - c ^ n) / (b - c) : ℝ) * ((c ^ n - a ^ n) / (c - a) : ℝ) > 0 := by positivity
    have c5 : (-p ^ 3 : ℝ) > 0 := by simpa [h6] using c4
    have c6 : (p ^ 3 : ℝ) > 0 := by have := hp.ne_zero; rify at this; positivity
    linarith

-- Let $$d$$ be the greatest common divisor of the three differences $$a-b, b-c, c-a$$,
  let d := ((a - b).gcd (b - c) : ℤ).gcd (c - a)

-- so that $$a-b=d u, b-c=d v, \quad c-a=d w $$
  have ⟨u, h8⟩ : (d : ℤ) ∣ a - b := by
    sorry
  have ⟨v, h9⟩ : (d : ℤ) ∣ b - c := by
    sorry
  have ⟨w, h10⟩ : (d : ℤ) ∣ c - a := by
    sorry
-- and $$\operatorname{gcd}(u, v, w)=1, u+v+w=0$$.
  have h11 : (u.gcd v : ℤ).gcd w = 1 := by
    sorry
  have h12 : u + v + w = 0 := by
    sorry

-- From $$a^{n}-b^{n}=-p(b-c)$$ we see that $$(a-b) \mid p(b-c)$$,
-- i.e., $$u \mid p v$$
  have h13 : u ∣ p * v := by
    sorry

--  and cyclically $$v|p w, w| p u$$.
  have h14 : v ∣ p * w := by
    sorry
  have h15 : w ∣ p * u := by
    sorry


-- Suppose that the prime $$p$$ does not divide any of $$u, v, w$$.
-- We get $$u|v, v| w, w \mid u$$, whence $$|u|=|v|=|w|=1$$;
-- but this quarrels with $$u+v+w=0$$.
-- So $$p$$ must divide at least one of $$u, v, w$$.
  have h16 : (p : ℤ) ∣ u ∨ (p : ℤ) ∣ v ∨ (p : ℤ) ∣ w := by
    by_contra! h16
    obtain ⟨c1, c2, c3⟩ := h16
    rw [←hp.coprime_iff_not_dvd] at c1 c2 c3
    have ⟨k1, hk1⟩ : u ∣ v := IsCoprime.dvd_of_dvd_mul_left c1.symm h13
    have ⟨k2, hk2⟩ : v ∣ w := IsCoprime.dvd_of_dvd_mul_left c2.symm h14
    have ⟨k3, hk3⟩ : w ∣ u := IsCoprime.dvd_of_dvd_mul_left c3.symm h15
    rw [hk2, hk1] at hk3
    have hu : u ≠ 0 := by
      sorry
    have hk : 1 = k1 * k2 * k3 := by
      sorry
    have hu' : |u| = 1 := by
      sorry
    have hv' : |v| = 1 := by
      sorry
    have hw' : |w| = 1 := by
      sorry
    rw [abs_eq (by norm_num)] at hu' hv' hw'
    -- contradicts $$u+v+w=0$$.
    omega

-- As $$\operatorname{gcd}(u, v, w)=1$$ and $$u+v+w=0$$,
-- at most one of $$u, v, w$$ can be divisible by $$p$$.
-- Therefore $$p$$ must divide exactly one of these numbers.
  have h17 :
      ((p : ℤ) ∣ u ∧ ¬(p : ℤ) ∣ v ∧ ¬(p : ℤ) ∣ w)
      ∨ (¬(p : ℤ) ∣ u ∧ (p : ℤ) ∣ v ∧ ¬(p : ℤ) ∣ w)
      ∨ (¬(p : ℤ) ∣ u ∧ ¬(p : ℤ) ∣ v ∧ (p : ℤ) ∣ w)
      := by
    sorry

  obtain ⟨⟨u1, h17⟩, h18, h19⟩ | ⟨h17, ⟨v1, h18⟩, h19⟩ | ⟨h17, h18, ⟨w1, h19⟩⟩ := h17
-- Let e.g. $$p \mid u$$ and write $$u=p u_{1}$$.
  .
-- Now we obtain, similarly as before, $$u_{1}|v, v| w, w \mid u_{1}$$ so that $$\left|u_{1}\right|=|v|=|w|=1$$.
    have h20 : u1 ∣ v := by
      sorry
    have h21 : v ∣ w := by
      sorry
    have h22 : w ∣ u1 := by
      sorry
    have hu1' : |u1| = 1 := by
      sorry
    have hv' : |v| = 1 := by
      sorry
    have hw' : |w| = 1 := by
      sorry

    rw [abs_eq (by norm_num)] at hu1' hv' hw'
-- The equation $$p u_{1}+v+w=0$$ forces that the prime $$p$$ must be even;
    have h23 : p % 2 = 0 := by
      rw [h17] at h12
      sorry
-- i.e. $$p=2$$.
    replace h23 : p = 2 := by
      refine (Nat.Prime.even_iff ?_).mp ?_
      . sorry
      . sorry

-- Hence $$v+w=-2 u_{1}= \pm 2$$, implying $$v=w(= \pm 1)$$ and $$u=-2 v$$.
    have h24 : v + w = 2 ∨ v + w = -2 := by
      sorry
    have h25 : u = -2 * v := by omega

--Consequently $$a-b=-2(b-c)$$.
    have h26 : a - b = -2 * (b - c) := by
      rw [h8, h9, h25]
      ring

-- Knowing that $$n$$ is even, say $$n=2 k$$,
-- we rewrite the equation $$a^{n}-b^{n}=-p(b-c)$$ with $$p=2$$
-- in the form $$ \left(a^{k}+b^{k}\right)\left(a^{k}-b^{k}\right)=-2(b-c)=a-b . $$
    have h27 : (a ^ k + b ^ k) * (a ^ k - b ^ k) = a - b := by
      calc
        _ = a ^ n - b ^ n := by rw [h7]; ring
        _ = -p * (b - c) := by linarith
        _ = -2 * (b - c) := by rw [h23]; norm_cast
        _ = _ := by rw [h26]

-- The second factor on the left is divisible by $$a-b$$,
    have h28 : a - b ∣ a ^ k - b ^ k  := by
      sorry

-- so the first factor $$\left(a^{k}+b^{k}\right)$$ must be $$\pm 1$$.
    have h29 : a ^ k + b ^ k = 1 ∨ a ^ k + b ^ k = -1 := by
      sorry

-- Then exactly one of $$a$$ and $$b$$ must be odd
    have h30 : a % 2 = 1 ∧ b % 2 = 0 ∨ a % 2 = 0 ∧ b % 2 = 1 := by
      sorry
-- yet $$a-b=-2(b-c)$$ is even.
-- Contradiction ends the proof.
    omega
  . sorry
  . sorry
