import Mathlib

open Set

/- Let $  a, b, c$   be positive integers satisfying the conditions $  b>2 a$   and $  c>2 b$  .
Show that there exists a real number $  t$   with the property that
all the three numbers $  t a, t b, t c$   have their fractional parts lying in the interval $ (1/3,2/3]$ . -/
theorem algebra_25029
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : b > 2 * a) (hcb : c > 2 * b) :
    ∃ t : ℝ,
      Int.fract (t * a) ∈ Ioc (1 / 3) (2 / 3)
      ∧ Int.fract (t * b) ∈ Ioc (1 / 3) (2 / 3)
      ∧ Int.fract (t * c) ∈ Ioc (1 / 3) (2 / 3)
    := by

-- We note that $  \{t x\}$   lies in $  \left(\frac{1}{3}, \frac{2}{3}\right]$   if and only if
-- there is an integer $  k$   such that $  k+\frac{1}{3} < t x \leq k+\frac{2}{3}$  ,
  have h1 (t : ℝ) (x : ℕ) (hx : x > 0) : Int.fract (t * x) ∈ Ioc (1 / 3) (2 / 3) ↔
      ∃ k : ℤ, k + 1 / 3 < t * x ∧ t * x ≤ k + 2 / 3 := by
      constructor
      . intro ⟨c1, c2⟩
        rw [Int.fract] at c1 c2
        use ⌊t * x⌋
        split_ands <;> linarith
      . intro ⟨k, c1, c2⟩
        rw [Int.fract]
        have c3 : ⌊t * x⌋ = k := by apply Int.floor_eq_iff.mpr; split_ands <;> linarith
        rw [c3]
        constructor <;> linarith

-- i.e., if and only if $  t \in H_{k}=\left(\frac{k+1 / 3}{x}, \frac{k+2 / 3}{x}\right]$   for some $  k$  .
  let H (x : ℝ) (k : ℤ) : Set ℝ := Icc ((k + 1 / 3) / x) ((k + 2 / 3) / x)
  replace h1 (t : ℝ) (x : ℕ) (hx : x > 0) : Int.fract (t * x) ∈ Ioc (1 / 3) (2 / 3) ↔ ∃ k, t ∈ H x k := by
    sorry

-- If we write $  I_{k}=\left(\frac{k+1 / 3}{a}, \frac{k+2 / 3}{a}\right]$ , $  J_{m}=\left(\frac{m+1 / 3}{b}, \frac{m+2 / 3}{b}\right]$   and $  K_{n}=\left(\frac{n+1 / 3}{c}, \frac{n+2 / 3}{c}\right]$

-- We have to show that $  I_{k} \cap J_{m} \cap K_{n}$   is nonempty for some integers $  k, m, n$  .
  let I (k : ℤ) : Set ℝ := Icc ((k + 1 / 3) / a) ((k + 2 / 3) / a)
  let J (m : ℤ) : Set ℝ := Icc ((m + 1 / 3) / b) ((m + 2 / 3) / b)
  let K (n : ℤ) : Set ℝ := Icc ((n + 1 / 3) / c) ((n + 2 / 3) / c)
  suffices ∃ k m n : ℤ, ((I k) ∩ (J m) ∩ (K n)).Nonempty from by
    obtain ⟨k, m, n, c1⟩ := this
    obtain ⟨t, ⟨c1, c2⟩, c3⟩ := c1
    use t
    use by apply (h1 t a ha).mpr; use k
    use by apply (h1 t b hb).mpr; use m
    apply (h1 t c hc).mpr; use n

-- The intervals $  K_{n}$   are separated by a distance $  \frac{2}{3 c}$  , and since $  \frac{2}{3 c} < \frac{1}{3 b}$  ,
-- each of the intervals $  J_{m}$   intersects at least one of the $  K_{n}$   's.
  have h2 (m : ℤ) : ∃ n : ℤ, ((J m) ∩ (K n)).Nonempty := by
    sorry

-- Hence it is enough to prove that $  J_{m} \subset I_{k}$   for some $  k, m$  .
  suffices ∃ k m : ℤ, J m ⊆ I k from by
    obtain ⟨k, m, c1⟩ := this
    use k
    use m
    have ⟨n, ⟨t, c2, c3⟩⟩ := h2 m
    use n
    use t
    iterate 2 constructor
    . exact c1 c2
    . exact c2
    . exact c3

-- Let $  u_{m}$   and $  v_{m}$   be the left and right endpoints of $  J_{m}$  .
  let u (m : ℤ) : ℝ := (m + 1 / 3) / b
  let v (m : ℤ) : ℝ := (m + 2 / 3) / b

-- Since $  a v_{m}=a u_{m}+$   $  \frac{a}{3 b} < a u_{m}+\frac{1}{6}$  ,
  have h3 m : (a * v m : ℝ) < a * u m + 1 / 6 := calc
    (_ : ℝ) = a * u m + a / (3 * b) := by sorry
    _ < _ := by sorry

-- it will suffice to show that there is an integer $  m$   such that

-- the fractional part of $  a u_{m}$   lies in $  \left[\frac{1}{3}, \frac{1}{2}\right]$  .
  suffices ∃ m, Int.fract (a * u m) ∈ Icc (1 / 3) (1 / 2) from by
    obtain ⟨m, c1⟩ := this
    sorry

-- Let $  a=d \alpha, b=d \beta, \operatorname{gcd}(\alpha, \beta)=1$  .
  let d := Nat.gcd a b
  have hd : d > 0 := Nat.gcd_pos_of_pos_left b ha
  let α := a / d
  let β := b / d
  have hα : a = d * α := by symm; apply Nat.mul_div_cancel'; apply Nat.gcd_dvd_left
  have hβ : b = d * β := by symm; apply Nat.mul_div_cancel'; apply Nat.gcd_dvd_right
  have hαβ : Nat.gcd α β = 1 := Nat.coprime_div_gcd_div_gcd hd

-- Consider $ m∈ℤ$ .
-- we obtain that $  a u_{m}=a \frac{m+1 / 3}{b}=\frac{\alpha m}{\beta}+\frac{\alpha}{3 \beta}$  .
  have h4 (m : ℤ) : a * u m = (α * m / β + α / (3 * β) : ℝ) := calc
    (_ : ℝ) = a * ((m + 1 / 3) / b) := rfl
    _ = a * m / b + a / (3 * b) := by ring_nf
    _ = d * α * m / (d * β) + d * α / (3 * (d * β)) := by rify at hα hβ; rw [←hα, ←hβ]
    _ = α * m / β + α / (3 * β) := by
      congr 1
      . sorry
      . sorry

-- every term of the arithmetic progression $  \frac{j}{\beta}+\frac{\alpha}{3 \beta}(j \in \mathbb{Z})$
-- has its fractional part equal to the fractional part of some $  a u_{m}$  .
  have h5 (j : ℤ) : ∃ m, Int.fract (j / β + α / (3 * β) : ℝ) = Int.fract (a * u m) := by
    sorry

-- We now split the proof in cases $ β ≥ 6$ , $ β ≤ 5$ .
  obtain h6 | h6 : β ≥ 6 ∨ β ≤ 5 := by omega
-- Now for $  \beta \geq 6$   the progression step is $  \frac{1}{\beta} \leq \frac{1}{6}$  ,
  . have h7 : (1 / β : ℝ) ≤ 1 / 6 := by
      rify at h6
      refine one_div_le_one_div_of_le ?_ h6
      norm_num

    have ⟨j, h8⟩ : ∃ j : ℤ, Int.fract (j / β + α / (3 * β) : ℝ) ∈ Icc (1 / 3) (1 / 2) := by
      sorry

-- so at least one of the $  a u_{m}$   has its fractional part in $  [1 / 3,1 / 2]$  .
    obtain ⟨m, h9⟩ := h5 j
    use m
    rw [←h9]
    exact h8
  .
-- If otherwise $  \beta \leq 5$  , the only irreducible fractions $  \frac{\alpha}{\beta}$   that satisfy $  2 \alpha < \beta$   are $  \frac{1}{3}, \frac{1}{4}, \frac{1}{5}, \frac{2}{5}$  ;
    have h7 : α = 1 ∧ β = 3 ∨ α = 1 ∧ β = 4 ∨ α = 1 ∧ β = 5 ∨ α = 2 ∧ β = 5 := by
      sorry

-- hence one can take $  m$   to be $  1,1,2,3$   respectively.
    obtain ⟨h7, h8⟩ | ⟨h7, h8⟩ | ⟨h7, h8⟩ | ⟨h7, h8⟩ := h7
    . use 1
      norm_num [h4, h7, h8, Int.fract]
    . use 1
      norm_num [h4, h7, h8, Int.fract]
    . use 2
      norm_num [h4, h7, h8, Int.fract]
    . use 3
      norm_num [h4, h7, h8, Int.fract]
