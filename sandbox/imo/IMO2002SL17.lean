import Mathlib

open Polynomial Filter

/-
Let $P$ be a cubic polynomial given by $P(x)=a x^{3}+b x^{2}+c x+$ $d$,
where $a, b, c, d$ are integers and $a \neq 0$.
Suppose that $x P(x)=y P(y)$ for infinitely many pairs $x, y$ of integers with $x \neq y$.
Prove that the equation $P(x)=0$ has an integer root.
-/
theorem algebra_25116
    (a b c d : ℤ) (ha : a ≠ 0)
    (P : ℤ[X])
    (hP : P = C a * X ^ 3 + C b * X ^ 2 + C c * X + C d)
    (hP2 : { (x, y) : ℤ × ℤ | x ≠ y ∧ x * P.eval x = y * P.eval y }.Infinite)
    : ∃ x : ℤ, P.eval x = 0 := by

-- Let $x, y$ be distinct integers satisfying $x P(x)=y P(y)$;
-- this means $a\left(x^{4}-y^{4}\right)+b\left(x^{3}-y^{3}\right)+c\left(x^{2}-y^{2}\right)+d(x-y)=0$.
  have h1 (x y : ℤ) (hxy : x ≠ y) (c1 : x * P.eval x = y * P.eval y) :
      a * (x ^ 4 - y ^ 4) + b * (x ^ 3 - y ^ 3) + c * (x ^ 2 - y ^ 2) + d * (x - y) = 0 := by
    simp [hP] at c1
    linarith

-- Dividing by $x-y$ we obtain $ a\left(x^{3}+x^{2} y+x y^{2}+y^{3}\right)+b\left(x^{2}+x y+y^{2}\right)+c(x+y)+d=0 $
  have h2 (x y : ℤ) (hxy : x ≠ y) (c1 : x * P.eval x = y * P.eval y) :
      a * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3) + b * (x ^ 2 + x * y + y ^ 2) + c * (x + y) + d = 0 := by
    specialize h1 x y hxy c1
    qify at h1 hxy ⊢
    apply_fun (. / (x - y : ℚ)) at h1
    convert h1 using 1
    . symm
      calc
        (_ : ℚ) = a * ((x ^ 4 - y ^ 4) / (x - y)) + b * ((x ^ 3 - y ^ 3) / (x - y))
            + c * ((x ^ 2 - y ^ 2) / (x - y)) + d * ((x - y) / (x - y)) := by field_simp
        _ = a * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3) + b * (x ^ 2 + x * y + y ^ 2)
            + c * (x + y) + d * 1 := by
          replace hxy : (x - y : ℚ) ≠ 0 := by exact sub_ne_zero_of_ne hxy
          iterate 3 congr 1
          all_goals congr 1
          all_goals field_simp
          all_goals ring
        _ = _ := by ring
    . simp

-- Putting $x+y=p, x^{2}+y^{2}=q$ leads to $x^{2}+x y+y^{2}=\frac{p^{2}+q}{2}$,
  let p (x y : ℤ) := x + y
  let q (x y : ℤ) := x ^ 2 + y ^ 2
  have h3 (x y : ℤ) : x ^ 2 + x * y + y ^ 2 = ((p x y ^ 2 + q x y) / 2 : ℚ) := by
    field_simp [p, q]
    ring

-- so the above equality becomes $ a p q+b\frac{p^{2}+q}{2}+c p+d=0, \quad \text { i.e. } \quad(2 a p+b) q=-\left(b p^{2}+2 c p+2 d\right) $
  have h4 (x y : ℤ) (hxy : x ≠ y) (c1 : x * P.eval x = y * P.eval y) :
      (2 * a * p x y + b) * q x y = -(b * p x y ^ 2 + 2 * c * p x y + 2 * d) := by
    suffices a * p x y * q x y + b * ((p x y ^ 2 + q x y) / 2 : ℚ) + c * p x y + d = 0 by
      qify
      linarith
    specialize h3 x y
    rw [←h3]
    dsimp [p, q]
    specialize h2 x y hxy c1
    qify at h2 ⊢
    linarith

-- Since $2 q \geq p^{2} $, it follows that $p^{2}|2 a p+b| \leq 2\left|b p^{2}+2 c p+2 d\right|$,
  have h5 (x y : ℤ) (hxy : x ≠ y) (c1 : x * P.eval x = y * P.eval y) :
      p x y ^ 2 * |2 * a * p x y + b| ≤ 2 * |b * p x y ^ 2 + 2 * c * p x y + 2 * d| := by
    specialize h4 x y hxy c1
    have c1 : p x y ^ 2 ≤ 2 * q x y := by
      dsimp [p, q]
      suffices (x - y) ^ 2 ≥ 0 by linarith
      positivity
    calc
      (_ : ℤ) ≤ 2 * q x y * |2 * a * p x y + b| := by gcongr
      _ = 2 * (|2 * a * p x y + b| * q x y) := by ring
      _ = 2 * (|2 * a * p x y + b| * |q x y|) := by
        congr 2
        symm
        apply abs_of_nonneg
        positivity
      _ = 2 * (|(2 * a * p x y + b) * (q x y)|) := by
        congr 1
        rw [abs_mul]
      _ = 2 * |-(b * p x y ^ 2 + 2 * c * p x y + 2 * d)| := by congr 2
      _ = _ := by
        congr 1
        apply abs_neg

-- which is possible only for finitely many values of $p$,
  have h6 : { p : ℤ | p ^ 2 * |2 * a * p + b| ≤ 2 * |b * p ^ 2 + 2 * c * p + 2 * d| }.Finite := by
    let u (p : ℤ) := (p ^ 2 * (2 * a * p + b) / (2 * (b * p ^ 2 + 2 * c * p + 2 * d)) : ℚ)
    convert_to { p : ℤ | |u p| ≤ 1 }.Finite using 3 with p
    . symm
      calc
        |u p| ≤ 1 ↔ |(p ^ 2 * (2 * a * p + b) : ℚ) / (2 * (b * p ^ 2 + 2 * c * p + 2 * d))| ≤ 1 := by
          congr! 1
        _ ↔ (|(p ^ 2 * (2 * a * p + b) : ℚ)| / |(2 * (b * p ^ 2 + 2 * c * p + 2 * d) : ℚ)|) ≤ 1 := by
          congr! 1
          apply abs_div
        _ ↔ (|(p ^ 2 : ℚ)| * |((2 * a * p + b) : ℚ)| / (|(2 : ℚ)| * |(b * p ^ 2 + 2 * c * p + 2 * d : ℚ)|)) ≤ 1 := by
          congr! 2 <;> apply abs_mul
        _ ↔ ((p ^ 2 : ℚ) * |((2 * a * p + b) : ℚ)| / ((2 : ℚ) * |(b * p ^ 2 + 2 * c * p + 2 * d : ℚ)|)) ≤ 1 := by
          congr! 3
          apply abs_sq
        _ ↔ ((p ^ 2 : ℚ) * |((2 * a * p + b) : ℚ)| ≤ ((2 : ℚ) * |(b * p ^ 2 + 2 * c * p + 2 * d : ℚ)|)) := by
          apply div_le_one₀
          sorry
        _ ↔ _ := by norm_cast
    suffices Tendsto u atTop atTop by sorry
    sorry

-- So there are finitely many values of $x + y$ with $x \neq y$ and $x P(x)=y P(y)$.
  have h7 : { p : ℤ | ∃ (x y : ℤ) (_ : x ≠ y) (_ : x * P.eval x = y * P.eval y),
      p = x + y }.Finite := by
    set A := {p | p ^ 2 * |2 * a * p + b| ≤ 2 * |b * p ^ 2 + 2 * c * p + 2 * d|}
    set B := {p | ∃ x y, ∃ (_ : x ≠ y) (_ : x * eval x P = y * eval y P), p = x + y}
    suffices B ⊆ A by exact Set.Finite.subset h6 this
    intro q ⟨x, y, c1, c2, hq⟩
    specialize h5 x y c1 c2
    have c3 : p x y = q := by rw [hq]
    simpa [c3] using h5

-- Now, it can't be the case that for every given value of $p = x + y$,
-- there are finitely many $x$ with $x \neq y$ and $x P(x)=y P(y)$.
-- Otherwise, there would be finitely many pairs $(x, y)$ with $x \neq y$ and $x P(x)=y P(y)$.
-- Hence there must exists $p$ such that $x P(x)=(p-x) P(p-x)$ for infinitely many $x$.
  have ⟨p, h8⟩ : ∃ p : ℤ, { x : ℤ | x * P.eval x = (p - x) * P.eval (p - x) }.Infinite := by
    sorry

-- and therefore for all $x$ since these expressions are polynomials in $x$.
  have h9 (x : ℤ) : x * P.eval x = (p - x) * P.eval (p - x) := by
    let Q := X * P - (C p - X) * P.comp (C p - X)
    have c1 (x : ℤ) : x * P.eval x = (p - x) * P.eval (p - x) ↔ Q.eval x = 0 := by
      dsimp [Q]
      constructor
      all_goals intro h
      all_goals simp at h ⊢
      all_goals linarith
    simp only [c1] at h8 ⊢
    suffices Q = 0 by simp [this]
    exact eq_zero_of_infinite_isRoot Q h8

  obtain h10 | h10 : p ≠ 0 ∨ p = 0 := by omega
-- If $p \neq 0$, then $p$ is a root of $P(x)$.
  . use p
    specialize h9 p
    simpa [h10] using h9
-- If $p=0$, the above relation gives $P(x)=-P(-x)$.
  . subst h10
-- This forces $b=d=0$, so $P(x)=x\left(a x^{2}+c\right)$.
-- Thus 0 is a root of $P(x)$.
    simp at h9
    rw [hP] at h9
    simp at h9
    sorry
