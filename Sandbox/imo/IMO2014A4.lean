import Mathlib

/- Determine all functions $f: \mathbb{Z} \rightarrow \mathbb{Z}$ satisfying
$ f(f(m)+n)+f(m)=f(n)+f(3 m)+2014 $  for all integers $m$ and $n$.    (1)
-/
theorem algebra_24394 :
    {f : ℤ → ℤ | ∀ m n, f (f m + n) + f m = f n + f (3 * m) + 2014} =
    {f : ℤ → ℤ | ∀ n, f n = 2 * n + 1007} := by
  ext f
  dsimp
  constructor
  .
-- Let $f$ be a function satisfying (1).
    intro h1
-- Set $C=1007$ and define the function $g: \mathbb{Z} \rightarrow \mathbb{Z}$ by $g(m)=f(3 m)-f(m)+2 C$ for all $m \in \mathbb{Z}$;
    let C := 1007
    let g (m : ℤ) := f (3 * m) - f m + 2 * C

-- in particular, $g(0)=2 C$.
    have h2 : g 0 = 2 * C := by simp [g]

-- Now (1) rewrites as $ f(f(m)+n)=g(m)+f(n) $ for all $m, n \in \mathbb{Z}$.
    have h3 (m n : ℤ) : f (f m + n) = g m + f n := by
      unfold g
      have c1 : (2 * C : ℤ) = 2014 := by norm_num [C]
      rw [c1]
      specialize h1 m n
      linarith

-- By induction in both directions it follows that $ f(t f(m)+n)=t g(m)+f(n) $ holds for all $m, n, t \in \mathbb{Z}$.   (2)
    have h4 (m n t : ℤ) : f (t * f m + n) = t * g m + f n := by
      sorry

-- Applying this, for any $r \in \mathbb{Z}$, to the triples $(r, 0, f(0))$ and $(0,0, f(r))$ in place of $(m, n, t)$ we obtain
-- $ f(0) g(r)=f(f(r) f(0))-f(0)=f(r) g(0) $
    have h5 (r : ℤ) : f 0 * g r = f r * g 0 := by
      sorry

-- Now if $f(0)$ vanished, then $g(0)=2 C > 0$ would entail that $f$ vanishes identically, contrary to (1).
-- Thus $f(0) \neq 0$
    have h6 : f 0 ≠ 0 := by
      by_contra! h6
      replace h3 : 0 = g 0 := by simpa [h6] using h3 0 0
      simp [h2, C] at h3
-- and the previous equation yields $g(r)=\alpha f(r)$,
-- where $\alpha=\frac{g(0)}{f(0)}$ is some nonzero constant.
    let α := (g 0 / f 0 : ℚ)
    have h7 (r : ℤ) : g r = α * f r := by
      unfold α
      field_simp
      specialize h5 r
      qify at h5
      convert h5 using 1 <;> ring

-- So the definition of $g$ reveals $f(3 m)=(1+\alpha) f(m)-2 C$
    have h8 (m : ℤ) : f (3 * m) = (1 + α) * f m - 2 * C := by
      specialize h7 m
      unfold g at h7
      push_cast at h7
      have c1 : (2014 : ℚ) = 2 * C := by norm_num [C]
      rw [c1] at h7
      linarith
-- i.e., $ f(3 m)-\beta=(1+\alpha)(f(m)-\beta) $ for all $m \in \mathbb{Z}$, where $\beta=\frac{2 C}{\alpha}$.      (3)
    let β := (2 * C / α : ℚ)
    replace h8 (m : ℤ) : f (3 * m) - β = (1 + α) * (f m - β) := by
      unfold β
      calc
        _ = (1 + α) * f m - 2 * C - 2 * C / α := by simp [h8]
        _ = _ := by
          field_simp
          ring

-- By induction on $k$ this implies $ f\left(3^{k} m\right)-\beta=(1+\alpha)^{k}(f(m)-\beta) $ for all integers $k \geqslant 0$ and $m$.    (4)
    have h9 (k : ℕ) (m : ℤ) : f (3 ^ k * m) - β = (1 + α) ^ k * (f m - β) := by
      induction' k with k ih
      . simp
      . calc
          _ = f (3 * (3 ^ k * m)) - β := by ring_nf
          _ = _ := by
            rw [h8, ih]
            ring

-- Since $3 \nmid 2014$, there exists by (1) some value $d=f(a)$ attained by $f$ that is not divisible by 3 .
    obtain ⟨a, h10⟩ : ∃ a : ℤ, f a % 3 ≠ 0 := by
      by_contra! h10
      specialize h1 0 0
      replace h1 : f (f 0) + f 0 = f 0 + f 0 + 2014 := by simpa using h1
      have c1 := h10 0
      have c2 := h10 (f 0)
      omega
    let d := f a

-- Now by (2) we have $f(n+t d)=f(n)+t g(a)=f(n)+\alpha \cdot t f(a)$
    have h11 (n t : ℤ) : f (n + t * d) = f n + α * t * f a := by
      specialize h4 a n t
      qify at h4
      convert h4 using 1
      . ring_nf
      . calc
        _ = t * (α * f a) + f n := by ring
        _ = _ := by
          congr 2
          rw [h7]
-- i.e., $ f(n+t d)=f(n)+\alpha \cdot t d $ for all $n, t \in \mathbb{Z}$.        (5)
    replace h11 (n t : ℤ) : f (n + t * d) = f n + α * t * d := by convert h11 n t using 1

-- Let us fix any positive integer $k$ with $d \mid\left(3^{k}-1\right)$,
-- which is possible, since $\operatorname{gcd}(3, d)=1$.
-- E.g., by the Euler-Fermat theorem, we may take $k=\varphi(|d|)$.
    obtain ⟨k, hk, h12⟩ : ∃ k : ℕ, k > 0 ∧ d ∣ (3 ^ k - 1) := by
      use Nat.totient d.natAbs
      constructor
      . refine Nat.totient_pos.mpr ?_
        refine Int.natAbs_pos.mpr ?_
        unfold d
        omega
      . calc
          d ∣ d.natAbs := by exact Int.dvd_natAbs_self
          _ ∣ _ := by
            obtain hd | hd | hd : d.natAbs = 0 ∨ d.natAbs = 1 ∨ d.natAbs > 1 := by
              omega
            . simp [hd]
            . simp [hd]
            . refine Int.dvd_sub_of_emod_eq ?_
              norm_cast
              refine Nat.mod_eq_of_modEq ?_ hd
              . refine Nat.ModEq.pow_totient ?_
                have c2 : (3).Prime := by decide
                have c3 := Nat.coprime_or_dvd_of_prime c2 d.natAbs
                omega

-- Now for each $m \in \mathbb{Z}$ we get $ f\left(3^{k} m\right)=f(m)+\alpha\left(3^{k}-1\right) m $ from (5),
    have h13 (m : ℤ) : f (3 ^ k * m) = f m + α * (3 ^ k - 1) * m := by
      convert h11 m (m * ((3 ^ k - 1) / d)) using 1
      . congr 2
        calc
          _ = m + m * (3 ^ k - 1) := by ring
          _ = _ := by
            congr 1
            calc
              _ = m * ((3 ^ k - 1) / d * d) := by rw [Int.ediv_mul_cancel h12]
              _ = _ := by ring
      . congr 1
        calc
          _ = α * (m * (3 ^ k - 1)) := by ring
          _ = α * (m * (((3 ^ k - 1) / d : ℤ) * d)) := by
            congr 2
            calc
              (_ : ℚ) = (3 ^ k - 1 : ℤ) := by norm_cast
              _ = ((3 ^ k - 1) / d * d : ℤ) := by rw [Int.ediv_mul_cancel h12]
              _ = _ := by norm_cast
          _ = _ := by
            push_cast
            ring

-- which in view of (4) yields $\left((1+\alpha)^{k}-1\right)(f(m)-\beta)=\alpha\left(3^{k}-1\right) m$.
    have h14 (m : ℤ) : ((1 + α) ^ k - 1) * (f m - β) = α * (3 ^ k - 1) * m := by
      specialize h9 k m
      specialize h13 m
      calc
        _ = ((1 + α) ^ k) * (f m - β) - f m + β := by ring
        _ = f (3 ^ k * m) - f m := by
          rw [←h9]
          ring
        _ = _ := by
          rw [h13]
          ring
-- Since $\alpha \neq 0$, the right hand side does not vanish for $m \neq 0$,
-- wherefore the first factor on the left hand side cannot vanish either.
-- It follows that $ f(m)=\frac{\alpha\left(3^{k}-1\right)}{(1+\alpha)^{k}-1} \cdot m+\beta $
    have h15 (m : ℤ) : f m = (α * (3 ^ k - 1) / ((1 + α) ^ k - 1) : ℚ) * m + β := by
      obtain c0 | c0 : m = 0 ∨ m ≠ 0 := by omega
      . simp [c0]
        unfold β α
        rw [h2]
        field_simp
      . have c1 : (1 + α) ^ k - 1 ≠ 0 := by
          have d1 : α ≠ 0 := by
            unfold α
            suffices g 0 ≠ 0 by field_simp; simpa using this
            rw [h2]
            unfold C
            norm_num
          have d2 : (3 ^ k - 1 : ℚ) ≠ 0 := by
            by_contra! d2
            replace d2 : 3 ^ k = 3 ^ 0 := by
              qify
              linarith
            replace d2 : k = 0 := Nat.pow_right_injective (by norm_num : 2 ≤ 3) d2
            omega
          have d3 : (m : ℚ) ≠ 0 := by norm_cast
          have d4 : α * (3 ^ k - 1) * m ≠ 0 := by positivity
          rw [←h14] at d4
          exact left_ne_zero_of_mul d4
        specialize h14 m
        field_simp [c1]
        linarith

-- So $f$ is a linear function, say $f(m)=A m+\beta$ for all $m \in \mathbb{Z}$ with some constant $A \in \mathbb{Q}$.
    set A := (α * (3 ^ k - 1) / ((1 + α) ^ k - 1) : ℚ)

-- Plugging this into (1) one obtains $\left(A^{2}-2 A\right) m+(A \beta-2 C)=0$ for all $m$,
    have h16 (m : ℤ) : (A ^ 2 - 2 * A) * m + (A * β - 2 * C) = 0 := by
      sorry

-- which is equivalent to the conjunction of $ A^{2}=2 A \quad \text { and } \quad A \beta=2 C $
    have ⟨h17, h18⟩ : A ^ 2 = 2 * A ∧ A * β = 2 * C := by
      have c1 : A * β = 2 * C := by
        specialize h16 0
        simp at h16 ⊢
        linarith
      have c2 : A ^ 2 = 2 * A := by
        specialize h16 1
        simp [c1] at h16 ⊢
        linarith
      constructor
      . exact c2
      . exact c1

-- The first equation is equivalent to $A \in\{0,2\}$,
    have h19 : A = 0 ∨ A = 2 := by
      replace h17 : A * (A - 2) = 0 := by linarith
      rw [mul_eq_zero] at h17
      obtain h17 | h17 := h17
      . left
        linarith
      . right
        linarith
-- and as $C \neq 0$ the second one gives $ A=2 \quad \text { and } \quad \beta=C $
    have ⟨h20, h21⟩ : A = 2 ∧ β = C := by
      obtain h19 | h19 := h19
      . simp [h19] at h18
      . constructor
        . exact h19
        . rw [h19] at h18
          linarith

-- This shows that $f$ is indeed the function mentioned in the answer
-- and as the numbers found in (7) do indeed satisfy the equations (6) this function is indeed as desired.
    intro n
    qify
    convert h15 n using 2
    . simp [h20]
    . simp [h21]

-- Conversely, the function $f(n)=2 n+1007$ satisfies (1) for all integers $m$ and $n$,
  . intro h1
    intro m n
    simp [h1]
    ring
