import Mathlib

/- Find all functions $f: \mathbb{N} \rightarrow \mathbb{N}$ such that $f(n!)=f(n)!$ for all positive integers $n$ and such
that $m-n$ divides $f(m)-f(n)$ for all distinct positive integers $m, n$.

-/
theorem number_theory_248688 (f : ℕ → ℕ) :
    (∀ n, n > 0 → f n.factorial = (f n).factorial) ∧
    (∀ m n : ℕ, 0 < m → 0 < n → m ≠ n → (m - n : ℤ) ∣ (f m - f n : ℤ)) ↔
    (∀ n, n > 0 → f n = 1) ∨ (∀ n, n > 0 → f n = 2) ∨ ∀ n, n > 0 → f n = n := by
  constructor
  · intro ⟨h1, h2⟩

-- By putting $n=1$ and $n=2$ we obtain $f(1), f(2) \in\{1,2\}$.
    have h3 : f 1 = 1 ∨ f 1 = 2 := by
      specialize h1 1 (by norm_num)
      convert_to f 1 = (f 1).factorial using 1 at h1
      by_contra! c1
      obtain c2 | c2 : f 1 = 0 ∨ f 1 ≥ 3 := by omega
      · simp [c2] at h1
      · have c3 := (f 1).lt_factorial_self c2
        omega
    have h4 : f 2 = 1 ∨ f 2 = 2 := by
      specialize h1 2 (by norm_num)
      convert_to f 2 = (f 2).factorial using 1 at h1
      by_contra! c1
      obtain c2 | c2 : f 2 = 0 ∨ f 2 ≥ 3 := by omega
      · simp [c2] at h1
      · have c3 := (f 2).lt_factorial_self c2
        omega

-- Also, we will use the condition $m!-n!$ divides $f(m)!-f(n)!$.
    have h5 (m n : ℕ) (hm : m > 0) (hn : n > 0) :
        (m.factorial - n.factorial : ℤ) ∣ ((f m).factorial - (f n).factorial : ℤ) := by
      specialize h2 m.factorial n.factorial m.factorial_pos n.factorial_pos
      by_cases hmn : m = n
      · subst hmn
        simp
      · sorry

-- We consider four cases on $f(1)$ and $f(2)$, and dispense with three of them.

-- - If $f(2)=1$ then for all $m \geq 3$ we have $m!-2$ divides $f(m)!-1$, so $f(m)=1$ for modulo 2 reasons.
-- And clearly $f(1)=1$.
    have h6 (c1 : f 2 = 1) (m : ℕ) (hm : m > 0) : f m = 1 := by
      obtain hm | hm | hm : m = 2 ∨ m ≥ 3 ∨ m = 1 := by omega
      · subst hm
        exact c1
      · have c2 : (m.factorial - 2 : ℤ) ∣ (f m).factorial - 1 := by
          convert h5 m 2 (by omega) (by norm_num) using 2
          symm
          simp only [Nat.cast_eq_one, Nat.factorial_eq_one]
          omega
        by_contra! c3
        obtain c3 | c3 : f m = 0 ∨ f m ≥ 2 := by omega
        · sorry
        · obtain ⟨k, c2⟩ := c2
          have c4 : ((f m).factorial : ℤ) % 2 = 0 := by sorry
          have c5 : (m.factorial : ℤ) % 2 = 0 := by sorry
          replace c5 : (m.factorial - 2 : ℤ) * k % 2 = 0 := by sorry
          omega
      · sorry

-- - If $f(1)=f(2)=2$ we first obtain $3!-1 \mid f(3)!-2$, which implies $f(3)=2$.
-- Then $m!-3 \mid f(m)!-2$ for $m \geq 4$ implies $f(m)=2$ for modulo 3 reasons.
    have h7 (c1 : f 1 = 2) (c2 : f 2 = 2) (m : ℕ) (hm : m > 0) : f m = 2 := by
      sorry

-- Hence we are left with the case where $f(1)=1$ and $f(2)=2$.
    suffices f 1 = 1 ∧ f 2 = 2 → ∀ m > 0, f m = m by
      obtain h4 | h4 := h4
      · specialize h6 h4
        tauto
      · obtain h3 | h3 := h3
        · specialize this ⟨h3, h4⟩
          tauto
        · specialize h7 h3 h4
          tauto
    intro ⟨h8, h9⟩

-- Continuing, we have $$ 3!-1 \mid f(3)!-1 \quad \text { and } \quad 3!-2 \mid f(3)!-2 \Longrightarrow f(3)=3 \text {. } $$
    have h10 : f 3 = 3 := by
      have c1 : ((3).factorial - 1 : ℤ) ∣ (f 3).factorial - 1 := by
        sorry
      have c2 : ((3).factorial - 2 : ℤ) ∣ (f 3).factorial - 2 := by
        sorry
      sorry

-- Continuing by induction, suppose $f(1)=1, \ldots, f(k)=k$. $$ k!\cdot k=(k+1)!-k!\mid f(k+1)!-k! $$
-- and thus we deduce that $f(k+1) \geq k$, and hence $$ k \left\lvert\, \frac{f(k+1)!}{k!}-1\right. $$
-- Then plainly $f(k+1) \leq 2 k$ for $\bmod k$ reasons, but also $f(k+1) \equiv 1(\bmod k)$
-- so we conclude $f(k+1)=k+1$.
    have h11 : ∀ k, f (k + 1) = k + 1 := by
      apply Nat.strongRec
      intro k ih
      obtain hk | hk | hk : k = 0 ∨ k = 1 ∨ k ≥ 2 := by omega
      · subst hk
        simpa using h8
      · subst hk
        simpa using h9
      · have c1 := calc
          (k.factorial * k : ℤ) = (k + 1).factorial - k.factorial := by
            rw [Nat.factorial_succ]
            push_cast
            ring
          _ ∣ (f (k + 1)).factorial - k.factorial := by
            convert h5 (k + 1) k (by omega) (by omega) using 4
            symm
            convert ih (k - 1) (by omega) using 2
            all_goals omega
        have c2 : f (k + 1) ≥ k := by
          sorry
        have c3 : (k : ℤ) ∣ (f (k + 1)).factorial / k.factorial - 1 := by
          obtain ⟨l, c1⟩ := c1
          use l
          apply_fun (fun x : ℤ => x * k.factorial)
          swap
          · refine mul_left_injective₀ ?_
            norm_cast
            exact Nat.factorial_ne_zero k
          beta_reduce
          convert c1 using 1
          · rw [sub_mul]
            congr 1
            · refine Int.ediv_mul_cancel ?_
              norm_cast
              exact Nat.factorial_dvd_factorial c2
            · ring
          · ring
        have c4 : f (k + 1) ≤ 2 * k := by
          sorry
        have c5 : (f (k + 1) - 1 : ℤ) % k = 0 := by
          sorry
        replace ⟨l, c5⟩ := Int.dvd_of_emod_eq_zero c5
        replace c5 : f (k + 1) = k * l + 1 := by omega
        zify at c2 c4 hk
        obtain c6 | c6 | c6 : l ≤ 0 ∨ l ≥ 2 ∨ l = 1 := by omega
        · nlinarith
        · nlinarith
        · subst c6
          zify
          convert c5 using 1
          ring

-- The desired functions must be $f \equiv 1, f \equiv 2$, or the identity.
    intro m hm
    convert h11 (m - 1) using 2
    · omega
    · omega
-- As these functions obviously work, they are the only ones.
  · intro h1
    obtain h1 | h1 | h1 := h1
    all_goals
      split_ands
      · intro n hn
        simp [h1 n hn]
        apply h1 n.factorial
        apply Nat.factorial_pos
      · intro m n hm hn hmn
        simp [h1 m hm, h1 n hn]
