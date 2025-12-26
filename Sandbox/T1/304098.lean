import Mathlib

/-
Let $$k$$ be an integer greater than 1, and the sequence $$\left\{a_{n}\right\}$$ is defined as follows:
$$a_{0}=0$$, $$a_{1}=1,$$ and $$∀ n \ge 1, a_{n+1}=k a_{n}+a_{n-1} .$$
Find all $$k$$ that satisfy the following condition:
there exist non-negative integers $$l, m (l \neq m)$$, and positive integers $$p, q$$, such that
$$a_{l}+k a_{p}=a_{m}+k a_{q} $$
-/
theorem algebra_304098
    (k : ℕ) (hk : k > 1)
    (a : ℕ → ℤ) (ha0 : a 0 = 0) (ha1 : a 1 = 1) (ha2 : ∀ n ≥ 1, a (n + 1) = k * a n + a (n - 1))
    : (∃ (l : ℕ) (m : ℕ) (hlm : l ≠ m) (p : ℕ) (hp : p > 0) (q : ℕ) (hq : q > 0),
        a l + k * a p = a m + k * a q) ↔ k = 2 := by
  constructor
  swap
  . intro h1
-- When $$k=2$$, $$a_{0}=0, a_{1}=1, a_{2}=2$$, then from $$a_{0}+2 a_{2}=a_{2}+2 a_{1}=4$$,
-- we know that taking $$l=0, m=2, p=$$ $$2, q=1$$ is sufficient.
    subst h1
    use 0, 2, by norm_num, 2, by norm_num, 1, by norm_num
    have ha2 : a 2 = 2 * a 1 + a 0 := by convert ha2 1 (by norm_num) using 1
    norm_num [ha2, ha0, ha1]

  . intro ⟨l, m, hlm, p, hp, q, hq, h1⟩

-- Without loss of generality, we will assume $$l < p$$, then

-- For $$k \geqslant 3$$, by the recurrence relation,
-- $$\left\{a_{n}\right\}$$ is positive for $$n \geqslant 1$$,
    have h2 (n : ℕ) (hn : n ≥ 1) : a n > 0 := by
      revert n
      apply Nat.strongRec
      . intro m ih hm
        obtain hm | hm | hm : m = 1 ∨ m = 2 ∨ m ≥ 3 := by omega
        . simp [hm, ha1]
        . simp [hm, ha2 1 (by omega), ha0, ha1]
          omega
        . obtain ⟨n, hn1, hn2⟩ : ∃ n ≥ 1, m = n + 1 := by use m - 1, by omega, by omega
          subst hn2
          calc
            _ = _ := ha2 n hn1
            _ > _ := by
              have ih1 := ih n (by omega) (by omega)
              have ih2 := ih (n - 1) (by omega) (by omega)
              positivity

-- $$\left\{a_{n}\right\}$$ is a strictly increasing sequence of natural numbers
    have h3 : StrictMono a := by
      apply strictMono_nat_of_lt_succ
      intro n
      obtain c2 | c2 | c2 : n = 0 ∨ n = 1 ∨ n ≥ 2 := by omega
      . simp [c2, ha0, ha1]
      . simp [c2, ha1, ha2 1 (by omega), ha0]
        omega
      . calc
          a (n + 1) = _ := ha2 n (by omega)
          _ > k * a n + 0 := by
            gcongr
            exact h2 (n - 1) (by omega)
          _ = k * a n := by ring
          _ > 1 * a n := by
            gcongr
            . exact h2 n (by omega)
            . omega
          _ = a n := by ring

-- and $$k \mid\left(a_{n+1}-a_{n-1}\right)$$.
    have h4 (n : ℕ) (hn : n ≥ 1) : (k : ℤ) ∣ (a (n + 1) - a (n - 1)) := by
      specialize ha2 n hn
      use a n
      omega

    sorry

-- then $$ \begin{array}{l} a_{2 n} \equiv a_{0}=0(\bmod k), \\ a_{2 n+1} \equiv a_{1}=1(\bmod k)(n=0,1, \cdots) . \end{array} $$



-- As $$l < p$$

-- $$ \begin{array}{l} a_{l}+k a_{p} \leqslant k a_{p}+a_{p-1}=a_{p+1} \\ \leqslant a_{m}\frac{a_{l}+k a_{p}-a_{m}}{k}=a_{q} \text {. } \end{array} $$

-- From $$k a_{q}+a_{m}=k a_{p}+a_{l} \geqslant k a_{p}$$, we know $$a_{q} \geqslant a_{p}-\frac{a_{m}}{k} \geqslant a_{p}-\frac{a_{p}}{k}=\frac{k-1}{k} a_{p}$$.

-- Noting that $$a_{p} \geqslant k a_{p-1}$$. Thus, $$a_{p} > a_{q} \geqslant \frac{k-1}{k} a_{p} \geqslant(k-1) a_{p-1} \geqslant a_{p-1}$$.
-- From equation (4), we know $$a_{q}=a_{p-1}$$.
-- Therefore, the equalities in equations (1), (2), and (3) must all hold.
-- From equations (2) and (3), we get $$m=p, p=2$$.
-- Thus, $$a_{q}=a_{p-1}=a_{1}=1$$. From equation (1), we know $$l=0$$.
-- Therefore, from $$a_{l}+k a_{p}=a_{m}+k a_{q}$$, we get $$k^{2}=k+k$$, i.e., $$k=2$$, which is a contradiction.
-- Thus, $$k \geqslant 3$$ does not satisfy the problem's conditions.
-- Hence, $$k$$ can only be 2.

-- #check Ideal.radical
