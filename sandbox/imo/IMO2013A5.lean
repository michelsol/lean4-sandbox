import Mathlib

open Finset

/-
Let $\mathbb{Z}_{\geqslant 0}$ be the set of all nonnegative integers. Find all the functions $f: \mathbb{Z}_{\geqslant 0} \rightarrow \mathbb{Z}_{\geqslant 0}$ satisfying the relation  $ f(f(f(n)))=f(n+1)+1 $  for all $n \in \mathbb{Z}_{\geqslant 0}$.   (*)
 Answer. There are two such functions: $f(n)=n+1$ for all $n \in \mathbb{Z}_{\geqslant 0}$, and  $ f(n)=\left\{\begin{array}{ll} n+1, & n \equiv 0(\bmod 4) \text { or } n \equiv 2(\bmod 4), \\ n+5, & n \equiv 1(\bmod 4), \\ n-3, & n \equiv 3(\bmod 4) \end{array} \quad \text { for all } n \in \mathbb{Z}_{\geqslant 0}\right. $   (1)


Throughout all the solutions, we write $h^{k}(x)$ to abbreviate the $k$ th iteration of function $h$, so $h^{0}$ is the identity function, and

 $h^{k}(x)=\underbrace{h(\ldots h}_{k \text { times }}(x) \ldots))$ for $k \geqslant 1$.
-/

theorem algebra_24344 (f : ℕ → ℕ) :
    (∀ n, f (f (f n)) = f (n + 1) + 1)
    ↔ (∀ n, f n = n + 1) ∨ (
      ∀ n, f n = match n % 4 with
        | 0 => n + 1 | 1 => n + 5 | 2 => n + 1 | 3 => n - 3 | _ + 3 => 0)
     := by
  constructor
  .
    intro h0
  -- To start, we get from (*) that $ f^{4}(n)=f\left(f^{3}(n)\right)=f(f(n+1)+1) \quad  $
    have h1 n : f^[4] n = f (f (n + 1) + 1) := by
      calc
        _ = f (f^[3] n) := by
          sorry
        _ = _ := by
          sorry

  -- and $ \quad f^{4}(n+1)=f^{3}(f(n+1))=f(f(n+1)+1)+1 $
    have h2 n : f^[4] (n + 1) = f (f (n + 1) + 1) := by
      calc
        _ = f^[3] (f (n + 1)) := by
          sorry
        _ = _ := by
          sorry

  -- thus $ f^{4}(n)+1=f^{4}(n+1) . $  (2)
    have h3 n : f^[4] n + 1 = f^[4] (n + 1) := by
      sorry

  -- I. Let us denote by $R_{i}$ the range of $f^{i}$;
    let R i := f^[i] '' Set.univ

  -- note that $R_{0}=\mathbb{Z}{\geqslant 0}$ since $f^{0}$ is the identity function.
    have h4 : R 0 = Set.univ := by simp [R]

  -- Obviously, $R{0} \supseteq R_{1} \supseteq \ldots$
    have h5 : AntitoneOn R Set.univ := by
      sorry

  -- Next, from (2) we get that if $a \in R_{4}$ then also $a+1 \in R_{4}$.
    have h6 a (ha : a ∈ R 4) : a + 1 ∈ R 4 := by
      sorry

  -- This implies that $\mathbb{Z}{\geqslant 0} \backslash R{4}$ - and hence $\mathbb{Z}{\geqslant 0} \backslash R{1}$ - is finite.
    have h7 : (Set.univ \ R 4).Finite := by
      sorry

    have h8 : (Set.univ \ R 1).Finite := by
      sorry

  --  In particular, $R_{1}$ is unbounded.
    have h9 : ∀ N ∈ R 1, ∃ n ∈ R 1, n > N := by
      sorry

  -- We will now prove that f is injective.
    have h10 : Set.InjOn f Set.univ := by
  -- Assume that $f(m)=f(n)$ for some distinct $m$ and $n$.
      intro m hm n hn c1
      by_contra! c2
  -- Then from $(*)$ we obtain $f(m+1)=$ $f(n+1)$
      have c3 : f (m + 1) = f (n + 1) := by
        sorry

  -- by an easy induction we then get that $f(m+c)=f(n+c)$ for every $c \geqslant 0$.
      have c4 c (hc : c ≥ 0) : f (m + c) = f (n + c) := by
        induction' c with c ih
        . sorry
        . sorry
  -- So the function $f(k)$ is periodic with period $|m-n|$ for $k \geqslant m$, and thus $R_{1}$ should be bounded, which is false.
      sorry

  --II. Denote now $S_{i}=R_{i-1} \backslash R_{i}$
    let S i := R (i - 1) \ R i

  --; all these sets are finite for $i \leqslant 4$.
    have h10' i (hi : i ≥ 1) (hi2 : i ≤ 4) : (S i).Finite := by
      sorry

  -- On the other hand, by the injectivity we have $n \in S_{i} \Longleftrightarrow f(n) \in S_{i+1}$.
    have h11 n i (hi : i ≥ 1) : n ∈ S i ↔ f n ∈ S (i + 1) := by
      sorry

  -- By the injectivity again, $f$ implements a bijection between $S_{i}$ and $S_{i+1}$,
    have h12 i (hi : i ≥ 1) : Set.BijOn f (S i) (S (i + 1)) := by
      sorry

  -- thus $\left|S_{1}\right|=\left|S_{2}\right|=\ldots$
    have h13 i (hi : i ≥ 1) : (S i).ncard = (S 1).ncard := by
      sorry

  -- denote this common cardinality by $k$.
    set k := (S 1).ncard

  -- If $0 \in R_{3}$ then $0=f(f(f(n)))$ for some $n$,
  -- thus from (*) we get $f(n+1)=-1$ which is impossible.
    have h14 : 0 ∉ R 3 := by
      intro h14
      obtain ⟨n, c1⟩ : ∃ n, f^[3] n = 0 := by
        sorry
      sorry

  -- Therefore $0 \in R_{0} \backslash R_{3}=S_{1} \cup S_{2} \cup S_{3}$,
    have h15 : R 0 \ R 3 = S 1 ∪ S 2 ∪ S 3 := by sorry
    have h16 : 0 ∈ S 1 ∪ S 2 ∪ S 3 := by
      sorry

  -- thus $k \geqslant 1$.
    have h17 : k ≥ 1 := by
      sorry

  -- Next, let us describe the elements $b$ of $R_{0} \backslash R_{3}=S_{1} \cup S_{2} \cup S_{3}$.
  -- We claim that each such element satisfies at least one of three conditions $(i) b=0,(i i) b=f(0)+1$, and (iii) $b-1 \in S_{1}$.
    have h18 b (hb : b ∈ S 1 ∪ S 2 ∪ S 3) : b = 0 ∨ b = f 0 + 1 ∨ b - 1 ∈ S 1 := by
  --Otherwise $b-1 \in \mathbb{Z}{\geqslant 0}$,
  -- and there exists some $n > 0$ such that $f(n)=b-1$;
  -- but then $f^{3}(n-1)=f(n)+1=b$, so $b \in R{3}$.
      by_contra! h18
      sorry

  -- This yields $ 3 k=\left|S_{1} \cup S_{2} \cup S_{3}\right| \leqslant 1+1+\left|S_{1}\right|=k+2, $ or $k \leqslant 1$.
    have h19 : k ≤ 1 := by sorry

  -- Therefore $k=1$.
    replace h19 : k = 1 := by sorry

  -- So we have $S_{1}=\{a\}$, $S_{2}=\{f(a)\}$, and $S_{3} = \{ f^{2}(a) \} $ for some $a \in \mathbb{Z}_{\geqslant 0}$,
    obtain ⟨a, h20, h21, h22⟩ : ∃ a, S 1 = {a} ∧ S 2 = {f a} ∧ S 3 = {f^[2] a} := by
      sorry

  -- and each one of the three options (i), (ii), and (iii) should be realized exactly once,
  -- which means that $ \{a, f(a), f^{2}(a)\}={0, a+1, f(0)+1} . $   (3)
    have h23 : {a, f a, f^[2] a} = ({0, a + 1, f 0 + 1} : Finset _) := by
      sorry

  -- III. From (3), we get $a+1 \in\{f(a), f^{2}(a)\}$ (the case $a+1=a$ is impossible).
    have h24 : a + 1 = f a ∨ a + 1 = f^[2] a := by
      sorry

  -- If $a+1=f^{2}(a)$ then we have $f(a+1)=f^{3}(a)=f(a+1)+1$ which is absurd.
  -- Therefore $ f(a)=a+1 $   (4)
    replace h24 : f a = a + 1 := by
      sorry

  -- Next, again from (3) we have $0 \in\{a, f^{2}(a)\}$.
    have h25 : a = 0 ∨ f^[2] a = 0 := by
      sorry

  -- Let us consider these two cases separately.
    obtain h25 | h25 := h25
 -- Case 1. Assume that $a=0$, then $f(0)=f(a)=a+1=1$.
    . have c1 : f 0 = 1 := by
        sorry
 -- Also from (3) we get $f(1)=f^{2}(a)=$ $f(0)+1=2$.
      have c2 : f 1 = 2 := by
        sorry
 -- Now, let us show that $f(n)=n+1$ by induction on $n$;
      have c3 n : f n = n + 1 := by
        induction' n with n ih
 -- the base cases $n \leqslant 1$ are established.
        . sorry
 -- Next, if $n \geqslant 2$ then the induction hypothesis implies $ n+1=f(n-1)+1=f^{3}(n-2)=f^{2}(n-1)=f(n), $ establishing the step.
        . sorry
 -- In this case we have obtained the first of two answers
      left
      exact c3
    .
 -- Case 2. Assume now that $f^{2}(a)=0$;
 -- then by (3) we get $a=f(0)+1$.
      have c1 : a = f 0 + 1 := by
        sorry
 -- By (4) we get $f(a+1)=$ $f^{2}(a)=0$,
      have c2 : f (a + 1) = 0 := by
        sorry
 -- then $f(0)=f^{3}(a)=f(a+1)+1=1$,
      have c3 : f 0 = 1 := by
        sorry
 -- hence $a=f(0)+1=2$
      have c4 : a = 2 := by sorry
 -- and $f(2)=3$ by (4).
      have c5 : f 2 = 3 := by sorry
 -- To summarize, $ f(0)=1, \quad f(2)=3, \quad f(3)=0 . $
      have c6 : f 3 = 0 := by sorry

 -- Now let us prove by induction on $m$ that (1) holds for all $n=4 m, 4 m +1, 4 m+2,4 m+3$
      right
      suffices ∀ m,
        (f (4 * m) = 4 * m + 1)
        ∧ (f (4 * m + 1) = 4 * m + 6)
        ∧ (f (4 * m + 2) = 4 * m + 3)
        ∧ (f (4 * m + 3) = 4 * m) from by
        intro n
        have d1 : n = 4 * (n / 4) + n % 4 := by omega
        set m := n / 4
        rw [d1]
        have d2 : (4 * m + n % 4) % 4 = n % 4 := by omega
        rw [d2]
        obtain ⟨e0, e1, e2, e3⟩ := this m
        obtain d3 | d3 | d3 | d3 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
        all_goals simpa [d3]
      apply Nat.strongRec
      intro m ih
      obtain hm | hm : m = 0 ∨ m ≥ 1 := by omega
 -- The base case $m=0$ is established above.
      . sorry
 -- For the step, assume that $m \geqslant 1$.
      .
        sorry


 -- Finally, it is straightforward to check that the constructed functions work:
  . intro h1
    obtain h1 | h1 := h1
    . intro n
      simp [h1]
    . intro n
      obtain c1 | c1 | c1 | c1 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
      . have : (n + 1) % 4 = 1 := by omega
        have : (n + 1 + 5) % 4 = 2 := by omega
        simp [*]
      . have : (n + 1) % 4 = 2 := by omega
        have : (n + 5) % 4 = 2 := by omega
        have : (n + 1 + 5) % 4 = 3 := by omega
        simp [*]
      . have : (n + 1) % 4 = 3 := by omega
        have : (n - 2) % 4 = 0 := by omega
        simp [*]
      . have : (n + 1) % 4 = 0 := by omega
        have : (n - 3) % 4 = 0 := by omega
        have : (n - 3 + 1) % 4 = 1 := by omega
        simp [*]
        omega
