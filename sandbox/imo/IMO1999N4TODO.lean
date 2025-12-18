import Mathlib

/-
Denote by $$S$$ the set of all primes $$p$$ such that the
decimal representation of $$1 / p$$ has its fundamental period divisible by 3 .
For every $$p \in S$$ such that $$1 / p$$ has its fundamental period $$3 r$$ one may
write $$1 / p=$$ $$0 . a_{1} a_{2} \ldots a_{3 r} a_{1} a_{2} \ldots a_{3 r} \ldots$$, where $$r=r(p)$$;
for every $$p \in S$$ and every integer $$k \geq 1$$ define $$f(k, p)$$ by  $$ f(k, p)=a_{k}+a_{k+r(p)}+a_{k+2 r(p)} $$
(a) Prove that $$S$$ is infinite.
(b) Find the highest value of $$f(k, p)$$ for $$k \geq 1$$ and $$p \in S$$.
-/

theorem number_theory_24945
-- (a) The fundamental period of $$1/p$$ is the smallest integer $$d(p)$$ such that $$p \mid 10^{d(p)}-1$$.
    (fp : ℕ → ℕ)
    (hfp : ∀ p, IsLeast { d : ℕ | p ∣ 10 ^ d - 1} (fp p))
    (S : Set ℕ)
    (hS : S = { p : ℕ | Prime p ∧ fp p = 3})
    :
    False
    :=
  sorry

-- Let $$s$$ be an arbitrary prime and set $$N_{s}=10^{2 s}+10^{s}+1$$.
-- In that case $$N_{s} \equiv 3(\bmod 9)$$. Let $$p_{s} \neq 37$$ be a prime dividing $$N_{s} / 3$$.
-- Clearly $$p_{s} \neq 3$$. We claim that such a prime exists and that $$3 \mid d\left(p_{s}\right)$$.
-- The prime $$p_{s}$$ exists, since otherwise $$N_{s}$$ could be written
-- in the form $$N_{s}=3 \cdot 37^{k} \equiv$$ $$3(\bmod 4)$$,
-- while on the other hand for $$s > 1$$ we have $$N_{s} \equiv 1(\bmod 4)$$.
-- Now we prove $$3 \mid d\left(p_{s}\right)$$. We have $$p_{s}\left|N_{s}\right| 10^{3 s}-1$$ and hence $$d\left(p_{s}\right) \mid 3 s$$.
-- We cannot have $$d\left(p_{s}\right) \mid s$$, for otherwise $$p_{s}\left|10^{s}-1 \Rightarrow p_{s}\right|\left(10^{2 s}+\right.$$ $$\left.10^{s}+1,10^{s}-1\right)=3$$;
-- and we cannot have $$d\left(p_{s}\right) \mid 3$$, for otherwise $$p_{s} \mid 10^{3}-1=999=3^{3} \cdot 37$$,
-- both of which contradict $$p_{s} \neq 3,37$$.
-- It follows that $$d\left(p_{s}\right)=3 s$$.
-- Hence for every prime $$s$$ there exists a prime $$p_{s}$$ such that $$d\left(p_{s}\right)=3 s$$.
-- It follows that the cardinality of $$S$$ is infinite.
-- (b) Let $$r=r(s)$$ be the fundamental period of $$p \in S$$.
-- Then $$p \mid 10^{3 r}-1$$, $$p \nmid 10^{r}-1 \Rightarrow p \mid 10^{2 r}+10^{r}+1$$.
-- Let $$x_{j}=\frac{10^{j-1}}{p}$$ and $$y_{j}=\left\{x_{j}\right\}=$$ $$0 . a_{j} a_{j+1} a_{j+2} \ldots$$.
-- Then $$a_{j} < 10 y_{j}$$
-- and hence $$ f(k, p)=a_{k}+a_{k+r}+a_{k+2 r} < 10\left(y_{k}+y_{k+r}+y_{k+2 r}\right) . $$
-- We note that $$x_{k}+x_{k+s(p)}+x_{k+2 s(p)}=\frac{10^{k-1} N_{p}}{p}$$ is an integer,
-- from which it follows that $$y_{k}+y_{k+s(p)}+y_{k+2 s(p)} \in \mathbb{N}$$.
-- Hence $$y_{k}+y_{k+s(p)}+$$ $$y_{k+2 s(p)} \leq 2$$.
-- It follows that $$f(k, p) < 20$$.
-- We note that $$f(2,7)=$$ $$4+8+7=19$$.
-- Hence 19 is the greatest possible value of $$f(k, p)$$.
