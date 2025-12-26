import Mathlib

/-
Find all functions $$f: \mathbb{Q}^{+} \rightarrow \mathbb{Q}$$ such that for all $$x, y \in \mathbb{Q}^{+}$$,

$$ f(x)+f(y)=\left(f(x+y)+\frac{1}{x+y}\right)(1-x y+f(x y)) $$
-/
theorem algebra_605737
    (f : ℚ → ℚ) :
    (∀ (x : ℚ) (_ : x > 0) (y : ℚ) (_ : y > 0),
      f x + f y = (f (x + y) + 1 / (x + y)) * (1 - x * y + f (x * y)))
    ↔ ∀ (x : ℚ), f x = x - 1 / x := by
-- The only function that satisfies is $$f\left(x\right)=x-\frac{1}{x}$$.
  constructor
  swap
  . intro h1
    intro x hx y hy
    symm
-- This function indeed satisfies because

-- $$ \left(f(x+y)+\frac{1}{x+y}\right)(1-x y+f(x y)) =\left((x+y)-\frac{1}{x+y}+\frac{1}{x+y}\right)\left(1-x y+x y-\frac{1}{x y}\right) $$

-- $$=(x+y)\left(1-\frac{1}{x y}\right) =x+y-\frac{1}{x}-\frac{1}{y} =f(x)+f(y) . $$
    calc
      _ = ((x + y) - 1 / (x + y) + 1 / (x + y)) * (1 - x * y + (x * y - 1 / (x * y))) := by
        congr 2
        . apply h1
        . apply h1
      _ = (x - 1 / x) + (y - 1 / y) := by
        field_simp
        ring
      _ = f x + f y := by
        symm
        congr 1
        . apply h1
        . apply h1

  . intro h1
    sorry
-- When dealing with a function on $$\mathbb{Q}^{+}$$, it is often a good idea
-- to first look at what happens with the natural numbers.
-- The idea is to play products $$x y$$ against sums $$x+y$$, such as $$2 \cdot 2=2+2$$.
-- Lemma. It holds that $$f(1)=0$$.
-- Proof. If we substitute $$x=y=1$$, we get $$2 f(1)=\left(f(2)+\frac{1}{2}\right) f(1)$$.
-- This means that $$f(1)=0$$ or $$f(2)=\frac{3}{2}$$.

-- Assume that $$f(2)=\frac{3}{2}$$. If we now substitute $$x=y=2$$, we get $$2 f(2)=\left(f(4)+\frac{1}{4}\right)(f(4)-3)$$.
-- This simplifies to $$3=f(4)^{2}-\frac{11}{4} f(4)-\frac{3}{4}$$.
-- After multiplying by 4, we can factorize this as $$(f(4)+1)(4 f(4)-15)=0$$.
-- Thus, $$f(4)=-1$$ or $$f(4)=\frac{15}{4}$$.

-- If we substitute $$y=1$$ into the original equation, we find that
-- $$ f(x)+f(1)=\left(f(x+1)+\frac{1}{x+1}\right)(f(x)-x+1) $$

-- If we substitute $$x=2,3,4,5$$ into this, we get respectively

-- $$ \begin{aligned} \frac{3}{2}+f(1) & =\left(f(3)+\frac{1}{3}\right) \cdot \frac{1}{2} \ f(3)+f(1) & =\left(f(4)+\frac{1}{4}\right)(f(3)-2) \ f(4)+f(1) & =\left(f(5)+\frac{1}{5}\right)(f(4)-3) \ f(5)+f(1) & =\left(f(6)+\frac{1}{6}\right)(f(5)-4) \end{aligned} $$

-- In the case that $$f(4)=\frac{15}{4}$$, the second equation gives $$f(3)+f(1)=4(f(3)-2)$$, so $$3 f(3)=f(1)+8$$.
-- The first equation, however, gives $$3 f(3)-6 f(1)=8$$.
-- We conclude that $$f(1)+8=3 f(3)=6 f(1)+9-1=6 f(1)+8$$.
-- Thus, in this case, $$f(1)=0$$ as we wanted to prove.

-- On the other hand, assume that $$f(4)=-1$$.
-- As we just saw, the first equation gives $$3 f(3)-6 f(1)=8$$.
-- The second equation, in this case, gives $$f(3)+f(1)=-\frac{3}{4}(f(3)-2)$$, so $$7 f(3)+4 f(1)=6$$.
-- If we solve this system (for example, by adding two times the first equation to three times the second),
-- we find that $$f(1)=-\frac{19}{27}$$ and $$f(3)=\frac{34}{27}$$.
-- If we substitute these into the third equation,
-- we get $$-1-\frac{19}{27}=-4\left(f(5)+\frac{1}{5}\right)$$, or $$f(5)=\frac{61}{270}$$.
--Similarly, from the fourth equation, we get $$\frac{61}{270}-\frac{19}{27}=\left(f(6)+\frac{1}{6}\right)\left(\frac{61}{270}-4\right)$$, or $$f(6)=-\frac{245}{6114}$$.

-- We have now calculated 6 as $$4+1+1$$, but we can also do it as $$2 \cdot 3$$. If we substitute $$x=2$$ and $$y=3$$, we get

-- $$ f(2)+f(3)=\left(f(5)+\frac{1}{5}\right)(f(6)-5) $$

-- If we substitute the calculated values of $$f(2), f(3), f(5)$$, and $$f(6)$$, we do not get
-- an equality, because the left side is greater than zero and the right side is less than zero.
-- We conclude that the case $$f(4)=-1$$ is not possible, and that $$f(1)=0$$.

-- Now we would like to use equation (1) for induction,
-- but the base case with $$x=1$$ does not work because $$f(1)=0$$.
-- As a new base case, we want to use the case $$f(4)=\frac{15}{4}$$ from above,
-- which did not lead to a contradiction but rather to $$f(1)=0$$.

-- Lemma. It holds that $$f(4)=\frac{15}{4}$$.
-- Proof. We actually use the same trick as above to calculate $$f(4)$$,
-- but now with the fact that we know $$f(1)$$ instead of $$f(2)$$.
-- With $$x=y=2$$, we find again that $$2 f(2)=\left(f(4)+\frac{1}{4}\right)(f(4)-3)$$.
-- By substituting $$x=2$$ into (1), we find $$f(2)=\left(f(3)+\frac{1}{3}\right)(f(2)-1)$$,
-- and by substituting $$x=3$$ into (1), we find $$f(3)=\left(f(4)+\frac{1}{4}\right)(f(3)-2)$$.
-- This system of three equations can be solved by rewriting the second equation as

-- $$ \begin{aligned} f(3) & =\frac{f(2)}{f(2)-1}-\frac{1}{3} \ & =\frac{f(2)-1+1}{f(2)-1}-\frac{1}{3} \ & =1+\frac{1}{f(2)-1}-\frac{1}{3} \ & =\frac{1}{f(2)-1}+\frac{2}{3} \end{aligned} $$

-- or $$f(2)=\frac{1}{f(3)-\frac{2}{3}}+1$$.
-- Similarly, from the third equation, we get $$f(4)=\frac{2}{f(3)-2}+\frac{3}{4}$$,
-- which we can rewrite as $$f(3)-\frac{2}{3}=\frac{\frac{4}{3} f(4)+1}{f(4)-\frac{3}{4}}$$.

-- By combining everything, we find that
-- $$ \left(f(4)+\frac{1}{4}\right)(f(4)-3) =2 f(2) =2\left(\frac{1}{f(3)-\frac{2}{3}}+1\right) =2\left(\frac{f(4)-\frac{3}{4}}{\frac{4}{3} f(4)+1}+1\right) =\frac{2 f(4)-\frac{3}{2}+\frac{8}{3} f(4)+2}{\frac{4}{3} f(4)+1} =\frac{\frac{14}{3} f(4)+\frac{1}{2}}{\frac{4}{3} f(4)+1 $$
