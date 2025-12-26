import Mathlib

open Finset Real

/- # Problem:
 Several (at least two) segments are drawn on a board.
 Select two of them, and let $a$ and $b$ be their lengths.
 Delete the selected segments and draw a segment of length $\frac{a b}{a+b}$.

 Continue this procedure until only one segment remains on the board. Prove:

a) the length of the last remaining segment does not depend on the order of the deletions.

b) for every positive integer $n$, the initial segments on the board
can be chosen with distinct integer lengths, such that the last remaining segment has length $n$.
-/
theorem algebra_605660 {n : ℕ} (hn : 0 < n) :
    ∃ a : Fin 3 → ℤ, (∀ i j, a i = a j → i = j) ∧
      (∀ i, 0 < a i) ∧ (∑ i, (1 : ℝ)/(a i) = 1/(2*n) + 1/(3*n) + 1/(6*n)) := by


-- a) Observe that $\frac{1}{\frac{a b}{a+b}}=\frac{1}{a}+\frac{1}{b}$.

-- Thus, if the lengths of the initial segments on the board were $a_{1}, a_{2}, \ldots, a_{n}$, and $c$

-- is the length of the last remaining segment, then $\frac{1}{c}=\frac{1}{a_{1}}+\frac{1}{a_{2}}+\ldots+\frac{1}{a_{n}}$, proving a).

-- b) From a) and the equation $\frac{1}{n}=\frac{1}{2 n}+\frac{1}{3 n}+\frac{1}{6 n}$

-- it follows that if the lengths of the starting segments are $2 n, 3 n$ and $6 n$,

-- then the length of the last remaining segment is $n$.

  sorry
