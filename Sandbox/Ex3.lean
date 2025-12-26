import Mathlib

/-
Two teams are in a best-two-out-of-three playoff:
the teams will play at most $3$ games, and the winner of the playoff
is the first team to win $2$ games.
The first game is played on Team A's home field,
and the remaining games are played on Team B's home field.
Team A has a $\frac{2}{3}$ chance of winning at home,
and its probability of winning when playing away from home is $p$.
Outcomes of the games are independent.
The probability that Team A wins the playoff is $\frac{1}{2}$.
What is $p$?
Answer: $p = \frac{4 - \sqrt{10}}{2}$.
-/

inductive Team where | A | B deriving DecidableEq, Repr, Fintype

def playoffWinner (playoff : Fin 3 → Team) : Team :=
  if playoff 0 = playoff 1 then playoff 0
  else if playoff 0 = playoff 2 then playoff 0
  else playoff 1

def gameField : Fin 3 → Team
  | 0 => Team.A
  | 1 => Team.B
  | 2 => Team.B

axiom p : ℝ

noncomputable def probabilityOfAwinningGame (game : Fin 3) :=
  match gameField game with
  | Team.A => 2 / 3
  | Team.B => p

noncomputable def probabilityOfHavingGivenPlayoff (playoff : Fin 3 → Team) :=
  ∏ i ∈ {0, 1, 2},
    if playoff i = Team.A then probabilityOfAwinningGame i else 1 - probabilityOfAwinningGame i

noncomputable def probabilityOfAwinningPlayoff : ℝ :=
  ∑ playoff ∈ ({
      fun | 0 => .A | 1 => .A | 2 => .A,
      fun | 0 => .A | 1 => .A | 2 => .B,
      fun | 0 => .A | 1 => .B | 2 => .A,
      fun | 0 => .A | 1 => .B | 2 => .B,
      fun | 0 => .B | 1 => .A | 2 => .A,
      fun | 0 => .B | 1 => .A | 2 => .B,
      fun | 0 => .B | 1 => .B | 2 => .A,
      fun | 0 => .B | 1 => .B | 2 => .B
    } : Finset (Fin 3 → Team)),
    probabilityOfHavingGivenPlayoff playoff * if playoffWinner playoff = Team.A then 1 else 0

axiom ax1 : probabilityOfAwinningPlayoff = 1 / 2

theorem th1 : 2 * p ^ 2 - 8 * p + 3 = 0 := by
  have h1 := ax1
  unfold probabilityOfAwinningPlayoff at h1
  iterate 7 rw [Finset.sum_insert (by decide)] at h1
  unfold probabilityOfHavingGivenPlayoff probabilityOfAwinningGame playoffWinner gameField at h1
  simp at h1
  cancel_denoms at h1
  ring_nf at h1
  linarith

theorem th2 : p = (4 - √10) / 2 := by
  sorry
