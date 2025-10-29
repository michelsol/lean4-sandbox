import Sandbox.Tuple

def BitString := Tuple Bool

namespace BitString

def op (b1 b2 : BitString) (f : Bool → Bool → Bool) : BitString :=
  ⟨max b1.length b2.length, fun ⟨i, _⟩ =>
    f (if h1 : i < b1.length then b1.toFun ⟨i, h1⟩ else false)
      (if h2 : i < b2.length then b2.toFun ⟨i, h2⟩ else false)⟩

theorem op_comm (b1 b2 : BitString) (f : Bool → Bool → Bool)
    (hcomm : ∀ x y, f x y = f y x) :
    op b1 b2 f = op b2 b1 f := by
  unfold op
  rw [Sigma.mk.injEq]
  split_ands
  · apply Nat.max_comm
  · refine (Fin.heq_fun_iff ?_).mpr ?_
    · apply Nat.max_comm
    · intro ⟨i, hi⟩
      apply hcomm

def and (b1 b2 : BitString) := op b1 b2 (· && ·)

instance : HAnd BitString BitString BitString where hAnd := BitString.and

theorem and_comm (b1 b2 : BitString) : b1 &&& b2 = b2 &&& b1 :=
  op_comm b1 b2 (· && ·) Bool.and_comm


def or (b1 b2 : BitString) := op b1 b2 (· || ·)

instance : HOr BitString BitString BitString where hOr := BitString.or

theorem or_comm (b1 b2 : BitString) : b1 ||| b2 = b2 ||| b1 :=
  op_comm b1 b2 (· || ·) Bool.or_comm


end BitString
