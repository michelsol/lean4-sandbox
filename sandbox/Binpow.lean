import Mathlib

def binpow (a : Nat) (n : Nat) : Nat :=
  if n = 0
  then 1
  else
    let b := binpow a (n / 2)
    if n % 2 = 0 then b * b else a * b * b

theorem binpow_eq (a : Nat) (n : Nat) : binpow a n = a ^ n := by
  revert n
  apply Nat.strongRec
  intro n ih
  unfold binpow
  by_cases hn : n = 0
  all_goals simp only [hn, ↓reduceIte]
  · simp
  · by_cases hn2 : n % 2 = 0
    all_goals simp only [hn2, ↓reduceIte]
    · calc
      _ = a ^ (n / 2) * a ^ (n / 2) := by rw [ih (n / 2) (by omega)]
      _ = a ^ (2 * (n / 2)) := by ring
      _ = a ^ n := by
        congr 1
        omega
    · calc
      _ = a * a ^ (n / 2) * a ^ (n / 2) := by rw [ih (n / 2) (by omega)]
      _ = a ^ (2 * (n / 2) + 1) := by ring
      _ = a ^ n := by
        congr 1
        omega
