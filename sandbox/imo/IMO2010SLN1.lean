import Mathlib

open Finset

/-
Find the least positive integer $n$ for which there exists a set
$\left\{s_{1}, s_{2}, \ldots, s_{n}\right\}$
consisting of $n$ distinct positive integers such that
$$ \left(1-\frac{1}{s_{1}}\right)\left(1-\frac{1}{s_{2}}\right)
\ldots\left(1-\frac{1}{s_{n}}\right)=\frac{51}{2010} $$
-/

theorem number_theory_23989 :
    IsLeast { n : ℕ | ∃ (s : ℕ → ℕ) (_ : ∀ i ∈ Icc 1 n, s i ≥ 1) (_ : Set.InjOn s (Icc 1 n)),
      ∏ i ∈ Icc 1 n, (1 - 1 / s i : ℚ) = 51 / 2010 } 39 := by
  constructor
-- We show that $n=39$ fits.
-- Consider the set $\{2,3, \ldots, 33,35,36, \ldots, 40,67\}$ which contains exactly 39 numbers.
  . let s n :=  if n ∈ Icc 1 32 then n + 1
                else if n ∈ Icc 33 38 then n + 2
                else if n = 39 then 67
                else 0
    use s
    use by
      intro i hi
      dsimp only [s]
      split_ifs
      all_goals simp at *; try omega
    use by
      intro i hi j hj hij
      dsimp only [s] at hij
      split_ifs at hij
      all_goals simp at *; omega
-- We have  $$ \frac{1}{2} \cdot \frac{2}{3} \cdots \frac{32}{33}
-- \cdot \frac{34}{35} \cdots \frac{39}{40} \cdot \frac{66}{67}=\frac{1}{33}
-- \cdot \frac{34}{40} \cdot \frac{66}{67}=\frac{17}{670}=\frac{51}{2010} $$
    calc
      ∏ i ∈ Icc 1 39, (1 - 1 / s i : ℚ) =
          ((∏ i ∈ Icc 1 32, (1 - 1 / ((i : ℕ) + 1) : ℚ))
          * ∏ i ∈ Icc 33 38, (1 - 1 / ((i : ℕ) + 2) : ℚ))
          * (1 - 1 / 67 : ℚ)
          := by
        have : Icc 1 39 = Icc 1 32 ∪ Icc 33 38 ∪ {39} := by ext i; simp; omega
        rw [this]
        rw [prod_union (by simp)]
        rw [prod_union (by intro s hs ht t hts; specialize hs hts; specialize ht hts; simp at *; omega)]
        congr 2
        . apply prod_congr rfl
          intro i hi
          dsimp only [s]
          split_ifs
          all_goals simp at *; try omega
        . apply prod_congr rfl
          intro i hi
          dsimp only [s]
          split_ifs
          all_goals simp at *; try omega
        . simp [s]
      _ = _ := by
        norm_cast

-- Suppose that for some $n$ there exist the desired numbers;
  . intro n ⟨s, s_ge_1, inj_s, hs⟩

-- Surely $n≥1$.
    have n_ge_1 : n ≥ 1 := by
      by_contra hn
      replace hn : n = 0 := by omega
      norm_num [hn] at hs

-- we may assume that $s_1 < s_2 < \cdots < s_n$ a.
    wlog strictmono_s : StrictMonoOn s (Icc 1 n)
    . have : ∃ (φ : ℕ → ℕ) (_ : Set.BijOn φ (Icc 1 n) (Icc 1 n)), MonotoneOn (s ∘ φ) (Icc 1 n) := by
        sorry
      obtain ⟨φ, bij_φ, mono_sφ⟩ := this
      have inj_sφ : Set.InjOn (s ∘ φ) (Icc 1 n) := by
        apply Set.InjOn.comp
        . exact inj_s
        . exact bij_φ.2.1
        . exact bij_φ.1
      apply this (s ∘ φ)
      . intro i hi j hj hij
        specialize mono_sφ hi hj (by omega)
        specialize inj_sφ hi hj
        omega
      . intro i hi; exact s_ge_1 (φ i) (bij_φ.1 hi)
      . exact inj_sφ
      . dsimp only [Function.comp_apply]
        rw [prod_nbij φ bij_φ.1]
        . exact hs
        . exact bij_φ.2.1
        . exact bij_φ.2.2
        . simp
      . omega

-- Surely $s_{1}>1$ since otherwise $1-\frac{1}{s_{1}}=0$.
    have h1 : s 1 ≥ 2 := by
      by_contra h1
      specialize s_ge_1 1 (by simp; omega)
      replace h1 : s 1 = 1 := by omega
      have : {1} ⊆ Icc 1 n := by simp; omega
      rw [←prod_sdiff this] at hs
      norm_num [h1] at hs

-- So we have $2 \leq s_{1} \leq s_{2}-1 \leq \cdots \leq s_{n}-(n-1)$,
-- hence $s_{i} \geq i+1$ for each $i=1, \ldots, n$.
    replace h1 : ∀ i ∈ Icc 1 n, s i ≥ i + 1 := by
      suffices ∀ i ≥ 1, i ≤ n → i + 1 ≤ s i from by simpa
      apply Nat.le_induction
      . intro _; simp [h1]
      . intro i hi ih hin; specialize ih (by omega)
        specialize strictmono_s (by simp; omega) (by simp; omega) (by omega : i < i + 1)
        omega

-- Therefore  $$ \begin{aligned} \frac{51}{2010} &
-- =\left(1-\frac{1}{s_{1}}\right)\left(1-\frac{1}{s_{2}}\right)
-- \ldots\left(1-\frac{1}{s_{n}}\right) \\
-- & \geq\left(1-\frac{1}{2}\right)\left(1-\frac{1}{3}\right)
-- \ldots\left(1-\frac{1}{n+1}\right)
-- =\frac{1}{2} \cdot \frac{2}{3} \cdots \frac{n}{n+1}=\frac{1}{n+1} \end{aligned} $$
    have h2 : (51 / 2010 : ℚ) ≥ (1 / (n + 1) : ℚ) := calc
      _ = _ := hs.symm
      _ ≥ ∏ i ∈ Icc 1 n, (1 - 1 / (i + 1) : ℚ) := by
        apply prod_le_prod
        . intro i hi; field_simp; positivity
        . intro i hi
          specialize h1 i hi
          simp at hi
          sorry
      _ = ∏ i ∈ Icc 1 n, (i / (i + 1) : ℚ) := by apply prod_congr rfl; field_simp
      _ = ((∏ i ∈ Icc 1 n, i) / ∏ i ∈ Icc 1 n, (i + 1) : ℚ) := by
        rw [prod_div_distrib]
        push_cast
        rfl
      _ = ((∏ i ∈ Icc 1 n, i) / (∏ i ∈ Icc 2 (n + 1), i) : ℚ) := by
        congr 1
        sorry
      _ = ((∏ i ∈ Icc 1 n, i) / ((∏ i ∈ Icc 1 n, i) * (n + 1)) : ℚ) := by
        congr 1
        sorry
      _ = ((∏ i ∈ Icc 1 n, i) / (∏ i ∈ Icc 1 n, i) : ℚ) * (1 / (n + 1) : ℚ) := by field_simp
      _ = 1 * (1 / (n + 1) : ℚ) := by
        congr 1
        . suffices (∏ i ∈ Icc 1 n, i : ℚ) ≠ 0 from by field_simp
          generalize n = n at n_ge_1
          revert n
          apply Nat.le_induction
          . simp
          . intro n hn ihn
            rw [prod_Icc_succ_top (by omega)]
            simp [ihn]; norm_cast
      _ = _ := by simp

-- which implies  $$ n+1 \geq \frac{2010}{51}=\frac{670}{17}>39 $$  so $n \geq 39$.
    have h3 : (51 / 2010 : ℚ) * (n + 1) ≥ 1 := (mul_inv_le_iff₀ (by norm_cast; omega)).mp h2
    cancel_denoms at h3
    norm_cast at h3
    omega
