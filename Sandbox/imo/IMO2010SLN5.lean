import Mathlib

/-
Let $\mathbb{N}$ be the set of all positive integers. Find all functions
$f: \mathbb{N} \rightarrow \mathbb{N}$ such that the number $(f(m)+n)(m+f(n))$ is a square
for all $m,n \in \mathbb{N}$.
-/

theorem number_theory_24000 (f : ℕ → ℕ) (f_pos : ∀ n > 0, f n > 0) :
    (∀ m (_ : m > 0) n (_ : n > 0), ∃ d, (f m + n) * (m + f n) = d ^ 2)
    ↔ (∃ c, ∀ n (_ : n > 0), f n = n + c)
    := by
  constructor
  swap
  -- First, it is clear that all functions of the form $f(n)=n+c$ with a constant nonnegative
  -- integer $c$ satisfy the problem conditions since $(f(m)+n)(f(n)+m)=(n+m+c)^2$ is a square.
  . intro ⟨c, hc⟩
    intro m hm n hn
    use n + m + c
    rw [hc n hn, hc m hm]
    ring_nf
  . intro h0
    suffices h1 : ∀ (p : ℕ) (_ : p.Prime), ∀ k > 0, ∀ l > 0,
                    (p : ℤ) ∣ (f k - f l : ℤ) → (p : ℤ) ∣ (k - l : ℤ) from by
      -- Show that f is injective using the lemma
      have inj_f : Set.InjOn f { n | n > 0 } := by
        intro k hk l hl hkl
        wlog h2 : l ≤ k generalizing k l
        . exact (this hl hk hkl.symm (by omega)).symm
        have h3 : ∀ (p : ℕ) (_ : p.Prime), (p : ℤ) ∣ (k - l : ℤ) := by
          intro p hp
          apply h1 p hp
          . simpa
          . simpa
          . simp [hkl]
        suffices (k - l : ℤ) ≠ 0 → (k - l : ℤ) = 0 from by omega
        intro h4
        obtain ⟨p, prime_p, hp, _⟩ := Nat.exists_prime_lt_and_le_two_mul (k - l) (by omega)
        apply Int.eq_zero_of_dvd_of_nonneg_of_lt (n := p)
        . omega
        . omega
        . exact h3 p prime_p
      -- Show that the gap between two consecutive f(k)'s is +1 or -1
      have h2 : ∀ k > 0, |(f (k + 1) - f k : ℤ)| = 1 := by
        intro k hk
        suffices |(f (k + 1) - f k : ℤ)|.toNat = 1 from by
          sorry
        rw [Nat.eq_one_iff_not_exists_prime_dvd]
        intro p prime_p h0
        replace h0 : (p : ℤ) ∣ |(f (k + 1) - f k : ℤ)| := by
          sorry
        replace h0 : (p : ℤ) ∣ (f (k + 1) - f k : ℤ) := by rwa [dvd_abs] at h0
        specialize h1 p prime_p (k + 1) (by omega) k (by omega) h0
        replace h1 : (p : ℤ) ∣ 1 := by push_cast at h1; ring_nf at h1 ⊢; exact h1
        replace h1 : p = 1 := by norm_cast at h1; exact Nat.eq_one_of_dvd_one h1
        subst h1
        exact Nat.not_prime_one prime_p
      -- Show by induction on n, that f(n + 1) = f(1) + q n
      -- where q = f(2) - f(1) ∈ {+1,-1}
      let q : ℤ := f 2 - f 1
      have hq : q = 1 ∨ q = -1 := by
        suffices |q| = 1 from abs_eq_abs.mp this
        specialize h2 1 (by norm_num)
        simpa using h2
      replace h2 : ∀ k > 0, f (k + 1) = (f k - q : ℤ) ∨ f (k + 1) = (f k + q : ℤ) := by
        intro k hk
        suffices (f (k + 1) - f k : ℤ) = 1 ∨ (f (k + 1) - f k : ℤ) = -1 from by omega
        exact abs_eq_abs.mp (h2 k hk)
      have h3 : ∀ n, f (n + 1) = f 1 + q * n := by
        apply Nat.twoStepInduction
        . simp
        . simp [q]
        . dsimp
          intro n ih1 ih2
          rcases h2 (n + 2) (by omega) with h2 | h2
          . rw [ih2] at h2
            replace h2 : f (n + 3) = f 1 + q * n := by
              push_cast at h2 ⊢; ring_nf at h2 ⊢; exact h2
            rw [←ih1] at h2
            norm_cast at h2
            have := inj_f (by simp) (by simp) h2
            omega
          . rw [h2, ih2]
            push_cast
            ring_nf
      -- Show that q must be 1 as f must remain positive.
      replace hq : q = 1 := by
        suffices q ≠ -1 from by omega
        intro hq
        rw [hq] at h3
        specialize h3 (f 1)
        replace h3 : f (f 1 + 1) = 0 := by simpa using h3
        specialize f_pos (f 1 + 1) (by omega)
        omega
      rw [hq] at h3
      -- Conclude by rearranging.
      use f 1 - 1
      intro n (hn : n ≥ 1)
      replace h3 : f n = f 1 + (n - 1 : ℤ) := by
        specialize h3 (n - 1)
        simpa [hn] using h3
      have : f 1 ≥ 1 := f_pos 1 (by norm_num)
      omega
    intro p prime_p k hk l hl h1
    -- Take some positive integer $D>max(f(k),f(l))$ not divisible by $p$
    have : ∃ (D : ℕ) (_ : D > f k) (_ : D > f l), ¬p ∣ D := by
      let d := max (f k) (f l) + 1
      let D := if p ∣ d then d + 1 else d
      use D
      use by
        sorry
      use by
        sorry
      use by
        sorry
    obtain ⟨D, D_gt_fk, D_gt_fl, p_notdvd_D⟩ := this
    have p_ge_2 : p ≥ 2 := Nat.Prime.two_le prime_p
    -- Suppose first that $p^2  |  f(k) - f(l)$, so $f(l)=f(k)+p^2a$ for some integer $a$.
    by_cases h2 : (p ^ 2 : ℤ) ∣ (f k - f l : ℤ)
    . have : ∃ a : ℤ, f l = f k + p ^ 2 * a := by obtain ⟨b, hb⟩ := h2; use -b; linarith
      obtain ⟨a, ha⟩ := this
      -- Set $n=pD-f(k)$.
      set n := (p * D - f k : ℕ) with hn'
      have pD_ge_fk : p * D > f k := calc
        p * D ≥ 1 * D := by gcongr; omega
        _ = D := by simp
        _ > f k := by omega
      have hn : n > 0 := by omega
      -- Then using the problem conditions, we show that $f(n)+k$ and $f(n)+l$ are divisible by $p$,
      -- and so is their difference $k-l$.
      have h3 : n + f k = p * D := by omega
      have h4 : n + f l = p * (D + p * a) := by
        rw [ha, hn']
        push_cast [pD_ge_fk]
        ring_nf
      have h5 : p ∣ f n + k := by
        obtain ⟨dk, hdk⟩ := h0 n hn k hk
        have h1 : p ∣ n + f k := by rw [h3]; exact dvd_mul_right ..
        have h2 : ¬p ∣ ((n + f k) / p) := by
          intro h
          have : p * p ∣ (n + f k) := by exact Nat.mul_dvd_of_dvd_div h1 h
          rw [h3] at this
          have : p ∣ D := Nat.dvd_of_mul_dvd_mul_left (by omega) this
          omega
        have : p ∣ dk ^ 2 := by
          rw [←hdk, h3]
          suffices p ∣ p * ((f n + k) * D) from by ring_nf at this ⊢; simpa
          exact Nat.dvd_mul_right ..
        replace : p ∣ dk := Nat.Prime.dvd_of_dvd_pow prime_p this
        replace : p ^ 2 ∣ dk ^ 2 := pow_dvd_pow_of_dvd this 2
        rw [pow_two, ←hdk] at this
        replace : p ∣ (f n + k) * (n + f k) / p := Nat.dvd_div_of_mul_dvd this
        rw [Nat.mul_div_assoc (f n + k) h1] at this
        replace := (Nat.Prime.dvd_mul prime_p).mp this
        omega
      have h6 : p ∣ f n + l := by
        obtain ⟨dl, hdl⟩ := h0 n hn l hl
        have h1 : p ∣ n + f l := by zify; rw [h4]; exact dvd_mul_right ..
        have h2 : ¬p ∣ ((n + f l) / p) := by
          intro h
          have : p * p ∣ (n + f l) := (Nat.dvd_div_iff_mul_dvd h1).mp h
          zify at this
          rw [h4] at this
          have : (p : ℤ) ∣ D := by
            have h1 : (p : ℤ) ∣ (D + p * a) := Int.dvd_of_mul_dvd_mul_left (by omega) this
            have h2 : (p : ℤ) ∣ p * a := by exact Int.dvd_mul_right ..
            exact (Int.dvd_iff_dvd_of_dvd_add h1).mpr h2
          omega
        have : p ∣ dl ^ 2 := by
          rw [←hdl]
          zify
          rw [h4]
          suffices (p : ℤ) ∣ p * ((f n + l) * (D + p * a)) from by ring_nf at this ⊢; simpa
          exact Int.dvd_mul_right ..
        replace : p ∣ dl := Nat.Prime.dvd_of_dvd_pow prime_p this
        replace : p ^ 2 ∣ dl ^ 2 := pow_dvd_pow_of_dvd this 2
        rw [pow_two, ←hdl] at this
        replace : p ∣ (f n + l) * (n + f l) / p := Nat.dvd_div_of_mul_dvd this
        rw [Nat.mul_div_assoc (f n + l) h1] at this
        replace := (Nat.Prime.dvd_mul prime_p).mp this
        omega
      zify at h5 h6
      have : (p : ℤ) ∣ (f n + k) - (f n + l) := Int.dvd_sub h5 h6
      ring_nf at this ⊢; simpa
    -- On the other hand, if $f(k)-f(l)$ is divisible by $p$ but not by $p^2$, then choose the same
    -- number $D$ and set $n=p^3 D-f(k)$
    . have : ∃ a : ℤ, f l = f k + p * a := by obtain ⟨b, hb⟩ := h1; use -b; linarith
      obtain ⟨a, ha⟩ := this
      let n := p ^ 3 * D - f k
      have pD_ge_fk : p ^ 3 * D > f k := calc
        (p ^ 3) * D = p * p * p * D := by ring_nf
        _ ≥ 1 * 1 * 1 * D := by gcongr <;> omega
        _ = D := by simp
        _ > f k := by omega
      have hn : n > 0 := by omega
      -- In an analogous way we obtain that numbers $f(n)+k$ and $f(n)+l$ are divisible by $p$
      -- and so is their difference $k-l$.
      have h3 : n + f k = p ^ 3 * D := by omega
      have h4 : n + f l = p ^ 3 * D + p * a := by zify at h3; omega
      have h5 : p ∣ f n + k := by
        have p3_dvd_fkpn : p ^ 3 ∣ n + f k := by
          rw [h3]
          exact Nat.dvd_mul_right ..
        have p4_notdvd_fkpn : ¬p ∣ (n + f k) / p ^ 3 := by
          intro h
          sorry
        obtain ⟨dk, hdk⟩ := h0 n hn k hk
        have : p ^ 3 ∣ dk ^ 2 := by
          rw [←hdk, h3]
          suffices p ^ 3 ∣ p ^ 3 * ((f n + k) * D) from by ring_nf at this ⊢; simpa
          exact Nat.dvd_mul_right ..
        -- p's multiplicity in dk ^ 2 must be even and ≥ 3, so it must be ≥ 4.
        replace : p ^ 4 ∣ dk ^ 2 :=
          sorry
        rw [←hdk] at this
        sorry
      have h6 : p ∣ f n + l := by
        have p_dvd_flpn : p ∣ n + f l := by
          zify
          rw [h4]
          suffices (p : ℤ) ∣ p * (p ^ 2 * D + a) from by ring_nf at this ⊢; simpa
          exact Int.dvd_mul_right ..
        have p2_notdvd_flpn : ¬p ∣ (n + f l) / p := by
          intro h
          have h7 : p * p ∣ (n + f l) := (Nat.dvd_div_iff_mul_dvd p_dvd_flpn).mp h
          zify at h7
          have h8 : p * p ∣ (n + f k) := by
            rw [h3]
            suffices p * p ∣ p * p * (p * D) from by ring_nf at this ⊢; simpa
            exact Nat.dvd_mul_right ..
          zify at h8
          apply h2
          have := Int.dvd_sub h8 h7
          ring_nf at this ⊢; simpa
        obtain ⟨dl, hdl⟩ := h0 n hn l hl
        have : p ∣ dl ^ 2 := by
          rw [←hdl]
          zify
          rw [h4]
          suffices (p : ℤ) ∣ p * ((f n + l) * (p ^ 2 * D + a)) from by ring_nf at this ⊢; simpa
          exact Int.dvd_mul_right ..
        replace : p ∣ dl := Nat.Prime.dvd_of_dvd_pow prime_p this
        replace : p ^ 2 ∣ dl ^ 2 := pow_dvd_pow_of_dvd this 2
        rw [pow_two, ←hdl] at this
        replace : p ∣ (f n + l) * (n + f l) / p := Nat.dvd_div_of_mul_dvd this
        rw [Nat.mul_div_assoc (f n + l) p_dvd_flpn] at this
        replace := (Nat.Prime.dvd_mul prime_p).mp this
        omega
      zify at h5 h6
      have : (p : ℤ) ∣ (f n + k) - (f n + l) := Int.dvd_sub h5 h6
      ring_nf at this ⊢; simpa
