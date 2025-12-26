import Mathlib

open Finset

/-
Let $k \geqslant 2$ be an integer.
Find the smallest integer $n \geqslant k+1$ with the property
that there exists a set of $n$ distinct real numbers such that each of its elements
can be written as a sum of $k$ other distinct elements of the set.
-/

theorem algebra_24395
    (k : ℕ) (hk : k ≥ 2)
    : let S := { n ≥ k + 1 |
        ∃ (A : Finset ℝ) (_ : A.card = n),
          ∀ x ∈ A, ∃ (S : Finset ℝ) (_ : S ⊆ A \ {x}) (_ : S.card = k),
            x = ∑ y ∈ S, y }
      IsLeast S (k + 4) := by
  intro S
  dsimp only [S]
  constructor
  swap

-- First we show that $n \geqslant k+4$.
  . intro n
    intro ⟨h1, A, hA, h2⟩

-- Suppose that there exists such a set with $n$ numbers
-- and denote them by $a_{1} < a_{2} < \cdots < a_{n}$.
    let label (s : Finset ℝ) i0 k := (s.sort (. ≤ .)).getD (k - i0) 0
    let a := label A 1
    have ha : StrictMonoOn a (Icc 1 n) := by
      have strictMonoOn_label (s : Finset ℝ) i0 : StrictMonoOn (label s i0) (Ico i0 (i0 + s.card)) := by
        intro i hi j hj hij
        simp at hi hj
        dsimp [label]
        have c0 := (s.sort_sorted (. ≤ .))
        have c1 := ((s.sort (. ≤ .)).getElem?_eq_some_getElem_iff (i - i0) (by simp; omega)).mpr trivial
        have c2 := ((s.sort (. ≤ .)).getElem?_eq_some_getElem_iff (j - i0) (by simp; omega)).mpr trivial
        simp only [List.getD_eq_getElem?_getD, Option.getD_some, c1, c2]
        apply lt_of_le_of_ne
        . exact List.pairwise_iff_getElem.mp c0 (i - i0) (j - i0) (by simp; omega) (by simp; omega) (by omega)
        . intro h
          have := (s.sort_nodup (. ≤ .)).getElem_inj_iff.mp h
          omega
      simpa [show Ico 1 (1 + #A) = Icc 1 n from by ext j; simp; omega] using strictMonoOn_label A 1
    have ha2 : image a (Icc 1 n) = A := by
      have image_label (s : Finset ℝ) i0 :
          (Ico i0 (s.card + i0)).image (label s i0) = s := by
        set p := label s i0
        apply eq_of_subset_of_card_le
        . intro x hx
          obtain ⟨k, hk, hk2⟩ : ∃ k, (i0 ≤ k ∧ k < s.card + i0) ∧ p k = x := by simpa using hx
          subst hk2
          suffices p k ∈ s.sort (. ≤ .) from by simpa only [mem_sort]
          apply List.mem_iff_get.mpr
          use ⟨k - i0, by simp at hk ⊢; omega⟩
          exact (List.getD_eq_getElem _ 0 (by simp at hk ⊢; omega)).symm
        . rw [card_image_of_injOn]
          . simp
          . intro i hi j hj hij
            simp at hi hj
            suffices i - i0 = j - i0 from by omega
            have c1 := ((s.sort (. ≤ .)).getElem?_eq_some_getElem_iff (i - i0) (by simp; omega)).mpr trivial
            have c2 := ((s.sort (. ≤ .)).getElem?_eq_some_getElem_iff (j - i0) (by simp; omega)).mpr trivial
            apply (s.sort_nodup (. ≤ .)).getElem_inj_iff.mp
            simpa [p, label, c1, c2] using hij
      simpa [show Ico 1 (#A + 1) = Icc 1 n from by ext j; simp; omega] using image_label A 1
    have ha3 i (hi : i ∈ Icc 1 n) : a i ∈ A := by
      rw [←ha2]
      suffices ∃ j ∈ Icc 1 n, a j = a i from by simpa
      use i
    replace h2 i (hi : i ∈ Icc 1 n) :
        ∃ (s : Finset ℕ) (_ : s ⊆ Icc 1 n \ {i}) (_ : s.card = k),
          a i = ∑ j ∈ s, a j := by
      obtain ⟨S, c1, c2, c3⟩ := h2 (a i) (ha3 i hi)
      rw [←ha2] at c1
      let s := { j ∈ Icc 1 n | a j ∈ S }
      use s
      use by
        intro j hj
        have ⟨hj1, hj2⟩ : j ∈ Icc 1 n ∧ a j ∈ S := by simpa [s] using hj
        specialize c1 hj2
        simp at c1 hj1 ⊢
        tauto
      use by
        sorry
      calc
        _ = _ := c3
        _ = _ := by
          rw [sum_filter]
          sorry

-- We will now need the following lemma :
    have sum_Ico_card_le_sum_of_monotoneOn
        {α} [Preorder α] [AddCommMonoid α] [AddLeftMono α]
        (a b : ℕ) (s : Finset ℕ) (hs : s ⊆ Icc a b) (f : ℕ → α) (hf : MonotoneOn f (Icc a b)) :
        ∑ i ∈ Ico a (a + s.card), f i ≤ ∑ i ∈ s, f i := by
      induction' hs2 : s.card with n ih generalizing s
      . simp [card_eq_zero] at hs2
        simp [hs2]
      . obtain ⟨j, hj1, hj2⟩ : ∃ j ∈ s, j ≥ a + n := by
          by_contra h
          push_neg at h
          replace h : s ⊆ Ico a (a + n) := by
            intro x hx
            specialize hs hx
            specialize h x hx
            simp at hs ⊢; omega
          replace h := card_le_card h
          simp at h
          omega
        have c1 := card_le_card hs
        simp at c1
        have h1 : {a + n} ⊆ Ico a (a + (n + 1 : ℕ)) := by intro k; simp; omega
        rw [←sum_sdiff h1]
        replace h1 : Ico a (a + (n + 1 : ℕ)) \ {a + n} = Ico a (a + n) := by ext k; simp; omega
        rw [h1]
        replace h1 : {j} ⊆ s := by intro k hk; simp at hk; subst hk; exact hj1
        rw [←sum_sdiff h1]
        iterate 2 rw [sum_singleton]
        have h2 : f (a + n) ≤ f j := hf (by simp; omega) (hs hj1) hj2
        specialize ih (s \ {j})
          (by intro k hk; simp at hk; exact hs hk.1)
          (by simp [card_sdiff h1]; omega)
        exact add_le_add ih h2

-- We will also need the following lemma :
    have sum_le_sum_Icc_card_of_monotoneOn
        {α} [Preorder α] [AddCommMonoid α] [AddLeftMono α]
        (a b : ℕ) (s : Finset ℕ) (hs : s ⊆ Icc a b) (f : ℕ → α) (hf : MonotoneOn f (Icc a b)) :
        ∑ i ∈ s, f i ≤ ∑ i ∈ Icc (b + 1 - s.card) b, f i := by
      induction' hs2 : s.card with n ih generalizing s
      . simp [card_eq_zero] at hs2
        simp [hs2]
      . obtain ⟨j, hj1, hj2⟩ : ∃ j ∈ s, j ≤ b - n := by
          by_contra h
          push_neg at h
          replace h : s ⊆ Ioc (b - n) b := by
            intro x hx
            specialize hs hx
            specialize h x hx
            simp at hs ⊢; omega
          replace h := card_le_card h
          simp at h
          omega
        have c1 := card_le_card hs
        simp at c1
        have h1 : {b - n} ⊆ Icc (b + 1 - (n + 1 : ℕ)) b := by intro k hk; simp at hk ⊢; omega
        rw [←sum_sdiff h1]
        replace h1 : Icc (b + 1 - (n + 1 : ℕ)) b \ {b - n} = Icc (b + 1 - n) b := by ext k; simp; omega
        rw [h1]
        have h1 : {j} ⊆ s := by intro k hk; simp at hk; subst hk; exact hj1
        rw [←sum_sdiff h1]
        iterate 2 rw [sum_singleton]
        have h2 : f j ≤ f (b - n) := hf (hs hj1) (by simp; omega) hj2
        specialize ih (s \ {j})
          (by intro k hk; simp at hk; exact hs hk.1)
          (by simp [card_sdiff h1]; omega)
        exact add_le_add ih h2


-- Note that in order to express $a_{1}$ as a sum of $k$ distinct elements of the set,
-- we must have $a_{1} \geqslant a_{2}+\cdots+a_{k+1}$
    have h3 : a 1 ≥ ∑ i ∈ Icc 2 (k + 1), a i := by
      specialize h2 1 (by simp; omega)
      obtain ⟨s, hs1, hs2, hs3⟩ := h2
      replace hs1 : s ⊆ Icc 2 n := by intro x hx; specialize hs1 hx; simp at hs1 ⊢; omega
      have c1 := sum_Ico_card_le_sum_of_monotoneOn 2 n s hs1 a (by
        intro i hi j hj hij
        simp at hi hj
        apply ha.monotoneOn
        . simp; omega
        . simp; omega
        . exact hij
        )
      rwa [hs2, ←hs3, show Ico 2 (2 + k) = Icc 2 (k + 1) from by ext x; simp; omega] at c1

-- and, similarly for $a_{n}$, we must have $a_{n-k}+\cdots+a_{n-1} \geqslant a_{n}$.
    have h4 : a n ≤ ∑ i ∈ Icc (n - k) (n - 1), a i := by
      specialize h2 n (by simp; omega)
      obtain ⟨s, hs1, hs2, hs3⟩ := h2
      replace hs1 : s ⊆ Icc 1 (n - 1) := by intro x hx; specialize hs1 hx; simp at hs1 ⊢; omega
      have c1 := sum_le_sum_Icc_card_of_monotoneOn 1 (n - 1) s hs1 a (by
        intro i hi j hj hij
        simp at hi hj
        apply ha.monotoneOn
        . simp; omega
        . simp; omega
        . exact hij
        )
      rwa [hs2, ←hs3, show n - 1 + 1 - k = n - k from by omega] at c1

-- We know that $n \geqslant k+1$, and will show by cases that n cannot be ≤  k + 3.
    rcases (by omega : n = k + 1 ∨ n = k + 2 ∨ n = k + 3 ∨ k + 4 ≤ n) with h5 | h5 | h5 | h5
-- If $n=k+1$ then we have
-- $a_{1} \geqslant a_{2}+\cdots+a_{k+1}>a_{1}+\cdots+a_{k} \geqslant a_{k+1}$,
-- which gives a contradiction.
    . subst h5
      have h5 : a 1 < a (k + 1) := by
        apply ha
        . simp
        . simp
        . omega
      have h6 : a 1 ≥ a (k + 1) := calc
        _ ≥ _ := h3
        _ ≥ ∑ i ∈ Icc 1 k, a i := by
          have c1 : {1} ⊆ Icc 1 k := by intro j; simp; omega
          rw [←sum_sdiff c1]
          replace c1 : Icc 1 k \ {1} = Icc 2 k := by ext j; simp; omega
          rw [c1]
          replace c1 : {k + 1} ⊆ Icc 2 (k + 1) := by intro j; simp; omega
          rw [←sum_sdiff c1]
          replace c1 : Icc 2 (k + 1) \ {k + 1} = Icc 2 k := by ext j; simp; omega
          rw [c1]
          suffices a 1 ≤ a (k + 1) from by simpa
          linarith
        _ ≥ _ := by simpa using h4
      linarith
-- If $n=k+2$ then we have $a_{1} \geqslant a_{2}+\cdots+a_{k+1} \geqslant a_{k+2}$,
-- that again gives a contradiction.
    . subst h5
      have h5 : a 1 < a (k + 2) := by
        apply ha
        . simp
        . simp
        . omega
      have h6 : a 1 ≥ a (k + 2) := calc
        _ ≥ _ := h3
        _ ≥ _ := by simpa using h4
      linarith
-- If $n=k+3$ then we have
-- $a_{1} \geqslant a_{2}+\cdots+a_{k+1}$ and $a_{3}+\cdots+a_{k+2} \geqslant a_{k+3}$.
-- Adding the two inequalities we get $a_{1}+a_{k+2} \geqslant a_{2}+a_{k+3}$,
-- again a contradiction.
    . subst h5
      sorry
-- Thus, $n ≥ k + 4$
    . exact h5

-- It remains to give an example of a set with $k+4$ elements
-- satisfying the condition of the problem.
  . split_ands; omega

    -- We will construct this set in ℤ
    suffices ∃ A : Finset ℤ, ∃ (_ : #A = (k : ℤ) + 4),
      ∀ x ∈ A, ∃ S,
        ∃ (_ : S ⊆ A \ {x}) (_ : #S = (k : ℤ)), x = ∑ y ∈ S, y from by
          obtain ⟨A, c1, c2⟩ := this
          use A.image (↑)
          use by
            rw [card_image_of_injOn (by apply Int.cast_injective.injOn)]
            zify
            exact c1
          intro x hx
          obtain ⟨a, hx1, hx2⟩ := by simpa using hx
          specialize c2 a hx1
          obtain ⟨S, c2, c3, c4⟩ := c2
          use S.image (↑)
          use by
            have : image ((↑) : ℤ → ℝ) S ⊆ image ((↑) : ℤ → ℝ) (A \ {a}):= image_subset_image c2
            rw [image_sdiff_of_injOn] at this
            . simpa [hx2]
            . apply Int.cast_injective.injOn
            . simpa [hx2]
          use by
            rw [card_image_of_injOn (by apply Int.cast_injective.injOn)]
            zify
            exact c3
          rify [hx2] at c4
          simpa

-- We will split the proof into two cases based on the parity of k.
    obtain ⟨l, hl | hl⟩ := Int.even_or_odd' k

-- We start with the case when $k=2 l$ and $l \geqslant 1$.
    . rw [hl]

-- In that case, denote by $A_{i}=\{-i, i\}$ and take the set $A_{1} \cup \cdots \cup A_{l+2}$,
-- which has exactly $k+4=2 l+4$ elements.
      let A i : Finset ℤ := {-i, i}
      let A' := (Icc 1 (l + 2)).biUnion A
      use A'
      use by
        rw [card_biUnion]
        push_cast
        . calc
            _ = ∑ i ∈ Icc 1 (l + 2), (2 : ℤ) := by
              apply sum_congr rfl
              intro i hi
              norm_cast
              apply card_pair
              simp at hi
              omega
            _ = _ := by simp; omega
        . intro i hi j hj hij
          intro s hsi hsj x hx
          specialize hsi hx
          specialize hsj hx
          simp [A] at hsi hsj hi hj ⊢
          omega

-- We are left to show that this set satisfies the required condition.

      intro i hi

-- Note that if a number $i$ can be expressed in the desired way,
-- then so can $-i$ by negating the expression.
-- Therefore, we consider only $1 \leqslant i \leqslant l+2$.
      clear S
      wlog hi' : i ∈ Icc 1 (l + 2)
      . specialize this k hk l hl (-i) (by
          simp [A', A] at hi hi' ⊢
          use -i
          omega) (by
          simp [A', A] at hi hi' ⊢
          omega)
        obtain ⟨S, c1, c2, c3⟩ := this
        let T := S.image (-.)
        use T
        use by
          sorry
        use by
          sorry
        sorry

-- We split in two cases as $i < l + 2$ or $i = l + 2$.
      have hi1 : 1 ≤ i := by simp at hi'; omega
      have hi2 : i ≤ l + 2 := by simp at hi'; omega
      rcases (show i < l + 2 ∨ i = l + 2 from by omega) with hi2 | hi2
-- If $i < l+2$, we sum the numbers from some $l-1$ sets $A_{j}$ with $j \neq 1, i+1$,
-- and the numbers $i+1$ and -1 .
      .
        let S := {i+1, -1} ∪ (Icc 2 (l + 1) \ {i}).biUnion A
        use S
        use by
          intro x hx
          simp [S, A] at hx
          sorry
        use by
          sorry
        sorry

-- For $i=l+2$, we sum the numbers from some $l-1$ sets $A_{j}$ with $j \neq 1, l+1$,
-- and the numbers $l+1$ and 1 .
      . sorry

-- It remains to a give a construction for odd $k=2 l+1$
-- with $l \geqslant 1$ (since $k \geqslant 2$ ).
    . sorry
-- To that end, we modify the construction for $k=2 l$ by adding 0 to the previous set.
-- This is a valid set as 0 can be added to each constructed expression,
-- and 0 can be expressed as follows : take the numbers $1,2,-3$
-- and all the numbers from the remaining $l-1$ sets $A_{4}, A_{5}, \cdots, A_{l+2}$.
