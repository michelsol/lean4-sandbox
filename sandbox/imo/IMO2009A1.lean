import Mathlib

open Finset Function
set_option maxRecDepth 10000

/- Find the largest possible integer $$ k$$ , such that the following statement is true:
Let 2009 arbitrary non-degenerated triangles be given.
In every triangle the three sides are colored, such that one is blue, one is red and one is white.
Now, for every color separately, let us sort the lengths of the sides.
We obtain
$$  \begin{array}{rlrl} b_{1} & \leq b_{2} & \leq \ldots \leq b_{2009} \quad & \\ & & \text { the lengths of the blue sides, } \\ r_{1} & \leq r_{2} & \leq \ldots \leq r_{2009} \quad \text { the lengths of the red sides, } \\ w_{1} & \leq w_{2} & \leq \ldots \leq w_{2009} \quad \text { the lengths of the white sides. } \end{array} $$



Then there exist $$ k$$  indices $$ j$$  such that we can form a non-degenerated triangle with side lengths $$ b_{j}, r_{j}, w_{j}$$  。 -/

theorem algebra_23897
    :
    let argmin {α β : Type _} [LinearOrder β] (f : α → β) (s : Finset α) (H : s.Nonempty) : α :=
      have h := (image f s).isLeast_min' (by simp [H])
      (Finset.mem_image.mp h.1).choose

    let monoLabelOn
        {α ι : Type _} [Zero α] [LinearOrder α] [Zero ι] [DecidableEq ι]
        (x : ι → α) (s : Finset ι) (i0 : ℕ) : ℕ → ι :=
      Nat.lt_wfRel.wf.fix (λ n ih ↦
        if hn : n ∈ Ico i0 (i0 + #s) then
        let label_lt_n k := if hk : k < n then ih k hk else 0
        argmin x (s \ (Ico i0 n).image label_lt_n) (by
          apply nonempty_of_ne_empty
          intro h1
          apply_fun (#.) at h1
          conv_rhs at h1 => simp
          have c1 := le_card_sdiff ((Ico i0 n).image label_lt_n) s
          have c2 : #((Ico i0 n).image label_lt_n) ≤ _ := card_image_le
          simp at c2
          simp at hn
          omega)
        else 0)

    -- assuming b > 0, r > 0, w > 0
    let sidesOfTriangle (b r w : ℝ) := b + r > w ∧ b + w > r ∧ r + w > b

    IsGreatest { k : ℕ |
      ∀ (B R W : ℕ → ℝ) (h1 : ∀ i ∈ Ico 1 2010, B i > 0 ∧ R i > 0 ∧ W i > 0 ∧ sidesOfTriangle (B i) (R i) (W i)),
        let b j := B (monoLabelOn B (Ico 1 2010) 1 j)
        let r j := R (monoLabelOn R (Ico 1 2010) 1 j)
        let w j := W (monoLabelOn W (Ico 1 2010) 1 j)
        ∃ (J : Finset ℕ) (hJ1 : J ⊆ Ico 1 2010) (hJ2 : #J = k),
          ∀ j ∈ J, sidesOfTriangle (b j) (r j) (w j) } 1 := by

  intro argmin
  intro monoLabelOn

  -- We introduce 7 lemmas that are not in mathlib, and that we will need to index sorted collections of triangle side lengths
  have argmin_mem {α β : Type _} [LinearOrder β] (f : α → β) (s : Finset α) (H : s.Nonempty) :
      argmin f s H ∈ s := by
    have h := (image f s).isLeast_min' (by simp [H])
    exact (Finset.mem_image.mp h.1).choose_spec.1

  have apply_argmin {α β : Type _} [LinearOrder β] (f : α → β) (s : Finset α) (H : s.Nonempty) :
      f (argmin f s H) = (s.image f).min' (by simp [H]) := by
    have h := (image f s).isLeast_min' (by simp [H])
    exact (Finset.mem_image.mp h.1).choose_spec.2

  have le_argmin {α β : Type _} [LinearOrder β] (f : α → β) (s : Finset α) (H : s.Nonempty) :
      ∀ a ∈ s, f (argmin f s H) ≤ f a := by
    have h := (image f s).isLeast_min' (by simp [H])
    simpa [lowerBounds, apply_argmin f s H] using h.2

  have nonempty_sdiff_Ico_of_lt_card
      {ι : Type _} [Zero ι] [DecidableEq ι]
      (y : ℕ → ι) {s : Finset ι} {i0 : ℕ} {n : ℕ} (hn : n ∈ Ico i0 (i0 + #s))
      : (s \ (Ico i0 n).image y).Nonempty := by
    apply nonempty_of_ne_empty
    intro h1
    apply_fun (#.) at h1
    conv_rhs at h1 => simp
    have c1 := le_card_sdiff ((Ico i0 n).image y) s
    have c2 : #((Ico i0 n).image y) ≤ _ := card_image_le
    simp at c2
    simp at hn
    omega

  have monoLabelOn_eq
      {α ι : Type _} [Zero α] [LinearOrder α] [Zero ι] [DecidableEq ι]
      (x : ι → α) (s : Finset ι) (i0 : ℕ) (n : ℕ) (hn : n ∈ Ico i0 (i0 + #s)) :
      monoLabelOn x s i0 n =
        argmin x (s \ (Ico i0 n).image (monoLabelOn x s i0))
          (nonempty_sdiff_Ico_of_lt_card _ hn) := by
      dsimp only [monoLabelOn]
      conv_lhs => rw [Nat.lt_wfRel.wf.fix_eq]
      split_ifs
      symm
      have h0 := nonempty_sdiff_Ico_of_lt_card (monoLabelOn x s i0) hn
      congr 2
      ext k
      simp only [mem_image, mem_Ico]
      constructor <;> intro ⟨l, h1, h2⟩
      . use l, h1
        simpa [h1.right] using h2
      . simp [h1.right] at h2
        use l

  have bijOn_monoLabelOn
      {α ι : Type _} [Zero α] [LinearOrder α] [Zero ι] [DecidableEq ι]
      (x : ι → α) (s : Finset ι) (i0 : ℕ) : Set.BijOn (monoLabelOn x s i0) (Ico i0 (i0 + #s)) s := by
    have a1 : Set.MapsTo (monoLabelOn x s i0) (Ico i0 (i0 + #s)) s := by
      intro n hn
      have h1 : monoLabelOn x s i0 n ∈ s \ (Ico i0 n).image (monoLabelOn x s i0) := by
        rw [monoLabelOn_eq x s i0 n hn]
        apply argmin_mem x _ (nonempty_sdiff_Ico_of_lt_card _ hn)
      rw [mem_sdiff] at h1
      exact h1.left
    have a2 : Set.InjOn (monoLabelOn x s i0) (Ico i0 (i0 + #s)) := by
      intro i hi j hj hij
      let m := monoLabelOn x s i0 i
      have h1 : m ∈ s \ (Ico i0 i).image (monoLabelOn x s i0) := by
        dsimp [m]
        rw [monoLabelOn_eq x s i0 i hi]
        apply argmin_mem x _ (nonempty_sdiff_Ico_of_lt_card _ hi)
      have h2 : m ∈ s \ (Ico i0 j).image (monoLabelOn x s i0) := by
        dsimp [m]
        rw [hij]
        rw [monoLabelOn_eq x s i0 j hj]
        apply argmin_mem x _ (nonempty_sdiff_Ico_of_lt_card _ hj)
      rw [mem_sdiff] at h1 h2
      replace h1 := h1.right
      replace h2 := h2.right
      simp at h1 h2
      simp at hi hj
      have h3 : ¬i < j := by
        intro h3
        apply h2 i (by omega) h3
        rfl
      have h4 : ¬j < i := by
        intro h4
        apply h1 j (by omega) h4
        exact hij.symm
      omega
    have a3 : Set.SurjOn (monoLabelOn x s i0) (Ico i0 (i0 + #s)) s := by
      have h1 := Set.surjOn_image (monoLabelOn x s i0) (Ico i0 (i0 + #s))
      suffices (monoLabelOn x s i0) '' (Ico i0 (i0 + #s)) = s from by rwa [this] at h1
      rw [←coe_image]
      apply congrArg Finset.toSet
      apply eq_of_subset_of_card_le
      . intro y hy
        obtain ⟨k, hk, hk2⟩ := by simpa only [mem_image] using hy
        subst hk2
        exact a1 hk
      . simp [card_image_of_injOn a2]
    split_ands
    . exact a1
    . exact a2
    . exact a3

  have monotoneOn_comp_monoLabelOn
      {α ι : Type _} [Zero α] [LinearOrder α] [Zero ι] [DecidableEq ι]
      (x : ι → α) (s : Finset ι) (i0 : ℕ) : MonotoneOn (x ∘ monoLabelOn x s i0) (Ico i0 (i0 + #s)) := by
    intro i hi j hj hij
    dsimp
    rw [monoLabelOn_eq x s i0 i hi]
    rw [monoLabelOn_eq x s i0 j hj]
    apply le_argmin x _ (nonempty_sdiff_Ico_of_lt_card _ hi)
    suffices s \ (Ico i0 j).image (monoLabelOn x s i0) ⊆ s \ (Ico i0 i).image (monoLabelOn x s i0) from by
      apply this
      apply argmin_mem x _ (nonempty_sdiff_Ico_of_lt_card _ hj)
    apply sdiff_subset_sdiff (by simp)
    apply image_subset_image
    intro k
    simp
    omega

  intro sidesOfTriangle

-- We will prove that the largest possible number $$ k$$  of indices satisfying the given condition is one.
  constructor

-- Firstly we prove that $$ b_{2009}, r_{2009}, w_{2009}$$  are always lengths of the sides of a triangle.
  . intro B R W h1 b r w
    use {2009}, by simp, by simp
    intro j hj
    simp at hj
    subst hj

-- Without loss of generality we may assume that $$ w_{2009} \geq r_{2009} \geq b_{2009}$$ .
    wlog h2 : w 2009 ≥ r 2009 ∧ r 2009 ≥ b 2009
    . have hb j : B (monoLabelOn B (Ico 1 2010) 1 j) = b j := rfl
      have hr j : R (monoLabelOn R (Ico 1 2010) 1 j) = r j := rfl
      have hw j : W (monoLabelOn W (Ico 1 2010) 1 j) = w j := rfl
      dsimp [sidesOfTriangle] at h1 ⊢
      by_cases c1 : w 2009 ≤ r 2009
      all_goals by_cases c2 : w 2009 ≤ b 2009
      all_goals by_cases c3 : r 2009 ≤ b 2009
      all_goals try linarith only [c1, c2, c3]
      all_goals iterate 7 specialize this (by assumption)
      . specialize this W R B (by
            intro i hi; obtain ⟨h1, h2, h3, h4⟩ := h1 i hi
            simp [h1, h2, h3]; ring_nf at h4 ⊢; simp [h4])
          (by simp only [hb, hr, hw]; split_ands <;> linarith)
        simp only [hb, hr, hw] at this; ring_nf at this ⊢; simp [this]
      . specialize this W B R (by
            intro i hi; obtain ⟨h1, h2, h3, h4⟩ := h1 i hi
            simp [h1, h2, h3]; ring_nf at h4 ⊢; simp [h4])
          (by simp only [hb, hr, hw]; split_ands <;> linarith)
        simp only [hb, hr, hw] at this; ring_nf at this ⊢; simp [this]
      . specialize this B W R (by
            intro i hi; obtain ⟨h1, h2, h3, h4⟩ := h1 i hi
            simp [h1, h2, h3]; ring_nf at h4 ⊢; simp [h4])
          (by simp only [hb, hr, hw]; split_ands <;> linarith)
        simp only [hb, hr, hw] at this; ring_nf at this ⊢; simp [this]
      . specialize this R W B (by
            intro i hi; obtain ⟨h1, h2, h3, h4⟩ := h1 i hi
            simp [h1, h2, h3]; ring_nf at h4 ⊢; simp [h4])
          (by simp only [hb, hr, hw]; split_ands <;> linarith)
        simp only [hb, hr, hw] at this; ring_nf at this ⊢; simp [this]
      . specialize this R B W (by
            intro i hi; obtain ⟨h1, h2, h3, h4⟩ := h1 i hi
            simp [h1, h2, h3]; ring_nf at h4 ⊢; simp [h4])
          (by simp only [hb, hr, hw]; split_ands <;> linarith)
        simp only [hb, hr, hw] at this; ring_nf at this ⊢; simp [this]
      . specialize this B R W (by
            intro i hi; obtain ⟨h1, h2, h3, h4⟩ := h1 i hi
            simp [h1, h2, h3]; ring_nf at h4 ⊢; simp [h4])
          (by simp only [hb, hr, hw]; split_ands <;> linarith)
        simp only [hb, hr, hw] at this; ring_nf at this ⊢; simp [this]

-- We show that the inequality $$ b_{2009}+r_{2009} > w_{2009}$$  holds.
    suffices b 2009 + r 2009 > w 2009 from by
      dsimp [sidesOfTriangle]
      split_ands
      . exact this
      . linarith
      . linarith

-- Evidently, there exists a triangle with side lengths $$ 𝓌, 𝒷, 𝓇$$  for the white, blue and red side, respectively, such that $$ w_{2009}=𝓌.$$
    let i := monoLabelOn W (Ico 1 2010) 1 2009
    have hi : i ∈ Ico 1 2010 := (bijOn_monoLabelOn W (Ico 1 2010) 1).mapsTo (by norm_num)
    have h3 := (h1 i hi).right.right.right
    dsimp [sidesOfTriangle] at h3
    set 𝒷 := B i
    let ib := (monoLabelOn B (Ico 1 2010) 1).invFunOn (Ico 1 2010) i
    have hib : ib ∈ Ico 1 2010 := by
      have c1 := bijOn_monoLabelOn B (Ico 1 2010) 1
      exact c1.invOn_invFunOn.left.mapsTo c1.surjOn hi
    have h𝒷 : 𝒷 = b ib := by
      dsimp [b, ib]
      have c1 := (bijOn_monoLabelOn B (Ico 1 2010) 1).invOn_invFunOn.right.eqOn hi
      simp at c1
      simp [c1]
    set 𝓇 := R i
    let ir := (monoLabelOn R (Ico 1 2010) 1).invFunOn (Ico 1 2010) i
    have hir : ir ∈ Ico 1 2010 := by
      have c1 := bijOn_monoLabelOn R (Ico 1 2010) 1
      exact c1.invOn_invFunOn.left.mapsTo c1.surjOn hi
    have h𝓇 : 𝓇 = r ir := by
      dsimp [r, ir]
      have c1 := (bijOn_monoLabelOn R (Ico 1 2010) 1).invOn_invFunOn.right.eqOn hi
      simp at c1
      simp [c1]
    set 𝓌 := W i
    have h𝓌 : 𝓌 = w 2009 := by simp [w]

-- By the conditions of the problem we have $$ 𝒷+𝓇 > 𝓌 \;$$
    have h5 : 𝒷 + 𝓇 > 𝓌 := by ring_nf at h3 ⊢; simp [h3]
-- $$b_{2009} \geq 𝒷 $$  and $$ r_{2009} \geq r$$ .
    have h5 : 𝒷 ≤ b 2009 := by
      rw [h𝒷]
      apply monotoneOn_comp_monoLabelOn B
      . simpa using hib
      . norm_num
      . simp at hib; omega
    have h6 : 𝓇 ≤ r 2009 := by
      rw [h𝓇]
      apply monotoneOn_comp_monoLabelOn R
      . simpa using hir
      . norm_num
      . simp at hir; omega

-- From these inequalities it follows $$  b_{2009}+r_{2009} \geq b+r > w=w_{2009} $$
    linarith


-- Secondly we will describe a sequence of triangles
-- for which $$ w_{j}, b_{j}, r_{j}$$  with $$ j < 2009$$  are not the lengths of the sides of a triangle.
  . dsimp [upperBounds]
    intro k h1

-- Let us define the sequence $$ \Delta_{j}, j=1,2, \ldots, 2009$$ , of triangles,
-- where $$ \Delta_{j}$$  has a blue side of length $$ 2 j$$ , a red side of length $$ j$$  for all $$ j \leq 2008$$  and 4018 for $$ j=2009$$ ,
-- and a white side of length $$ j+1$$  for all $$ j \leq 2007$$ , 4018 for $$ j=2008$$  and 1 for $$ j=2009$$ .

    let B (j : ℕ) : ℝ := 2 * j
    let R (j : ℕ) : ℝ := if j = 2009 then 4018 else j
    let W (j : ℕ) : ℝ := if j = 2008 then 4018 else if j = 2009 then 1 else j + 1

-- Since
-- $$  \begin{array}{rrrl} (j+1)+j > 2 j & \geq j+1 > j, & \text { if } & j \leq 2007 \\ 2 j+j > 4018 > 2 j \quad > j, & \text { if } & j=2008 \\ 4018+1 > 2 j & =4018 > 1, & \text { if } & j=2009 \end{array} $$

-- such a sequence of triangles exists.

    obtain ⟨J, hJ1, hJ2, h1⟩ := h1 B R W (by
      intro i hi
      simp at hi
      dsimp [B, R, W]
      split_ands
      all_goals norm_cast
      all_goals try split_ifs
      all_goals omega)

    suffices J ⊆ {2009} from by simpa [hJ2] using card_le_card this
    intro j hj
    specialize hJ1 hj
    specialize h1 j hj
    contrapose h1
    replace h1 : 1 ≤ j ∧ j ≤ 2008 := by simp at hJ1 h1; omega
    let b j := B (monoLabelOn B (Ico 1 2010) 1 j)
    let r j := R (monoLabelOn R (Ico 1 2010) 1 j)
    let w j := W (monoLabelOn W (Ico 1 2010) 1 j)
    show ¬sidesOfTriangle (b j) (r j) (w j)

-- Moreover as W, R, and B are already sorted, $$ w_{j}=j, r_{j}=j$$  and $$ b_{j}=2 j$$  for $$ 1 \leq j \leq 2008$$ .
    have h2 : w j = j := by
      sorry
    have h3 : r j = j := by
      sorry
    have h4 : b j = 2 * j := by
      sorry

-- Then $$  w_{j}+r_{j}=j+j=2 j=b_{j} $$  i.e., $$ b_{j}, r_{j}$$  and $$ w_{j}$$  are not the lengths of the sides of a triangle for $$ 1 \leq j \leq 2008$$ .
    dsimp [sidesOfTriangle]
    rw [h2, h3, h4]
    norm_cast
    omega
