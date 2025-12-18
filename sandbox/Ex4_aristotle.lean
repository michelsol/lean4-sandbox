/-
This file was edited by Aristotle.

Lean Toolchain version: leanprover/lean4:v4.20.0-rc5
Mathlib version: d62eab0cc36ea522904895389c301cf8d844fd69 (May 9, 2025)

Your Lean code is run in a custom environment, which uses these headers:

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

The following was proved by Aristotle:

- example :
    let f

- example :
    let f
-/

import Mathlib


/-
Example: Counting permutations of 123
-/
example :
    let f := fun p : Fin 3 ↪ Fin 3 => ![1, 2, 3] ∘ p
    (Finset.univ.image f).card = 6 := by
  bound;
  -- Since there are 6 permutations of Fin 3, and each permutation gives a distinct list, the image of f has 6 elements.
  have h_card : Finset.card (Finset.image f Finset.univ) = Finset.card (Finset.univ : Finset (Fin 3 ↪ Fin 3)) := by
    -- To prove injectivity, assume $f(p) = f(q)$ for some embeddings $p$ and $q$. We need to show that $p = q$.
    have h_inj : Function.Injective f := by
      intro p q h_eq; ext i; replace h_eq := congr_fun h_eq i; aesop;
      rcases p_i : p i with ( _ | _ | _ | p_i ) <;> rcases q_i : q i with ( _ | _ | _ | q_i ) <;> simp_all +decide <;> tauto;
    exact Finset.card_image_of_injective _ h_inj;
  norm_num +zetaDelta at *;
  convert h_card using 1

/-
Example: Counting permutations of 1233
-/
example :
    let f := fun p : Fin 4 ↪ Fin 4 => ![1, 2, 3, 3] ∘ p
    (Finset.univ.image f).card = 12 := by
  bound;
  -- To prove the cardinality is 12, we can show that the image of f is exactly the set of all distinct permutations of ![1, 2, 3, 3].
  have h_image : Finset.image f Finset.univ = Finset.image (fun p : Fin 4 → Fin 4 => ![1, 2, 3, 3] ∘ p) (Finset.filter (fun p => Function.Injective p) (Finset.univ : Finset (Fin 4 → Fin 4))) := by
    -- To prove the equality of the images, we show mutual inclusion.
    apply Finset.ext
    intro x
    simp [f];
    -- If there exists an embedding $p$ such that $![1, 2, 3, 3] \circ p = x$, then since $p$ is injective, we can take $a = p$.
    apply Iff.intro
    intro h
    obtain ⟨p, hp⟩ := h
    use p
    aesop;
    · exact p.injective;
    · -- If there exists an injective function $a$ such that $![1, 2, 3, 3] \circ a = x$, then since $a$ is injective, we can take $a$ as the embedding.
      intro h
      obtain ⟨a, ha_inj, ha_eq⟩ := h
      use ⟨a, ha_inj⟩
      aesop;
  exact h_image ▸ by native_decide;
