import Mathlib.Data.Vector.Defs

import QuantifierLean.Definitions
import QuantifierLean.Lemmas

open Mathlib

theorem f_bij_on' {l a: Vector Int (k+1)} (p: Props a n) (C: Vector Int (k+1) → Prop):
  Set.BijOn (f b a) (X a l n C) (Y a l (offset b a l) n C) := by
  rw [Y3_subset_Y2', ← cond_image (f_inv_on p) (f_bij_on p), ← X3_subset_X3']
  apply Set.BijOn.subset_left (f_bij_on p) (X3_subset_X2 a l n C)

theorem f_inv_on' {a l: Vector Int (k+1)} (p: Props a n):
  Set.InvOn (f_inv (offset b a l) a l) (f b a) (X a l n C) (Y a l (offset b a l) n C) := by
  apply Set.InvOn.mono (f_inv_on p)
  rw [X3_subset_X3']
  apply Set.inter_subset_left
  rw [Y3_subset_Y2']
  apply Set.inter_subset_left

theorem equiv_quantifier' (a l: Vector Int (k+1)) (n: Int) (C: Vector Int (k+1) → Prop) (p: Props a n)
  (A: Int → α) -- This models an array/arbitrary data structure which is indexed by an integer
  (R: α → Vector Int (k+1) → Prop): -- This models a random property, which takes an array value
  (∀ xs: Vector Int (k+1), xs ∈ X a l n C → R (A (f b a xs)) xs) =
  (∀ x: Int, x ∈ (Y a l (offset b a l) n C) → R (A x) (f_inv (offset b a l) a l x)) := by
  apply equiv_quantifier
  apply (f_inv_on' p)
  apply (f_bij_on' p)
