import Mathlib.Data.Vector.Defs

import QuantifierLean.Definitions2
import QuantifierLean.Lemmas2
import QuantifierLean.Lemmas2_1

open Mathlib

theorem f_inv_on {l a: Vector Int (k+1)} (p: Props2 a n):
  Set.InvOn (f_inv (offset b a l) a l) (f b a ls_zero) (X2 a l n) (Y2 a (offset b a l) n) := by
  rw [← f_lzero]
  rw [f_comp', f_comp]
  apply f_comp_comp_inv_on p


theorem f_bij_on {l a: Vector Int (k+1)} (p: Props2 a n):
  Set.BijOn (f b a ls_zero) (X2 a l n) (Y2 a (offset b a l) n) := by
  have hf : Set.MapsTo (f b a ls_zero) (X2 a l n) (Y2 a (offset b a l) n) := by
    rw [← @f_lzero k b l]
    rw [f_comp]
    have h_m := @h_maps_to (offset b a l) k a n
    apply Set.MapsTo.comp
    · apply h_maps_to
    · apply Set.MapsTo.comp
      · apply (f_maps_to p)
      · apply g_maps_to

  have hf' : Set.MapsTo (f_inv (offset b a l) a l) (Y2 a (offset b a l) n) (X2 a l n) := by
    rw [f_comp']
    apply Set.MapsTo.comp
    · apply Set.MapsTo.comp
      · apply g_maps_to'
      · apply f_inv_maps_to p
    · apply  h_maps_to'

  exact Set.InvOn.bijOn (f_inv_on p) hf hf'
