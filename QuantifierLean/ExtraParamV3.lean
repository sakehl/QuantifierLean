import Mathlib.Data.Vector.Defs

import QuantifierLean.Definitions2
import QuantifierLean.Lemmas2
import QuantifierLean.Lemmas2_1

open Mathlib

-- @[inline] def Vector.range (n : Nat) : Vector Nat n := ⟨List.range n, by simp⟩

@[inline] def Vector.fin_range (n : Nat) : Vector (Fin n) n :=
  ⟨(List.range n).pmap (fun i h => ⟨i, h⟩) (by simp), by simp⟩

@[simp]
lemma Vector.get_fin_range (n: Nat) (i: Fin n): (Vector.fin_range n).get i = i := by
  simp [Vector.fin_range]
  rw [Vector.get]
  simp
  rw [List.getElem_pmap]
  simp

def f_inv'' (off: Int) (as ls: Mathlib.Vector Int (k+1)) (x': Int): Vector Int (k+1) :=
  (Vector.fin_range (k+1)).map fun i => base off as x' i / |as.get i| + ls.get i

lemma f_inv_same (k: Nat) (as ls: Vector Int (k+1)):
  f_inv'' off as ls x' = f_inv off as ls x' := by
  rw [f_inv'']
  apply Mathlib.Vector.ext
  intro i
  rw [f_get_is_f_inv_el]
  simp
  rw [f_inv_el]

def Fin.FinSet (n: Nat): Finset (Fin n) :=
  Finset.attachFin (Finset.range n) (by intro m; simp)

def f' (b: Int) (as xs:  Vector Int k) : Int :=
  b + ∑ i ∈ Fin.FinSet k, as.get i * xs.get i

lemma Multiset.pmap_map {p : β → Prop} (g : ∀ b, p b → γ) (f : α → β) (s) :
    ∀ H, (pmap g (map f s) H) = pmap (fun a h => g (f a) h) s fun _ h => H _ (mem_map_of_mem _ h):= by
    induction s using Quot.inductionOn with
    | h l =>
      intro H
      apply congr_arg _ (List.pmap_map g f l H)

lemma fin_sum_prod {k: Nat} (x y: Vector Int k) :
  ∑ i in Fin.FinSet k, x.get i * y.get i = prodSum x y := by
  induction k with
  | zero =>
    match x, y with
    | ⟨[],_⟩, ⟨[],_⟩ =>
    simp [prodSum, Fin.FinSet, Finset.attachFin]
  | succ k ih =>
    cases' x, y using Vector.casesOn₂ with cons x y xs ys
    rw [prodSum_cons]
    rw [<- ih xs ys]
    conv =>
      rw [Fin.FinSet]
      arg 1; arg 1; arg 1
      rw [Finset.range]
      arg 1
      rw [Nat.add_comm, Multiset.range_add]
    rw [Finset.sum, Finset.val, Finset.attachFin]
    simp
    rw [Multiset.map_pmap, Multiset.pmap_map]
    -- Rewrite rhs
    rw[Fin.FinSet, Finset.attachFin, Finset.sum]
    rw [Multiset.map_pmap]
    apply congr_arg
    apply Multiset.pmap_congr
    intro i _ lt lt2
    have eq: (⟨1 + i, lt⟩: Fin (k+1)) = (⟨i, lt2⟩: Fin k).succ := by
      simp
      rw [Nat.add_comm]
    rw [eq, Vector.get_cons_succ, Vector.get_cons_succ]

lemma f_equiv (b: Int) (as xs:  Vector Int k):
  f' b as xs = f b as ls_zero xs := by
  rw [f', f]
  rw [fin_sum_prod]
  simp


theorem f_inv_on {a l: Vector Int (k+1)} (p: Props2 a n):
  Set.InvOn (f_inv (offset b a l) a l) (f b a ls_zero) (X2 a l n) (Y2 a (offset b a l) n) := by
  rw [← f_lzero]
  rw [f_comp', f_comp]
  apply f_comp_comp_inv_on p

lemma f_maps_to'{a l: Vector Int (k+1)} (p: Props2 a n): Set.MapsTo (f b a ls_zero) (X2 a l n) (Y2 a (offset b a l) n) := by
  rw [← @f_lzero k b l]
  rw [f_comp]
  have h_m := @h_maps_to (offset b a l) k a n
  apply Set.MapsTo.comp
  · apply h_maps_to
  · apply Set.MapsTo.comp
    · apply (f_maps_to p)
    · apply g_maps_to

lemma f_inv_maps_to'{a l: Vector Int (k+1)} (p: Props2 a n): Set.MapsTo (f_inv (offset b a l) a l) (Y2 a (offset b a l) n) (X2 a l n) := by
  rw [f_comp']
  apply Set.MapsTo.comp
  · apply Set.MapsTo.comp
    · apply g_maps_to'
    · apply f_inv_maps_to p
  · apply  h_maps_to'

theorem f_bij_on {l a: Vector Int (k+1)} (p: Props2 a n):
  Set.BijOn (f b a ls_zero) (X2 a l n) (Y2 a (offset b a l) n) := by
  exact Set.InvOn.bijOn (f_inv_on p) (f_maps_to' p) (f_inv_maps_to' p)


def X3 (as ls : Vector Int (k+1)) (n : Int)
(C: Vector Int (k+1) → Prop)
: Set (Vector Int (k+1)) :=
  {xs : Vector Int (k+1) |
    xs.head < ls.head + n ∧
    (∀ i: Fin (k+1), ls.get i ≤ xs.get i) ∧
    (∀ i: Fin (k+1), ↑i<k →
      (0 < as.last → upToProd as ls xs (i+1)  < as.get i) ∧
      (as.last < 0 → as.get i < upToProd as ls xs (i+1))
    )
    ∧ C xs
  }

def Y3 (as ls: Vector Int (k+1)) (off n: Int)
(C: Vector Int (k+1) → Prop)
: Set Int :=
  {x : Int |
    base off as x k % as.last = 0 ∧
    (0<as.last → 0 ≤ x-off ∧ x-off < as.head*n) ∧
    (as.last<0 → as.head*n < x-off ∧ x-off ≤ 0)
    ∧ C (f_inv off as ls x)
  }

lemma implies_eq_and{a b: Prop}: ((a → b) ∧ a) = (b ∧ a) := by
  apply Eq.propIntro
  tauto
  tauto

lemma set_implies' {a b: α → Prop} {s : α}: {s: α | b s ∧ a s} = {s: α | (a s → b s) ∧ a s} := by
  conv =>
    -- rhs
    -- rw [setOf]
    -- arg 2
    pattern (_ → _) ∧ _
    rw [implies_eq_and]


lemma X3_subset_X2 (a l: Vector Int (k+1)) (n: Int) (C: Vector Int (k+1) → Prop):
  X3 a l n C ⊆ X2 a l n := by
  -- rw [Set.inter_comm, Set.left_eq_inter]
  intro xs
  intro h
  constructor
  apply h.left
  constructor
  apply h.right.left
  apply h.right.right.left

lemma Y3_subset_Y2 (a l: Vector Int (k+1)) (n: Int) (C: Vector Int (k+1) → Prop):
  Y3 a l off n C = Y2 a off n ∩ Y3 a l off n C := by
  rw [Set.inter_comm, Set.left_eq_inter]
  intro xs
  intro h
  constructor
  apply h.left
  constructor
  apply h.right.left
  apply h.right.right.left

lemma Y3_subset_Y2' (a l: Vector Int (k+1)) (n: Int) (C: Vector Int (k+1) → Prop):
  Y3 a l off n C = Y2 a off n ∩ {x : Int | C (f_inv off a l x)}  := by
  rw [Y3]
  conv =>
    lhs
    pattern _ ∧ _
    tactic =>
      nth_rewrite 2 [← and_assoc]
      nth_rewrite 1 [← and_assoc]
  rw [Set.setOf_and]
  rw [Y2]

lemma X3_subset_X3' (a l: Vector Int (k+1)) (n: Int) (C: Vector Int (k+1) → Prop):
  X3 a l n C = X2 a l n ∩ {x : Vector Int (k+1) | C x}  := by
  rw [X3]
  conv =>
    lhs
    pattern _ ∧ _
    tactic =>
      nth_rewrite 2 [← and_assoc]
      nth_rewrite 1 [← and_assoc]
  rw [Set.setOf_and]
  rw [X2]



lemma cond_image  {α : Type u_1} {β : Type u_2} {f : α → β} {f_inv : β → α} {s : Set α} {t : Set β} {p : α → Prop}
  (inv: Set.InvOn f_inv f s t) (bij: Set.BijOn f s t):
  f '' ((s ∩ {x : α | p x})) = t ∩ {y : β | p (f_inv y)} := by
  apply Set.Subset.antisymm
  case h₁ =>
    intro y yinIm
    match yinIm with
    | ⟨x, xin, h⟩ =>
    have xinS: x ∈ s := by
      apply Set.mem_of_mem_inter_left xin
    have xinPx: x ∈ {x | p x} := by
      apply Set.mem_of_mem_inter_right xin
    apply Set.mem_inter
    have h1 := Set.BijOn.image_eq bij
    rw [← h, ← h1]
    use x
    apply Set.mem_setOf.mpr
    have eq: f_inv y = x := by
      rw [← h]
      apply Set.RightInvOn.eq inv.left xinS
    rw [eq]
    apply Set.mem_setOf.mp xinPx
  case h₂ =>
    intro y yinInter
    match yinInter with
    | ⟨yinT, yinP⟩ =>
    use (f_inv y)
    constructor
    apply Set.mem_inter
    have h1 := Set.BijOn.image_eq (Set.BijOn.symm inv.symm bij)
    rw [← h1]
    use y
    apply yinP
    apply Set.RightInvOn.eq inv.right yinT

theorem f_bij_on' {l a: Vector Int (k+1)} (p: Props2 a n) (C: Vector Int (k+1) → Prop):
  Set.BijOn (f b a ls_zero) (X3 a l n C) ((f b a ls_zero) '' (X3 a l n C)) := by
  apply Set.BijOn.subset_left (f_bij_on p) (X3_subset_X2 a l n C)
