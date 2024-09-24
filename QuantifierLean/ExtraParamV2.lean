import Mathlib.Data.Vector.Defs

import QuantifierLean.Definitions
import QuantifierLean.Lemmas

open Mathlib

-- F applied to F_inv gives back the same answer
theorem f_f_inv :
  ∀ a n: Vector Int (k+1), ∀ x': Int,
  x' ∈ Y' n a →
  f a (f_inv a x') = x' := by
  induction k
  case zero =>
    intro a n x' xInY
    simp
    rw [f_inv]
    conv =>
      lhs; arg 2; arg 1
      rw [f_inv_h, f_inv_el, base]
      simp
    match a, n with
    | ⟨head::[], a_length⟩, ⟨headn::[], n_length⟩ =>
      match xInY with
      | ⟨h1, ⟨h2, ⟨h3, ⟨_, ⟨h5, h6⟩⟩⟩⟩⟩ =>
      repeat rw [f]
      simp_all
      conv =>
        lhs
        arg 2
        arg 2
        rw [Vector.head]
        simp
      rw [vector_head_1, vector_last_1] at h5
      rw [vector_head_1, vector_last_1] at h6
      rw [@vector_last_1] at h1
      match Int.lt_or_lt_of_ne h1 with
      | Or.inr hl =>
        cases' h5 hl with left right
        rw [abs_of_nonneg left, abs_of_pos hl]
        apply Int.mul_ediv_cancel'
        exact h2
      | Or.inl hr =>
        cases' h6 hr with left right
        rw [abs_of_neg hr, abs_of_nonpos right]
        simp
        apply Int.neg_eq_comm.mp
        symm
        apply Int.mul_ediv_cancel'
        apply Int.dvd_neg.mpr
        exact h2
  case succ k ih =>
    intro a n x' xInY
    let x := (f_inv a x')
    let a_tail := a.tail
    let n_tail := n.tail
    have aeq: a_tail = a.tail := by rfl
    have neq: n_tail = n.tail := by rfl
    have xInImg : x ∈ (f_inv a '' Y' n a) := by
      rw [Set.image, Set.mem_setOf_eq]
      use x'
    match xInY_prev aeq neq xInY with
    | ⟨inPrev_pos, inPrev_neg⟩ =>
    match xInY with
    | ⟨h1, ⟨_, ⟨h3, ⟨h4, ⟨h5, h6⟩⟩⟩⟩⟩ =>
    have aheadnzero := a_not_zero 0 h4 h3 h1
    rw [Vector.get_zero] at aheadnzero
    match Int.lt_or_lt_of_ne h1 with
    | Or.inr a_pos =>
      have hhead := a_same1 0 h4 h3 a_pos
      have inPrev := inPrev_pos a_pos
      have ih_applied := ih a.tail n.tail (|x'| % a.head) inPrev
      have f_inv_pred' := f_inv_h_pred' a x' aheadnzero
      rw [f_inv]
      conv =>
        lhs; arg 2; arg 1
        rw [f_inv_h]
        simp
      match a with
      | ⟨ah :: a, alength⟩ =>
      rw [f]
      simp
      rw [Vector.tail] at ih_applied
      simp at ih_applied
      rw [← f_inv_pred', Vector.tail, ih_applied]
      rw [f_inv_el, base, Vector.head]
      simp
      rw [Vector.head]
      simp
      rw [Vector.get] at hhead
      simp at hhead

      rw [abs_of_pos hhead, abs_of_nonneg (h5 a_pos).left]
      rw [Int.ediv_add_emod]
    | Or.inl a_neg =>
      have hhead := a_same2 0 h4 h3 a_neg
      have inPrev := inPrev_neg a_neg

      have ih_applied := ih a.tail n.tail (-(-x' % a.head)) inPrev
      have f_inv_pred' := f_inv_h_pred2' a x' aheadnzero
      rw [f_inv]
      conv =>
        lhs; arg 2; arg 1
        rw [f_inv_h]
        simp
      match a with
      | ⟨ah :: a, alength⟩ =>
      rw [f]
      simp
      rw [Vector.tail] at ih_applied
      simp at ih_applied
      rw [← f_inv_pred', Vector.tail, ih_applied]
      rw [f_inv_el, base, Vector.head]
      simp
      rw [Vector.head]
      simp
      rw [Vector.get] at hhead
      simp at hhead

      rw [abs_of_neg hhead, abs_of_nonpos (h6 a_neg).right]
      rw [Int.ediv_neg, ← Int.neg_mul_comm]
      simp
      rw [← Int.neg_add]
      rw [Int.ediv_add_emod]
      simp
      exact (h6 a_neg).right

theorem left_invf_f {nₖ aₖ : Vector Int (k+1)} :
  Set.LeftInvOn (f aₖ) (f_inv aₖ) (Y' nₖ aₖ) := by
  rw [Set.LeftInvOn]
  intro xy xyInSet
  apply f_f_inv aₖ nₖ xy xyInSet

theorem right_invf_f {nₖ aₖ : Vector Int (k+1)} :
  Props nₖ aₖ →
  Set.RightInvOn (f aₖ) (f_inv aₖ) (X nₖ) := by
  rw [Set.RightInvOn]
  intro props x xInSet
  apply f_inv_f aₖ nₖ x props xInSet

lemma f_maps_to {nₖ aₖ : Vector Int (k+1)}:
  (∀ i, 0 < nₖ.get i) →
  Props nₖ aₖ →
  Set.MapsTo (f aₖ) (X nₖ) (Y' nₖ aₖ) := by
  intro n_pos props xy xyInX
  have f_in_bounds := f_in_bounds aₖ nₖ xy props xyInX
  match props with
  | ⟨h1, h2⟩ =>
  exact ⟨h1, f_in_bounds.right.right, n_pos, h2, f_in_bounds.left, f_in_bounds.right.left⟩

lemma f_inv_maps_to {nₖ aₖ : Vector Int (k+1)}:
  Set.MapsTo (f_inv aₖ) (Y' nₖ aₖ) (X nₖ) := by
  revert nₖ aₖ
  induction k
  case zero =>
    intro nₖ aₖ x xinY
    match xinY with
    | ⟨h1, h2, h3, _, h5, h6⟩ =>
    constructor
    case left => exact h3
    case right =>
      intro i
      have ieq0: i = 0 := Fin.fin_one_eq_zero i
      simp_all
      rw [f_inv]
      conv =>
        arg 1; arg 2; arg 1; arg 1;
        rw [f_inv_h, f_inv_el, base];
        simp
      conv =>
        arg 2; arg 1; arg 1; arg 1;
        rw [f_inv_h, f_inv_el, base];
        simp
      rw [Vector.get_head]
      constructor
      case left =>
        apply Int.ediv_nonneg
        exact abs_nonneg x
        exact abs_nonneg aₖ.head
      case right =>
        match xinY with
        | ⟨h7, h8, h9, h10, h11, h12⟩ =>
        rw [← Vector.tail_head] at *
        have a_pos: 0 < |aₖ.head| := abs_pos.mpr h1
        apply (Int.ediv_lt_iff_lt_mul a_pos).mpr
        have h3 := h3 0
        rw [Vector.get_zero] at h3
        match Int.lt_or_lt_of_ne h1 with
        | Or.inl a_neg =>
          rw [abs_of_neg a_neg, abs_of_nonpos (h12 a_neg).right, Int.mul_comm]
          simp
          exact (h12 a_neg).left
        | Or.inr a_pos  =>
          rw [abs_of_pos a_pos, abs_of_nonneg (h11 a_pos).left, Int.mul_comm]
          exact (h11 a_pos).right
  case succ k ih =>
    intro nₖ aₖ x xinY
    match xinY with
    | ⟨h1, _, h3, h4, h5, h6⟩ =>
    match (@ih nₖ.tail aₖ.tail) with
    | ih'  =>
    rw [Set.MapsTo] at ih'
    constructor
    case left => exact h3
    case right =>
      intro i
      have aheadnzero := a_not_zero 0 h4 h3 h1
      rw [Vector.get_zero] at aheadnzero
      have inPrev := xInY_prev (by rfl) (by rfl) xinY
      match i, Int.lt_or_lt_of_ne h1 with
      | 0, Or.inr a_pos =>
        have h5 := h5 a_pos
        rw [f_inv_pred aheadnzero, Mathlib.Vector.get_cons_zero, Vector.get_zero]
        constructor
        case left => exact Int.ediv_nonneg (abs_nonneg x) (abs_nonneg aₖ.head)
        case right =>
          have head_pos := GT.gt.lt (a_same1 0 h4 h3 a_pos)
          simp at head_pos
          have h2: |x| < nₖ.head * |aₖ.head| := by
            rw [abs_of_pos head_pos, abs_of_nonneg h5.left, Int.mul_comm]
            exact h5.right
          exact Int.ediv_lt_of_lt_mul (abs_pos_of_pos head_pos) h2
      | 0, Or.inl a_neg =>
        have h6 := h6 a_neg
        rw [f_inv_pred2 aheadnzero h6.right, Mathlib.Vector.get_cons_zero, Vector.get_zero]
        constructor
        case left =>
          exact Int.ediv_nonneg (abs_nonneg x) (abs_nonneg aₖ.head)
        case right =>
          have head_neg := GT.gt.lt (a_same2 0 h4 h3 a_neg)
          simp at head_neg
          have h2: |x| < nₖ.head * |aₖ.head| := by
            rw [abs_of_neg head_neg, abs_of_nonpos h6.right, Int.mul_comm]
            simp
            exact h6.left
          exact Int.ediv_lt_of_lt_mul (abs_pos_of_neg head_neg) h2
      | ⟨i+1, isLt⟩, Or.inr a_pos =>
        let j: Fin (k+1+1) := Fin.succ ⟨i, Nat.add_one_lt_add_one_iff.mp isLt⟩
        let i': Fin (k+1) := ⟨i, by simp at isLt; exact isLt⟩
        have jeq : ⟨i+1, isLt⟩ = j := by rfl
        rw [jeq]
        rw [f_inv_pred aheadnzero, Vector.get_cons_succ]
        have ih' := (ih (inPrev.left a_pos)).right i'
        rw [Vector.get_tail, jeq] at ih'
        exact ih'
      | ⟨i+1, isLt⟩, Or.inl a_neg =>
        have h6 := h6 a_neg
        let j: Fin (k+1+1) := Fin.succ ⟨i, Nat.add_one_lt_add_one_iff.mp isLt⟩
        let i': Fin (k+1) := ⟨i, by simp at isLt; exact isLt⟩
        have jeq : ⟨i+1, isLt⟩ = j := by rfl
        rw [jeq]
        rw [f_inv_pred2 aheadnzero h6.right, Vector.get_cons_succ]
        have ih' := (ih (inPrev.right a_neg)).right i'
        rw [Vector.get_tail, jeq] at ih'
        exact ih'

theorem f_is_bijection {nₖ aₖ : Vector Int (k+1)}:
  (aₖ.last ≠ 0) →
  (∀ i, 0 < nₖ.get i) →
  (∀ i, i<k → aₖ.get i = aₖ.get (i+1) * nₖ.get (i+1)) →
  Set.BijOn (f aₖ) (X nₖ) (Y' nₖ aₖ) := by
  intro h1
  intro h2
  intro h3
  have left: Set.LeftInvOn (f aₖ) (f_inv aₖ) (Y' nₖ aₖ) := left_invf_f
  have right: Set.RightInvOn (f aₖ) (f_inv aₖ) (X nₖ) := right_invf_f (⟨h1, h3⟩)
  have h4 : Set.InvOn (f aₖ) (f_inv aₖ) (Y' nₖ aₖ) (X nₖ) := by
    exact ⟨left, right⟩
  have h4 : Set.InvOn (f_inv aₖ) (f aₖ) (X nₖ)  (Y' nₖ aₖ) := by
    exact Set.InvOn.symm h4
  have hf : Set.MapsTo (f aₖ) (X nₖ) (Y' nₖ aₖ) :=
    f_maps_to h2 (⟨h1, h3⟩)
  have hf' : Set.MapsTo (f_inv aₖ) (Y' nₖ aₖ) (X nₖ) :=
    f_inv_maps_to
  exact Set.InvOn.bijOn h4 hf hf'
