import Mathlib.Tactic
import Mathlib.Data.Vector.Defs
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Vector.Zip
import Mathlib.Order.Defs

import Init.Data.Int.DivModLemmas
import Init.Data.List
import Init.Data.List.Lemmas

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
    let x_tail := x.tail
    have xeq: x_tail = x.tail := by rfl
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
      have h3' : ∀ (i : Fin (k + 1)), 0 < n_tail.get i := by
        rw [neq]
        apply smaller_n h3
      have h4' := tail_an aeq neq h4
      have hlast: 0 < a_tail.last := by
        rw [aeq]
        rw [Vector.tail_last]
        exact a_pos
      have hhead := a_same1 0 h4 h3 a_pos -- hlast
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
      have h3' : ∀ (i : Fin (k + 1)), 0 < n_tail.get i := by
        rw [neq]
        apply smaller_n h3
      have h4' := tail_an aeq neq h4
      have hlast: a_tail.last < 0 := by
        rw [aeq]
        rw [Vector.tail_last]
        exact a_neg
      have hhead := a_same2 0 h4 h3 a_neg -- hlast
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
  (0 ≠ aₖ.last) →
  (∀ i, 0 < nₖ.get i) →
  (∀ i, i<k → aₖ.get i = aₖ.get (i+1) * nₖ.get (i+1)) →
  Set.LeftInvOn (f aₖ) (f_inv aₖ) (Y' nₖ aₖ) := by
  rw [Set.LeftInvOn]
  intro h1 h2 h3 xy xyInSet
  apply Set.mem_setOf.mp at xyInSet
  cases' xyInSet with h4 h5
  match h5 with
  | ⟨h5, ⟨_, ⟨_, h6⟩⟩⟩ =>
  apply f_f_inv aₖ nₖ xy h1 h5 h2 h3 h6

theorem right_invf_f {nₖ aₖ : Vector Int (k+1)} :
  (0 ≠ aₖ.last) →
  (∀ i, 0 < nₖ.get i) →
  (∀ i, i<k → aₖ.get i = aₖ.get (i+1) * nₖ.get (i+1)) →
  Set.RightInvOn (f aₖ) (f_inv aₖ) (f_inv aₖ '' Y' nₖ aₖ) := by
  intro h1 h2 h3
  exact Set.LeftInvOn.rightInvOn_image (left_invf_f h1 h2 h3)


lemma image {nₖ aₖ : Vector Int (k+1)}:
  (∀ i, 0 < nₖ.get i) →
  (∀ i, i<k → aₖ.get i = aₖ.get (i+1) * nₖ.get (i+1)) →
  (f_inv aₖ '' Y' nₖ aₖ) = X nₖ := by
  intro h2 h3
  apply Set.Subset.antisymm
  case h₁ =>
    rw [Set.subset_def]
    induction k
    intro x xInY
    cases' xInY with x' h4
    cases' h4 with x'inY fx'x
    rw [Y', Set.mem_setOf_eq] at x'inY
    rw [X, Set.mem_setOf_eq]
    case zero =>
      match x'inY with
      | ⟨h5, ⟨h6, ⟨h7, ⟨h8, ⟨h9, h10⟩⟩⟩⟩⟩ =>
      simp_all
      intro i
      have h11: i = 0 := Fin.fin_one_eq_zero i
      simp [h11]
      have h12: x.head = |x'| / |aₖ.head| := by
        conv =>
          lhs
          arg 1
          rw [← fx'x]
          rw [f_inv]
          arg 1
          rw [f_inv_h]
          rw [f_inv_el]
          simp
          rw [base]
          simp
        rfl
      have h13: aₖ.head = aₖ.last := by
        rw [← Vector.get_zero, Vector.last]
        rfl
      apply Int.lt_or_lt_of_ne at h5
      cases h5
      rw [h12]
      case inl h1 =>
        have h15: aₖ.last < 0 := h1
        apply h10 at h15
        cases' h15 with h16 h17
        rw [h13] at *
        constructor
        · exact Int.ediv_nonneg (abs_nonneg x') (abs_nonneg aₖ.last)
        · have h2: |x'| < nₖ.head * |aₖ.last| := by
            rw [abs_of_neg h1, abs_of_nonpos h17, Int.mul_comm]
            simp
            exact h16
          exact Int.ediv_lt_of_lt_mul (abs_pos_of_neg h1) h2
      case inr h1 =>
        have h15: 0 < aₖ.last := h1
        apply h9 at h15
        cases' h15 with h16 h17
        rw [h12]
        rw [h13] at *
        constructor
        · exact Int.ediv_nonneg (abs_nonneg x') (abs_nonneg aₖ.last)
        · have h2: |x'| < nₖ.head * |aₖ.last| := by
            rw [abs_of_pos h1, abs_of_nonneg h16, Int.mul_comm]
            exact h17
          exact Int.ediv_lt_of_lt_mul (abs_pos_of_pos h1) h2
    case succ k ih =>
      intro x xInY
      cases' xInY with x' h4
      cases' h4 with x'inY fx'x
      rw [Y', Set.mem_setOf_eq] at x'inY
      rw [X, Set.mem_setOf_eq]
      match x'inY with
      | ⟨h5, ⟨h6, ⟨h7, ⟨h8, ⟨h9, h10⟩⟩⟩⟩⟩ =>
      let nk_tail := nₖ.tail
      let ak_tail := aₖ.tail
      have l1: nk_tail = nₖ.tail := by simp
      have l2: ak_tail = aₖ.tail := by simp
      have h7': (∀ i, 0 < nk_tail.get i) := by
        intro j
        have l1: nk_tail = nₖ.tail := by simp
        rw [l1, Mathlib.Vector.get_tail]
        apply h7
      match an_eq l2 l1 h3 with
      | h3' =>
      have aheadnzero: aₖ.head ≠ 0 := by sorry
      match @ih nk_tail ak_tail (smaller_n h7) h3', f_inv_pred aₖ x' aheadnzero with
      | ih', h4 =>
      intro i
      match i with
      | ⟨0, _⟩ =>
        simp_all
        rw [← fx'x]
        apply Int.lt_or_lt_of_ne at h5
        simp
        cases h5
        case inl hl =>
          match h10 hl with
          | ⟨hl1, hl2⟩ =>
          constructor
          case left =>
            exact Int.ediv_nonneg (abs_nonneg x') (abs_nonneg aₖ.head)
          case right =>
            have head_neg := GT.gt.lt (a_same2 0 h3 h7 hl)
            simp at head_neg
            have h2: |x'| < nₖ.head * |aₖ.head| := by
              rw [abs_of_neg head_neg, abs_of_nonpos hl2, Int.mul_comm]
              simp
              exact hl1
            exact Int.ediv_lt_of_lt_mul (abs_pos_of_neg head_neg) h2
        case inr hr =>
          match h9 hr with
          | ⟨hr1, hr2⟩ =>
          constructor
          · exact Int.ediv_nonneg (abs_nonneg x') (abs_nonneg aₖ.head)
          · have head_pos := GT.gt.lt (a_same1 0 h3 h7 hr)
            simp at head_pos
            have h2: |x'| < nₖ.head * |aₖ.head| := by
              rw [abs_of_pos head_pos, abs_of_nonneg hr1, Int.mul_comm]
              exact hr2
            exact Int.ediv_lt_of_lt_mul (abs_pos_of_pos head_pos) h2
      | ⟨i+1,isLt⟩ =>
        let xtail := x.tail
        let ntail := nₖ.tail
        have alast_pos: aₖ.last > 0 := by sorry
        have xtail: x.tail = f_inv aₖ.tail (|x'| % aₖ.head) := by
          rw [← fx'x, h4, Mathlib.Vector.tail_cons]
        have xin: x.tail ∈ (f_inv ak_tail '' Y' nk_tail ak_tail) := by
          rw [Set.image]
          apply Set.mem_setOf.mpr
          use |x'| % aₖ.head
          constructor
          case left =>
            rw [Y', Set.mem_setOf_eq]
            constructor
            case left =>
              rw[Vector.tail_last]
              exact h5
            case right =>

            -- · exact a_not_zero i h3 h7 (Ne.symm aheadnzero)
            -- · exact Int.mod_eq_of_lt (abs_nonneg x') (abs_pos_of_pos alast_pos)
            -- · exact h7'
            -- · exact h3'
            -- · cases' h10 alast_pos with h10_1 h10_2
            -- · exact h10_1
            -- · exact h10_2


          -- |x'| % aₖ.head
          -- rw [← fx'x]

          apply (Set.mem_image (f_inv ak_tail) (Y' nk_tail ak_tail) xtail).mpr





          rw [Set.mem_setOf_eq]

          -- constructor
        have xinX := ih' xtail xin
        have xtailGet: x.get ⟨i + 1, isLt⟩ = xtail.get ⟨i, by sorry⟩ := by
          sorry
        have ntailGet: nₖ.get ⟨i + 1, isLt⟩ = ntail.get ⟨i, by sorry⟩ := by
          sorry
        rw [X] at xinX
        rw [Set.mem_setOf_eq] at xinX
        have inX := xinX ⟨i, by sorry⟩
        rw [← xtailGet, ← ntailGet] at inX
        exact inX
  case h₂ =>
    rw [Set.subset_def]

    intro xy xyInX
    simp
    use f aₖ xy
    constructor
    case left =>
      rw [Y', Set.mem_setOf_eq]

      sorry
    case right =>
      -- apply f_f_inv aₖ nₖ xy h1
      sorry

lemma maps_to {nₖ aₖ : Vector Int (k+1)}:
  (0 ≠ aₖ.last) →
  (∀ i, 0 < nₖ.get i) →
  (∀ i, i<k → aₖ.get i = aₖ.get (i+1) * nₖ.get (i+1)) →
  Set.MapsTo (f aₖ) (f_inv aₖ '' Y' nₖ aₖ) (Y' nₖ aₖ) := by
  intro h1 h2 h3
  apply Set.LeftInvOn.mapsTo (left_invf_f h1 h2 h3)
  apply Set.surjOn_image

theorem f_is_bijection {nₖ aₖ : Vector Int (k+1)}:
  (0 ≠ aₖ.last) →
  (∀ i, 0 < nₖ.get i) →
  (∀ i, i<k → aₖ.get i = aₖ.get (i+1) * nₖ.get (i+1)) →
  Set.BijOn (f aₖ) (f_inv aₖ '' Y' nₖ aₖ) (Y' nₖ aₖ) := by
  intro h1
  intro h2
  intro h3
  have left: Set.LeftInvOn (f aₖ) (f_inv aₖ) (Y' nₖ aₖ) := left_invf_f h1 h2 h3
  have right: Set.RightInvOn (f aₖ) (f_inv aₖ) (f_inv aₖ '' Y' nₖ aₖ) := right_invf_f h1 h2 h3
  have h4 : Set.InvOn (f aₖ) (f_inv aₖ) (Y' nₖ aₖ) (f_inv aₖ '' Y' nₖ aₖ) := by
    exact ⟨left, right⟩
  have h4 : Set.InvOn (f_inv aₖ) (f aₖ) (f_inv aₖ '' Y' nₖ aₖ)  (Y' nₖ aₖ) := by
    exact Set.InvOn.symm h4
  have hf : Set.MapsTo (f aₖ) (f_inv aₖ '' Y' nₖ aₖ) (Y' nₖ aₖ) :=
    maps_to h1 h2 h3
  have hf' : Set.MapsTo (f_inv aₖ) (Y' nₖ aₖ) (f_inv aₖ '' Y' nₖ aₖ) :=
    Set.mapsTo_image  (f_inv aₖ) (Y' nₖ aₖ)
  exact Set.InvOn.bijOn h4 hf hf'
