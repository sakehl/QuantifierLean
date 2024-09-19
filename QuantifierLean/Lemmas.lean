
import Mathlib.Tactic
import QuantifierLean.Definitions

open Mathlib

lemma base_l2 (h : i < k + 1): i < k + 1 + 1 := by
  have kk1: (k + 1 < k+1+1) := by simp;
  exact Nat.lt_trans h kk1

lemma base_l3 (h: i + 1 < k + 1): i < k+1 := by
  have h2: i < i+1 := by simp
  exact Nat.lt_trans h2 h


lemma pred_l5 (h: i < k) : ¬k - i = 0 := by
  have h1: i ≠ k := by exact Nat.ne_of_lt h
  contrapose h1
  simp_all
  rw [<- Nat.add_sub_self_left i k]
  rw [Nat.add_sub_assoc]
  rw [h1]
  simp
  apply le_of_lt
  assumption

lemma pred_l1 (h: i < k+1) : i < k + 1 + 1 := by
  have kk1: (k+1 < k+1+1) := by simp;
  exact Nat.lt_trans h kk1

lemma pred_l2: k - i - 1 = k - (i + 1) := by
  rw [Nat.sub_add_eq]

lemma pred_l3 (h: i < k) : k - (i + 1) + 1 = k - i := by
  rw [Nat.sub_add_eq, Nat.sub_one_add_one]
  simp
  exact pred_l5 h

lemma pred_l4 : k - i - 1 < k + 1 := by
  have h1: k - i - 1 ≤ k - i := by simp
  have h2: k - i ≤ k := by simp
  have h3: k - i - 1 ≤ k := Nat.le_trans h1 h2
  have h4: k<k+1 := by simp
  exact lt_of_le_of_lt h3 h4

lemma l2: k < k + 1 + 1 := Nat.lt_trans (Nat.lt_add_one k) (Nat.lt_add_one (k+1))

lemma stupidCoercions {k j: Nat} (h: j < k): ↑(j + 1) = (↑j: Fin (k+1)).succ := by
  simp
  apply Fin.mk_eq_mk.mpr
  simp
  rw [Nat.mod_eq_of_lt]
  simp
  rw [Nat.mod_eq_of_lt]
  apply lt_trans h
  simp
  simp
  apply lt_trans h
  simp

lemma ff_l3 {j k: Nat} (h: j<k) : ((↑j: Fin (k+1)).succ: Fin (k + 1).succ) = ↑(j+ 1) := by
  have jkk: j < k + 1 := by
    exact Nat.lt_trans h (Nat.lt_add_one k)
  simp
  apply Fin.mk_eq_mk.mpr
  simp
  rw [Nat.mod_eq_of_lt]
  rw [Nat.mod_eq_of_lt]
  simp
  repeat assumption

lemma ff_l4 (h: j<k) : j+1 < k+1 := by
  exact Nat.add_lt_add_right h 1

lemma ff_l5 {j k: Nat} (h: j<k) : (↑(j + 1) + 1: Fin (k + 1 + 1)) = ((↑j: Fin (k+1)) + 1).succ := by
  simp
  apply Fin.mk_eq_mk.mpr
  simp
  repeat rw [Nat.mod_eq_of_lt]
  exact Nat.add_lt_add_right h 1

  apply @ff_l4 (j+1) (k+1)
  exact Nat.add_lt_add_right h 1



theorem eq_or_not (a b: Int) : a=b ∨ a≠b := by
  have h := Int.lt_or_le a b
  cases h
  case inl h =>
    contrapose h
    simp_all
  case inr h =>
    contrapose h
    simp_all

-- lemma base_pos (as: Mathlib.Vector Int k) (x: Int): 0 ≤ base as x i  := by
--   cases' i with v lt
--   revert x
--   induction v
--   case zero =>
--     intro x
--     rw [base]
--     simp
--   case succ v =>
--     intro x
--     rw [base]
--     simp


--     match eq_or_not (as.get ⟨v, by
--       have h1: v <= v+1 := by simp
--       exact lt_of_le_of_lt h1 lt⟩) 0 with
--     | Or.inl h =>
--       rw [h]
--       simp
--     | Or.inr h =>
--       apply Int.emod_nonneg
--       exact h


lemma base_lemma (as: Mathlib.Vector Int (k+1+1)) (x': Int) (h: i < k+1) (h2: as.head ≠ 0):
  base as x' ⟨i, base_l2 h⟩ % as.get ⟨i, base_l2 h⟩ =
  base as.tail (|x'| % as.head) ⟨i, by simp; exact h⟩ := by
    revert x'
    induction i
    case zero =>
      intro x'
      rw [base, base]
      simp
      have h' := Int.emod_nonneg (|x'|) h2
      rw [abs_of_nonneg h']
    case succ i ih =>
      intro x'
      have h': i < k + 1 := base_l3 h
      rw [base, base]
      simp
      rw [ih h']

lemma base_lemma2 (as: Mathlib.Vector Int (k+1+1)) (x': Int) (h: i < k+1) (h2: as.head ≠ 0) (h3: x' ≤ 0):
  base as x' ⟨i, base_l2 h⟩ % as.get ⟨i, base_l2 h⟩ =
  base as.tail (-((- x') % as.head)) ⟨i, by simp; exact h⟩ := by
    revert x'
    induction i
    case zero =>
      intro x' x3
      rw [base, base]
      simp
      have h' := Int.emod_nonneg (- x') h2
      rw [abs_of_nonpos x3]
      rw [abs_of_nonneg h']
    case succ i ih =>
      intro x' x3
      have h': i < k + 1 := base_l3 h
      rw [base, base]
      simp
      rw [ih h']
      exact x3



lemma f_inv_h_pred (k i: Nat) (as: Mathlib.Vector Int (k+1+1)) (x': Int) (h: i < k+1) (h2: as.head ≠ 0):
  f_inv_h as x' ⟨i, pred_l1 h⟩ = f_inv_h as.tail (|x'| % as.head) ⟨i, h⟩ := by
    revert x' as
    induction i
    case zero =>
      intro as x' h2
      rw [f_inv_h, f_inv_h, f_inv_el, f_inv_el]
      simp
      rw [base]
      simp
      rw [base_lemma as x' (Nat.lt_add_one k) h2]
    case succ i ih =>
      intro as x' h2
      rw [f_inv_h, f_inv_h, f_inv_el, f_inv_el]
      simp
      constructor
      case left =>
        rw [base]
        simp_all
        simp at h
        have h5: ¬k - i = 0 := pred_l5 h
        simp_all
        rw [base_lemma as x' pred_l4 h2]
        simp
        conv =>
          lhs
          arg 1
          arg 3
          arg 1
          rw [pred_l2]
        conv =>
          rhs
          arg 2
          arg 1
          arg 2
          arg 1
          rw [pred_l3 h]

      case right =>
        have h': i < k+1 := Nat.lt_trans (Nat.lt_add_one i) h
        rw [ih h' as x' h2]

lemma f_inv_h_pred2 (k i: Nat) (as: Mathlib.Vector Int (k+1+1)) (x': Int) (h: i < k+1) (h2: as.head ≠ 0) (h3: x' ≤ 0):
  f_inv_h as x' ⟨i, pred_l1 h⟩ = f_inv_h as.tail (-((- x') % as.head)) ⟨i, h⟩ := by
    revert x' as
    induction i
    case zero =>
      intro as x' h2 h3
      rw [f_inv_h, f_inv_h, f_inv_el, f_inv_el]
      simp
      rw [base]
      simp
      rw [base_lemma2 as x' (Nat.lt_add_one k) h2 h3]

    case succ i ih =>
      intro as x' h2 h3
      rw [f_inv_h, f_inv_h, f_inv_el, f_inv_el]
      simp
      constructor
      case left =>
        rw [base]
        simp_all
        simp at h
        have h5: ¬k - i = 0 := pred_l5 h
        simp_all
        rw [base_lemma2 as x' pred_l4 h2 h3]
        simp
        conv =>
          lhs
          arg 1
          arg 3
          arg 1
          rw [pred_l2]
        conv =>
          rhs
          arg 2
          arg 1
          arg 2
          arg 1
          rw [pred_l3 h]

      case right =>
        have h': i < k+1 := Nat.lt_trans (Nat.lt_add_one i) h
        rw [ih h' as x' h2 h3]

lemma f_inv_h_pred' (as: Mathlib.Vector Int (k+1+1)) (x': Int) (h2: as.head ≠ 0):
  f_inv as.tail (|x'| % as.head) =
   ⟨(f_inv_h as x' ⟨k, l2⟩), f_inv_length⟩ := by
    rw [f_inv]
    -- simp_all
    conv =>
      rhs
      arg 1
      rw [f_inv_h_pred k k as x' (by simp) h2]

lemma f_inv_h_pred2' (as: Mathlib.Vector Int (k+1+1)) (x': Int) (h2: as.head ≠ 0) (h3: x' ≤ 0):
  f_inv as.tail (-((- x') % as.head)) =
   ⟨(f_inv_h as x' ⟨k, l2⟩), f_inv_length⟩ := by
    rw [f_inv]
    -- simp_all
    conv =>
      rhs
      arg 1
      rw [f_inv_h_pred2 k k as x' (by simp) h2 h3]


lemma f_inv_pred (as: Mathlib.Vector Int (k+1+1)) (x': Int) (h2: as.head ≠ 0):
  (f_inv as x') = |x'| / |as.head| ::ᵥ f_inv as.tail (|x'| % as.head) := by
  rw [f_inv_h_pred' as x' h2]
  rw [f_inv]
  conv =>
    lhs
    arg 1
    rw [f_inv_h, f_inv_el, base]
    simp
  rw [Mathlib.Vector.cons]

lemma f_inv_pred2 (as: Mathlib.Vector Int (k+1+1)) (x': Int) (h2: as.head ≠ 0) (h3: x' ≤ 0):
  (f_inv as x') = |x'| / |as.head| ::ᵥ f_inv as.tail (-((- x') % as.head)) := by
  rw [f_inv_h_pred2' as x' h2 h3]
  rw [f_inv]
  conv =>
    lhs
    arg 1
    rw [f_inv_h, f_inv_el, base]
    simp
  rw [Mathlib.Vector.cons]


lemma Vector.tail_last {α: Type} {n: Nat} (v: Vector α (n+1+1)): v.tail.last = v.last := by
  repeat rw [Vector.last]
  rw [Mathlib.Vector.get_tail]
  rfl

lemma head_is_div {a: Vector Int (k+1)} {n: Vector Int (k+1)}:
  (∀ i: Nat, i<k → a.get i = a.get (i+1) * n.get (i+1)) →
  ∃ q, a.head = q * a.last := by
    intro h
    induction k
    case zero =>
      simp_all
      use 1
      simp [Vector.head, Vector.last, Vector.get]
      cases' a with a al
      cases a
      case nil =>
        rw [List.length] at al
        simp_all
      case cons head tail =>
        rw [List.length] at al
        simp_all
    case succ k ih =>
      have tail: ∃ q, a.tail.head = q * a.tail.last := by
        apply @ih a.tail n.tail
        intro j jk
        repeat rw [Mathlib.Vector.get_tail_succ]
        simp
        have h0: a.get ↑(j+1) = a.get (↑(j+1) + 1) * n.get (↑(j+1) + 1) := by
          rw [h (j+1)]
          simp
          simp_all
        have h1: ↑(j + 1) = (↑j: Fin (k+1)).succ := by
          exact stupidCoercions jk
        have h2: (↑(j + 1) + 1) = ((↑j : Fin (k+1)) + 1).succ := by
          simp
          apply Fin.mk_eq_mk.mpr
          simp
          rw [Nat.mod_eq_of_lt]
          simp
          rw [Nat.mod_eq_of_lt]
          simp
          assumption
          simp
          assumption
        rw [<- h1]
        rw [h0]
        rw [h2]
      have h0: a.get ↑(0:Nat) = a.get (↑0 + 1) * n.get (↑0 + 1) := by
        rw [h 0]
        simp
        simp_all
      simp at h0
      rw [h0]
      cases' tail with q tail
      use n.get 1*q
      rw [← Vector.tail_last a, mul_assoc, ← tail, mul_comm, ← Vector.get_zero, Vector.get_tail_succ]
      simp

lemma last_zero {a: Vector Int (k+1+1)} (h: 0 ≠ a.last) : 0 ≠ a.tail.last := by
  rw [Vector.last, Vector.get_tail]
  exact h

lemma last_div_x {a n: Vector Int (k+1+1)}
  (h1: a.last ∣ x')
  (h2: ∀ i, i<k+1 → a.get i = a.get (i+1) * n.get (i+1))
  : a.last ∣ |x'| % a.head := by
  match head_is_div h2 with
  | ⟨q, l1⟩ =>
  apply Int.dvd_of_emod_eq_zero
  rw [l1, Int.mod_mul_left_mod]
  apply Int.emod_eq_zero_of_dvd
  match abs_choice x' with
  | Or.inl h =>
    rw [h]
    exact h1
  | Or.inr h =>
    rw [h]
    exact Dvd.dvd.neg_right h1

lemma last_div_x' {a n: Vector Int (k+1+1)}
  (h1: a.last ∣ x')
  (h2: ∀ i, i<k+1 → a.get i = a.get (i+1) * n.get (i+1))
  : a.last ∣ -(-x' % a.head) := by
  match head_is_div h2 with
  | ⟨q, l1⟩ =>
  rw [Int.dvd_def] at h1
  match h1 with
  | ⟨k, l2⟩ =>
  rw [l1, l2]
  simp
  apply Int.dvd_of_emod_eq_zero
  rw [Int.mod_mul_left_mod, ← Int.neg_mul, Int.neg_mul_comm]
  simp

lemma smaller_n {a: Vector Int (k+1+1)} (h: ∀ i, 0 < a.get i):
  (∀ i, 0 < a.tail.get i) := by
  intro j
  rw [Mathlib.Vector.get_tail]
  apply h

lemma an_eq {a n: Vector Int (k+1+1)} {atail ntail: Vector Int (k+1)}
  (h1: atail = a.tail) (h2: ntail = n.tail)
  (h: ∀ i, i<k+1 → a.get i = a.get (i+1) * n.get (i+1)):
  (∀ i, i<k → atail.get i = atail.get (i+1) * ntail.get (i+1)) := by
  intro j jk
  rw [h1, h2]
  rw [Mathlib.Vector.get_tail_succ]
  rw [Mathlib.Vector.get_tail_succ, Mathlib.Vector.get_tail_succ]
  have l3: ((↑j: Fin (k+1)).succ: Fin (k + 1).succ) = ↑(j+1) := ff_l3 jk
  have l5: (↑(j + 1) + 1: Fin (k + 1 + 1)) = ((↑j: Fin (k+1)) + 1).succ := ff_l5 jk
  rw [l3, h, l5]
  exact Nat.add_lt_add_right jk 1

lemma Vector.tail_head {a: Vector Int 1}: a.head = a.last := by
  rw [Mathlib.Vector.last, ← Mathlib.Vector.get_zero]
  rfl

lemma a_same1 {a: Vector Int (k+1)} {n: Vector Int (k+1)}
  (j: Fin (k+1))
  (h1: ∀ i: Nat, i<k → a.get i = a.get (i+1) * n.get (i+1))
  (h2: ∀ i, 0 < n.get i)
  (h3: 0< a.last):
  0 < a.get j := by
  revert j
  induction k
  case zero =>
    intro j
    rw [Vector.last] at h3
    rw [Fin.fin_one_eq_zero j]
    exact h3
  case succ k ih =>
    intro j
    have h4: a.tail.last > 0 := by
      rw [Vector.last, Vector.get_tail]
      exact h3
    match an_eq (rfl) (rfl) h1, smaller_n h2 with
    | h1', h2' =>
    cases k
    case zero =>
      match j with
      | ⟨0, h⟩ =>
        simp_all
        rw [Vector.last] at h3
        exact h3
      | ⟨1, h⟩ =>
        simp_all
        rw [Vector.last] at h3
        exact h3
    case succ k =>
      match ih h1' h2' (h4), h1 j, h2 (j+1) with
      | ih', h1'', h2'' =>
      match j with
      | ⟨0, jk0⟩  =>
        have jkk: 0 < k + 1 + 1 := by
          simp
        apply h1'' at jkk
        simp at jkk
        simp
        rw [jkk]
        have ih'':= ih' 0
        rw [Mathlib.Vector.get_tail] at ih''
        simp at ih''
        exact Int.mul_pos ih'' h2''
      | ⟨j+1, jk0⟩ =>
        let idx: Fin (k+1+1) := ⟨j, Nat.add_one_lt_add_one_iff.mp jk0⟩
        have ih'':= ih' idx
        have eqa : a.tail.get idx = a.get ⟨j+1, jk0⟩ := by
          rw [Mathlib.Vector.get_tail]
        rw [eqa] at ih''
        exact ih''

lemma a_not_zero {a: Vector Int (k+1)} {n: Vector Int (k+1)}
  (j: Fin (k+1))
  (h1: ∀ i: Nat, i<k → a.get i = a.get (i+1) * n.get (i+1))
  (h2: ∀ i, 0 < n.get i)
  (h3: a.last ≠ 0):
  a.get j ≠ 0 := by
  revert j
  induction k
  case zero =>
    intro j
    rw [Vector.last] at h3
    rw [Fin.fin_one_eq_zero j]
    exact h3
  case succ k ih =>
    intro j
    have h4: a.tail.last ≠ 0 := by
      rw [Vector.tail_last]
      exact h3
    match an_eq (rfl) (rfl) h1, smaller_n h2 with
    | h1', h2' =>
    cases k
    case zero =>
      match j with
      | ⟨0, h⟩ =>
        rw [Vector.last] at h3
        simp_all
        constructor
        case left => exact h3
        case right => exact Ne.symm (ne_of_lt (h2 1))
      | ⟨1, h⟩ =>
        simp_all
        rw [Vector.last] at h3
        exact h3
    case succ k =>
      match ih h1' h2' (h4), h1 j, h2 (j+1) with
      | ih', h1'', h2'' =>
      match j with
      | ⟨0, jk0⟩  =>
        have jkk: 0 < k + 1 + 1 := by
          simp
        apply h1'' at jkk
        simp at jkk
        simp
        rw [jkk]
        have ih'':= ih' 0
        rw [Mathlib.Vector.get_tail] at ih''
        simp at ih''
        exact Int.mul_ne_zero  ih'' (Ne.symm (ne_of_lt h2''))
      | ⟨j+1, jk0⟩ =>
        let idx: Fin (k+1+1) := ⟨j, Nat.add_one_lt_add_one_iff.mp jk0⟩
        have ih'':= ih' idx
        have eqa : a.tail.get idx = a.get ⟨j+1, jk0⟩ := by
          rw [Mathlib.Vector.get_tail]
        rw [eqa] at ih''
        exact ih''

lemma a_same2 {a: Vector Int (k+1)} {n: Vector Int (k+1)}
  (j: Fin (k+1))
  (h1: ∀ i: Nat, i<k → a.get i = a.get (i+1) * n.get (i+1))
  (h2: ∀ i, 0 < n.get i)
  (h3: 0 > a.last):
  0 > a.get j := by
  revert j
  induction k
  case zero =>
    intro j
    rw [Vector.last] at h3
    rw [Fin.fin_one_eq_zero j]
    exact h3
  case succ k ih =>
    intro j
    have h4: a.tail.last < 0 := by
      rw [Vector.last, Vector.get_tail]
      exact h3
    match an_eq (rfl) (rfl) h1, smaller_n h2 with
    | h1', h2' =>
    cases k
    case zero =>
      match j with
      | ⟨0, h⟩ =>
        simp_all
        rw [Vector.last, Fin.last] at h3
        simp at h3
        apply Int.mul_neg_of_neg_of_pos h3 (h2 1)
      | ⟨1, h⟩ =>
        simp_all
        rw [Vector.last] at h3
        exact h3
    case succ k =>
      match ih h1' h2' (h4), h1 j, h2 (j+1) with
      | ih', h1'', h2'' =>
      match j with
      | ⟨0, jk0⟩  =>
        have jkk: 0 < k + 1 + 1 := by
          simp
        apply h1'' at jkk
        simp at jkk
        simp
        rw [jkk]
        have ih'':= ih' 0
        rw [Mathlib.Vector.get_tail] at ih''
        simp at ih''
        exact Int.mul_neg_of_neg_of_pos ih'' h2''
      | ⟨j+1, jk0⟩ =>
        let idx: Fin (k+1+1) := ⟨j, Nat.add_one_lt_add_one_iff.mp jk0⟩
        have ih'':= ih' idx
        have eqa : a.tail.get idx = a.get ⟨j+1, jk0⟩ := by
          rw [Mathlib.Vector.get_tail]
        rw [eqa] at ih''
        exact ih''

lemma vector_head_1 {head: Int}:
  Vector.head ⟨head :: xs, by rw[List.length]⟩ = head := by
    rw [Vector.head]

lemma vector_last_1 {head: Int}:
  Vector.last ⟨[head], by rw[List.length]⟩ = head := by
    rw [Vector.last, Vector.get]
    simp

theorem ediv_nonneg' {a b : Int} (Ha : a ≤ 0) (Hb : b ≤ 0) : 0 ≤ a / b := by
  match a, b with
  | Int.ofNat a, b =>
    match Int.le_antisymm Ha (Int.ofNat_zero_le a) with
    | h1 =>
      rw [h1, Int.zero_ediv]
  | a, Int.ofNat b =>
    match Int.le_antisymm Hb (Int.ofNat_zero_le  b) with
    | h1 =>
      rw [h1, Int.ediv_zero]
  | Int.negSucc a, Int.negSucc b =>
    exact Int.le_add_one (Int.ediv_nonneg (Int.ofNat_zero_le a) (Int.le_trans (Int.ofNat_zero_le b) (Int.le.intro 1 rfl)))
