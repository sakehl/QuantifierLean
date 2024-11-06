
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
  base as.tail (-(- x' % as.head)) ⟨i, by simp; exact h⟩ := by
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
  f_inv_h as x' ⟨i, pred_l1 h⟩ = f_inv_h as.tail (-(- x' % as.head)) ⟨i, h⟩ := by
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
    conv =>
      rhs
      arg 1
      rw [f_inv_h_pred k k as x' (by simp) h2]

lemma f_inv_h_pred2' (as: Mathlib.Vector Int (k+1+1)) (x': Int) (h2: as.head ≠ 0) (h3: x' ≤ 0):
  f_inv as.tail (-(- x' % as.head)) =
   ⟨(f_inv_h as x' ⟨k, l2⟩), f_inv_length⟩ := by
    rw [f_inv]
    conv =>
      rhs
      arg 1
      rw [f_inv_h_pred2 k k as x' (by simp) h2 h3]


lemma f_inv_pred {as: Mathlib.Vector Int (k+1+1)} {x': Int} (h2: as.head ≠ 0):
  (f_inv as x') = |x'| / |as.head| ::ᵥ f_inv as.tail (|x'| % as.head) := by
  rw [f_inv_h_pred' as x' h2]
  rw [f_inv]
  conv =>
    lhs
    arg 1
    rw [f_inv_h, f_inv_el, base]
    simp
  rw [Mathlib.Vector.cons]

lemma f_inv_pred2 {as: Mathlib.Vector Int (k+1+1)} {x': Int} (h2: as.head ≠ 0) (h3: x' ≤ 0):
  (f_inv as x') = |x'| / |as.head| ::ᵥ f_inv as.tail (-(- x' % as.head)) := by
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

lemma Vector.tail_last' {α: Type} {n: Nat} {a_h: α} {a_tail: List α}
  {a_len: (a_h::a_tail).length = n+1+1} {a_tail_len: a_tail.length = n+1}:
  Vector.last (⟨a_h :: a_tail, a_len⟩: Vector α (n+1+1)) =
  Vector.last (⟨a_tail, a_tail_len⟩: Vector α (n+1)) := by
  rw [Vector.last, Vector.last]
  rw [Vector.get, Vector.get]
  simp
  conv =>
    lhs
    arg 2
    rw [a_tail_len]
  simp

lemma Vector.tail_get_head {α: Type} {n: Nat} (v: Vector α (n+1+1)): v.get 1 = v.tail.head := by
  rw [← Vector.get_zero, Vector.get_tail]
  rfl

lemma Vector.get_head {α: Type} {a: α} {n: Nat} {as: List α} {a_len: (a::as).length = n+1}
: @Vector.head α n ⟨a:: as, a_len⟩ = a := by
  rw [Vector.head]

lemma Vector.get_one_cons {α: Type} {a: α} {n: Nat} {as: List α} {a_len: (a::as).length = n+1+1}
: @Vector.get α (n+1+1) ⟨a:: as, a_len⟩ 1 = @Vector.head α n ⟨as, by rw [List.length] at a_len; simp at a_len; exact a_len⟩ := by
  rw [<- Vector.get_zero]
  simp [Vector.get]
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

lemma Int.mul_add_lt {a x b n: Int} (h1: x<n) (h2: 0 < a) (h3: b < a) :
  a*x+b < a*n := by
  have h5: a*(x+1) ≤ a*n := Int.mul_le_mul_of_nonneg_left
     (Int.add_one_le_of_lt h1) (Int.le_of_lt h2)
  rw [Int.mul_add, Int.mul_one] at h5
  have h6: a*x + b < a*x + a := by
    apply Int.add_lt_add_left h3
  apply Int.lt_of_lt_of_le h6 h5

lemma Int.mul_add_lt2 {a x b n: Int} (h1: x<n) (h2: a < 0) (h3: a < b) :
  a*n < a*x+b := by
  have rev: -a*x-b < -a*n := by
    apply Int.mul_add_lt h1 (Int.neg_pos_of_neg h2)
    apply Int.lt_of_neg_lt_neg
    simp
    exact h3
  apply Int.lt_of_neg_lt_neg
  rw [Int.neg_add]
  simp at rev
  exact rev

lemma get_tail_succ {a_tail: Vector Int (k+1)} {a: Vector Int (k+1+1)}
  (j i: Nat)
  (aeq: a_tail = a.tail) (h1: j<k)
  (h2: j+1=i):
  a_tail.get ((↑j: Fin (k+1))+1) = a.get (i+1) := by
    rw [aeq, Mathlib.Vector.get_tail_succ]
    have j_suc_eq:
      (↑↑i + 1: Fin (k + 1 + 1)) = (↑j + 1: Fin (k + 1)).succ := by
      rw [← h2]
      have jk_succ: j+1<k+1 := by
        simp; exact h1
      apply Fin.mk_eq_mk.mpr
      simp
      rw [Nat.mod_eq_of_lt]
      simp
      rw [Nat.mod_eq_of_lt jk_succ]
      simp
      exact h1
    rw [j_suc_eq]

lemma get_tail_succ' {a_tail: Vector Int (k+1)} {a: Vector Int (k+1+1)}
  (j: Nat) (aeq: a_tail = a.tail) (h1: j<k):
  a_tail.get (j+1) = a.get ((j+1: Nat) +1) := by
  rw [get_tail_succ j (j+1) aeq h1 (by simp)]

lemma tail_an
  {a_tail n_tail: Vector Int (k+1)}
  {a n: Vector Int (k+1+1)}
  (aeq: a_tail = a.tail)
  (neq: n_tail = n.tail)
  (h: ∀ i < k + 1, a.get i = a.get (i + 1) * n.get (i + 1))
  : ∀ i < k, a_tail.get i = a_tail.get (i + 1) * n_tail.get (i + 1) := by
    intro j jk
    rw [get_tail_succ' j aeq jk ]
    rw [get_tail_succ' j neq jk ]
    have jk': (j+1)<k+1 := by
      simp
      exact jk
    have jk'': j<k+1 := by
      apply Nat.lt_trans jk
      simp
    have h' := h (j+1) jk'
    rw [aeq, Mathlib.Vector.get_tail_succ]
    rw [← h']
    have j_succ_eq: (↑j: Fin (k+1)).succ = ↑(j+1) := by
      apply Fin.mk_eq_mk.mpr
      simp
      rw [Nat.mod_eq_of_lt jk'']
      rw [Nat.mod_eq_of_lt]
      apply Nat.lt_trans jk'
      simp
    rw [j_succ_eq]

lemma a_pos_bounds
  {a_tail n_tail: Vector Int (k+1)}
  {a n: Vector Int (k+1+1)}
  (aeq: a_tail = a.tail)
  (neq: n_tail = n.tail)
  (h1 : a.last ≠ 0)
  (h3 : ∀ (i : Fin (k + 1 + 1)), 0 < n.get i)
  (h4 : ∀ i < k + 1, a.get i = a.get (i + 1) * n.get (i + 1))
  : 0 < Vector.last a_tail →
    0 ≤ |x'| % a.head ∧ |x'| % a.head < Vector.head a_tail * n_tail.head := by
    intro h
    constructor
    case left =>
      have aNotZ := a_not_zero 0 h4 h3 h1
      simp at aNotZ
      exact Int.emod_nonneg |x'| aNotZ

    case right =>
      have h4_a := h4 0 (by simp)
      simp at h4_a
      have eqv: Vector.get a 1 * n.get 1 = Vector.head a_tail * n_tail.head := by
        rw [aeq, neq]
        rw [<- Mathlib.Vector.get_zero, <- Mathlib.Vector.get_zero]
        rw [Mathlib.Vector.get_tail, Mathlib.Vector.get_tail]
        rfl
      rw [h4_a, eqv]
      apply Int.emod_lt_of_pos

      have n_tail_head_pos: n_tail.head >0 := by
        rw [neq]
        rw [<- Mathlib.Vector.get_zero, Mathlib.Vector.get_tail]
        apply h3
      have h4' := tail_an aeq neq h4
      have h3' : ∀ (i : Fin (k + 1)), 0 < n_tail.get i := by
        rw [neq]
        apply smaller_n h3
      have hhead: 0 < a_tail.get 0 := a_same1 0 h4' h3' h
      simp at hhead
      apply Int.mul_pos hhead n_tail_head_pos

lemma a_neg_bounds
  {a_tail n_tail: Vector Int (k+1)}
  {a n: Vector Int (k+1+1)}
  (aeq: a_tail = a.tail)
  (neq: n_tail = n.tail)
  (h1 : a.last ≠ 0)
  (h3 : ∀ (i : Fin (k + 1 + 1)), 0 < n.get i)
  (h4 : ∀ i < k + 1, a.get i = a.get (i + 1) * n.get (i + 1))
  : a_tail.last < 0 →
    a_tail.head * n_tail.head < -(-x % a.head) ∧
    -(-x % a.head) ≤ 0 := by
    intro a_neg
    repeat rw [← Mathlib.Vector.get_zero]
    constructor
    case left =>
      have h3_a := h4 0 (by simp)
      rw [Nat.cast_zero, Fin.zero_add] at h3_a
      have eqv: a.get 1 * n.get 1 = a_tail.get 0 * n_tail.get 0
        := by
        rw [neq, aeq, Mathlib.Vector.get_tail, Mathlib.Vector.get_tail]
        rfl
      rw [h3_a]
      rw [eqv]
      apply Int.lt_neg_of_lt_neg
      have mod_lem {a b: Int} (h: b <0) : a % b < -b := by
        have b_abs := abs_of_neg h
        rw [← Int.emod_neg, ← b_abs]
        exact Int.emod_lt_of_pos a (abs_pos_of_neg h)
      apply mod_lem
      have wn_head_pos: n_tail.get 0 >0 := by
        rw [neq]
        rw [Mathlib.Vector.get_tail]
        apply h3
      have h3' : ∀ (i : Fin (k + 1)), 0 < n_tail.get i := by
        rw [neq]
        apply smaller_n h3
      have h4' := tail_an aeq neq h4
      have hhead := a_same2 0 h4' h3' a_neg
      apply Int.mul_neg_of_neg_of_pos hhead wn_head_pos
    case right =>
      apply Int.neg_nonpos_of_nonneg
      have aNotZ := a_not_zero 0 h4 h3 h1
      apply Int.emod_nonneg (-x) aNotZ

lemma xInY_prev {x: Int}
  {a_tail n_tail: Vector Int (k+1)}
  {a n: Vector Int (k+1+1)}
  (aeq: a_tail = a.tail)
  (neq: n_tail = n.tail)
  (h: x ∈ Y' n a):
  (0<a.last → |x| % a.head ∈ Y' n_tail a_tail) ∧
  (a.last<0 → -(-x % a.head) ∈ Y' n_tail a_tail)
  := by
  rw [Y', Set.mem_setOf_eq] at h
  match h with
  | ⟨h1, ⟨h2, ⟨h3, ⟨h4, _⟩⟩⟩⟩ =>
  have h1': a_tail.last ≠ 0:= by
    rw [aeq, Vector.tail_last]
    exact h1
  have h2': (|x| % a.head) % a_tail.last = 0:= by
    simp
    rw [aeq, Vector.tail_last]
    simp at h2
    apply last_div_x h2 h4
  have h2_neg': -(-x % a.head) % a_tail.last = 0:= by
    simp
    rw [aeq, Vector.tail_last]
    simp at h2
    have h1'' := last_div_x' h2 h4
    rw [dvd_neg] at h1''
    exact h1''
  have h3': ∀ (i : Fin (k + 1)), 0 < n_tail.get i := by
    intro j
    rw [neq, Mathlib.Vector.get_tail]
    apply h3
  have h4' := tail_an aeq neq h4
  have h5' : 0 < a_tail.last →
      0 ≤ |x| % a.head ∧
      |x| % a.head < a_tail.head * n_tail.head := by
    intro a_pos
    exact a_pos_bounds aeq neq h1 h3 h4 a_pos
  have h6' (apos: 0<a.last) : a_tail.last < 0 →
      a_tail.head * n_tail.head < |x| % a.head ∧
      |x| % a.head ≤ 0:= by
    intro a_neg
    contrapose apos
    rw [aeq, Vector.tail_last] at a_neg
    simp
    exact le_iff_lt_or_eq.mpr (Or.inl a_neg)

  have h5'_neg (aneg: a.last<0) : 0 < a_tail.last →
      0 ≤ -(-x % a.head) ∧
      -(-x % a.head) < a_tail.head * n_tail.head := by
    intro a_neg
    contrapose aneg
    rw [aeq, Vector.tail_last] at a_neg
    simp
    exact le_iff_lt_or_eq.mpr (Or.inl a_neg)

  have h6'_neg: a_tail.last < 0 →
      a_tail.head * n_tail.head < -(-x % a.head) ∧
      -(-x % a.head) ≤ 0:= by
    intro a_neg
    exact a_neg_bounds aeq neq h1 h3 h4 a_neg

  constructor
  case left =>
    intro apos
    rw [Y', Set.mem_setOf_eq]
    exact ⟨h1', ⟨h2', ⟨h3', ⟨h4', ⟨h5', h6' apos⟩⟩⟩⟩⟩
  case right =>
    intro aneg
    rw [Y', Set.mem_setOf_eq]
    exact ⟨h1', ⟨h2_neg', ⟨h3', ⟨h4', ⟨h5'_neg aneg, h6'_neg⟩⟩⟩⟩⟩

lemma xInYIm_prev {a n: Vector Int (k+1+1)}
  (xeq: x_tail = x.tail)
  (aeq: a_tail = a.tail)
  (neq: n_tail = n.tail)
  (h: x ∈ (f_inv a '' Y' n a)):
  x_tail ∈ (f_inv a_tail '' Y' n_tail a_tail) := by
  rw [Set.image, Set.mem_setOf_eq] at h
  match h with
  | ⟨x', ⟨x'inImg, f_inv_x'⟩⟩ =>
  match x'inImg with
  | ⟨h1, ⟨_, ⟨h3, ⟨h4, ⟨_, h6⟩⟩⟩⟩⟩ =>
  have aheadnzero := a_not_zero 0 h4 h3 h1
  rw [Vector.get_zero] at aheadnzero

  match Int.lt_or_lt_of_ne h1 with
  | Or.inr a_pos =>
    have f_inv_pred' := @f_inv_pred k a x' aheadnzero
    have xtaileq: x_tail = f_inv a_tail (|x'| % a.head) := by
      rw [xeq, aeq]
      rw [← f_inv_x', f_inv_pred']
      simp
    match xInY_prev aeq neq x'inImg with
    | ⟨inpos, _⟩ =>
    have inYtail := inpos a_pos
    rw [Set.image, Set.mem_setOf_eq]
    use |x'| % a.head
    exact ⟨inYtail, xtaileq.symm⟩
  | Or.inl a_neg =>
    match h6 a_neg with
    | ⟨_, h7⟩ =>
    have f_inv_pred' := @f_inv_pred2 k a x' aheadnzero
    have xtaileq: x_tail = f_inv a_tail (-(-x' % a.head)) := by
      rw [xeq, aeq]
      rw [← f_inv_x', f_inv_pred' h7]
      simp
    match xInY_prev aeq neq x'inImg with
    | ⟨_, inneg⟩ =>
    have inYtail := inneg a_neg
    rw [Set.image, Set.mem_setOf_eq]
    use (-(-x' % a.head))
    exact ⟨inYtail, xtaileq.symm⟩

lemma xInX_prev
  {x_tail n_tail: Vector Int (k+1)}
  {x n: Vector Int (k+1+1)}
  (neq: n_tail = n.tail)
  (xeq: x_tail = x.tail)
  (h: x ∈ X n):
  (x_tail ∈ X n_tail) := by
  rw [X, Set.mem_setOf_eq] at h
  match h with
  | ⟨h1, h2⟩ =>
  rw [neq, xeq, X, Set.mem_setOf_eq]
  constructor
  case left =>
    exact smaller_n h1
  case right =>
    intro i
    -- intro j
    rw [Mathlib.Vector.get_tail, Mathlib.Vector.get_tail]
    apply h2

lemma Prop_prev_prop
  {a_tail n_tail: Vector Int (k+1)}
  {n a: Vector Int (k+1+1)}
  (neq: n_tail = n.tail)
  (aeq: a_tail = a.tail)
  (h: Props n a):
  Props n_tail a_tail := by
    match h with
    | ⟨h1, h2⟩ =>
    have h1': a_tail.last ≠ 0:= by
      rw [aeq, Vector.tail_last]
      exact h1
    have h2' := tail_an aeq neq h2
    exact ⟨h1', h2'⟩




lemma f_in_bounds: ∀ a n x: Vector Int (k+1),
  Props n a →
  x ∈ X n →
  (0<a.last → 0 ≤ f a x ∧ f a x < a.head*n.head) ∧
  (a.last<0 → a.head*n.head < f a x ∧ f a x ≤ 0 ) ∧
  f a x % a.last = 0 := by
  induction k
  case zero =>
    intro a n x props xinX
    match props, xinX with
    | ⟨h1, h2⟩, ⟨h3, h4⟩ =>
    match a, x with
    | ⟨[a_h], _⟩, ⟨[x_h], _⟩ =>
    rw [f, ← Vector.tail_head, Vector.get_head, f]
    have h4' := h4 0
    rw [Vector.get_zero, Vector.get_head] at h4'
    rw [← Vector.tail_head, Vector.get_head] at h1
    simp_all
    intro a_neg
    apply mul_nonpos_of_nonpos_of_nonneg (Int.le_of_lt a_neg) h4'.left
  case succ k ih =>
    intro a n x props xinX
    match props, xinX with
    | ⟨h1, h2⟩, ⟨h3, h4⟩ =>
    match a, x with
    | ⟨a_h::a_tail, a_len⟩, ⟨x_h::x_tail, x_len⟩ =>
    let a_tail_v: Vector Int (k+1) := ⟨a_tail, f.proof_1 a_h a_tail a_len⟩
    let x_tail_v: Vector Int (k+1) := ⟨x_tail, f.proof_2 x_h x_tail x_len⟩
    have aeq: a_tail_v =
      Vector.tail ⟨a_h::a_tail, a_len⟩ := by
      rw [Vector.tail]
    have aNotZ := a_not_zero 0 h2 h3 h1
    rw [Vector.get_zero] at aNotZ
    rw [f]
    have prevProp := Prop_prev_prop (by rfl) (aeq) props
    have ih' := ih ⟨a_tail, f.proof_1 a_h a_tail a_len⟩ n.tail x_tail_v prevProp (xInX_prev (by rfl) (by rfl) xinX)
    match ih' with
    | ⟨ih1, ih2, ih3⟩ =>
    have h4' := h4 0
    rw [Vector.get_zero, Vector.get_zero, Vector.get_head] at h4'
    constructor
    case left =>
      intro a_pos
      have ah_pos := a_same1 0 h2 h3 a_pos
      rw [Vector.get_zero, Vector.get_head] at ah_pos
      rw [← Vector.tail_last, Vector.tail] at a_pos
      simp at a_pos
      have ih1' := ih1 a_pos
      constructor
      case left =>
        apply Int.add_nonneg
        exact Int.mul_nonneg (Int.le_of_lt ah_pos) (h4'.left)
        exact ih1'.left
      case right =>
        rw [Vector.get_head]
        have h2' := h2 0
        simp at h2'
        rw [Vector.get_head] at h2'
        apply Int.mul_add_lt h4'.right ah_pos
        rw [h2', Vector.get_one_cons, Vector.tail_get_head]
        exact ih1'.right
    case right =>
      constructor
      case left =>
        intro a_neg
        have ah_neg := a_same2 0 h2 h3 a_neg
        rw [Vector.get_zero, Vector.get_head] at ah_neg
        rw [← Vector.tail_last, Vector.tail] at a_neg
        simp at a_neg
        have ih1' := ih2 a_neg
        constructor
        case right =>
          apply Int.add_nonpos
          apply Int.mul_nonpos_of_nonpos_of_nonneg (Int.le_of_lt ah_neg) (h4'.left)
          exact ih1'.right
        case left =>
          rw [Vector.get_head]
          have h2' := h2 0
          simp at h2'
          rw [Vector.get_head] at h2'
          apply Int.mul_add_lt2 h4'.right ah_neg
          rw [h2', Vector.get_one_cons, Vector.tail_get_head]
          exact ih1'.left
      case right =>
        match head_is_div h2 with
        | ⟨q, l1⟩ =>
        rw [Vector.head, Vector.tail_last'] at l1
        simp at l1
        rw [Vector.tail_last']
        rw [l1]
        rw [Int.add_comm]
        rw [Int.mul_comm, Int.mul_assoc]
        rw [Int.add_mul_emod_self_left]
        exact ih3

theorem f_inv_f :
  ∀ a n x: Vector Int (k+1),
  Props n a →
  x ∈ X n →
  f_inv a (f a x) = x := by
  induction k
  case zero =>
    intro a n x props xinX
    match props, xinX with
    | ⟨h1, h2⟩, ⟨_, h4⟩ =>
    match a, x with
    | ⟨[a_h], _⟩, ⟨[x_h], _⟩ =>
    simp
    rw [f, f_inv]
    simp
    simp at h2
    have baseCase: |a_h * x_h| / |a_h| = x_h := by
      rw [Int.mul_comm, abs_mul, Int.mul_ediv_cancel (|x_h|)]
      have x_not_zero := (h4 0).left
      rw [Vector.get_zero, Vector.get_head] at x_not_zero
      exact (abs_of_nonneg x_not_zero)
      rw [Vector.last_def, Fin.last] at h1
      simp at h1
      rw [Vector.head] at h1
      simp at h1
      contrapose h1
      simp
      simp at h1
      exact h1
    conv =>
      arg 1; arg 1
      rw [f_inv_h, f_inv_el, base, f]
      simp
      rw [Vector.head]
      simp
      rw [baseCase]
  case succ k ih =>
    intro a n x props xinX
    match props, xinX with
    | ⟨h1, h2⟩, ⟨h3, h4⟩ =>
    match a, x with
    | ⟨a_h::a_tail, a_len⟩, ⟨x_h::x_tail, x_len⟩ =>
    let a_tail_v: Vector Int (k+1) := ⟨a_tail, f.proof_1 a_h a_tail a_len⟩
    let x_tail_v: Vector Int (k+1) := ⟨x_tail, f.proof_2 x_h x_tail x_len⟩
    have aeq: a_tail_v =
      Vector.tail ⟨a_h::a_tail, a_len⟩ := by
      rw [Vector.tail]
    have aNotZ := a_not_zero 0 h2 h3 h1
    rw [Vector.get_zero] at aNotZ
    rw [f]
    have prevProp := Prop_prev_prop (by rfl) (aeq) props
    match f_in_bounds ⟨a_h :: a_tail, a_len⟩ n ⟨x_h::x_tail, x_len⟩ props xinX with
    | ⟨bounds1a, bounds2a, bounds3a⟩ =>
    match f_in_bounds a_tail_v n.tail x_tail_v prevProp (xInX_prev (by rfl) (by rfl) xinX) with
    | ⟨bounds1b, bounds2b, bounds3b⟩ =>
    match Int.lt_or_lt_of_ne h1 with
    | Or.inr a_pos =>
      have a_h_pos : 0 < a_h := by
        have same := a_same1 0 h2 h3 a_pos
        rw [Vector.get_zero, Vector.get_head] at same
        exact same
      rw [f_inv_pred aNotZ]
      rw [Vector.get_head] at aNotZ
      rw [Vector.tail, Vector.get_head]
      simp
      have bounds1a := bounds1a a_pos
      have bounds1b := bounds1b a_pos
      have f_pos: 0 ≤ f a_tail_v x_tail_v := bounds1b.left
      have arg_pos: 0 ≤ a_h * x_h + f a_tail_v x_tail_v := by
        have almost := bounds1a.left
        rw [f] at almost
        exact almost
      have f_smaller: f a_tail_v x_tail_v < a_h := by
        have h2' := h2 0
        simp at h2'
        rw [Vector.get_head] at h2'
        rw [h2', Vector.get_one_cons, Vector.tail_get_head]
        exact bounds1b.right

      rw [abs_of_nonneg arg_pos]
      have x_h_eq: (a_h * x_h + f a_tail_v x_tail_v) / |a_h| = x_h := by
        rw [abs_of_pos a_h_pos, Int.add_comm]
        rw [Int.add_mul_ediv_left (f a_tail_v x_tail_v) x_h aNotZ]
        rw [Int.ediv_eq_zero_of_lt f_pos f_smaller]
        simp
      conv =>
        lhs; arg 2; arg 2
        rw [Int.add_comm, Int.add_mul_emod_self_left]
        rw [Int.emod_eq_of_lt f_pos f_smaller]

      rw [ih a_tail_v n.tail x_tail_v prevProp (xInX_prev (by rfl) (by rfl) xinX)]
      rw [x_h_eq]
      rfl
    | Or.inl a_neg =>
      have a_h_neg : a_h < 0 := by
        have same := a_same2 0 h2 h3 a_neg
        rw [Vector.get_zero, Vector.get_head] at same
        exact same
      have bounds2a := bounds2a a_neg
      have bounds2b := bounds2b a_neg
      have arg_neg: a_h * x_h + f a_tail_v x_tail_v ≤ 0 := by
        have almost := bounds2a.right
        rw [f] at almost
        exact almost
      rw [f_inv_pred2 aNotZ arg_neg]
      have min_a_not_zero: -a_h ≠ 0 := by
       simp
       assumption
      rw [Vector.tail, Vector.get_head]
      simp
      have f_neg: 0 ≤ -f a_tail_v x_tail_v  := by
        apply Int.neg_nonneg_of_nonpos
        exact bounds2b.right
      have f_smaller: -f a_tail_v x_tail_v < -a_h := by
        have h2' := h2 0
        simp at h2'
        rw [Vector.get_head] at h2'
        rw [h2', Vector.get_one_cons, Vector.tail_get_head]
        exact Int.neg_lt_neg bounds2b.left
      rw [abs_of_nonpos arg_neg]

      have x_h_eq: -(a_h * x_h + f a_tail_v x_tail_v) / |a_h| = x_h := by
        rw [abs_of_neg a_h_neg, Int.add_comm, Int.neg_add, ← Int.neg_mul]
        rw [Int.add_mul_ediv_left (-(f a_tail_v x_tail_v)) x_h min_a_not_zero]
        rw [Int.ediv_eq_zero_of_lt f_neg f_smaller]
        simp
      conv =>
        lhs; arg 2; arg 2
        simp
        rw [← Int.mul_neg, Int.add_mul_emod_self_left, ← Int.emod_neg]
        rw [Int.emod_eq_of_lt f_neg f_smaller]
        simp
      have prevProp := Prop_prev_prop (by rfl) (aeq) props
      rw [ih a_tail_v n.tail x_tail_v prevProp (xInX_prev (by rfl) (by rfl) xinX)]
      rw [x_h_eq]
      rfl
