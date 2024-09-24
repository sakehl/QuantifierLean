
import Mathlib.Tactic
open Mathlib

lemma base_l1 {i: Fin k} : ↑i - 1 < k := by
  cases' i with v lt
  simp_all
  have h1: v - 1 <= v := by simp
  exact lt_of_le_of_lt h1 lt

lemma f_inv_h_l1 {i: Fin (k+1)}: k - ↑i < k+1 := by
  cases' i with v lt
  simp
  have h1: k-v ≤ k := by simp;
  have h2: k < (k+1) := by simp;
  apply lt_of_le_of_lt h1 h2

lemma f_inv_h_l2 {i: Fin (k+1)} (h : ¬(↑i == (0: Nat)) = true) : ↑i - 1 < k + 1 := by
  apply base_l1

-- Definitions
def f : Mathlib.Vector Int k → Mathlib.Vector Int k → Int
  | ⟨[], _⟩, ⟨[], _⟩ => 0
  | ⟨a :: as, ha⟩, ⟨x :: xs, hx⟩ => a*x + f ⟨as, congrArg Nat.pred ha⟩ ⟨xs, congrArg Nat.pred hx⟩

def base (as: Mathlib.Vector Int k) (x': Int) : (i: Fin k) → Int :=
  λ i ↦
  if h: ↑i == (0: Nat) then
    |x'|
  else
    let ipred : Fin k := Fin.mk (↑i - 1) (base_l1)
    base as x' ipred % as.get ipred
termination_by i => i.val
decreasing_by
  all_goals simp_wf
  cases' i with v lt
  simp_all
  contrapose h
  simp_all

def f_inv_el (as: Mathlib.Vector Int k) (x': Int) (i: Fin k): Int :=
  let aᵢ := as.get i
  let baseᵢ := base as x' i
  baseᵢ / |aᵢ|

def f_inv_h (as: Mathlib.Vector Int (k+1)) (x': Int): (i: Fin (k+1)) → List Int :=
  λ i ↦
    let idx: Fin (k+1) := ⟨k-↑i, f_inv_h_l1⟩
    f_inv_el as x' idx ::
    if h: ↑i == (0: Nat) then
      []
    else
      f_inv_h as x' ⟨i.val-1, f_inv_h_l2 h⟩
  termination_by i => i.val
  decreasing_by
    all_goals simp_wf
    cases' i with v lt
    simp_all
    cases v
    repeat simp_all

theorem f_inv_length  {as: Mathlib.Vector Int (k+1)} {x': Int} {i: Fin (k+1)} :
    (f_inv_h as x' i).length = i+1 := by
    rw [f_inv_h]
    cases' i with i isLt
    simp
    induction i
    case zero =>
      simp
    case succ i ih =>
      simp_all
      have isLt2: (i <k+1) := by
        simp_all;
        have kk1: (k < k+1) := by simp;
        exact Nat.lt_trans isLt kk1
      rw [f_inv_h]
      simp
      rw [ih isLt2]

def f_inv (as: Mathlib.Vector Int (k+1)) (x': Int): Mathlib.Vector Int (k+1) :=
  ⟨(f_inv_h as x' ⟨k, by simp⟩),
   by
   rw [f_inv_length]⟩


def X (nₖ : Vector Int (k+1)): Set (Vector Int (k+1)) :=
  {xs : Vector Int (k+1) |
    (∀ i, 0 < nₖ.get i) ∧
    (∀ i: Fin (k+1), 0 ≤ xs.get i ∧ xs.get i < nₖ.get i)
  }

def Y (nₖ aₖ : Vector Int (k+1)): Set Int := f aₖ '' X nₖ

def Y' (nₖ aₖ : Vector Int (k+1)): Set Int :=
  {x' : Int |
    aₖ.last ≠ 0 ∧
    x' % aₖ.last = 0 ∧
    (∀ i, 0 < nₖ.get i) ∧
    (∀ i, i<k → aₖ.get i = aₖ.get (i+1) * nₖ.get (i+1)) ∧
    (0<aₖ.last → 0 ≤ x' ∧ x' < aₖ.head*nₖ.head) ∧
    (aₖ.last<0 → aₖ.head*nₖ.head < x' ∧ x' ≤ 0 )
  }

def Props (nₖ aₖ : Vector Int (k+1)): Prop :=
  aₖ.last ≠ 0 ∧
  (∀ i, i<k → aₖ.get i = aₖ.get (i+1) * nₖ.get (i+1))
