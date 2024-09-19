import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Simps.Basic
import Mathlib.Init.Set
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Function
import Mathlib.Tactic
import Init.Data.Int.Order
import Init.Data.Int.Lemmas
import Init.ByCases


open Nat

example (P Q : Prop) (hsj: Q → P) (hjs: P → Q) : Q ↔ P := by
  constructor
  repeat assumption

example (x y z: Nat) : x*y*z = 0 → x=0 ∨ y=0 ∨ z=0 := by
  intro h
  have h1 : x*y = 0 → x=0 ∨ y=0 := λ xy0 ↦ (Nat.mul_eq_zero.mp xy0)
  have h2 : x*y*z = 0 → x*y=0 ∨ z=0 := λ xyz0 ↦ (Nat.mul_eq_zero.mp xyz0)
  rw [Nat.mul_assoc] at h
  rw [Nat.mul_eq_zero] at h
  cases h
  case inl h =>
    left
    exact h
  case inr h =>
    right
    rw [<- Nat.mul_eq_zero]
    exact h
  done

example (x: Nat) : 2*x = x + x := by
  induction x
  case zero =>
    simp
  case succ n inh =>
    rw [Nat.mul_add_one]
    rw [inh]
    simp [Nat.add_assoc, Nat.add_comm]
    nth_rewrite 2 [Nat.add_comm]
    rw [Nat.add_assoc]
  done


theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p :=
  fun hpq : p ∧ q =>
  have hp : p := And.left hpq
  have hq : q := And.right hpq
  show q ∧ p from And.intro hq hp

def a (yₐ: Int) (p: Prod Int Int): Int := yₐ * p.snd + p.fst

def a_inv (yₐ: Int) (xy: Int) : Prod Int Int :=
  {fst:= xy % yₐ, snd:= xy / yₐ}

def X (xₙ yₙ : Int): Set (Prod Int Int) :=
  {p : Prod Int Int | 0 ≤ p.fst ∧ p.fst < xₙ ∧ 0 ≤ p.snd ∧ p.snd < yₙ}

def Y (xₙ yₙ yₐ : Int): Set Int :=
  {xy : Int | ∃ x y : Int , a yₐ {fst:=x, snd:=y} = xy ∧
   {fst:=x, snd:=y} ∈ X xₙ yₙ}

theorem ainY {xₙ yₙ yₐ : Int} {xy : Prod Int Int} :
  xy ∈ X xₙ yₙ → a yₐ xy ∈ Y xₙ yₙ yₐ := by
  intro h
  rw [Y]
  exact ⟨xy.fst, xy.snd, rfl, h⟩

theorem xBiggerZero {xₙ yₙ : Int} {xy : Prod Int Int}:
  xy ∈ X xₙ yₙ -> 0 ≤ xy.fst := by
  intro h
  cases h with
  | intro left right => exact left

theorem xSmallerN {xₙ yₙ : Int} {xy : Prod Int Int}:
  xy ∈ X xₙ yₙ -> xy.fst < xₙ := by
  intro h
  cases h with
  | intro left right =>
  cases right with
  | intro lleft right =>
  exact lleft


theorem a_inv_a_set {xₙ yₙ yₐ : Int} {xy: Prod Int Int} :
 0<yₐ → 0≤xₙ → xₙ≤yₐ → xy ∈ X xₙ yₙ →
 a_inv yₐ (a yₐ xy) = xy
  := by
  intro yaBiggerZero _ xnSEya xyInSet
  have xBiggerZero: 0 ≤ xy.fst := xBiggerZero xyInSet
  have xSmallerN: xy.fst < xₙ := xSmallerN xyInSet
  rw [a_inv, a]
  rw [Int.add_comm, Int.add_mul_emod_self_left]
  have xSmallerya : xy.fst < yₐ:= by exact Int.lt_of_lt_of_le xSmallerN xnSEya
  rw [Int.emod_eq_of_lt xBiggerZero xSmallerya]
  have h3 : (yₐ: Int) ∣ yₐ * xy.snd :=
    by exact Int.dvd_mul_right yₐ xy.snd
  rw [Int.add_ediv_of_dvd_right h3]

  rw [Int.ediv_eq_zero_of_lt xBiggerZero xSmallerya]
  have yaNotZero : yₐ ≠ 0 :=
    by exact Int.ne_of_gt yaBiggerZero
  rw [Int.mul_ediv_cancel_left xy.snd yaNotZero]
  simp
  done

theorem a_a_inv {yₐ: Int} {xy: Int} :
 a yₐ (a_inv yₐ xy) = xy
  := by
  rw [a_inv, a, Prod.fst, Prod.snd]
  simp
  rw [Int.ediv_add_emod]
  done


theorem a_maps_to {xₙ yₙ yₐ : Int} : Set.MapsTo (a yₐ) (X xₙ yₙ) (Y xₙ yₙ yₐ)
 := by
 rw [Set.MapsTo]
 intro xy
 intro inSet
 apply Set.mem_setOf.mpr
 use xy.fst
 use xy.snd

 theorem left_inva_a {xₙ yₙ yₐ : Int} : 0<yₐ → 0≤xₙ → xₙ≤yₐ →
  Set.LeftInvOn (a_inv yₐ) (a yₐ) (X xₙ yₙ) := by
  intro h1
  intro h2
  intro h3
  rw [Set.LeftInvOn]
  intro xy
  intro xyInSet
  exact a_inv_a_set h1 h2 h3 xyInSet

theorem right_inva_a {xₙ yₙ yₐ : Int} : Set.RightInvOn (a_inv yₐ) (a yₐ) (Y xₙ yₙ yₐ) := by
  rw [Set.RightInvOn]
  intro xy
  intro _
  exact a_a_inv

theorem left_inva_a' {xₙ yₙ yₐ : Int} : Set.LeftInvOn (a yₐ) (a_inv yₐ) (Y xₙ yₙ yₐ) := by
  rw [Set.LeftInvOn]
  intro xy
  intro _
  exact a_a_inv

theorem right_inva_a' {xₙ yₙ yₐ : Int} : Set.RightInvOn (a yₐ) (a_inv yₐ) (a_inv yₐ '' Y xₙ yₙ yₐ) := by
  exact Set.LeftInvOn.rightInvOn_image (left_inva_a')


theorem hf : Set.SurjOn (a yₐ) (X xₙ yₙ) (Y xₙ yₙ yₐ) := by
  rw [Set.SurjOn]
  intro a
  intro xInY
  apply Set.mem_setOf.mpr
  apply Set.mem_setOf.mp at xInY
  cases' xInY with x xInY
  cases' xInY with y xInY
  cases' xInY with left right
  use ⟨x,y⟩

theorem a_inv_maps_to {xₙ yₙ yₐ : Int} : 0<yₐ → 0≤xₙ → xₙ≤yₐ →
 Set.MapsTo (a_inv yₐ) (Y xₙ yₙ yₐ) (X xₙ yₙ)
 := by
 intro h1
 intro h2
 intro h3
 exact Set.LeftInvOn.mapsTo (left_inva_a h1 h2 h3) hf

theorem a_is_bijection {xₙ yₙ yₐ : Int} : 0<yₐ → 0≤xₙ → xₙ≤yₐ →
  Set.BijOn (a yₐ) (X xₙ yₙ) (Y xₙ yₙ yₐ) := by
  intro h1
  intro h2
  intro h3
  have h4 : Set.InvOn (a_inv yₐ) (a yₐ) (X xₙ yₙ) (Y xₙ yₙ yₐ) := by exact ⟨left_inva_a h1 h2 h3, right_inva_a⟩
  exact Set.InvOn.bijOn h4 a_maps_to (a_inv_maps_to h1 h2 h3)
