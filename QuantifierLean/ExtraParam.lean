prelude
import Mathlib.Tactic
import Mathlib.Data.Vector.Defs
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Vector.Zip

import Init.Data.Int.DivModLemmas

-- import Mathlib.Tactic.NthRewrite
-- import Mathlib.Tactic.Simps.Basic
-- import Mathlib.Init.Set
-- import Mathlib.Data.Set.Defs
-- import Mathlib.Data.Set.Function
-- import Init.Data.Int.Order
-- import Init.Data.Int.Lemmas
-- import Init.ByCases
-- import Mathlib.Algebra.BigOperators.Finprod



-- import Mathlib.Init.Data.List.Lemmas
-- import Mathlib.Tactic.Common

-- open Mathlib.Vector
open Mathlib
-- open Nat

def f : Mathlib.Vector Int k → Mathlib.Vector Int k → Int
  | ⟨[], _⟩, ⟨[], _⟩ => 0
  | ⟨a :: as, ha⟩, ⟨x :: xs, hx⟩ => a*x + f ⟨as, congrArg Nat.pred ha⟩ ⟨xs, congrArg Nat.pred hx⟩


-- lemma lemma1 {k n: Nat} {nk: k ≠ n} : k ≤ n → k+1 ≤ n := by
--   intro h1
--   apply Nat.le_of_lt_add_one
--   apply Nat.succ_lt_succ
--   apply Nat.lt_iff_le_and_ne.mpr
--   constructor
--   repeat assumption


-- def base {n: Nat} (as: Mathlib.Vector Int k) (x': Int) : (k: Nat) → (zk: k ≤ n) → Int :=
--   λ k zk ↦
--   if h: k==n then
--     x'
--   else
--     have h1 : k ≠ n := by simp at h; simp; assumption
--     have h1 : k < n := by apply lemma1 zk; exact h1
--     let base_p1 := (base as x' (k+1) h1)
--     base_p1 % as.get ⟨k, h1⟩
-- termination_by k => n-k
-- decreasing_by
--   all_goals simp_wf
--   rw [Nat.sub_add_eq]
--   apply Nat.sub_succ_lt_self
--   apply Nat.zero_lt_sub_of_lt
--   apply Nat.lt_iff_le_and_ne.mpr
--   constructor
--   repeat assumption

lemma lemma1 {k: Nat} {i: Fin k} : (ki: ¬(↑i == k - 1) = true) -> ↑i+1 < k := by
  let h1: i.val < k := by simp_all
  apply Nat.lt_iff_add_one_le.mp at h1
  apply Nat.eq_or_lt_of_le at h1
  cases h1
  case inl h1 =>
    apply congrArg Nat.pred at h1
    simp_all
  case inr h1 =>
    simp_all


def base {k: Nat} (as: Mathlib.Vector Int k) (x': Int) : (i: Fin k) → Int :=
  λ i ↦
  if h: i==k-1 then
    x'
  else
    let isucc : Fin k := Fin.mk (i.val + 1) (lemma1 h)
    let base_p1 := (base as x' isucc)
    base_p1 % as.get isucc
termination_by i => k-(i+1)
decreasing_by
  all_goals simp_wf
  apply Nat.lt_of_add_one_le
  rw [Nat.sub_add_eq]
  apply lemma1 at h
  have h1: 1 ≤ k - (↑i + 1) := by
    apply Nat.lt_iff_add_one_le.mp at h
    apply Nat.le.dest at h
    cases' h with c hc
    have h2: 1 + c = k - (↑i + 1) := by
      apply congrArg (λ x ↦ x - (i.val + 1))  at hc; simp at hc
      nth_rewrite 2 [Nat.add_comm] at hc
      rw [Nat.add_right_comm] at hc
      rw [Nat.add_sub_self_right] at hc
      assumption
    apply Nat.le.intro h2
  rw [Nat.sub_add_cancel h1]



-- List.length_range (Init.Data.List.Nat.Range)
-- List.length_map (Init.Data.List.Lemmas)
-- List.mem_range
-- def f_inv (as: Mathlib.Vector Int k) (x': Int): Mathlib.Vector Int k :=
--   -- let range := List.range n
--   -- let basek := λ k ↦ base as x' k (by sorry)
--   -- let ak := λ k ↦ as.get ⟨k, by sorry⟩
--   -- let res := List.map (λ k ↦ basek k / ak k) range
--   -- ⟨res, by (have l: res.length = range.length := by sorry); rw [l]; sorry⟩
--   match as.toList with
--   | nil => List.nil
--   | cons y ys => ys


def f_inv_h (as: Mathlib.Vector Int k) (x': Int) (i: Fin k): Int :=
  let aᵢ := as.get i
  let baseᵢ := base as x' i
  baseᵢ / aᵢ

lemma lemma2 (ik : i < k) (h : ¬i = 0):  i - 1 < k := by
    apply Nat.lt_iff_add_one_le.mpr
    apply Nat.lt_iff_add_one_le.mp at ik
    have h2: 1 ≤ i :=
      by contrapose h; simp_all;
    rw [Nat.sub_add_cancel h2]
    apply Nat.le.dest at ik
    cases' ik with i knn
    rw [Nat.add_assoc] at knn
    exact Nat.le.intro knn

-- def f_inv (as: Mathlib.Vector Int k) (x': Int) (kz: 0<k): List Int :=
--   List.map (λ i ↦ f_inv_h as x' i (by sorry)) (List.range' 0 k 1)


def f_inv_hh (as: Mathlib.Vector Int k) (x': Int): (i: Fin k) → List Int → List Int :=
  λ i ns ↦
  if h: i.val == 0 then
    f_inv_h as x' i :: ns
  else
    f_inv_hh as x' ⟨i.val-1, by sorry⟩ (f_inv_h as x' i :: ns)
  termination_by i => i.val
  decreasing_by
    all_goals simp_wf
    contrapose h
    simp_all
    sorry

theorem f_inv_length  {as: Mathlib.Vector Int k} {x': Int} {i: Fin k} :
    (f_inv_hh as x' i []).length = i+1
    := by
    cases' i with i isLt
    induction' i with d hd
    rw[f_inv_hh]
    simp

    rw[f_inv_hh]
    simp_all

    sorry --apply hd

    -- conv =>
    --   lhs
    --   rw [List.length]

    -- conv =>
    --   lhs
    --   arg 1
    --   arg

      -- apply hd

    -- theorem congrArg {α : Sort u} {β : Sort v} {a₁ a₂ : α}
    -- (f : α → β) (h : Eq a₁ a₂) : Eq (f a₁) (f a₂) :=
    -- induction' i with d hd
    -- simp
    -- rw[f_inv_hh]
    -- simp

    -- rw[f_inv_hh]
    -- simp

    -- rw[f_inv_hh]
    -- simp_all

    -- apply hd ik
    -- rw [hd]
    -- rw [add_assoc]

def f_inv_hh2 (as: Mathlib.Vector Int k) (x': Int): (i: Fin k) → List Int :=
  λ i ↦ if h: i.val == 0 then
      f_inv_h as x' i :: []
    else
      f_inv_h as x' i :: f_inv_hh2 as x' ⟨i.val-1, by sorry⟩
  termination_by i => i.val
  decreasing_by
    all_goals simp_wf
    apply Fin.lt_def.mpr
    contrapose h
    simp_all

theorem f_inv_length2  {as: Mathlib.Vector Int k} {x': Int} {i: Fin k} :
    (f_inv_hh2 as x' i).length = i+1
    := by sorry

lemma f_inv_hh2_pred (as: Mathlib.Vector Int (k+1)) (x': Int) (i: Fin (k+1)) (h0: ↑i < k):
  (f_inv_hh2 as x' i).tail = f_inv_hh2 as.tail (x' % as.head) ⟨i.val, h0⟩  :=
  by sorry

def f_inv (as: Mathlib.Vector Int k) (x': Int) (kz: 0<k): Mathlib.Vector Int k :=
  ⟨f_inv_hh2 as x' ⟨k-1, by simp; assumption⟩,
   by
   rw [f_inv_length2]
   simp
   rw [Nat.sub_add_cancel]
   exact Nat.lt_iff_add_one_le.mp kz⟩

def X (nₖ : Vector Int k): Set (Vector Int k) :=
  {xs : Vector Int k |
    List.Forall id
    (Mathlib.Vector.zipWith (λ xn x ↦ 0 ≤ x ∧ x < xn) nₖ xs).toList
  }

def Y (nₖ aₙ : Vector Int k): Set Int :=
  {x' : Int | ∃ xs : Vector Int k , f aₙ xs = x' ∧
   xs ∈ X nₖ}

-- example (a b c : Nat) : a * (b * c) = a * (c * b) := by

--   conv =>
--     -- ⊢ a * (b * c) = a * (c * b)
--     rhs
--     -- ⊢ a * (b * c)
--     arg 2
--     -- ⊢ b * c
--     --  rw [Nat.mul_comm]


theorem f_f_inv :
 ∀ aₙ: Vector Int (k+1), ∀ x': Int ,  ∀ i,  aₙ.get i ≠ 0 → x' % aₙ.get 1 = 0 →
 f aₙ (f_inv aₙ x' (by simp)) = x'
  := by
  induction k
  case zero =>
    intro an x' i h0 h1
    simp
    rw [f_inv]
    conv =>
      lhs
      arg 2
      arg 1
      rw [f_inv_hh]
      rw [f_inv_h]
      rw [base]
      simp
      -- rw [List.Cons]
    cases' an with a a_length
    cases a -- with a as
    case nil =>
      rw [List.length] at a_length
      simp_all
    case cons head tail =>
      simp at a_length
      simp_all
      repeat rw [f]
      simp_all
      conv =>
        lhs
        arg 2
        arg 2
        rw [Vector.head]
        simp

      rw [Vector.get] at h1
      simp_all
      apply Int.mul_ediv_cancel'
      exact h1

  case succ k ih =>
    intro an x' i h0 h1
    -- simp_all
    rw [f_inv]
    conv =>
      lhs
      arg 2
      arg 1
      rw [f_inv_hh]
      rw [f_inv_h]
      rw [base]
      simp
    cases' an with a a_length
    cases a
    case nil =>
      rw [List.length] at a_length
      simp_all
    case cons head tail =>
      conv =>
        lhs
        arg 2
        arg 1
        rw [f_inv_hh]
        rw [f_inv_h]
        rw [base]
        simp
      cases k
      case zero => sorry
      case succ k =>

        simp

        sorry

      rw [f]

      sorry


    sorry


  -- rw [f_inv]
  -- conv =>
  --   lhs
  --   arg 2
  --   arg 1
  --   rw [f_inv_hh]
  --   rw [f_inv_h]
  --   rw [base]
  --   simp

  -- have aNotZero: Vector.get aₙ k ≠ 0 := by
  --   apply h₁
  -- cases' aₙ with a a_length
  -- cases' a with a as
  -- rw [List.length] at a_length
  -- simp_all

  -- induction' k with d hd
  -- simp_all

  -- cases' as with aa aas
  -- -- simp_all
  -- -- cases' as with aa aas
  -- -- simp_all

  -- repeat rw [f]
  -- rw [Vector.head]
  -- rw [Vector.get] at h2
  -- simp_all
  -- rw [mul_comm]
  -- exact Int.ediv_mul_cancel h2

  -- rw [List.length] at a_length
  -- simp_all

  -- -- simp_all
  -- rw [f]






  sorry

-- def f_inv (as: Vector Int k) (k: Int) : Vector Int k :=
--   {fst:= xy % yₐ, snd:= xy / yₐ}

-- def X (xₙ yₙ : Int): Set (Prod Int Int) :=
--   {p : Prod Int Int | 0 ≤ p.fst ∧ p.fst < xₙ ∧ 0 ≤ p.snd ∧ p.snd < yₙ}

-- def Y (xₙ yₙ yₐ : Int): Set Int :=
--   {xy : Int | ∃ x y : Int , a yₐ {fst:=x, snd:=y} = xy ∧
--    {fst:=x, snd:=y} ∈ X xₙ yₙ}

-- theorem ainY {xₙ yₙ yₐ : Int} {xy : Prod Int Int} :
--   xy ∈ X xₙ yₙ → a yₐ xy ∈ Y xₙ yₙ yₐ := by
--   intro h
--   rw [Y]
--   exact ⟨xy.fst, xy.snd, rfl, h⟩

-- theorem xBiggerZero {xₙ yₙ : Int} {xy : Prod Int Int}:
--   xy ∈ X xₙ yₙ -> 0 ≤ xy.fst := by
--   intro h
--   cases h with
--   | intro left right => exact left

-- theorem xSmallerN {xₙ yₙ : Int} {xy : Prod Int Int}:
--   xy ∈ X xₙ yₙ -> xy.fst < xₙ := by
--   intro h
--   cases h with
--   | intro left right =>
--   cases right with
--   | intro lleft right =>
--   exact lleft


-- theorem a_inv_a_set {xₙ yₙ yₐ : Int} {xy: Prod Int Int} :
--  0<yₐ → 0≤xₙ → xₙ≤yₐ → xy ∈ X xₙ yₙ →
--  a_inv yₐ (a yₐ xy) = xy
--   := by
--   intro yaBiggerZero _ xnSEya xyInSet
--   have xBiggerZero: 0 ≤ xy.fst := xBiggerZero xyInSet
--   have xSmallerN: xy.fst < xₙ := xSmallerN xyInSet
--   rw [a_inv, a]
--   rw [Int.add_comm, Int.add_mul_emod_self_left]
--   have xSmallerya : xy.fst < yₐ:= by exact Int.lt_of_lt_of_le xSmallerN xnSEya
--   rw [Int.emod_eq_of_lt xBiggerZero xSmallerya]
--   have h3 : (yₐ: Int) ∣ yₐ * xy.snd :=
--     by exact Int.dvd_mul_right yₐ xy.snd
--   rw [Int.add_ediv_of_dvd_right h3]

--   rw [Int.ediv_eq_zero_of_lt xBiggerZero xSmallerya]
--   have yaNotZero : yₐ ≠ 0 :=
--     by exact Int.ne_of_gt yaBiggerZero
--   rw [Int.mul_ediv_cancel_left xy.snd yaNotZero]
--   simp
--   done

-- theorem a_a_inv {yₐ: Int} {xy: Int} :
--  a yₐ (a_inv yₐ xy) = xy
--   := by
--   rw [a_inv, a, Prod.fst, Prod.snd]
--   simp
--   rw [Int.ediv_add_emod]
--   done


-- theorem a_maps_to {xₙ yₙ yₐ : Int} : Set.MapsTo (a yₐ) (X xₙ yₙ) (Y xₙ yₙ yₐ)
--  := by
--  rw [Set.MapsTo]
--  intro xy
--  intro inSet
--  apply Set.mem_setOf.mpr
--  use xy.fst
--  use xy.snd

--  theorem left_inva_a {xₙ yₙ yₐ : Int} : 0<yₐ → 0≤xₙ → xₙ≤yₐ →
--   Set.LeftInvOn (a_inv yₐ) (a yₐ) (X xₙ yₙ) := by
--   intro h1
--   intro h2
--   intro h3
--   rw [Set.LeftInvOn]
--   intro xy
--   intro xyInSet
--   exact a_inv_a_set h1 h2 h3 xyInSet

-- theorem right_inva_a {xₙ yₙ yₐ : Int} : Set.RightInvOn (a_inv yₐ) (a yₐ) (Y xₙ yₙ yₐ) := by
--   rw [Set.RightInvOn]
--   intro xy
--   intro _
--   exact a_a_inv

-- theorem hf : Set.SurjOn (a yₐ) (X xₙ yₙ) (Y xₙ yₙ yₐ) := by
--   rw [Set.SurjOn]
--   intro a
--   intro xInY
--   apply Set.mem_setOf.mpr
--   apply Set.mem_setOf.mp at xInY
--   cases' xInY with x xInY
--   cases' xInY with y xInY
--   cases' xInY with left right
--   use ⟨x,y⟩

-- theorem a_inv_maps_to {xₙ yₙ yₐ : Int} : 0<yₐ → 0≤xₙ → xₙ≤yₐ →
--  Set.MapsTo (a_inv yₐ) (Y xₙ yₙ yₐ) (X xₙ yₙ)
--  := by
--  intro h1
--  intro h2
--  intro h3
--  exact Set.LeftInvOn.mapsTo (left_inva_a h1 h2 h3) hf

-- theorem a_is_bijection {xₙ yₙ yₐ : Int} : 0<yₐ → 0≤xₙ → xₙ≤yₐ →
--   Set.BijOn (a yₐ) (X xₙ yₙ) (Y xₙ yₙ yₐ) := by
--   intro h1
--   intro h2
--   intro h3
--   have h4 : Set.InvOn (a_inv yₐ) (a yₐ) (X xₙ yₙ) (Y xₙ yₙ yₐ) := by exact ⟨left_inva_a h1 h2 h3, right_inva_a⟩
--   exact Set.InvOn.bijOn h4 a_maps_to (a_inv_maps_to h1 h2 h3)
