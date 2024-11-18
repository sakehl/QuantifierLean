import Mathlib.Tactic
import Mathlib.Data.Vector.Zip

open Mathlib


lemma Vector.drop_tail {a: Vector Int (k+1)}:
  Vector.drop (i+1) a = (Vector.drop (i) a.tail).congr (Nat.add_comm 1 i ▸ Nat.sub_sub (k+1) 1 i) := by
  match a with | ⟨_::_, _⟩ => rfl

lemma congr_zipWith {f : α → β → γ} {a: Mathlib.Vector α n} {x: Mathlib.Vector β n} (h : n = m) :
    Vector.zipWith f (a.congr h) (x.congr h) = (Vector.zipWith f a x).congr h := by
  subst h
  rfl

lemma Vector.congr_arg (f: ∀ k, Mathlib.Vector α k → β) (v : Mathlib.Vector α n) (h : n = m) :
    f m (v.congr h) = f n v := by
  subst h
  rfl

lemma Vector.congr_arg₂ (f: ∀ k₁ k₂, Mathlib.Vector α₁ k₁ → Mathlib.Vector α₂ k₂ → β)
  (v₁ : Mathlib.Vector α₁ n₁) (v₂ : Mathlib.Vector α₂ n₂) (h₁ : n₁ = m₁) (h : n₂ = m₂) :
    f m₁ m₂ (v₁.congr h₁) (v₂.congr h₂) = f n₁ n₂ v₁ v₂ := by
  subst h₁
  subst h₂
  rfl

lemma Vector.congr_arg₃
  (f: ∀ k₁ k₂ k₃, Mathlib.Vector α₁ k₁ → Mathlib.Vector α₂ k₂ → Mathlib.Vector α₃ k₃ → β)
  (v₁ : Mathlib.Vector α₁ n₁) (v₂ : Mathlib.Vector α₂ n₂) (v₃ : Mathlib.Vector α₃ n₃)
  (h₁ : n₁ = m₁) (h : n₂ = m₂) :
    f m₁ m₂ m₃ (v₁.congr h₁) (v₂.congr h₂) (v₃.congr h₃) = f n₁ n₂ n₃ v₁ v₂ v₃ := by
  subst h₁
  subst h₂
  subst h₃
  rfl

-- lemma apply_congr (a: Vector Int (k+1)):
--   vector_sum (Vector.drop (i+1) a) = vector_sum (Vector.drop (i) a.tail) := by
--   rw [vector_drop_tail]
--   simp

-- def shiftRightFill (v : Vector α n) (i : ℕ) (fill : α) : Vector α n :=
--   Vector.congr (by omega) <|
--    Vector.append (Vector.replicate (min n i) fill) (Vector.take (n - i) v)

-- lemma mul_bound (h: a<b) (h1: 0 < a) (h2: 0<b): a*((b+a-1) / a) ≤ b := by
--   cases b
--   case zero =>
--     omega
--   case succ b =>
--     induction b
--     case zero =>
--       simp_all
--       -- simp_all
--     case succ b ih =>
--       simp_all
--       match a with
--       | 0 => simp_all
--       | 1 => simp_all
--       | a+1+1 =>
--         match b with
--         | 0 => simp_all; omega
--         | 1 =>
--           simp_all;
--           match a with
--           | 0 => simp_all; omega
--           | a+1 =>
--             contrapose h
--             simp
--         | b+1+1 => sorry
--         -- omega



--       --   omega
