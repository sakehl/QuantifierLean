-- open Nat (succ)

namespace Int

theorem ediv_nonneg_of_nonpos_of_nonpos {a b : Int} (Ha : a ≤ 0) (Hb : b ≤ 0) : 0 ≤ a / b := by
  match a, b with
  | ofNat a, b =>
    match Int.le_antisymm Ha (ofNat_zero_le a) with
    | h1 =>
    rw [h1, zero_ediv,]
    exact Int.le_refl 0
  | a, ofNat b =>
    match Int.le_antisymm Hb (ofNat_zero_le  b) with
    | h1 =>
    rw [h1, Int.ediv_zero]
    exact Int.le_refl 0
  | negSucc a, negSucc b =>
    rw [Int.div_def, ediv]
    have le_succ {a: Int} : a ≤ a+1 := (le_add_one (Int.le_refl a))
    have h2: 0 ≤ ((↑b:Int) + 1) := Int.le_trans (ofNat_zero_le b) le_succ
    have h3: (0:Int) ≤ ↑a / (↑b + 1) := (ediv_nonneg (ofNat_zero_le a) h2)
    exact Int.le_trans h3 le_succ
