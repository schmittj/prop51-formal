/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Dyadic interval checker for the Prop52 mid-range certificate

This module is the executable interval companion to `Prop52.Mid`.  It keeps
the exact row constants `R_{k,r}` and `S_r` from that module, converts them to
dyadic intervals, and performs the expensive sweep over `X_r(N)` by outward
rounded interval arithmetic.

The soundness theorem connecting this checker to `PrintedCoeffNegativityMid`
is intentionally left to the next layer.  The definitions are arranged to
match the `Prop51.IntervalCert` style: an executable Boolean checker first,
then a separate proof that each interval table encloses the exact rational
quantity it names.
-/

import Prop52.Mid
import Prop51.Dyadic
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

namespace Prop52

open Prop51

/-! ## Exact rational constants as dyadic intervals -/

/-- Exact singleton interval for an integer. -/
def midDIOfInt (z : Int) : DI :=
  if z < 0 then
    (DI.exact z.natAbs).neg
  else
    DI.exact z.toNat

/--
Dyadic enclosure of a rational number, obtained by outward-rounded division
of the exact integer numerator by the positive natural denominator.
-/
def midDIOfRat (q : ℚ) : DI :=
  (midDIOfInt q.num).divNat q.den

/-- The interval `[1/2^k, 1/2^k]`. -/
def midDIPowTwoInv (k : Nat) : DI :=
  DI.shr k DI.one

/-- Boolean test that an interval is strictly below zero. -/
def midDINeg (I : DI) : Bool :=
  I.hi.m < 0

/-- The convex interval hull of `max(-x,0)` for `x` enclosed by `I`. -/
def midDINegPart (I : DI) : DI :=
  (DI.neg I).hull0

theorem midDIOfInt_mem (z : Int) :
    DI.mem (z : ℚ) (midDIOfInt z) := by
  unfold midDIOfInt
  by_cases hz : z < 0
  · rw [if_pos hz]
    have hmem := DI.mem_neg (DI.mem_exact z.natAbs)
    have hzabs : (z : ℚ) = -((z.natAbs : Nat) : ℚ) := by
      rcases Int.natAbs_eq z with h | h
      · have hnonneg : (0 : ℤ) ≤ z := by omega
        omega
      · exact_mod_cast h
    rw [hzabs]
    exact hmem
  · rw [if_neg hz]
    have hnonneg : (0 : ℤ) ≤ z := by omega
    have hzto : ((z.toNat : Nat) : ℤ) = z := Int.toNat_of_nonneg hnonneg
    have hmem := DI.mem_exact z.toNat
    have hzcast : ((z.toNat : Nat) : ℚ) = (z : ℚ) := by exact_mod_cast hzto
    rw [← hzcast]
    exact hmem

theorem midDIOfRat_mem (q : ℚ) :
    DI.mem q (midDIOfRat q) := by
  unfold midDIOfRat
  have hq : ((q.num : ℚ) / (q.den : ℚ)) = q := by
    change ((q.num : ℚ) / (((q.den : Nat) : Int) : ℚ)) = q
    rw [Rat.intCast_div_eq_divInt, Rat.num_divInt_den]
  have hmem := DI.mem_divNat q.den q.den_pos (midDIOfInt_mem q.num)
  simpa [hq] using hmem

theorem midDIPowTwoInv_mem (k : Nat) :
    DI.mem (1 / (2 : ℚ)^k) (midDIPowTwoInv k) := by
  unfold midDIPowTwoInv
  simpa using DI.mem_shr k DI.mem_one

theorem midDINegPart_mem {x : ℚ} {I : DI} (hx : DI.mem x I) :
    DI.mem (midNegPart x) (midDINegPart I) := by
  unfold midNegPart midDINegPart
  by_cases hneg : x < 0
  · rw [if_pos hneg]
    exact DI.mem_hull0_of_mem (DI.mem_neg hx)
  · rw [if_neg hneg]
    exact DI.zero_mem_hull0 (DI.neg I)

theorem midDINeg_sound {x : ℚ} {I : DI}
    (hx : DI.mem x I) (hI : midDINeg I = true) :
    x < 0 := by
  unfold midDINeg at hI
  have hhi : I.hi.m < 0 := of_decide_eq_true hI
  exact lt_of_le_of_lt hx.2 (DF.val_neg_of_m_neg hhi)

private theorem getD_range_map_toArray {α : Type} (fallback : α)
    (f : Nat → α) (n i : Nat) (hi : i < n) :
    (((List.range n).map f).toArray.getD i fallback) = f i := by
  simp [Array.getD_eq_getD_getElem?, hi]

/-! ## Precomputed row constants -/

/-- Matrix of dyadic enclosures for `R_{k,r}`, indexed by row `r` then `k`. -/
def midRMatrix (D : Array ℚ) (a : Nat) : Array (Array DI) :=
  ((List.range (a + 1)).map fun r : Nat =>
    ((List.range (a + 1)).map fun k : Nat =>
      midDIOfRat (midRTab D k r)).toArray).toArray

/-- Lookup in a matrix produced by `midRMatrix`. -/
def midRMatrixGet (R : Array (Array DI)) (k r : Nat) : DI :=
  (R.getD r #[]).getD k DI.zero

theorem midRMatrixGet_mem (D : Array ℚ) (a k r : Nat)
    (hk : k ≤ a) (hr : r ≤ a) :
    DI.mem (midRTab D k r) (midRMatrixGet (midRMatrix D a) k r) := by
  unfold midRMatrixGet midRMatrix
  have hrlt : r < a + 1 := by omega
  have hklt : k < a + 1 := by omega
  rw [getD_range_map_toArray #[] (fun r : Nat =>
    ((List.range (a + 1)).map fun k : Nat =>
      midDIOfRat (midRTab D k r)).toArray) (a + 1) r hrlt]
  rw [getD_range_map_toArray DI.zero
    (fun k : Nat => midDIOfRat (midRTab D k r)) (a + 1) k hklt]
  exact midDIOfRat_mem _

/-- Dyadic enclosures of `S_r(M)` for a fixed row. -/
def midSIntervals (D Y : Array ℚ) (a : Nat) : Array DI :=
  let m := M a
  ((List.range (a + 1)).map fun r : Nat =>
    midDIOfRat (midSTab D Y m r)).toArray

theorem midSIntervals_mem (D Y : Array ℚ) (a r : Nat) (hr : r ≤ a) :
    DI.mem (midSTab D Y (M a) r) ((midSIntervals D Y a).getD r DI.zero) := by
  unfold midSIntervals
  have hrlt : r < a + 1 := by omega
  rw [getD_range_map_toArray DI.zero
    (fun r : Nat => midDIOfRat (midSTab D Y (M a) r)) (a + 1) r hrlt]
  exact midDIOfRat_mem _

/-! ## Interval `X` recurrence and row check -/

/-- Interval prefix table for `X_r(N) = B_r(N)/(N c_r)`. -/
def midXIntervalTab (R : Array (Array DI)) (N : Nat) : Nat → Array DI
  | 0 => #[DI.zero]
  | 1 => #[DI.zero, (DI.exact 1).neg]
  | n + 2 =>
      let r := n + 2
      let T := midXIntervalTab R N (r - 1)
      let s : DI := ((List.range (r - 1)).map fun j : Nat =>
        let k := j + 1
        DI.nsmul k ((midRMatrixGet R k r).mul (T.getD (r - k) DI.zero))).foldl
          DI.add DI.zero
      let scaled := (DI.nsmul N s).divNat r
      T.push ((DI.exact 1).neg.add scaled.neg)

/-- Interval enclosure of the normalized upper bound `U_a(N)/(N c_a)`. -/
def midUNormIntervalWithRows (R : Array (Array DI)) (S : Array DI)
    (a N : Nat) : DI :=
  let m := M a
  let X := midXIntervalTab R N a
  let tail : DI := ((List.range (a - 1)).map fun j : Nat =>
    let k := j + 1
    let s := a - k
    DI.nsmul m
      ((((midRMatrixGet R k a).mul (midDIPowTwoInv s)).mul
          (midDINegPart (X.getD k DI.zero))).mul
        (S.getD s DI.zero))).foldl DI.add DI.zero
  (X.getD a DI.zero).add tail

/-- One-row interval check for `M(a)+1 <= N <= 2M(a)`. -/
def checkPrintedMidRowInterval (a : Nat) : Bool :=
  let m := M a
  let D := midDTab a
  let Y := midYTab D m a
  let R := midRMatrix D a
  let S := midSIntervals D Y a
  (List.range m).all fun i : Nat =>
    let N := m + 1 + i
    midDINeg (midUNormIntervalWithRows R S a N)

/--
Slice of one row of the interval check.  The slice variable is the zero-based
offset `i` in `N = M(a)+1+i`.
-/
def checkPrintedMidRowIntervalSlice (a start len : Nat) : Bool :=
  let m := M a
  let D := midDTab a
  let Y := midYTab D m a
  let R := midRMatrix D a
  let S := midSIntervals D Y a
  (List.range len).all fun j : Nat =>
    let i := start + j
    if i < m then
      let N := m + 1 + i
      midDINeg (midUNormIntervalWithRows R S a N)
    else
      true

/-- Consecutive row interval check. -/
def checkPrintedMidRowsInterval (lo len : Nat) : Bool :=
  (List.range len).all fun i : Nat =>
    checkPrintedMidRowInterval (lo + i)

theorem checkPrintedMidRowInterval_14 :
    checkPrintedMidRowInterval 14 = true := by
  native_decide

theorem checkPrintedMidRowIntervalSlice_149_0_100 :
    checkPrintedMidRowIntervalSlice 149 0 100 = true := by
  native_decide

end Prop52
