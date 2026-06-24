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

/-- Right-associated interval sum, chosen to make enclosure proofs simple. -/
def midDISum : List DI → DI
  | [] => DI.zero
  | I :: Is => I.add (midDISum Is)

theorem midDISum_mem {α : Type} (xs : List α) (f : α → ℚ) (g : α → DI)
    (h : ∀ x ∈ xs, DI.mem (f x) (g x)) :
    DI.mem ((xs.map f).sum) (midDISum (xs.map g)) := by
  induction xs with
  | nil =>
      simpa [midDISum] using DI.mem_zero
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, midDISum]
      exact DI.mem_add (h x (by simp))
        (ih fun y hy => h y (by simp [hy]))

private theorem list_sum_map_mul_left {α : Type} (xs : List α) (c : ℚ)
    (f : α → ℚ) :
    ((xs.map fun x => c * f x).sum) = c * (xs.map f).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring

private theorem getD_range_map_toArray {α : Type} (fallback : α)
    (f : Nat → α) (n i : Nat) (hi : i < n) :
    (((List.range n).map f).toArray.getD i fallback) = f i := by
  simp [Array.getD_eq_getD_getElem?, hi]

private theorem getD_push_lt {α : Type} (T : Array α) (x fallback : α) (i : Nat)
    (h : i < T.size) :
    (T.push x).getD i fallback = T.getD i fallback := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, Nat.ne_of_lt h]

private theorem getD_push_size {α : Type} (T : Array α) (x fallback : α) (i : Nat)
    (h : i = T.size) :
    (T.push x).getD i fallback = x := by
  subst h
  simp [Array.getD_eq_getD_getElem?]

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
      let s : DI := midDISum (((List.range (r - 1)).map fun j : Nat =>
        let k := j + 1
        DI.nsmul k ((midRMatrixGet R k r).mul (T.getD (r - k) DI.zero))))
      let scaled := (DI.nsmul N s).divNat r
      T.push ((DI.exact 1).neg.add scaled.neg)

theorem midXTab_size (D : Array ℚ) (N : Nat) :
    ∀ n, (midXTab D N n).size = n + 1
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      show ((midXTab D N (n + 1)).push _).size = _
      rw [Array.size_push, midXTab_size D N (n + 1)]

theorem midXIntervalTab_size (R : Array (Array DI)) (N : Nat) :
    ∀ n, (midXIntervalTab R N n).size = n + 1
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      show ((midXIntervalTab R N (n + 1)).push _).size = _
      rw [Array.size_push, midXIntervalTab_size R N (n + 1)]

private theorem midXStepSum_mem (D : Array ℚ) (a N r : Nat) (hr : r ≤ a)
    (hprev : ∀ i, i ≤ r - 1 →
      DI.mem ((midXTab D N (r - 1)).getD i 0)
        ((midXIntervalTab (midRMatrix D a) N (r - 1)).getD i DI.zero)) :
    DI.mem (((List.range (r - 1)).map fun j : Nat =>
      let k := j + 1
      (k : ℚ) * midRTab D k r * (midXTab D N (r - 1)).getD (r - k) 0).sum)
      (midDISum (((List.range (r - 1)).map fun j : Nat =>
        let k := j + 1
        DI.nsmul k ((midRMatrixGet (midRMatrix D a) k r).mul
          ((midXIntervalTab (midRMatrix D a) N (r - 1)).getD (r - k) DI.zero))))) := by
  refine midDISum_mem _ _ _ ?_
  intro j hj
  have hjlt : j < r - 1 := List.mem_range.mp hj
  let k := j + 1
  have hkr : k < r := by omega
  have hka : k ≤ a := by omega
  have hrka : r - k ≤ r - 1 := by omega
  have hR := midRMatrixGet_mem D a k r hka hr
  have hX := hprev (r - k) hrka
  have hterm := DI.mem_nsmul k (DI.mem_mul hR hX)
  simpa [k, mul_assoc] using hterm

theorem midXIntervalTab_mem (D : Array ℚ) (a N : Nat) :
    ∀ n i, n ≤ a → i ≤ n →
      DI.mem ((midXTab D N n).getD i 0)
        ((midXIntervalTab (midRMatrix D a) N n).getD i DI.zero)
  | 0, i, _hn, hi => by
      have hi0 : i = 0 := by omega
      subst hi0
      simpa [midXTab, midXIntervalTab] using DI.mem_zero
  | 1, i, _hn, hi => by
      interval_cases i
      · simpa [midXTab, midXIntervalTab] using DI.mem_zero
      · simpa [midXTab, midXIntervalTab] using DI.mem_neg (DI.mem_exact 1)
  | n + 2, i, hn, hi => by
      let r := n + 2
      by_cases hlt : i < r
      · have hrec := midXIntervalTab_mem D a N (n + 1) i (by omega) (by omega)
        change DI.mem (((midXTab D N (n + 1)).push _).getD i 0)
          (((midXIntervalTab (midRMatrix D a) N (n + 1)).push _).getD i DI.zero)
        rw [getD_push_lt _ _ _ _ (by rw [midXTab_size]; omega),
          getD_push_lt _ _ _ _ (by rw [midXIntervalTab_size]; omega)]
        exact hrec
      · have hi_eq : i = r := by omega
        subst i
        let sexact : ℚ := ((List.range (r - 1)).map fun j : Nat =>
          let k := j + 1
          (k : ℚ) * midRTab D k r * (midXTab D N (r - 1)).getD (r - k) 0).sum
        let sint : DI := midDISum (((List.range (r - 1)).map fun j : Nat =>
          let k := j + 1
          DI.nsmul k ((midRMatrixGet (midRMatrix D a) k r).mul
            ((midXIntervalTab (midRMatrix D a) N (r - 1)).getD (r - k) DI.zero))))
        change DI.mem
          (((midXTab D N (n + 1)).push (-1 - ((N : ℚ) / (r : ℚ)) * sexact)).getD r 0)
          (((midXIntervalTab (midRMatrix D a) N (n + 1)).push
            ((DI.exact 1).neg.add (((DI.nsmul N sint).divNat r).neg))).getD r DI.zero)
        rw [getD_push_size _ _ _ _ (by rw [midXTab_size]),
          getD_push_size _ _ _ _ (by rw [midXIntervalTab_size])]
        have hs : DI.mem sexact sint := by
          dsimp [sexact, sint]
          exact midXStepSum_mem D a N r (by omega) (fun idx hidx =>
            midXIntervalTab_mem D a N (r - 1) idx (by omega) hidx)
        have hscaled0 :
            DI.mem (((N : ℚ) * sexact) / (r : ℚ)) ((DI.nsmul N sint).divNat r) :=
          DI.mem_divNat r (by omega) (DI.mem_nsmul N hs)
        have hscaled :
            DI.mem (((N : ℚ) / (r : ℚ)) * sexact) ((DI.nsmul N sint).divNat r) := by
          convert hscaled0 using 1
          ring
        have hone : DI.mem (-1 : ℚ) (DI.exact 1).neg := by
          simpa using DI.mem_neg (DI.mem_exact 1)
        have hadd := DI.mem_add hone (DI.mem_neg hscaled)
        convert hadd using 1
        ring

/-- Interval enclosure of the normalized upper bound `U_a(N)/(N c_a)`. -/
def midUNormIntervalWithRows (R : Array (Array DI)) (S : Array DI)
    (a N : Nat) : DI :=
  let m := M a
  let X := midXIntervalTab R N a
  let tail : DI := midDISum (((List.range (a - 1)).map fun j : Nat =>
    let k := j + 1
    let s := a - k
    DI.nsmul m
      ((((midRMatrixGet R k a).mul (midDIPowTwoInv s)).mul
          (midDINegPart (X.getD k DI.zero))).mul
        (S.getD s DI.zero))))
  (X.getD a DI.zero).add tail

private theorem midUTailSum_mem (D Y : Array ℚ) (a N : Nat) :
    DI.mem (((List.range (a - 1)).map fun j : Nat =>
      let k := j + 1
      (M a : ℚ) *
        (((midRTab D k a * (1 / (2 : ℚ) ^ (a - k))) *
          midNegPart ((midXTab D N a).getD k 0)) *
          midSTab D Y (M a) (a - k))).sum)
      (midDISum (((List.range (a - 1)).map fun j : Nat =>
        let k := j + 1
        let s := a - k
        DI.nsmul (M a)
          ((((midRMatrixGet (midRMatrix D a) k a).mul (midDIPowTwoInv s)).mul
              (midDINegPart ((midXIntervalTab (midRMatrix D a) N a).getD k DI.zero))).mul
            ((midSIntervals D Y a).getD s DI.zero))))) := by
  refine midDISum_mem _ _ _ ?_
  intro j hj
  have hjlt : j < a - 1 := List.mem_range.mp hj
  let k := j + 1
  let s := a - k
  have hka : k ≤ a := by omega
  have hsa : s ≤ a := by omega
  have hR := midRMatrixGet_mem D a k a hka le_rfl
  have h2 := midDIPowTwoInv_mem s
  have hX := midXIntervalTab_mem D a N a k le_rfl hka
  have hNeg := midDINegPart_mem hX
  have hS := midSIntervals_mem D Y a s hsa
  have hprod := DI.mem_mul (DI.mem_mul (DI.mem_mul hR h2) hNeg) hS
  have hterm := DI.mem_nsmul (M a) hprod
  simpa [k, s, mul_assoc] using hterm

theorem midUNormIntervalWithRows_mem (D Y : Array ℚ) (a N : Nat) :
    DI.mem (midUNormWithTabs D Y a N)
      (midUNormIntervalWithRows (midRMatrix D a) (midSIntervals D Y a) a N) := by
  unfold midUNormWithTabs midUNormIntervalWithRows
  let X := midXTab D N a
  let XI := midXIntervalTab (midRMatrix D a) N a
  let base : List ℚ := (List.range (a - 1)).map fun j : Nat =>
    let k := j + 1
    midRTab D k a * (1 / (2 : ℚ) ^ (a - k)) *
      midNegPart (X.getD k 0) * midSTab D Y (M a) (a - k)
  let scaled : List ℚ := (List.range (a - 1)).map fun j : Nat =>
    let k := j + 1
    (M a : ℚ) *
      (((midRTab D k a * (1 / (2 : ℚ) ^ (a - k))) *
        midNegPart (X.getD k 0)) * midSTab D Y (M a) (a - k))
  let tailI : DI := midDISum (((List.range (a - 1)).map fun j : Nat =>
    let k := j + 1
    let s := a - k
    DI.nsmul (M a)
      ((((midRMatrixGet (midRMatrix D a) k a).mul (midDIPowTwoInv s)).mul
          (midDINegPart (XI.getD k DI.zero))).mul
        ((midSIntervals D Y a).getD s DI.zero))))
  change DI.mem (X.getD a 0 + (M a : ℚ) * base.sum) ((XI.getD a DI.zero).add tailI)
  have hx : DI.mem (X.getD a 0) (XI.getD a DI.zero) := by
    dsimp [X, XI]
    exact midXIntervalTab_mem D a N a a le_rfl le_rfl
  have htail : DI.mem scaled.sum tailI := by
    dsimp [scaled, X, XI, tailI]
    exact midUTailSum_mem D Y a N
  have hscaled : scaled.sum = (M a : ℚ) * base.sum := by
    dsimp [scaled, base]
    rw [list_sum_map_mul_left]
  rw [← hscaled]
  exact DI.mem_add hx htail

theorem midUNormFast_neg_of_interval (a N : Nat)
    (h :
      let m := M a
      let D := midDTab a
      let Y := midYTab D m a
      midDINeg (midUNormIntervalWithRows (midRMatrix D a) (midSIntervals D Y a) a N) = true) :
    midUNormFast a N < 0 := by
  unfold midUNormFast
  let m := M a
  let D := midDTab a
  let Y := midYTab D m a
  exact midDINeg_sound (midUNormIntervalWithRows_mem D Y a N) h

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

theorem midUNormFast_neg_of_rowInterval (a i : Nat)
    (hcheck : checkPrintedMidRowInterval a = true) (hi : i < M a) :
    midUNormFast a (M a + 1 + i) < 0 := by
  unfold checkPrintedMidRowInterval at hcheck
  dsimp only at hcheck
  have himem : i ∈ List.range (M a) := List.mem_range.mpr hi
  have hentry := List.all_eq_true.mp hcheck i himem
  exact midUNormFast_neg_of_interval a (M a + 1 + i) hentry

theorem midUNormFast_neg_of_rowIntervalSlice (a start len i : Nat)
    (hcheck : checkPrintedMidRowIntervalSlice a start len = true)
    (hlo : start ≤ i) (hhi : i < start + len) (him : i < M a) :
    midUNormFast a (M a + 1 + i) < 0 := by
  unfold checkPrintedMidRowIntervalSlice at hcheck
  dsimp only at hcheck
  have hjmem : i - start ∈ List.range len := List.mem_range.mpr (by omega)
  have hentry := List.all_eq_true.mp hcheck (i - start) hjmem
  have hidx : start + (i - start) = i := by omega
  rw [hidx, if_pos him] at hentry
  exact midUNormFast_neg_of_interval a (M a + 1 + i) hentry

theorem checkPrintedMidRowInterval_14 :
    checkPrintedMidRowInterval 14 = true := by
  native_decide

theorem midUNormFast_neg_row14 (i : Nat) (hi : i < M 14) :
    midUNormFast 14 (M 14 + 1 + i) < 0 :=
  midUNormFast_neg_of_rowInterval 14 i checkPrintedMidRowInterval_14 hi

theorem checkPrintedMidRowIntervalSlice_149_0_100 :
    checkPrintedMidRowIntervalSlice 149 0 100 = true := by
  native_decide

theorem midUNormFast_neg_row149_slice_0_100 (i : Nat)
    (hi : i < 100) (him : i < M 149) :
    midUNormFast 149 (M 149 + 1 + i) < 0 :=
  midUNormFast_neg_of_rowIntervalSlice 149 0 100 i
    checkPrintedMidRowIntervalSlice_149_0_100 (by omega) (by omega) him

end Prop52
