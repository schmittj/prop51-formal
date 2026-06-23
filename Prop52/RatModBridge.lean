/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Denominator-aware rational-to-modular bridge

Casting rationals into `ZMod p` is not a ring homomorphism in characteristic
`p`: denominators divisible by `p` collapse.  The finite Prop52 certificates use
the large prime `finitePrime1`, and all relevant finite-range denominators are
prime to it.  This file records local arithmetic lemmas under the corresponding
denominator side condition.
-/

import Prop52.ModularNatBridge
import Mathlib.Data.List.Infix

namespace Prop52

/-- A rational number whose normalized denominator is nonzero modulo the
certificate prime. -/
def RatGood (q : ℚ) : Prop :=
  ((q.den : Nat) : ZMod finitePrime1) ≠ 0

theorem RatGood_natCast (n : Nat) : RatGood (n : ℚ) := by
  unfold RatGood
  simp

theorem RatGood_neg {q : ℚ} (hq : RatGood q) : RatGood (-q) := by
  simpa [RatGood]

theorem ratCast_neg (q : ℚ) :
    (((-q : ℚ) : ZMod finitePrime1) = -(q : ZMod finitePrime1)) := by
  rw [Rat.cast_def, Rat.cast_def]
  simp [div_eq_mul_inv]

theorem ratCast_mul_of_good
    (x y : ℚ) (_hx : RatGood x) (_hy : RatGood y) (hxy : RatGood (x * y)) :
    (((x * y : ℚ) : ZMod finitePrime1) =
      (x : ZMod finitePrime1) * (y : ZMod finitePrime1)) := by
  rw [Rat.cast_def, Rat.cast_def, Rat.cast_def]
  unfold RatGood at _hx _hy hxy
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  have h := Rat.mul_num_den' x y
  have hz :
      ((x * y).num : ZMod finitePrime1) * (x.den : ZMod finitePrime1) *
          (y.den : ZMod finitePrime1) =
        (x.num : ZMod finitePrime1) * (y.num : ZMod finitePrime1) *
          ((x * y).den : ZMod finitePrime1) := by
    have hz0 := congrArg (fun z : ℤ => (z : ZMod finitePrime1)) h
    norm_num at hz0
    simpa using hz0
  field_simp [_hx, _hy, hxy] at hz ⊢
  simpa [mul_assoc, mul_comm, mul_left_comm] using hz

theorem ratCast_add_of_good
    (x y : ℚ) (_hx : RatGood x) (_hy : RatGood y) (hxy : RatGood (x + y)) :
    (((x + y : ℚ) : ZMod finitePrime1) =
      (x : ZMod finitePrime1) + (y : ZMod finitePrime1)) := by
  rw [Rat.cast_def, Rat.cast_def, Rat.cast_def]
  unfold RatGood at _hx _hy hxy
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  have h := Rat.add_num_den' x y
  have hz :
      ((x + y).num : ZMod finitePrime1) * (x.den : ZMod finitePrime1) *
          (y.den : ZMod finitePrime1) =
        (((x.num : ZMod finitePrime1) * (y.den : ZMod finitePrime1) +
            (y.num : ZMod finitePrime1) * (x.den : ZMod finitePrime1)) *
          ((x + y).den : ZMod finitePrime1)) := by
    have hz0 := congrArg (fun z : ℤ => (z : ZMod finitePrime1)) h
    norm_num at hz0
    simpa [add_comm, add_left_comm, add_assoc, mul_assoc, mul_comm, mul_left_comm] using hz0
  field_simp [_hx, _hy, hxy] at hz ⊢
  simpa [mul_assoc, mul_comm, mul_left_comm, add_comm, add_left_comm, add_assoc] using hz

theorem ratCast_sub_of_good
    (x y : ℚ) (_hx : RatGood x) (_hy : RatGood y) (hxy : RatGood (x - y)) :
    (((x - y : ℚ) : ZMod finitePrime1) =
      (x : ZMod finitePrime1) - (y : ZMod finitePrime1)) := by
  rw [Rat.cast_def, Rat.cast_def, Rat.cast_def]
  unfold RatGood at _hx _hy hxy
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  have h := Rat.substr_num_den' x y
  have hz :
      ((x - y).num : ZMod finitePrime1) * (x.den : ZMod finitePrime1) *
          (y.den : ZMod finitePrime1) =
        (((x.num : ZMod finitePrime1) * (y.den : ZMod finitePrime1) -
            (y.num : ZMod finitePrime1) * (x.den : ZMod finitePrime1)) *
          ((x - y).den : ZMod finitePrime1)) := by
    have hz0 := congrArg (fun z : ℤ => (z : ZMod finitePrime1)) h
    norm_num at hz0
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      mul_assoc, mul_comm, mul_left_comm] using hz0
  field_simp [_hx, _hy, hxy] at hz ⊢
  simpa [sub_eq_add_neg, mul_assoc, mul_comm, mul_left_comm,
    add_comm, add_left_comm, add_assoc] using hz

theorem RatGood_list_sum_of_pairwise
    (xs : List ℚ)
    (hgood : ∀ ys : List ℚ, List.Sublist ys xs → RatGood ys.sum) :
    RatGood xs.sum :=
  hgood xs (List.Sublist.refl xs)

theorem ratCast_list_sum_of_good
    (xs : List ℚ)
    (hgood : ∀ ys : List ℚ, List.Sublist ys xs → RatGood ys.sum) :
    (((xs.sum : ℚ) : ZMod finitePrime1) =
      (xs.map fun x => (x : ZMod finitePrime1)).sum) := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : RatGood x := by
        simpa using hgood [x] (by simp)
      have hxs : ∀ ys : List ℚ, List.Sublist ys xs → RatGood ys.sum := by
        intro ys hys
        exact hgood ys (hys.trans (List.sublist_cons_self x xs))
      have hsum_xs : RatGood xs.sum := hxs xs (List.Sublist.refl xs)
      have hsum_all : RatGood (x + xs.sum) := by
        simpa [List.sum_cons] using hgood (x :: xs) (List.Sublist.refl (x :: xs))
      simp only [List.sum_cons]
      rw [ratCast_add_of_good x xs.sum hx hsum_xs hsum_all, ih hxs]
      rfl

/-! ## Finite-range denominator certificates -/

theorem finitePrime1_RatGood_c (r : Nat) (hr : r ≤ 13) :
    RatGood (Prop51.c r) := by
  unfold RatGood
  interval_cases r <;> native_decide

theorem finitePrime1_RatGood_invPow (q r : Nat) (hq : q ≤ 73) (hr : r ≤ 13) :
    RatGood (1 / ((q : ℚ)^r)) := by
  unfold RatGood
  interval_cases q <;> interval_cases r <;> native_decide

theorem finitePrime1_RatGood_sPower_summand
    (mi r : Nat) (hmi : mi + 1 ≤ 73) (hr : r ≤ 13) :
    RatGood (1 / (((mi + 1 : Nat) : ℚ)^r)) :=
  finitePrime1_RatGood_invPow (mi + 1) r hmi hr

theorem finitePrime1_RatGood_markedWeight_summand
    (mi r : Nat) (hmi : mi + 1 ≤ 73) (hr : r ≤ 13) :
    RatGood ((mi : ℚ) / (((mi + 1 : Nat) : ℚ)^r)) := by
  unfold RatGood
  have hq : mi ≤ 72 := by omega
  interval_cases mi <;> interval_cases r <;> native_decide

theorem finitePrime1_ratCast_invPow
    (q r : Nat) (hq : q ≤ 73) (hr : r ≤ 13) :
    (((1 / ((q : ℚ)^r) : ℚ) : ZMod finitePrime1) =
      1 / ((q : ZMod finitePrime1)^r)) := by
  interval_cases q <;> interval_cases r <;> native_decide

theorem finitePrime1_ratCast_sPower_summand
    (mi r : Nat) (hmi : mi + 1 ≤ 73) (hr : r ≤ 13) :
    (((1 / (((mi + 1 : Nat) : ℚ)^r) : ℚ) : ZMod finitePrime1) =
      1 / ((((mi + 1 : Nat) : ZMod finitePrime1)^r))) := by
  exact finitePrime1_ratCast_invPow (mi + 1) r hmi hr

theorem finitePrime1_ratCast_markedWeight_summand
    (mi r : Nat) (hmi : mi + 1 ≤ 73) (hr : r ≤ 13) :
    ((((mi : ℚ) / (((mi + 1 : Nat) : ℚ)^r) : ℚ) : ZMod finitePrime1) =
      (mi : ZMod finitePrime1) / ((((mi + 1 : Nat) : ZMod finitePrime1)^r))) := by
  have hq : mi ≤ 72 := by omega
  interval_cases mi <;> interval_cases r <;> native_decide

theorem finitePrime1_ratCast_sPower_of_good
    (a : Nat) (μ : List Nat) (r : Nat)
    (ha : a ≤ 13) (hμsum : μ.sum = M a) (hr : r ≤ a)
    (hgood : ∀ ys : List ℚ,
      List.Sublist ys (μ.map fun mi : Nat => 1 / (((mi + 1 : Nat) : ℚ)^r)) →
        RatGood ys.sum) :
    (((sPower μ r : ℚ) : ZMod finitePrime1) = sPowerMod finitePrime1 μ r) := by
  unfold sPower sPowerMod
  rw [ratCast_list_sum_of_good _ hgood]
  let fQ : Nat → ℚ := fun mi => 1 / (((mi + 1 : Nat) : ℚ)^r)
  let fZ : Nat → ZMod finitePrime1 :=
    fun mi => 1 / (((mi + 1 : Nat) : ZMod finitePrime1)^r)
  refine congrArg (fun xs : List (ZMod finitePrime1) => xs.sum) ?_
  simpa [fQ, fZ, List.map_eq_flatMap, List.flatMap_assoc] using
    (List.map_congr_left fun mi hmi => by
      have hq : mi + 1 ≤ 73 := by
        exact le_trans
          (Nat.add_le_add_right (by simpa [hμsum] using le_sum_of_mem hmi) 1)
          (M_add_one_le_73_of_le_13 ha)
      simpa [div_eq_mul_inv] using
        finitePrime1_ratCast_sPower_summand mi r hq (le_trans hr ha))

theorem finitePrime1_ratCast_markedWeight_of_good
    (a : Nat) (μ : List Nat) (r : Nat)
    (ha : a ≤ 13) (hμsum : μ.sum = M a) (hr : r ≤ a)
    (hgood : ∀ ys : List ℚ,
      List.Sublist ys
        (μ.map fun mi : Nat => (mi : ℚ) / (((mi + 1 : Nat) : ℚ)^r)) →
        RatGood ys.sum) :
    (((markedWeight μ r : ℚ) : ZMod finitePrime1) =
      markedWeightMod finitePrime1 μ r) := by
  unfold markedWeight markedWeightMod
  rw [ratCast_list_sum_of_good _ hgood]
  let fQ : Nat → ℚ := fun mi => (mi : ℚ) / (((mi + 1 : Nat) : ℚ)^r)
  let fZ : Nat → ZMod finitePrime1 :=
    fun mi => (mi : ZMod finitePrime1) / (((mi + 1 : Nat) : ZMod finitePrime1)^r)
  refine congrArg (fun xs : List (ZMod finitePrime1) => xs.sum) ?_
  simpa [fQ, fZ, List.map_eq_flatMap, List.flatMap_assoc] using
    (List.map_congr_left fun mi hmi => by
      have hq : mi + 1 ≤ 73 := by
        exact le_trans
          (Nat.add_le_add_right (by simpa [hμsum] using le_sum_of_mem hmi) 1)
          (M_add_one_le_73_of_le_13 ha)
      simpa [div_eq_mul_inv] using
        finitePrime1_ratCast_markedWeight_summand mi r hq (le_trans hr ha))

theorem finitePrime1_ratCast_hCoeff_of_good
    (a : Nat) (μ : List Nat) (r : Nat)
    (ha : a ≤ 13) (hμsum : μ.sum = M a) (hr : r ≤ a)
    (hsPowerGood : ∀ ys : List ℚ,
      List.Sublist ys (μ.map fun mi : Nat => 1 / (((mi + 1 : Nat) : ℚ)^r)) →
        RatGood ys.sum)
    (hDiffGood : RatGood ((N μ : ℚ) - sPower μ r))
    (hCoeffGood : RatGood (hCoeff μ r)) :
    (((hCoeff μ r : ℚ) : ZMod finitePrime1) = hCoeffMod finitePrime1 μ r) := by
  unfold hCoeff hCoeffMod
  rw [ratCast_mul_of_good (Prop51.c r) ((N μ : ℚ) - sPower μ r)
    (finitePrime1_RatGood_c r (le_trans hr ha)) hDiffGood hCoeffGood]
  rw [ratCast_sub_of_good (N μ : ℚ) (sPower μ r)
    (RatGood_natCast (N μ)) (RatGood_list_sum_of_pairwise _ hsPowerGood) hDiffGood]
  rw [finitePrime1_ratCast_sPower_of_good a μ r ha hμsum hr hsPowerGood]
  simp

end Prop52
