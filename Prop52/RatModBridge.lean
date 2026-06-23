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
import Prop51.ExpSeries
import Mathlib.Data.List.Infix

namespace Prop52

/-- A rational number whose normalized denominator is nonzero modulo the
certificate prime. -/
def RatGood (q : ℚ) : Prop :=
  ((q.den : Nat) : ZMod finitePrime1) ≠ 0

theorem RatGood_iff_not_dvd (q : ℚ) :
    RatGood q ↔ ¬ finitePrime1 ∣ q.den := by
  unfold RatGood
  exact not_congr (ZMod.natCast_eq_zero_iff q.den finitePrime1)

theorem RatGood_of_den_dvd {q : ℚ} {d : Nat}
    (hdvd : q.den ∣ d) (hd : ¬ finitePrime1 ∣ d) : RatGood q := by
  rw [RatGood_iff_not_dvd]
  intro hp
  exact hd (hp.trans hdvd)

theorem RatGood_mul {x y : ℚ} (hx : RatGood x) (hy : RatGood y) :
    RatGood (x * y) := by
  rw [RatGood_iff_not_dvd] at hx hy
  exact RatGood_of_den_dvd (Rat.mul_den_dvd x y) (by
    intro hdiv
    have hprime : finitePrime1.Prime := by native_decide
    rcases hprime.dvd_mul.mp hdiv with hxdiv | hydiv
    · exact hx hxdiv
    · exact hy hydiv)

theorem RatGood_add {x y : ℚ} (hx : RatGood x) (hy : RatGood y) :
    RatGood (x + y) := by
  rw [RatGood_iff_not_dvd] at hx hy
  exact RatGood_of_den_dvd (Rat.add_den_dvd x y) (by
    intro hdiv
    have hprime : finitePrime1.Prime := by native_decide
    rcases hprime.dvd_mul.mp hdiv with hxdiv | hydiv
    · exact hx hxdiv
    · exact hy hydiv)

theorem RatGood_sub {x y : ℚ} (hx : RatGood x) (hy : RatGood y) :
    RatGood (x - y) := by
  rw [RatGood_iff_not_dvd] at hx hy
  exact RatGood_of_den_dvd (Rat.sub_den_dvd x y) (by
    intro hdiv
    have hprime : finitePrime1.Prime := by native_decide
    rcases hprime.dvd_mul.mp hdiv with hxdiv | hydiv
    · exact hx hxdiv
    · exact hy hydiv)

theorem RatGood_list_sum (xs : List ℚ) (hxs : ∀ x ∈ xs, RatGood x) :
    RatGood xs.sum := by
  induction xs with
  | nil =>
      unfold RatGood
      simp
  | cons x xs ih =>
      simp only [List.sum_cons]
      exact RatGood_add (hxs x (by simp))
        (ih (fun y hy => hxs y (by simp [hy])))

theorem RatGood_list_sum_of_sublist {xs ys : List ℚ}
    (hxs : ∀ x ∈ xs, RatGood x) (hys : ys.Sublist xs) :
    RatGood ys.sum :=
  RatGood_list_sum ys (fun y hy => hxs y (hys.subset hy))

theorem RatGood_list_sum_of_suffix {xs ys : List ℚ}
    (hxs : ∀ x ∈ xs, RatGood x) (hys : List.IsSuffix ys xs) :
    RatGood ys.sum :=
  RatGood_list_sum_of_sublist hxs hys.sublist

theorem RatGood_getD (xs : List ℚ) (i : Nat)
    (hxs : ∀ x ∈ xs, RatGood x) :
    RatGood (xs.getD i 0) := by
  by_cases hi : i < xs.length
  · rw [List.getD_eq_getElem (l := xs) (d := 0) hi]
    exact hxs xs[i] (List.getElem_mem hi)
  · have hle : xs.length ≤ i := Nat.le_of_not_gt hi
    rw [List.getD_eq_default (l := xs) (d := 0) hle]
    unfold RatGood
    simp

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

theorem ratCast_mul_of_RatGood
    (x y : ℚ) (hx : RatGood x) (hy : RatGood y) :
    (((x * y : ℚ) : ZMod finitePrime1) =
      (x : ZMod finitePrime1) * (y : ZMod finitePrime1)) :=
  ratCast_mul_of_good x y hx hy (RatGood_mul hx hy)

theorem ratCast_add_of_RatGood
    (x y : ℚ) (hx : RatGood x) (hy : RatGood y) :
    (((x + y : ℚ) : ZMod finitePrime1) =
      (x : ZMod finitePrime1) + (y : ZMod finitePrime1)) :=
  ratCast_add_of_good x y hx hy (RatGood_add hx hy)

theorem ratCast_sub_of_RatGood
    (x y : ℚ) (hx : RatGood x) (hy : RatGood y) :
    (((x - y : ℚ) : ZMod finitePrime1) =
      (x : ZMod finitePrime1) - (y : ZMod finitePrime1)) :=
  ratCast_sub_of_good x y hx hy (RatGood_sub hx hy)

theorem finitePrime1_RatGood_invNat (n : Nat) (hpos : 0 < n) (hle : n ≤ 13) :
    RatGood (1 / (n : ℚ)) := by
  unfold RatGood
  interval_cases n <;> native_decide

theorem finitePrime1_ratCast_invNat (n : Nat) (hpos : 0 < n) (hle : n ≤ 13) :
    (((1 / (n : ℚ) : ℚ) : ZMod finitePrime1) = 1 / (n : ZMod finitePrime1)) := by
  interval_cases n <;> native_decide

theorem finitePrime1_ratCast_divNat_of_good
    (x : ℚ) (n : Nat) (hpos : 0 < n) (hle : n ≤ 13)
    (hx : RatGood x) (hdiv : RatGood (x / (n : ℚ))) :
    (((x / (n : ℚ) : ℚ) : ZMod finitePrime1) =
      (x : ZMod finitePrime1) / (n : ZMod finitePrime1)) := by
  have hmul := ratCast_mul_of_good x (1 / (n : ℚ))
    hx (finitePrime1_RatGood_invNat n hpos hle) (by simpa [div_eq_mul_inv] using hdiv)
  rw [finitePrime1_ratCast_invNat n hpos hle] at hmul
  simpa [div_eq_mul_inv, mul_assoc] using hmul

theorem finitePrime1_ratCast_divNat_of_RatGood
    (x : ℚ) (n : Nat) (hpos : 0 < n) (hle : n ≤ 13)
    (hx : RatGood x) :
    (((x / (n : ℚ) : ℚ) : ZMod finitePrime1) =
      (x : ZMod finitePrime1) / (n : ZMod finitePrime1)) := by
  exact finitePrime1_ratCast_divNat_of_good x n hpos hle hx (by
    simpa [div_eq_mul_inv] using
      RatGood_mul hx (finitePrime1_RatGood_invNat n hpos hle))

theorem finitePrime1_RatGood_expList_of_good
    (n : Nat) (LQ : Nat → ℚ) (hn : n ≤ 13)
    (hLGood : ∀ r : Nat, r ≤ n → RatGood (LQ r)) :
    ∀ x ∈ Prop51.expList LQ n, RatGood x := by
  induction n with
  | zero =>
      intro x hx
      simp [Prop51.expList] at hx
      subst x
      exact RatGood_natCast 1
  | succ n ih =>
      have ihGood : ∀ x ∈ Prop51.expList LQ n, RatGood x :=
        ih (by omega) (fun r hr => hLGood r (by omega))
      intro x hx
      dsimp [Prop51.expList] at hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact ihGood x hx
      · simp only [List.mem_singleton] at hx
        subst x
        let terms : List ℚ := (List.range (n + 1)).map fun t : Nat =>
          ((t + 1 : Nat) : ℚ) * LQ (t + 1) *
            (Prop51.expList LQ n).getD (n - t) 0
        have hterms : ∀ z ∈ terms, RatGood z := by
          intro z hz
          rcases List.mem_map.mp hz with ⟨t, ht, rfl⟩
          have htlt : t < n + 1 := List.mem_range.mp ht
          exact RatGood_mul
            (RatGood_mul (RatGood_natCast (t + 1)) (hLGood (t + 1) (by omega)))
            (RatGood_getD (Prop51.expList LQ n) (n - t) ihGood)
        have hsumGood : RatGood terms.sum := RatGood_list_sum terms hterms
        have hdivGood : RatGood (terms.sum / ((n + 1 : Nat) : ℚ)) := by
          simpa [div_eq_mul_inv] using RatGood_mul hsumGood
            (finitePrime1_RatGood_invNat (n + 1) (by omega) (by omega))
        simpa [terms] using hdivGood

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

theorem ratCast_list_sum_of_suffix_good
    (xs : List ℚ)
    (hterm : ∀ x ∈ xs, RatGood x)
    (hsuffix : ∀ ys : List ℚ, List.IsSuffix ys xs → RatGood ys.sum) :
    (((xs.sum : ℚ) : ZMod finitePrime1) =
      (xs.map fun x => (x : ZMod finitePrime1)).sum) := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : RatGood x := hterm x (by simp)
      have hterm_tail : ∀ y ∈ xs, RatGood y := by
        intro y hy
        exact hterm y (by simp [hy])
      have hsuffix_tail : ∀ ys : List ℚ, List.IsSuffix ys xs → RatGood ys.sum := by
        intro ys hys
        exact hsuffix ys (hys.trans (List.suffix_cons x xs))
      have hsum_xs : RatGood xs.sum := hsuffix_tail xs (List.suffix_refl xs)
      have hsum_all : RatGood (x + xs.sum) := by
        simpa [List.sum_cons] using hsuffix (x :: xs) (List.suffix_refl (x :: xs))
      simp only [List.sum_cons]
      rw [ratCast_add_of_good x xs.sum hx hsum_xs hsum_all,
        ih hterm_tail hsuffix_tail]
      rfl

theorem finitePrime1_ratCast_expList_of_RatGood
    (n : Nat) (LQ : Nat → ℚ) (LMod : Nat → ZMod finitePrime1)
    (hn : n ≤ 13)
    (hLCast : ∀ r : Nat, r ≤ n → (((LQ r : ℚ) : ZMod finitePrime1) = LMod r))
    (hLGood : ∀ r : Nat, r ≤ n → RatGood (LQ r)) :
    List.map (fun x : ℚ => (x : ZMod finitePrime1)) (Prop51.expList LQ n) =
      expListMod finitePrime1 LMod n := by
  induction n with
  | zero =>
      simp [Prop51.expList, expListMod]
  | succ n ih =>
      have ih' :
          List.map (fun x : ℚ => (x : ZMod finitePrime1)) (Prop51.expList LQ n) =
            expListMod finitePrime1 LMod n :=
        ih (by omega)
          (fun r hr => hLCast r (by omega))
          (fun r hr => hLGood r (by omega))
      have ihGood : ∀ x ∈ Prop51.expList LQ n, RatGood x :=
        finitePrime1_RatGood_expList_of_good n LQ (by omega)
          (fun r hr => hLGood r (by omega))
      dsimp [Prop51.expList, expListMod]
      rw [List.map_append, ih', List.map_singleton]
      congr 1
      let termsQ : List ℚ := (List.range (n + 1)).map fun t : Nat =>
        ((t + 1 : Nat) : ℚ) * LQ (t + 1) *
          (Prop51.expList LQ n).getD (n - t) 0
      let termsZ : List (ZMod finitePrime1) := (List.range (n + 1)).map fun t : Nat =>
        ((t + 1 : Nat) : ZMod finitePrime1) * LMod (t + 1) *
          (expListMod finitePrime1 LMod n).getD (n - t) 0
      have htermsGood : ∀ z ∈ termsQ, RatGood z := by
        intro z hz
        rcases List.mem_map.mp hz with ⟨t, ht, rfl⟩
        have htlt : t < n + 1 := List.mem_range.mp ht
        exact RatGood_mul
          (RatGood_mul (RatGood_natCast (t + 1)) (hLGood (t + 1) (by omega)))
          (RatGood_getD (Prop51.expList LQ n) (n - t) ihGood)
      have hsum :
          (((termsQ.sum : ℚ) : ZMod finitePrime1) = termsZ.sum) := by
        rw [ratCast_list_sum_of_suffix_good]
        · refine congrArg (fun xs : List (ZMod finitePrime1) => xs.sum) ?_
          have hmap :
              termsQ.map (fun x : ℚ => (x : ZMod finitePrime1)) = termsZ := by
            have hmapBase :
                (List.range (n + 1)).map (fun t : Nat =>
                  ((((t + 1 : Nat) : ℚ) * LQ (t + 1) *
                    (Prop51.expList LQ n).getD (n - t) 0 : ℚ) :
                    ZMod finitePrime1)) =
                  (List.range (n + 1)).map fun t : Nat =>
                    ((t + 1 : Nat) : ZMod finitePrime1) * LMod (t + 1) *
                      (expListMod finitePrime1 LMod n).getD (n - t) 0 := by
              refine List.map_congr_left fun t ht => ?_
              have htlt : t < n + 1 := List.mem_range.mp ht
              have htle : t + 1 ≤ n + 1 := by omega
              have hgetGood :
                  RatGood ((Prop51.expList LQ n).getD (n - t) 0) :=
                RatGood_getD (Prop51.expList LQ n) (n - t) ihGood
              have hget :
                  (((Prop51.expList LQ n).getD (n - t) 0 : ℚ) :
                      ZMod finitePrime1) =
                    (expListMod finitePrime1 LMod n).getD (n - t) 0 := by
                have h := congrArg
                  (fun xs : List (ZMod finitePrime1) =>
                    xs.getD (n - t) ((0 : ℚ) : ZMod finitePrime1)) ih'
                change (List.map (fun x : ℚ => (x : ZMod finitePrime1))
                    (Prop51.expList LQ n)).getD
                      (n - t) ((0 : ℚ) : ZMod finitePrime1) =
                    (expListMod finitePrime1 LMod n).getD
                      (n - t) ((0 : ℚ) : ZMod finitePrime1) at h
                rw [List.getD_map] at h
                exact h
              have hNatCast :
                  ((((t + 1 : Nat) : ℚ) : ZMod finitePrime1) =
                    ((t + 1 : Nat) : ZMod finitePrime1)) := by
                simpa using (Rat.cast_natCast (α := ZMod finitePrime1) (t + 1))
              rw [ratCast_mul_of_RatGood
                  (((t + 1 : Nat) : ℚ) * LQ (t + 1))
                  ((Prop51.expList LQ n).getD (n - t) 0)
                  (RatGood_mul (RatGood_natCast (t + 1)) (hLGood (t + 1) (by omega)))
                  hgetGood,
                ratCast_mul_of_RatGood ((t + 1 : Nat) : ℚ) (LQ (t + 1))
                  (RatGood_natCast (t + 1)) (hLGood (t + 1) (by omega)),
                hNatCast, hLCast (t + 1) (by omega), hget]
            simpa [termsQ, termsZ, List.map_map] using hmapBase
          simpa [termsQ, termsZ, List.map_eq_flatMap, List.flatMap_assoc] using hmap
        · exact htermsGood
        · intro ys hys
          exact RatGood_list_sum_of_suffix htermsGood hys
      rw [finitePrime1_ratCast_divNat_of_RatGood termsQ.sum (n + 1)
        (by omega) (by omega) (RatGood_list_sum termsQ htermsGood), hsum]

theorem finitePrime1_RatGood_expCoeff_of_good
    (n : Nat) (LQ : Nat → ℚ) (hn : n ≤ 13)
    (hLGood : ∀ r : Nat, r ≤ n → RatGood (LQ r)) :
    RatGood (Prop51.expCoeff LQ n) := by
  unfold Prop51.expCoeff
  exact RatGood_getD (Prop51.expList LQ n) n
    (finitePrime1_RatGood_expList_of_good n LQ hn hLGood)

theorem finitePrime1_ratCast_expCoeff_of_RatGood
    (n : Nat) (LQ : Nat → ℚ) (LMod : Nat → ZMod finitePrime1)
    (hn : n ≤ 13)
    (hLCast : ∀ r : Nat, r ≤ n → (((LQ r : ℚ) : ZMod finitePrime1) = LMod r))
    (hLGood : ∀ r : Nat, r ≤ n → RatGood (LQ r)) :
    (((Prop51.expCoeff LQ n : ℚ) : ZMod finitePrime1) =
      expCoeffMod finitePrime1 LMod n) := by
  unfold Prop51.expCoeff expCoeffMod
  have hlist := finitePrime1_ratCast_expList_of_RatGood n LQ LMod hn hLCast hLGood
  have h := congrArg
    (fun xs : List (ZMod finitePrime1) => xs.getD n ((0 : ℚ) : ZMod finitePrime1))
    hlist
  change (List.map (fun x : ℚ => (x : ZMod finitePrime1)) (Prop51.expList LQ n)).getD
      n ((0 : ℚ) : ZMod finitePrime1) =
    (expListMod finitePrime1 LMod n).getD n ((0 : ℚ) : ZMod finitePrime1) at h
  rw [List.getD_map] at h
  exact h

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

theorem finitePrime1_ratCast_sPower_of_suffix_good
    (a : Nat) (μ : List Nat) (r : Nat)
    (ha : a ≤ 13) (hμsum : μ.sum = M a) (hr : r ≤ a)
    (hsuffix : ∀ ys : List ℚ,
      List.IsSuffix ys (μ.map fun mi : Nat => 1 / (((mi + 1 : Nat) : ℚ)^r)) →
        RatGood ys.sum) :
    (((sPower μ r : ℚ) : ZMod finitePrime1) = sPowerMod finitePrime1 μ r) := by
  unfold sPower sPowerMod
  rw [ratCast_list_sum_of_suffix_good]
  · let fQ : Nat → ℚ := fun mi => 1 / (((mi + 1 : Nat) : ℚ)^r)
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
  · intro x hx
    rcases List.mem_map.mp hx with ⟨mi, hmi, rfl⟩
    have hq : mi + 1 ≤ 73 := by
      exact le_trans
        (Nat.add_le_add_right (by simpa [hμsum] using le_sum_of_mem hmi) 1)
        (M_add_one_le_73_of_le_13 ha)
    exact finitePrime1_RatGood_sPower_summand mi r hq (le_trans hr ha)
  · exact hsuffix

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

theorem finitePrime1_ratCast_markedWeight_of_suffix_good
    (a : Nat) (μ : List Nat) (r : Nat)
    (ha : a ≤ 13) (hμsum : μ.sum = M a) (hr : r ≤ a)
    (hsuffix : ∀ ys : List ℚ,
      List.IsSuffix ys
        (μ.map fun mi : Nat => (mi : ℚ) / (((mi + 1 : Nat) : ℚ)^r)) →
        RatGood ys.sum) :
    (((markedWeight μ r : ℚ) : ZMod finitePrime1) =
      markedWeightMod finitePrime1 μ r) := by
  unfold markedWeight markedWeightMod
  rw [ratCast_list_sum_of_suffix_good]
  · let fQ : Nat → ℚ := fun mi => (mi : ℚ) / (((mi + 1 : Nat) : ℚ)^r)
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
  · intro x hx
    rcases List.mem_map.mp hx with ⟨mi, hmi, rfl⟩
    have hq : mi + 1 ≤ 73 := by
      exact le_trans
        (Nat.add_le_add_right (by simpa [hμsum] using le_sum_of_mem hmi) 1)
        (M_add_one_le_73_of_le_13 ha)
    exact finitePrime1_RatGood_markedWeight_summand mi r hq (le_trans hr ha)
  · exact hsuffix

theorem finitePrime1_RatGood_sPower_of_suffix_good
    (μ : List Nat) (r : Nat)
    (hsuffix : ∀ ys : List ℚ,
      List.IsSuffix ys (μ.map fun mi : Nat => 1 / (((mi + 1 : Nat) : ℚ)^r)) →
        RatGood ys.sum) :
    RatGood (sPower μ r) := by
  unfold sPower
  exact hsuffix _ (List.suffix_refl _)

theorem finitePrime1_RatGood_markedWeight_of_suffix_good
    (μ : List Nat) (r : Nat)
    (hsuffix : ∀ ys : List ℚ,
      List.IsSuffix ys
        (μ.map fun mi : Nat => (mi : ℚ) / (((mi + 1 : Nat) : ℚ)^r)) →
        RatGood ys.sum) :
    RatGood (markedWeight μ r) := by
  unfold markedWeight
  exact hsuffix _ (List.suffix_refl _)

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

theorem finitePrime1_RatGood_hCoeff_of_suffix_good
    (a : Nat) (μ : List Nat) (r : Nat)
    (ha : a ≤ 13) (hr : r ≤ a)
    (hsPowerSuffix : ∀ ys : List ℚ,
      List.IsSuffix ys (μ.map fun mi : Nat => 1 / (((mi + 1 : Nat) : ℚ)^r)) →
        RatGood ys.sum) :
    RatGood (hCoeff μ r) := by
  unfold hCoeff
  exact RatGood_mul (finitePrime1_RatGood_c r (le_trans hr ha))
    (RatGood_sub (RatGood_natCast (N μ))
      (finitePrime1_RatGood_sPower_of_suffix_good μ r hsPowerSuffix))

theorem finitePrime1_ratCast_hCoeff_of_suffix_good
    (a : Nat) (μ : List Nat) (r : Nat)
    (ha : a ≤ 13) (hμsum : μ.sum = M a) (hr : r ≤ a)
    (hsPowerSuffix : ∀ ys : List ℚ,
      List.IsSuffix ys (μ.map fun mi : Nat => 1 / (((mi + 1 : Nat) : ℚ)^r)) →
        RatGood ys.sum) :
    (((hCoeff μ r : ℚ) : ZMod finitePrime1) = hCoeffMod finitePrime1 μ r) := by
  unfold hCoeff hCoeffMod
  have hsPowerGood : RatGood (sPower μ r) :=
    finitePrime1_RatGood_sPower_of_suffix_good μ r hsPowerSuffix
  rw [ratCast_mul_of_RatGood (Prop51.c r) ((N μ : ℚ) - sPower μ r)
    (finitePrime1_RatGood_c r (le_trans hr ha))
    (RatGood_sub (RatGood_natCast (N μ)) hsPowerGood)]
  rw [ratCast_sub_of_RatGood (N μ : ℚ) (sPower μ r)
    (RatGood_natCast (N μ)) hsPowerGood]
  rw [finitePrime1_ratCast_sPower_of_suffix_good a μ r ha hμsum hr hsPowerSuffix]
  simp

theorem finitePrime1_ratCast_expList_of_good
    (n : Nat) (LQ : Nat → ℚ) (LMod : Nat → ZMod finitePrime1)
    (hn : n ≤ 13)
    (hTermCast : ∀ m t : Nat, m < n → t ∈ List.range (m + 1) →
      ((((t + 1 : Nat) : ℚ) * LQ (t + 1) *
          (Prop51.expList LQ m).getD (m - t) 0 : ℚ) : ZMod finitePrime1) =
        ((t + 1 : Nat) : ZMod finitePrime1) * LMod (t + 1) *
          (expListMod finitePrime1 LMod m).getD (m - t) 0)
    (hTermGood : ∀ m t : Nat, m < n → t ∈ List.range (m + 1) →
      RatGood (((t + 1 : Nat) : ℚ) * LQ (t + 1) *
        (Prop51.expList LQ m).getD (m - t) 0))
    (hTermSuffix : ∀ m : Nat, m < n → ∀ ys : List ℚ,
      List.IsSuffix ys
        ((List.range (m + 1)).map fun t : Nat =>
          ((t + 1 : Nat) : ℚ) * LQ (t + 1) *
            (Prop51.expList LQ m).getD (m - t) 0) →
      RatGood ys.sum)
    (hNewGood : ∀ m : Nat, m < n →
      RatGood ((((List.range (m + 1)).map fun t : Nat =>
        ((t + 1 : Nat) : ℚ) * LQ (t + 1) *
          (Prop51.expList LQ m).getD (m - t) 0).sum) / ((m + 1 : Nat) : ℚ))) :
    List.map (fun x : ℚ => (x : ZMod finitePrime1)) (Prop51.expList LQ n) =
      expListMod finitePrime1 LMod n := by
  induction n with
  | zero =>
      simp [Prop51.expList, expListMod]
  | succ n ih =>
      have hn' : n ≤ 13 := le_trans (Nat.le_succ n) hn
      have ih' :
          List.map (fun x : ℚ => (x : ZMod finitePrime1)) (Prop51.expList LQ n) =
            expListMod finitePrime1 LMod n :=
        ih hn'
          (fun m t hm ht => hTermCast m t (Nat.lt_trans hm (Nat.lt_succ_self n)) ht)
          (fun m t hm ht => hTermGood m t (Nat.lt_trans hm (Nat.lt_succ_self n)) ht)
          (fun m hm ys hys =>
            hTermSuffix m (Nat.lt_trans hm (Nat.lt_succ_self n)) ys hys)
          (fun m hm => hNewGood m (Nat.lt_trans hm (Nat.lt_succ_self n)))
      dsimp [Prop51.expList, expListMod]
      rw [List.map_append, ih', List.map_singleton]
      congr 1
      have hsum :
          (((((List.range (n + 1)).map fun t : Nat =>
              ((t + 1 : Nat) : ℚ) * LQ (t + 1) *
                (Prop51.expList LQ n).getD (n - t) 0).sum : ℚ) :
              ZMod finitePrime1) =
            ((List.range (n + 1)).map fun t : Nat =>
              ((t + 1 : Nat) : ZMod finitePrime1) * LMod (t + 1) *
                (expListMod finitePrime1 LMod n).getD (n - t) 0).sum) := by
        rw [ratCast_list_sum_of_suffix_good]
        · refine congrArg (fun xs : List (ZMod finitePrime1) => xs.sum) ?_
          have hmap :
              (List.range (n + 1)).map (fun t : Nat =>
                  ((((t + 1 : Nat) : ℚ) * LQ (t + 1) *
                    (Prop51.expList LQ n).getD (n - t) 0 : ℚ) :
                    ZMod finitePrime1)) =
                (List.range (n + 1)).map fun t : Nat =>
                  ((t + 1 : Nat) : ZMod finitePrime1) * LMod (t + 1) *
                    (expListMod finitePrime1 LMod n).getD (n - t) 0 := by
            refine List.map_congr_left fun t ht => ?_
            exact hTermCast n t (Nat.lt_succ_self n) ht
          simpa [List.map_eq_flatMap, List.flatMap_assoc] using hmap
        · intro x hx
          rcases List.mem_map.mp hx with ⟨t, ht, rfl⟩
          exact hTermGood n t (Nat.lt_succ_self n) ht
        · exact hTermSuffix n (Nat.lt_succ_self n)
      rw [finitePrime1_ratCast_divNat_of_good
        (((List.range (n + 1)).map fun t : Nat =>
          ((t + 1 : Nat) : ℚ) * LQ (t + 1) *
            (Prop51.expList LQ n).getD (n - t) 0).sum)
        (n + 1) (by omega) (by omega)
        (hTermSuffix n (Nat.lt_succ_self n) _ (List.suffix_refl _))
        (hNewGood n (Nat.lt_succ_self n)), hsum]

theorem finitePrime1_ratCast_expCoeff_of_good
    (n : Nat) (LQ : Nat → ℚ) (LMod : Nat → ZMod finitePrime1)
    (hn : n ≤ 13)
    (hTermCast : ∀ m t : Nat, m < n → t ∈ List.range (m + 1) →
      ((((t + 1 : Nat) : ℚ) * LQ (t + 1) *
          (Prop51.expList LQ m).getD (m - t) 0 : ℚ) : ZMod finitePrime1) =
        ((t + 1 : Nat) : ZMod finitePrime1) * LMod (t + 1) *
          (expListMod finitePrime1 LMod m).getD (m - t) 0)
    (hTermGood : ∀ m t : Nat, m < n → t ∈ List.range (m + 1) →
      RatGood (((t + 1 : Nat) : ℚ) * LQ (t + 1) *
        (Prop51.expList LQ m).getD (m - t) 0))
    (hTermSuffix : ∀ m : Nat, m < n → ∀ ys : List ℚ,
      List.IsSuffix ys
        ((List.range (m + 1)).map fun t : Nat =>
          ((t + 1 : Nat) : ℚ) * LQ (t + 1) *
            (Prop51.expList LQ m).getD (m - t) 0) →
      RatGood ys.sum)
    (hNewGood : ∀ m : Nat, m < n →
      RatGood ((((List.range (m + 1)).map fun t : Nat =>
        ((t + 1 : Nat) : ℚ) * LQ (t + 1) *
          (Prop51.expList LQ m).getD (m - t) 0).sum) / ((m + 1 : Nat) : ℚ))) :
    (((Prop51.expCoeff LQ n : ℚ) : ZMod finitePrime1) =
      expCoeffMod finitePrime1 LMod n) := by
  unfold Prop51.expCoeff expCoeffMod
  have hlist := finitePrime1_ratCast_expList_of_good n LQ LMod hn
    hTermCast hTermGood hTermSuffix hNewGood
  have h := congrArg
    (fun xs : List (ZMod finitePrime1) => xs.getD n ((0 : ℚ) : ZMod finitePrime1))
    hlist
  change (List.map (fun x : ℚ => (x : ZMod finitePrime1)) (Prop51.expList LQ n)).getD
      n ((0 : ℚ) : ZMod finitePrime1) =
    (expListMod finitePrime1 LMod n).getD n ((0 : ℚ) : ZMod finitePrime1) at h
  rw [List.getD_map] at h
  exact h

theorem finitePrime1_ratCast_fCoeff_of_good
    (a : Nat) (μ : List Nat) (k : Nat)
    (ha : a ≤ 13) (hk : k ≤ a)
    (hTermCast : ∀ m t : Nat, m < k → t ∈ List.range (m + 1) →
      ((((t + 1 : Nat) : ℚ) * (-(hCoeff μ (t + 1))) *
          (Prop51.expList (fun r => -hCoeff μ r) m).getD (m - t) 0 : ℚ) :
          ZMod finitePrime1) =
        ((t + 1 : Nat) : ZMod finitePrime1) * (-(hCoeffMod finitePrime1 μ (t + 1))) *
          (expListMod finitePrime1 (fun r => -hCoeffMod finitePrime1 μ r) m).getD
            (m - t) 0)
    (hTermGood : ∀ m t : Nat, m < k → t ∈ List.range (m + 1) →
      RatGood (((t + 1 : Nat) : ℚ) * (-(hCoeff μ (t + 1))) *
        (Prop51.expList (fun r => -hCoeff μ r) m).getD (m - t) 0))
    (hTermSuffix : ∀ m : Nat, m < k → ∀ ys : List ℚ,
      List.IsSuffix ys
        ((List.range (m + 1)).map fun t : Nat =>
          ((t + 1 : Nat) : ℚ) * (-(hCoeff μ (t + 1))) *
            (Prop51.expList (fun r => -hCoeff μ r) m).getD (m - t) 0) →
      RatGood ys.sum)
    (hNewGood : ∀ m : Nat, m < k →
      RatGood ((((List.range (m + 1)).map fun t : Nat =>
        ((t + 1 : Nat) : ℚ) * (-(hCoeff μ (t + 1))) *
          (Prop51.expList (fun r => -hCoeff μ r) m).getD (m - t) 0).sum) /
            ((m + 1 : Nat) : ℚ))) :
    (((fCoeff μ k : ℚ) : ZMod finitePrime1) = fCoeffMod finitePrime1 μ k) := by
  unfold fCoeff fCoeffMod
  exact finitePrime1_ratCast_expCoeff_of_good k
    (fun r => -hCoeff μ r) (fun r => -hCoeffMod finitePrime1 μ r)
    (le_trans hk ha) hTermCast hTermGood hTermSuffix hNewGood

theorem finitePrime1_ratCast_kCoeff_of_suffix_good
    (a : Nat) (μ : List Nat) (r : Nat)
    (ha : a ≤ 13) (hμsum : μ.sum = M a) (hr : r ≤ a)
    (hMarkedSuffix : ∀ ys : List ℚ,
      List.IsSuffix ys
        (μ.map fun mi : Nat => (mi : ℚ) / (((mi + 1 : Nat) : ℚ)^r)) →
        RatGood ys.sum)
    (hKGood : RatGood (kCoeff μ r)) :
    (((kCoeff μ r : ℚ) : ZMod finitePrime1) = kCoeffMod finitePrime1 μ r) := by
  cases r with
  | zero =>
      simp [kCoeff, kCoeffMod]
  | succ r =>
      cases r with
      | zero =>
          have hmwGood : RatGood (markedWeight μ 1) := by
            unfold markedWeight
            exact hMarkedSuffix _ (List.suffix_refl _)
          rw [kCoeff, kCoeffMod,
            ratCast_mul_of_good (2 : ℚ) (markedWeight μ 1)
              (RatGood_natCast 2) hmwGood hKGood]
          rw [finitePrime1_ratCast_markedWeight_of_suffix_good a μ 1
            ha hμsum (by omega) hMarkedSuffix]
          norm_num
      | succ j =>
          have hj1 : j + 1 ≤ a := by omega
          have hj2 : j + 2 ≤ a := by simpa using hr
          have hprefixGood :
              RatGood (12 * ((j + 1 : Nat) : ℚ) * Prop51.c (j + 1)) := by
            unfold RatGood
            have hjle : j ≤ 12 := by omega
            interval_cases j <;> native_decide
          have hprefixCast :
              (((12 * ((j + 1 : Nat) : ℚ) * Prop51.c (j + 1) : ℚ) :
                  ZMod finitePrime1)
                = 12 * ((j + 1 : Nat) : ZMod finitePrime1) *
                    (Prop51.c (j + 1) : ZMod finitePrime1)) := by
            have hjle : j ≤ 12 := by omega
            interval_cases j <;> native_decide
          have hmwGood : RatGood (markedWeight μ (j + 2)) := by
            unfold markedWeight
            exact hMarkedSuffix _ (List.suffix_refl _)
          rw [kCoeff, kCoeffMod,
            ratCast_mul_of_good
              (12 * ((j + 1 : Nat) : ℚ) * Prop51.c (j + 1))
              (markedWeight μ (j + 2))
              hprefixGood hmwGood hKGood]
          rw [hprefixCast,
            finitePrime1_ratCast_markedWeight_of_suffix_good a μ (j + 2)
              ha hμsum hj2 hMarkedSuffix]

theorem finitePrime1_RatGood_kCoeff_of_suffix_good
    (a : Nat) (μ : List Nat) (r : Nat)
    (ha : a ≤ 13) (hr : r ≤ a)
    (hMarkedSuffix : ∀ ys : List ℚ,
      List.IsSuffix ys
        (μ.map fun mi : Nat => (mi : ℚ) / (((mi + 1 : Nat) : ℚ)^r)) →
        RatGood ys.sum) :
    RatGood (kCoeff μ r) := by
  cases r with
  | zero =>
      simpa [kCoeff] using RatGood_natCast 0
  | succ r =>
      cases r with
      | zero =>
          have hmwGood : RatGood (markedWeight μ 1) :=
            finitePrime1_RatGood_markedWeight_of_suffix_good μ 1 hMarkedSuffix
          simpa [kCoeff] using RatGood_mul (RatGood_natCast 2) hmwGood
      | succ j =>
          have hj1 : j + 1 ≤ a := by omega
          have hj2 : j + 2 ≤ a := by simpa using hr
          have hprefixGood :
              RatGood (12 * ((j + 1 : Nat) : ℚ) * Prop51.c (j + 1)) :=
            RatGood_mul
              (RatGood_mul (RatGood_natCast 12) (RatGood_natCast (j + 1)))
              (finitePrime1_RatGood_c (j + 1) (by omega))
          have hmwGood : RatGood (markedWeight μ (j + 2)) :=
            finitePrime1_RatGood_markedWeight_of_suffix_good μ (j + 2) hMarkedSuffix
          simpa [kCoeff, mul_assoc] using RatGood_mul hprefixGood hmwGood

theorem finitePrime1_ratCast_kCoeff_of_suffix_RatGood
    (a : Nat) (μ : List Nat) (r : Nat)
    (ha : a ≤ 13) (hμsum : μ.sum = M a) (hr : r ≤ a)
    (hMarkedSuffix : ∀ ys : List ℚ,
      List.IsSuffix ys
        (μ.map fun mi : Nat => (mi : ℚ) / (((mi + 1 : Nat) : ℚ)^r)) →
        RatGood ys.sum) :
    (((kCoeff μ r : ℚ) : ZMod finitePrime1) = kCoeffMod finitePrime1 μ r) :=
  finitePrime1_ratCast_kCoeff_of_suffix_good a μ r ha hμsum hr hMarkedSuffix
    (finitePrime1_RatGood_kCoeff_of_suffix_good a μ r ha hr hMarkedSuffix)

theorem finitePrime1_ratCast_correctedCoeffFast_of_good
    (a : Nat) (μ : List Nat)
    (_ha : a ≤ 13)
    (hfCast : ∀ k : Nat, k ≤ a →
      (((fCoeff μ k : ℚ) : ZMod finitePrime1) = fCoeffMod finitePrime1 μ k))
    (hkCast : ∀ k : Nat, k ≤ a →
      (((kCoeff μ k : ℚ) : ZMod finitePrime1) = kCoeffMod finitePrime1 μ k))
    (hfGood : ∀ k : Nat, k ≤ a → RatGood (fCoeff μ k))
    (hkGood : ∀ k : Nat, k ≤ a → RatGood (kCoeff μ k))
    (hProdGood : ∀ k : Nat, k ∈ List.range a →
      RatGood (kCoeff μ (k + 1) * fCoeff μ (a - (k + 1))))
    (hConvSuffix : ∀ ys : List ℚ,
      List.IsSuffix ys
        ((List.range a).map fun k : Nat =>
          kCoeff μ (k + 1) * fCoeff μ (a - (k + 1))) →
      RatGood ys.sum)
    (hMainGood : RatGood ((M a : ℚ) * fCoeff μ a))
    (hFastGood : RatGood (correctedCoeffFast a μ)) :
    (((correctedCoeffFast a μ : ℚ) : ZMod finitePrime1) =
      correctedCoeffMod finitePrime1 a μ) := by
  unfold correctedCoeffFast correctedCoeffMod
  have hMainCast :
      ((((M a : ℚ) * fCoeff μ a : ℚ) : ZMod finitePrime1) =
        (M a : ZMod finitePrime1) * fCoeffMod finitePrime1 μ a) := by
    rw [ratCast_mul_of_good (M a : ℚ) (fCoeff μ a)
      (RatGood_natCast (M a)) (hfGood a le_rfl) hMainGood,
      hfCast a le_rfl]
    simp
  have hConvCast :
      (((((List.range a).map fun k : Nat =>
          kCoeff μ (k + 1) * fCoeff μ (a - (k + 1))).sum : ℚ) :
          ZMod finitePrime1) =
        ((List.range a).map fun k : Nat =>
          kCoeffMod finitePrime1 μ (k + 1) *
            fCoeffMod finitePrime1 μ (a - (k + 1))).sum) := by
    rw [ratCast_list_sum_of_suffix_good]
    · refine congrArg (fun xs : List (ZMod finitePrime1) => xs.sum) ?_
      have hmap :
          (List.range a).map (fun k : Nat =>
              (((kCoeff μ (k + 1) * fCoeff μ (a - (k + 1)) : ℚ) :
                ZMod finitePrime1))) =
            (List.range a).map fun k : Nat =>
              kCoeffMod finitePrime1 μ (k + 1) *
                fCoeffMod finitePrime1 μ (a - (k + 1)) := by
        refine List.map_congr_left fun k hk => ?_
        have hklt : k < a := List.mem_range.mp hk
        have hk1 : k + 1 ≤ a := by omega
        have hka : a - (k + 1) ≤ a := by omega
        rw [ratCast_mul_of_good (kCoeff μ (k + 1)) (fCoeff μ (a - (k + 1)))
          (hkGood (k + 1) hk1) (hfGood (a - (k + 1)) hka)
          (hProdGood k hk), hkCast (k + 1) hk1, hfCast (a - (k + 1)) hka]
      simpa [List.map_eq_flatMap, List.flatMap_assoc] using hmap
    · intro x hx
      rcases List.mem_map.mp hx with ⟨k, hk, rfl⟩
      exact hProdGood k hk
    · exact hConvSuffix
  have hConvGood :
      RatGood (((List.range a).map fun k : Nat =>
        kCoeff μ (k + 1) * fCoeff μ (a - (k + 1))).sum) :=
    hConvSuffix _ (List.suffix_refl _)
  rw [ratCast_sub_of_good ((M a : ℚ) * fCoeff μ a)
    (((List.range a).map fun k : Nat =>
      kCoeff μ (k + 1) * fCoeff μ (a - (k + 1))).sum)
    hMainGood hConvGood hFastGood]
  rw [hMainCast, hConvCast]

theorem finitePrime1_ratCast_correctedCoeffFast_of_suffix_good
    (a : Nat) (μ : List Nat)
    (ha : a ≤ 13)
    (hfCast : ∀ k : Nat, k ≤ a →
      (((fCoeff μ k : ℚ) : ZMod finitePrime1) = fCoeffMod finitePrime1 μ k))
    (hkCast : ∀ k : Nat, k ≤ a →
      (((kCoeff μ k : ℚ) : ZMod finitePrime1) = kCoeffMod finitePrime1 μ k))
    (hfGood : ∀ k : Nat, k ≤ a → RatGood (fCoeff μ k))
    (hkGood : ∀ k : Nat, k ≤ a → RatGood (kCoeff μ k))
    (hConvSuffix : ∀ ys : List ℚ,
      List.IsSuffix ys
        ((List.range a).map fun k : Nat =>
          kCoeff μ (k + 1) * fCoeff μ (a - (k + 1))) →
      RatGood ys.sum) :
    (((correctedCoeffFast a μ : ℚ) : ZMod finitePrime1) =
      correctedCoeffMod finitePrime1 a μ) := by
  exact finitePrime1_ratCast_correctedCoeffFast_of_good a μ ha hfCast hkCast
    hfGood hkGood
    (fun k hk => by
      have hklt : k < a := List.mem_range.mp hk
      exact RatGood_mul (hkGood (k + 1) (by omega))
        (hfGood (a - (k + 1)) (by omega)))
    hConvSuffix
    (RatGood_mul (RatGood_natCast (M a)) (hfGood a le_rfl))
    (by
      have hMainGood : RatGood ((M a : ℚ) * fCoeff μ a) :=
        RatGood_mul (RatGood_natCast (M a)) (hfGood a le_rfl)
      have hConvGood :
          RatGood (((List.range a).map fun k : Nat =>
            kCoeff μ (k + 1) * fCoeff μ (a - (k + 1))).sum) :=
        hConvSuffix _ (List.suffix_refl _)
      simpa [correctedCoeffFast] using RatGood_sub hMainGood hConvGood)

end Prop52
