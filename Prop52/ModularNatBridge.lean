/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Bridge from Nat residues to `ZMod`

The fast finite certificates in `Prop52.ModularNat` compute residues as natural
numbers for performance.  This file starts the proof bridge showing that those
residues denote the corresponding `ZMod finitePrime1` computations.
-/

import Prop52.ModularNat11
import Prop51.PartitionsComplete
import Mathlib.Tactic.IntervalCases

namespace Prop52

/-! ## Elementary residue operations -/

theorem natCast_addMod (p x y : Nat) :
    ((addMod p x y : Nat) : ZMod p) = (x : ZMod p) + (y : ZMod p) := by
  unfold addMod
  simp

theorem natCast_mulMod (p x y : Nat) :
    ((mulMod p x y : Nat) : ZMod p) = (x : ZMod p) * (y : ZMod p) := by
  unfold mulMod
  simp

theorem natCast_subMod {p x y : Nat} (hyx : y ≤ x) :
    ((subMod p x y : Nat) : ZMod p) = (x : ZMod p) - (y : ZMod p) := by
  unfold subMod
  rw [if_pos hyx]
  rw [Nat.cast_sub hyx]

theorem natCast_subMod_of_le_add {p x y : Nat} (h : y ≤ x + p) :
    ((subMod p x y : Nat) : ZMod p) = (x : ZMod p) - (y : ZMod p) := by
  unfold subMod
  by_cases hyx : y ≤ x
  · rw [if_pos hyx, Nat.cast_sub hyx]
  · rw [if_neg hyx, Nat.cast_sub h]
    simp [Nat.cast_add]

theorem subMod_lt {p x y : Nat} (_hp : 0 < p) (hx : x < p) (hy : y < p) :
    subMod p x y < p := by
  unfold subMod
  by_cases hyx : y ≤ x
  · rw [if_pos hyx]
    omega
  · rw [if_neg hyx]
    omega

theorem natCast_foldl_addMod (p : Nat) (xs : List Nat) (acc : Nat) :
    (((xs.foldl (fun acc x => addMod p acc x) acc : Nat) : ZMod p)
      = (acc : ZMod p) + (xs.map fun x => (x : ZMod p)).sum) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (addMod p acc x), natCast_addMod]
      simp [List.map_cons, add_assoc, add_comm, add_left_comm]

theorem natCast_sumMod (p : Nat) (xs : List Nat) :
    ((sumMod p xs : Nat) : ZMod p) = (xs.map fun x => (x : ZMod p)).sum := by
  simpa [sumMod] using natCast_foldl_addMod p xs 0

theorem natCast_sumMod_map {α : Type} (p : Nat) (xs : List α) (f : α → Nat) :
    ((sumMod p (xs.map f) : Nat) : ZMod p) =
      (xs.map fun x => (f x : ZMod p)).sum := by
  simpa [List.map_eq_flatMap, List.flatMap_assoc] using natCast_sumMod p (xs.map f)

theorem foldl_addMod_lt {p : Nat} (hp : 0 < p) (xs : List Nat) :
    ∀ acc : Nat, acc < p → xs.foldl (fun acc x => addMod p acc x) acc < p := by
  induction xs with
  | nil =>
      intro acc hacc
      simpa using hacc
  | cons x xs ih =>
      intro acc _hacc
      exact ih (addMod p acc x) (by unfold addMod; exact Nat.mod_lt _ hp)

theorem sumMod_lt {p : Nat} (hp : 0 < p) (xs : List Nat) :
    sumMod p xs < p := by
  unfold sumMod
  exact foldl_addMod_lt hp xs 0 hp

/-! ## Certificate-prime table facts -/

theorem M_add_one_le_73_of_le_13 {a : Nat} (ha : a ≤ 13) :
    M a + 1 ≤ 73 := by
  unfold M
  omega

theorem finitePrime1_invPow_cast (q r : Nat) (hq : q ≤ 73) (hr : r ≤ 13) :
    ((powMod finitePrime1 (invMod finitePrime1 q) r : Nat) : ZMod finitePrime1)
      = ((q : ZMod finitePrime1)⁻¹)^r := by
  interval_cases q <;> interval_cases r <;> native_decide

theorem finitePrime1_invIntTable_cast
    (a r : Nat) (ha : a ≤ 13) (hr : r ≤ a) :
    (((invIntTable finitePrime1 a).getD r 0 : Nat) : ZMod finitePrime1)
      = (r : ZMod finitePrime1)⁻¹ := by
  interval_cases a <;> interval_cases r <;> native_decide

theorem finitePrime1_invPowTable_getD_all :
    ∀ a : Nat, a ≤ 13 →
    ∀ q : Nat, q ≤ M a + 1 →
    ∀ r : Nat, r ≤ a →
      get2D (invPowTable finitePrime1 a (M a + 1)) q r
        = powMod finitePrime1 (invMod finitePrime1 q) r := by
  native_decide

theorem finitePrime1_invPowTable_getD
    (a q r : Nat) (ha : a ≤ 13) (hq : q ≤ M a + 1) (hr : r ≤ a) :
    get2D (invPowTable finitePrime1 a (M a + 1)) q r
      = powMod finitePrime1 (invMod finitePrime1 q) r :=
  finitePrime1_invPowTable_getD_all a ha q hq r hr

theorem finitePrime1_invPowTable_cast
    (a q r : Nat) (ha : a ≤ 13) (hq : q ≤ M a + 1) (hr : r ≤ a) :
    ((get2D (invPowTable finitePrime1 a (M a + 1)) q r : Nat) : ZMod finitePrime1)
      = ((q : ZMod finitePrime1)⁻¹)^r := by
  rw [finitePrime1_invPowTable_getD a q r ha hq hr]
  exact finitePrime1_invPow_cast q r (le_trans hq (M_add_one_le_73_of_le_13 ha)) (le_trans hr ha)

theorem finitePrime1_cListModNat_cast
    (a r : Nat) (ha : a ≤ 13) (hr : r ≤ a) :
    (((cListModNat finitePrime1 a).getD r 0 : Nat) : ZMod finitePrime1)
      = (Prop51.c r : ZMod finitePrime1) := by
  interval_cases a <;> interval_cases r <;> native_decide

theorem finitePrime1_cArray_cast_all :
    ∀ a : Nat, a ≤ 13 →
    ∀ r : Nat, r ≤ a →
      ((((cListModNat finitePrime1 a).toArray.getD r 0 : Nat) : ZMod finitePrime1)
        = (Prop51.c r : ZMod finitePrime1)) := by
  native_decide

theorem finitePrime1_cArray_cast
    (a r : Nat) (ha : a ≤ 13) (hr : r ≤ a) :
    (((cListModNat finitePrime1 a).toArray.getD r 0 : Nat) : ZMod finitePrime1)
      = (Prop51.c r : ZMod finitePrime1) :=
  finitePrime1_cArray_cast_all a ha r hr

/-! ## Partition-dependent sums -/

/- Nat-side pieces of the finitePrime1 checker, factored out for bridge proofs. -/

def hCoeffModNatCore (a : Nat) (μ : List Nat) (r : Nat) : Nat :=
  mulMod finitePrime1
    ((cListModNat finitePrime1 a).toArray.getD r 0)
    (subMod finitePrime1 (N μ % finitePrime1)
      (sPowerModNat finitePrime1 (invPowTable finitePrime1 a (M a + 1)) μ r))

def bListModNatCore (a : Nat) (μ : List Nat) : List Nat :=
  expListModNat finitePrime1 (invIntTable finitePrime1 a)
    (fun r => subMod finitePrime1 0 (hCoeffModNatCore a μ r)) a

def kCoeffModNatCore (a : Nat) (μ : List Nat) : Nat → Nat
  | 0 => 0
  | 1 => mulMod finitePrime1 2
      (markedWeightModNat finitePrime1 (invPowTable finitePrime1 a (M a + 1)) μ 1)
  | j + 2 =>
      mulMod finitePrime1
        (mulMod finitePrime1
          (mulMod finitePrime1 12 (j + 1))
          ((cListModNat finitePrime1 a).toArray.getD (j + 1) 0))
        (markedWeightModNat finitePrime1 (invPowTable finitePrime1 a (M a + 1)) μ (j + 2))

def correctedCoeffModNatCore (a : Nat) (μ : List Nat) : Nat :=
  let bList := bListModNatCore a μ
  let bCoeff := fun r => bList.getD r 0
  let conv := sumMod finitePrime1 <| (List.range a).map fun k =>
    mulMod finitePrime1 (kCoeffModNatCore a μ (k + 1)) (bCoeff (a - (k + 1)))
  subMod finitePrime1 (mulMod finitePrime1 (M a % finitePrime1) (bCoeff a)) conv

theorem correctedCoeffModNat_eq_core (a : Nat) (μ : List Nat) :
    correctedCoeffModNat finitePrime1 a μ = correctedCoeffModNatCore a μ := by
  rfl

theorem le_sum_of_mem {x : Nat} {xs : List Nat} (hx : x ∈ xs) :
    x ≤ xs.sum := by
  induction xs with
  | nil =>
      simp at hx
  | cons y ys ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · simp
      · exact le_trans (ih hx) (Nat.le_add_left ys.sum y)

theorem finitePrime1_sPowerModNat_cast
    (a : Nat) (μ : List Nat) (r : Nat)
    (ha : a ≤ 13) (hμsum : μ.sum = M a) (hr : r ≤ a) :
    ((sPowerModNat finitePrime1 (invPowTable finitePrime1 a (M a + 1)) μ r : Nat) :
        ZMod finitePrime1) = sPowerMod finitePrime1 μ r := by
  unfold sPowerModNat sPowerMod
  rw [natCast_sumMod_map]
  congr 1
  refine List.map_congr_left fun mi hmi => ?_
  have hq : mi + 1 ≤ M a + 1 := by
    exact Nat.add_le_add_right (by simpa [hμsum] using le_sum_of_mem hmi) 1
  rw [finitePrime1_invPowTable_cast a (mi + 1) r ha hq hr]
  simp [div_eq_mul_inv, inv_pow]

theorem finitePrime1_markedWeightModNat_cast
    (a : Nat) (μ : List Nat) (r : Nat)
    (ha : a ≤ 13) (hμsum : μ.sum = M a) (hr : r ≤ a) :
    ((markedWeightModNat finitePrime1 (invPowTable finitePrime1 a (M a + 1)) μ r : Nat) :
        ZMod finitePrime1) = markedWeightMod finitePrime1 μ r := by
  unfold markedWeightModNat markedWeightMod
  rw [natCast_sumMod_map]
  congr 1
  refine List.map_congr_left fun mi hmi => ?_
  have hq : mi + 1 ≤ M a + 1 := by
    exact Nat.add_le_add_right (by simpa [hμsum] using le_sum_of_mem hmi) 1
  rw [natCast_mulMod, finitePrime1_invPowTable_cast a (mi + 1) r ha hq hr]
  simp [div_eq_mul_inv, inv_pow]

theorem finitePrime1_hCoeffModNat_cast
    (a : Nat) (μ : List Nat) (r : Nat)
    (ha : a ≤ 13) (hμsum : μ.sum = M a) (hr : r ≤ a) :
    ((mulMod finitePrime1
        ((cListModNat finitePrime1 a).toArray.getD r 0)
        (subMod finitePrime1 (N μ % finitePrime1)
          (sPowerModNat finitePrime1 (invPowTable finitePrime1 a (M a + 1)) μ r)) : Nat) :
        ZMod finitePrime1) = hCoeffMod finitePrime1 μ r := by
  have hp : 0 < finitePrime1 := by native_decide
  have hslt :
      sPowerModNat finitePrime1 (invPowTable finitePrime1 a (M a + 1)) μ r < finitePrime1 := by
    unfold sPowerModNat
    exact sumMod_lt hp _
  have hsub :
      sPowerModNat finitePrime1 (invPowTable finitePrime1 a (M a + 1)) μ r
        ≤ N μ % finitePrime1 + finitePrime1 := by
    omega
  rw [natCast_mulMod, finitePrime1_cArray_cast a r ha hr,
    natCast_subMod_of_le_add hsub,
    finitePrime1_sPowerModNat_cast a μ r ha hμsum hr]
  simp [hCoeffMod]

theorem finitePrime1_hCoeffModNatCore_cast
    (a : Nat) (μ : List Nat) (r : Nat)
    (ha : a ≤ 13) (hμsum : μ.sum = M a) (hr : r ≤ a) :
    ((hCoeffModNatCore a μ r : Nat) : ZMod finitePrime1) = hCoeffMod finitePrime1 μ r := by
  simpa [hCoeffModNatCore] using finitePrime1_hCoeffModNat_cast a μ r ha hμsum hr

theorem finitePrime1_kCoeffModNat_cast
    (a : Nat) (μ : List Nat) (r : Nat)
    (ha : a ≤ 13) (hμsum : μ.sum = M a) (hr : r ≤ a) :
    ((match r with
      | 0 => 0
      | 1 => mulMod finitePrime1 2
          (markedWeightModNat finitePrime1 (invPowTable finitePrime1 a (M a + 1)) μ 1)
      | j + 2 =>
          mulMod finitePrime1
            (mulMod finitePrime1
              (mulMod finitePrime1 12 (j + 1))
              ((cListModNat finitePrime1 a).toArray.getD (j + 1) 0))
            (markedWeightModNat finitePrime1 (invPowTable finitePrime1 a (M a + 1)) μ (j + 2)) : Nat) :
        ZMod finitePrime1) = kCoeffMod finitePrime1 μ r := by
  cases r with
  | zero =>
      simp [kCoeffMod]
  | succ r =>
      cases r with
      | zero =>
          have h1 : 1 ≤ a := by simpa using hr
          rw [natCast_mulMod,
            finitePrime1_markedWeightModNat_cast a μ 1 ha hμsum h1]
          simp [kCoeffMod]
      | succ j =>
          have hj1 : j + 1 ≤ a := by omega
          have hj2 : j + 2 ≤ a := by simpa using hr
          rw [natCast_mulMod, natCast_mulMod, natCast_mulMod,
            finitePrime1_cArray_cast a (j + 1) ha hj1,
            finitePrime1_markedWeightModNat_cast a μ (j + 2) ha hμsum hj2]
          simp [kCoeffMod, mul_assoc]

theorem finitePrime1_kCoeffModNatCore_cast
    (a : Nat) (μ : List Nat) (r : Nat)
    (ha : a ≤ 13) (hμsum : μ.sum = M a) (hr : r ≤ a) :
    ((kCoeffModNatCore a μ r : Nat) : ZMod finitePrime1) = kCoeffMod finitePrime1 μ r := by
  cases r with
  | zero =>
      simp [kCoeffModNatCore, kCoeffMod]
  | succ r =>
      cases r with
      | zero =>
          have h1 : 1 ≤ a := by simpa using hr
          rw [kCoeffModNatCore, natCast_mulMod,
            finitePrime1_markedWeightModNat_cast a μ 1 ha hμsum h1]
          simp [kCoeffMod]
      | succ j =>
          have hj1 : j + 1 ≤ a := by omega
          have hj2 : j + 2 ≤ a := by simpa using hr
          rw [kCoeffModNatCore, natCast_mulMod, natCast_mulMod, natCast_mulMod,
            finitePrime1_cArray_cast a (j + 1) ha hj1,
            finitePrime1_markedWeightModNat_cast a μ (j + 2) ha hμsum hj2]
          simp [kCoeffMod, mul_assoc]

/-! ## Exponential recurrence -/

theorem expListMod_succ_append (p : Nat) [Fact p.Prime] (L : Nat → ZMod p) (n : Nat) :
    ∃ x : ZMod p, expListMod p L (n + 1) = expListMod p L n ++ [x] :=
  ⟨_, rfl⟩

theorem expListMod_length (p : Nat) [Fact p.Prime] (L : Nat → ZMod p) :
    ∀ n, (expListMod p L n).length = n + 1
  | 0 => rfl
  | n + 1 => by
      obtain ⟨x, hx⟩ := expListMod_succ_append p L n
      rw [hx, List.length_append, expListMod_length p L n]
      rfl

theorem expListMod_getD_eq
    (p : Nat) [Fact p.Prime] (L : Nat → ZMod p) (r m : Nat) (h : r ≤ m) :
    (expListMod p L m).getD r 0 = expCoeffMod p L r := by
  induction m with
  | zero =>
      have : r = 0 := by omega
      subst this
      rfl
  | succ m ih =>
      rcases Nat.lt_or_ge r (m + 1) with hlt | hge
      · obtain ⟨x, hx⟩ := expListMod_succ_append p L m
        rw [hx, List.getD_eq_getElem?_getD,
            List.getElem?_append_left (by rw [expListMod_length]; omega),
            ← List.getD_eq_getElem?_getD]
        exact ih (by omega)
      · have : r = m + 1 := le_antisymm h hge
        subst this
        rfl

theorem finitePrime1_expListModNat_cast
    (a n : Nat) (LNat : Nat → Nat) (LMod : Nat → ZMod finitePrime1)
    (ha : a ≤ 13) (hn : n ≤ a)
    (hL : ∀ r : Nat, r ≤ n → ((LNat r : Nat) : ZMod finitePrime1) = LMod r) :
    List.map (fun x : Nat => (x : ZMod finitePrime1))
      (expListModNat finitePrime1 (invIntTable finitePrime1 a) LNat n)
      = expListMod finitePrime1 LMod n := by
  induction n with
  | zero =>
      simp [expListModNat, expListMod]
  | succ n ih =>
      have hn' : n ≤ a := le_trans (Nat.le_succ n) hn
      have ih' :
          List.map (fun x : Nat => (x : ZMod finitePrime1))
            (expListModNat finitePrime1 (invIntTable finitePrime1 a) LNat n)
            = expListMod finitePrime1 LMod n :=
        ih hn' (fun r hr => hL r (le_trans hr (Nat.le_succ n)))
      dsimp [expListModNat, expListMod]
      rw [List.map_append, ih', List.map_singleton]
      congr 1
      rw [natCast_mulMod, finitePrime1_invIntTable_cast a (n + 1) ha hn]
      have hsum :
          ((sumMod finitePrime1
            ((List.range (n + 1)).map fun t =>
              mulMod finitePrime1
                (mulMod finitePrime1 (t + 1) (LNat (t + 1)))
                ((expListModNat finitePrime1 (invIntTable finitePrime1 a) LNat n).getD
                  (n - t) 0)) : Nat) : ZMod finitePrime1) =
            ((List.range (n + 1)).map (fun (t : Nat) =>
              ((t + 1 : Nat) : ZMod finitePrime1) * LMod (t + 1) *
                (expListMod finitePrime1 LMod n).getD (n - t) 0)).sum := by
        rw [natCast_sumMod_map]
        congr 1
        refine List.map_congr_left fun t ht => ?_
        have htle : t + 1 ≤ n + 1 := by
          have ht' : t < n + 1 := List.mem_range.mp ht
          omega
        have hget :
            (((expListModNat finitePrime1 (invIntTable finitePrime1 a) LNat n).getD
              (n - t) 0 : Nat) : ZMod finitePrime1) =
                (expListMod finitePrime1 LMod n).getD (n - t) 0 := by
          have h := congrArg
            (fun xs : List (ZMod finitePrime1) =>
              xs.getD (n - t) ((0 : Nat) : ZMod finitePrime1)) ih'
          change (List.map (fun x : Nat => (x : ZMod finitePrime1))
              (expListModNat finitePrime1 (invIntTable finitePrime1 a) LNat n)).getD
                (n - t) ((0 : Nat) : ZMod finitePrime1) =
              (expListMod finitePrime1 LMod n).getD
                (n - t) ((0 : Nat) : ZMod finitePrime1) at h
          rw [List.getD_map] at h
          exact h
        rw [natCast_mulMod, natCast_mulMod, hL (t + 1) htle, hget]
      rw [hsum]
      simp [div_eq_mul_inv, mul_assoc]

theorem finitePrime1_expListModNat_getD_cast
    (a n k : Nat) (LNat : Nat → Nat) (LMod : Nat → ZMod finitePrime1)
    (ha : a ≤ 13) (hn : n ≤ a)
    (hL : ∀ r : Nat, r ≤ n → ((LNat r : Nat) : ZMod finitePrime1) = LMod r) :
    (((expListModNat finitePrime1 (invIntTable finitePrime1 a) LNat n).getD k 0 : Nat) :
        ZMod finitePrime1)
      = (expListMod finitePrime1 LMod n).getD k 0 := by
  have h := congrArg
    (fun xs : List (ZMod finitePrime1) =>
      xs.getD k ((0 : Nat) : ZMod finitePrime1))
    (finitePrime1_expListModNat_cast a n LNat LMod ha hn hL)
  change (List.map (fun x : Nat => (x : ZMod finitePrime1))
      (expListModNat finitePrime1 (invIntTable finitePrime1 a) LNat n)).getD
        k ((0 : Nat) : ZMod finitePrime1) =
      (expListMod finitePrime1 LMod n).getD k ((0 : Nat) : ZMod finitePrime1) at h
  rw [List.getD_map] at h
  exact h

theorem finitePrime1_bListModNatCore_getD_cast
    (a : Nat) (μ : List Nat) (k : Nat)
    (ha : a ≤ 13) (hμsum : μ.sum = M a) :
    (((bListModNatCore a μ).getD k 0 : Nat) : ZMod finitePrime1)
      = (expListMod finitePrime1 (fun r => -hCoeffMod finitePrime1 μ r) a).getD k 0 := by
  unfold bListModNatCore
  refine finitePrime1_expListModNat_getD_cast a a k
    (fun r => subMod finitePrime1 0 (hCoeffModNatCore a μ r))
    (fun r => -hCoeffMod finitePrime1 μ r) ha le_rfl ?_
  intro r hr
  have hp : 0 < finitePrime1 := by native_decide
  have hlt : hCoeffModNatCore a μ r < finitePrime1 := by
    unfold hCoeffModNatCore mulMod
    exact Nat.mod_lt _ hp
  have hsub : hCoeffModNatCore a μ r ≤ 0 + finitePrime1 := by
    omega
  rw [natCast_subMod_of_le_add hsub,
    finitePrime1_hCoeffModNatCore_cast a μ r ha hμsum hr]
  simp

theorem finitePrime1_correctedCoeffModNatCore_cast
    (a : Nat) (μ : List Nat)
    (ha : a ≤ 13) (hμsum : μ.sum = M a) :
    ((correctedCoeffModNatCore a μ : Nat) : ZMod finitePrime1)
      = correctedCoeffMod finitePrime1 a μ := by
  unfold correctedCoeffModNatCore correctedCoeffMod fCoeffMod expCoeffMod
  have hp : 0 < finitePrime1 := by native_decide
  have hconvlt :
      sumMod finitePrime1
        ((List.range a).map fun k =>
          mulMod finitePrime1 (kCoeffModNatCore a μ (k + 1))
            ((bListModNatCore a μ).getD (a - (k + 1)) 0)) < finitePrime1 := by
    exact sumMod_lt hp _
  have hprodlt :
      mulMod finitePrime1 (M a % finitePrime1) ((bListModNatCore a μ).getD a 0)
        < finitePrime1 := by
    unfold mulMod
    exact Nat.mod_lt _ hp
  have hsub :
      sumMod finitePrime1
        ((List.range a).map fun k =>
          mulMod finitePrime1 (kCoeffModNatCore a μ (k + 1))
            ((bListModNatCore a μ).getD (a - (k + 1)) 0))
        ≤ mulMod finitePrime1 (M a % finitePrime1) ((bListModNatCore a μ).getD a 0)
          + finitePrime1 := by
    omega
  rw [natCast_subMod_of_le_add hsub, natCast_mulMod,
    finitePrime1_bListModNatCore_getD_cast a μ a ha hμsum]
  have hconv :
      ((sumMod finitePrime1
        ((List.range a).map fun k =>
          mulMod finitePrime1 (kCoeffModNatCore a μ (k + 1))
            ((bListModNatCore a μ).getD (a - (k + 1)) 0)) : Nat) :
          ZMod finitePrime1) =
        ((List.range a).map (fun (k : Nat) =>
          kCoeffMod finitePrime1 μ (k + 1) *
            (expListMod finitePrime1 (fun r => -hCoeffMod finitePrime1 μ r) a).getD
              (a - (k + 1)) 0)).sum := by
    rw [natCast_sumMod_map]
    congr 1
    refine List.map_congr_left fun k hk => ?_
    have hklt : k < a := List.mem_range.mp hk
    have hka : k + 1 ≤ a := by omega
    rw [natCast_mulMod,
      finitePrime1_kCoeffModNatCore_cast a μ (k + 1) ha hμsum hka,
      finitePrime1_bListModNatCore_getD_cast a μ (a - (k + 1)) ha hμsum]
  rw [hconv]
  have hM : (((M a % finitePrime1 : Nat) : ZMod finitePrime1) =
      (M a : ZMod finitePrime1)) := by
    simp
  rw [hM]
  congr 1
  refine congrArg (fun xs : List (ZMod finitePrime1) => xs.sum)
    (List.map_congr_left fun k hk => ?_)
  have hklt : k < a := List.mem_range.mp hk
  have hka : a - (k + 1) ≤ a := by omega
  rw [expListMod_getD_eq finitePrime1
    (fun r => -hCoeffMod finitePrime1 μ r) (a - (k + 1)) a hka]
  rfl

theorem finitePrime1_correctedCoeffModNat_cast
    (a : Nat) (μ : List Nat)
    (ha : a ≤ 13) (hμsum : μ.sum = M a) :
    ((correctedCoeffModNat finitePrime1 a μ : Nat) : ZMod finitePrime1)
      = correctedCoeffMod finitePrime1 a μ := by
  rw [correctedCoeffModNat_eq_core]
  exact finitePrime1_correctedCoeffModNatCore_cast a μ ha hμsum

theorem finitePrime1_correctedCoeffModNat_lt (a : Nat) (μ : List Nat) :
    correctedCoeffModNat finitePrime1 a μ < finitePrime1 := by
  rw [correctedCoeffModNat_eq_core]
  unfold correctedCoeffModNatCore
  have hp : 0 < finitePrime1 := by native_decide
  refine subMod_lt hp ?_ ?_
  · unfold mulMod
    exact Nat.mod_lt _ hp
  · exact sumMod_lt hp _

theorem finitePrime1_correctedCoeffMod_nonzero_of_nat_ne
    (a : Nat) (μ : List Nat)
    (ha : a ≤ 13) (hμsum : μ.sum = M a)
    (hne : (correctedCoeffModNat finitePrime1 a μ != 0) = true) :
    correctedCoeffMod finitePrime1 a μ ≠ 0 := by
  have hnatne : correctedCoeffModNat finitePrime1 a μ ≠ 0 := by
    simpa using hne
  intro hzero
  have hcast0 : ((correctedCoeffModNat finitePrime1 a μ : Nat) : ZMod finitePrime1) = 0 := by
    rw [finitePrime1_correctedCoeffModNat_cast a μ ha hμsum, hzero]
  have hdiv : finitePrime1 ∣ correctedCoeffModNat finitePrime1 a μ :=
    (ZMod.natCast_eq_zero_iff (correctedCoeffModNat finitePrime1 a μ) finitePrime1).mp hcast0
  have hlt := finitePrime1_correctedCoeffModNat_lt a μ
  have hnat0 : correctedCoeffModNat finitePrime1 a μ = 0 := by
    obtain ⟨c, hc⟩ := hdiv
    by_cases hc0 : c = 0
    · subst c
      simpa using hc
    · have hcpos : 0 < c := Nat.pos_of_ne_zero hc0
      have : finitePrime1 ≤ correctedCoeffModNat finitePrime1 a μ := by
        rw [hc]
        exact Nat.le_mul_of_pos_right _ hcpos
      omega
  exact hnatne hnat0

theorem finitePrime1_correctedCoeffMod_ne_of_checkGenerated
    (a : Nat) (μ : List Nat)
    (ha : a ≤ 13)
    (hcheck : checkGeneratedModNat finitePrime1 a = true)
    (hmem : μ ∈ Prop51.partitions (M a)) :
    correctedCoeffMod finitePrime1 a μ ≠ 0 := by
  have hall :
      ∀ ν : List Nat, ν ∈ Prop51.partitions (M a) →
        (correctedCoeffModNatWith finitePrime1 a
          (cListModNat finitePrime1 a).toArray
          (invIntTable finitePrime1 a)
          (invPowTable finitePrime1 a (M a + 1)) ν != 0) = true := by
    simpa [checkGeneratedModNat] using hcheck
  have hnatWith := hall μ hmem
  have hnat : (correctedCoeffModNat finitePrime1 a μ != 0) = true := by
    simpa [correctedCoeffModNat] using hnatWith
  have hsum : μ.sum = M a := by
    exact (Prop51.mem_partitions_iff.mp hmem).1
  exact finitePrime1_correctedCoeffMod_nonzero_of_nat_ne a μ ha hsum hnat

theorem finitePrime1_correctedCoeffMod_ne_9_generated :
    ∀ μ ∈ Prop51.partitions (M 9), correctedCoeffMod finitePrime1 9 μ ≠ 0 := by
  intro μ hmem
  exact finitePrime1_correctedCoeffMod_ne_of_checkGenerated 9 μ
    (by decide) checkGeneratedModNat_9_prime1 hmem

theorem finitePrime1_correctedCoeffMod_ne_10_generated :
    ∀ μ ∈ Prop51.partitions (M 10), correctedCoeffMod finitePrime1 10 μ ≠ 0 := by
  intro μ hmem
  exact finitePrime1_correctedCoeffMod_ne_of_checkGenerated 10 μ
    (by decide) checkGeneratedModNat_10_prime1 hmem

end Prop52
