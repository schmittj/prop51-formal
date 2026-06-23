/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Large-range arithmetic for the printed Proposition 5.2 coefficient

This module records exact rational arithmetic from the printed-series
large-range argument.  The analytic estimates proving the lower bound are not
yet formalized here; the final rational margin used to close the proof is.
-/

import Prop52.Statement
import Prop52.Recurrence
import Prop51.Majorant
import Prop51.DNorm
import Prop51.ExpBounds
import Prop51.HPow
import Mathlib.Tactic

namespace Prop52

open PowerSeries

/-! ## Printed sign range split -/

/-- The interval-certificate range of the printed coefficient proof. -/
def PrintedCoeffNegativityMid : Prop :=
  ∀ a : Nat, 14 ≤ a → a ≤ 149 →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      printedCoeff μ a < 0

/-- The large-tail range of the printed coefficient proof. -/
def PrintedCoeffNegativityTail : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      printedCoeff μ a < 0

theorem printedCoeffNegativityLarge_of_mid_tail
    (hmid : PrintedCoeffNegativityMid)
    (htail : PrintedCoeffNegativityTail) :
    PrintedCoeffNegativityLarge := by
  intro a ha μ hμ
  by_cases h149 : a ≤ 149
  · exact hmid a ha h149 μ hμ
  · exact htail a (by omega) μ hμ

/-! ## Final large-range margin -/

/-- The explicit lower margin appearing at the end of the human large-tail
argument:

`9/(40(a-2)) - (36*delta+4)/a^2`, with
`36*delta+4 = 95444/3125`.

The formal expression is kept rational and uses coercions from `Nat` to `ℚ`.
-/
def printedLargeMargin (a : Nat) : ℚ :=
  9 / (40 * ((a : ℚ) - 2)) - (95444 / 3125) / ((a : ℚ)^2)

/-- Exact positivity of the final large-tail margin for `a >= 150`.

This is the arithmetic sentence in the paper after the analytic estimates:
at `a = 150` the margin is `3389201 / 20812500000`, and the lower bound only
improves for larger `a`.  The proof below avoids decimals by clearing
denominators and reducing to a positive quadratic. -/
theorem printedLargeMargin_pos (a : Nat) (ha : 150 ≤ a) :
    0 < printedLargeMargin a := by
  unfold printedLargeMargin
  have haQ : (150 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
  have ha_pos : (0 : ℚ) < (a : ℚ) := by nlinarith
  have ha2_pos : (0 : ℚ) < (a : ℚ) - 2 := by nlinarith
  have ha_sq_pos : (0 : ℚ) < (a : ℚ)^2 := sq_pos_of_ne_zero (by nlinarith)
  have hquad :
      0 < 28125 * (a : ℚ)^2 - 3817760 * (a : ℚ) + 7635520 := by
    have hshift : 0 ≤ (a : ℚ) - 150 := by nlinarith
    have hsquare : 0 ≤ ((a : ℚ) - 150)^2 := sq_nonneg _
    have hdecomp :
        28125 * (a : ℚ)^2 - 3817760 * (a : ℚ) + 7635520 =
          28125 * ((a : ℚ) - 150)^2 +
            4619740 * ((a : ℚ) - 150) + 67784020 := by
      ring
    rw [hdecomp]
    nlinarith
  have hmul :
      95444 / 3125 / ((a : ℚ)^2) < 9 / (40 * ((a : ℚ) - 2)) := by
    field_simp [ne_of_gt ha_sq_pos, ne_of_gt ha2_pos]
    nlinarith
  linarith

theorem printedLargeMargin_pos_150 :
    printedLargeMargin 150 = 3389201 / 20812500000 := by
  norm_num [printedLargeMargin]

/-! ## Normalized large-tail assembly

The printed proof of the range `a >= 150` proves a normalized lower bound

`printedLargeMargin a <= -T_a(μ)/(N(μ) c_a)`,

where `T_a(μ)` is `printedCoeff μ a`.  The declarations in this section
separate that remaining analytic inequality from the final sign extraction.
-/

/-- The remaining normalized analytic target for the printed large-tail range.

This is the exact final inequality in the human proof after the
Gamma/truncation/error estimates have been assembled. -/
def PrintedTailNormalizedLowerBound : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      printedLargeMargin a ≤
        (-printedCoeff μ a) / (((N μ : Nat) : ℚ) * Prop51.c a)

private theorem printedTail_N_pos {a : Nat} {μ : List Nat}
    (ha : 150 ≤ a) (hμ : Prop51.IsPartitionOf μ (M a)) :
    0 < N μ := by
  obtain ⟨hsum, _hpos⟩ := hμ
  have hN : N μ = M a + μ.length := by
    unfold N
    rw [Prop51.sum_map_add_one, hsum]
  have hM : 0 < M a := by
    unfold M
    omega
  omega

private theorem printedTail_N_ge_five_mul {a : Nat} {μ : List Nat}
    (ha : 150 ≤ a) (hμ : Prop51.IsPartitionOf μ (M a)) :
    5 * a ≤ N μ := by
  obtain ⟨hsum, _hpos⟩ := hμ
  have hN : N μ = M a + μ.length := by
    unfold N
    rw [Prop51.sum_map_add_one, hsum]
  unfold M at hN
  omega

private theorem printedTail_den_pos {a : Nat} {μ : List Nat}
    (ha : 150 ≤ a) (hμ : Prop51.IsPartitionOf μ (M a)) :
    0 < (((N μ : Nat) : ℚ) * Prop51.c a) := by
  have hN : (0 : ℚ) < ((N μ : Nat) : ℚ) := by
    exact_mod_cast printedTail_N_pos (a := a) (μ := μ) ha hμ
  have hc : 0 < Prop51.c a := Prop51.c_pos a (by omega)
  exact mul_pos hN hc

/-- Closing the printed large-tail sign from the normalized lower bound. -/
theorem printedCoeffNegativityTail_of_normalizedLowerBound
    (hbound : PrintedTailNormalizedLowerBound) :
    PrintedCoeffNegativityTail := by
  intro a ha μ hμ
  have hmargin_pos : 0 < printedLargeMargin a := printedLargeMargin_pos a ha
  have hnorm :
      0 < (-printedCoeff μ a) / (((N μ : Nat) : ℚ) * Prop51.c a) :=
    lt_of_lt_of_le hmargin_pos (hbound a ha μ hμ)
  have hden_pos :
      0 < (((N μ : Nat) : ℚ) * Prop51.c a) :=
    printedTail_den_pos (a := a) (μ := μ) ha hμ
  have hneg_pos : 0 < -printedCoeff μ a := by
    have hmul :
        0 < ((-printedCoeff μ a) / (((N μ : Nat) : ℚ) * Prop51.c a)) *
          (((N μ : Nat) : ℚ) * Prop51.c a) :=
      mul_pos hnorm hden_pos
    rwa [div_mul_cancel₀ _ hden_pos.ne'] at hmul
  linarith

theorem printedCoeffNegativityLarge_of_mid_normalizedTail
    (hmid : PrintedCoeffNegativityMid)
    (htail : PrintedTailNormalizedLowerBound) :
    PrintedCoeffNegativityLarge :=
  printedCoeffNegativityLarge_of_mid_tail hmid
    (printedCoeffNegativityTail_of_normalizedLowerBound htail)

/-! ## The printed coefficient as a power-series coefficient -/

noncomputable def printedFullFSeries (μ : List Nat) : ℚ⟦X⟧ :=
  Prop51.expSeries (fun r => -hCoeff μ r)

noncomputable def printedFullKSeries (μ : List Nat) : ℚ⟦X⟧ :=
  mk (kCoeff μ)

theorem coeff_printedFullFSeries (μ : List Nat) (a : Nat) :
    coeff a (printedFullFSeries μ) = fCoeff μ a := by
  simp [printedFullFSeries, fCoeff]

theorem coeff_printedFullKSeries (μ : List Nat) (r : Nat) :
    coeff r (printedFullKSeries μ) = kCoeff μ r := by
  simp [printedFullKSeries]

theorem coeff_printedFullFSeries_mul_KSeries (μ : List Nat) (a : Nat) :
    coeff a (printedFullFSeries μ * printedFullKSeries μ) =
      ((List.range a).map fun j : Nat =>
        kCoeff μ (j + 1) * fCoeff μ (a - (j + 1))).sum := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_printedFullFSeries, coeff_printedFullKSeries]
  rw [Finset.sum_range_succ]
  rw [Nat.sub_self]
  change (∑ x ∈ Finset.range a, fCoeff μ x * kCoeff μ (a - x)) +
      fCoeff μ a * kCoeff μ 0 =
    ∑ i ∈ Finset.range a, kCoeff μ (i + 1) * fCoeff μ (a - (i + 1))
  rw [show kCoeff μ 0 = 0 by rfl, mul_zero, add_zero]
  rw [← Finset.sum_range_reflect (fun x : Nat =>
    fCoeff μ x * kCoeff μ (a - x)) a]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjlt : j < a := Finset.mem_range.mp hj
  have hsub : a - (a - 1 - j) = j + 1 := by omega
  have hsub' : a - (j + 1) = a - 1 - j := by omega
  rw [hsub, hsub']
  ring

theorem coeff_printedFullSeries_eq_printedCoeff (μ : List Nat) (a : Nat) :
    coeff a (printedFullFSeries μ * (1 - printedFullKSeries μ)) =
      printedCoeff μ a := by
  unfold printedCoeff markedConvolution
  rw [mul_sub, mul_one, map_sub, coeff_printedFullFSeries,
    coeff_printedFullFSeries_mul_KSeries]
  rw [← bCoeff_eq_fCoeff μ a]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun k _hk => ?_)
  rw [kCoeff_eq_markedCoeff, ← bCoeff_eq_fCoeff μ (a - (k + 1))]

/-! ## Low/high split interface for the printed large tail

The human proof expands the printed coefficient using
`p = floor(a/2)`, keeps the low polynomials

`L(t) = sum_{r<=p} h_r t^r` and `J(t) = sum_{r<=p} k_r t^r`,

and writes `E = exp(-L)` and `W = E*(1-J)`.  The hard remaining work is to
prove the exact split and the estimates below from the coefficient
recurrences.  This section records the precise Lean objects and proves the
final normalized-error assembly.
-/

def printedTailP (a : Nat) : Nat :=
  a / 2

def printedTailR0 (a : Nat) : Nat :=
  a - printedTailP a - 1

private theorem N_eq_M_add_length_of_partition {a : Nat} {μ : List Nat}
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    N μ = M a + μ.length := by
  obtain ⟨hsum, _hpos⟩ := hμ
  unfold N
  rw [Prop51.sum_map_add_one, hsum]

private theorem N_le_twoM_of_partition {a : Nat} {μ : List Nat}
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    N μ ≤ 2 * M a := by
  have hN := N_eq_M_add_length_of_partition (a := a) (μ := μ) hμ
  obtain ⟨hsum, hpos⟩ := hμ
  have hlen := Prop51.length_le_sum μ hpos
  omega

private theorem sPower_nonneg_of_coeffs (μ : List Nat) (r : Nat) :
    0 ≤ sPower μ r := by
  unfold sPower
  refine List.sum_nonneg fun x hx => ?_
  simp only [List.mem_map] at hx
  obtain ⟨mi, _hmi, rfl⟩ := hx
  positivity

private theorem sPower_le_length (μ : List Nat) (r : Nat) :
    sPower μ r ≤ (μ.length : ℚ) := by
  induction μ with
  | nil =>
      simp [sPower]
  | cons mi μ ih =>
      unfold sPower at ih ⊢
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
        Nat.cast_one]
      have ih' :
          (List.map (fun mi : Nat => 1 / (((mi : ℚ) + 1)^r)) μ).sum
            ≤ (μ.length : ℚ) := by
        simpa [Nat.cast_add, Nat.cast_one] using ih
      change
        1 / (((mi : ℚ) + 1)^r) +
            (List.map (fun mi : Nat => 1 / (((mi : ℚ) + 1)^r)) μ).sum
          ≤ (μ.length : ℚ) + 1
      have hq_ge_one : (1 : ℚ) ≤ (mi : ℚ) + 1 := by
        have hmi_nonneg : (0 : ℚ) ≤ (mi : ℚ) := by exact_mod_cast Nat.zero_le mi
        linarith
      have hpow_ge_one : (1 : ℚ) ≤ (((mi : ℚ) + 1)^r) :=
        one_le_pow₀ hq_ge_one
      have hinv_le_one : 1 / (((mi : ℚ) + 1)^r) ≤ 1 := by
        simpa using
          (one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 1) hpow_ge_one)
      have hmain :
          1 / (((mi : ℚ) + 1)^r) +
              (List.map (fun mi : Nat => 1 / (((mi : ℚ) + 1)^r)) μ).sum
            ≤ 1 + (μ.length : ℚ) :=
        add_le_add hinv_le_one ih'
      calc
        1 / (((mi : ℚ) + 1)^r) +
            (List.map (fun mi : Nat => 1 / (((mi : ℚ) + 1)^r)) μ).sum
            ≤ 1 + (μ.length : ℚ) := hmain
        _ = (μ.length : ℚ) + 1 := by ring

private theorem sPower_le_N (μ : List Nat) (r : Nat) :
    sPower μ r ≤ (N μ : ℚ) := by
  have hslen := sPower_le_length μ r
  have hlenN : μ.length ≤ N μ := by
    unfold N
    rw [Prop51.sum_map_add_one]
    omega
  have hlenNQ : (μ.length : ℚ) ≤ (N μ : ℚ) := by exact_mod_cast hlenN
  exact hslen.trans hlenNQ

theorem hCoeff_nonneg_of_partition {a : Nat} {μ : List Nat}
    (_hμ : Prop51.IsPartitionOf μ (M a)) (r : Nat) :
    0 ≤ hCoeff μ r := by
  unfold hCoeff
  have hs : sPower μ r ≤ (N μ : ℚ) := sPower_le_N μ r
  exact mul_nonneg (Prop51.c_nonneg r) (sub_nonneg.mpr hs)

theorem hCoeff_le_twoM_c_of_partition {a : Nat} {μ : List Nat}
    (hμ : Prop51.IsPartitionOf μ (M a)) (r : Nat) :
    hCoeff μ r ≤ (2 * (M a : ℚ)) * Prop51.c r := by
  unfold hCoeff
  have hs : sPower μ r ≤ (N μ : ℚ) := sPower_le_N μ r
  have hs_nonneg : 0 ≤ sPower μ r := sPower_nonneg_of_coeffs μ r
  have hN : ((N μ : Nat) : ℚ) ≤ 2 * (M a : ℚ) := by
    exact_mod_cast N_le_twoM_of_partition (a := a) (μ := μ) hμ
  have hc : 0 ≤ Prop51.c r := Prop51.c_nonneg r
  calc
    Prop51.c r * ((N μ : ℚ) - sPower μ r)
        ≤ Prop51.c r * (N μ : ℚ) :=
          mul_le_mul_of_nonneg_left (by linarith) hc
    _ ≤ Prop51.c r * (2 * (M a : ℚ)) :=
          mul_le_mul_of_nonneg_left hN hc
    _ = (2 * (M a : ℚ)) * Prop51.c r := by ring

private theorem q_sub_inv_pow_le_marked_two_sub (mi r : Nat) (hmi : 1 ≤ mi) :
    ((mi + 1 : Nat) : ℚ) - 1 / (((mi + 1 : Nat) : ℚ)^r) ≤
      (mi : ℚ) * (2 - 1 / (2 : ℚ)^r) := by
  by_cases hr0 : r = 0
  · subst r
    norm_num
  by_cases hmi_one : mi = 1
  · subst mi
    norm_num
  let q : ℚ := ((mi + 1 : Nat) : ℚ)
  have hmi_ge_two : 2 ≤ mi := by omega
  have hq3 : (3 : ℚ) ≤ q := by
    dsimp [q]
    exact_mod_cast Nat.succ_le_succ hmi_ge_two
  have hqpos : (0 : ℚ) < q := by
    dsimp [q]
    exact_mod_cast Nat.succ_pos mi
  have hrpos : 1 ≤ r := by omega
  have hpow_mono : (2 : ℚ)^1 ≤ (2 : ℚ)^r :=
    pow_le_pow_right₀ (by norm_num : (0 : ℚ) ≤ 2) hrpos
  have htwo_inv_le_half : 1 / (2 : ℚ)^r ≤ 1 / 2 := by
    simpa using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < (2 : ℚ)^1) hpow_mono)
  have hfactor_ge : (3 / 2 : ℚ) ≤ 2 - 1 / (2 : ℚ)^r := by
    linarith
  have hleft_le_q : q - 1 / q^r ≤ q := by
    have hinv_nonneg : 0 ≤ 1 / q^r := by positivity
    linarith
  have hq_le_rhs : q ≤ (q - 1) * (2 - 1 / (2 : ℚ)^r) := by
    nlinarith
  have hq_minus : q - 1 = (mi : ℚ) := by
    dsimp [q]
    push_cast
    ring
  calc
    ((mi + 1 : Nat) : ℚ) - 1 / (((mi + 1 : Nat) : ℚ)^r)
        = q - 1 / q^r := by rfl
    _ ≤ q := hleft_le_q
    _ ≤ (q - 1) * (2 - 1 / (2 : ℚ)^r) := hq_le_rhs
    _ = (mi : ℚ) * (2 - 1 / (2 : ℚ)^r) := by rw [hq_minus]

private theorem N_sub_sPower_le_partition_mass_two_sub
    {μ : List Nat} (hpos : ∀ m ∈ μ, 1 ≤ m) (r : Nat) :
    (N μ : ℚ) - sPower μ r ≤ (μ.sum : ℚ) * (2 - 1 / (2 : ℚ)^r) := by
  induction μ with
  | nil =>
      simp [N, sPower]
  | cons mi μ ih =>
      have hmi : 1 ≤ mi := hpos mi (by simp)
      have htail : ∀ m ∈ μ, 1 ≤ m := by
        intro m hm
        exact hpos m (by simp [hm])
      have ih_raw := ih htail
      have ih' :
          (((List.map (fun x : Nat => x + 1) μ).sum : Nat) : ℚ) -
              (List.map (fun mi : Nat => 1 / (((mi : ℚ) + 1)^r)) μ).sum
            ≤ (μ.sum : ℚ) * (2 - 1 / (2 : ℚ)^r) := by
        unfold N sPower at ih_raw
        simpa [Nat.cast_add, Nat.cast_one] using ih_raw
      unfold N sPower
      simp only [List.map_cons, List.sum_cons, Nat.cast_add]
      have hterm := q_sub_inv_pow_le_marked_two_sub mi r hmi
      have hterm' :
          (mi : ℚ) + 1 - 1 / ((mi : ℚ) + 1)^r ≤
            (mi : ℚ) * (2 - 1 / (2 : ℚ)^r) := by
        simpa [Nat.cast_add, Nat.cast_one] using hterm
      change
        (mi : ℚ) + 1 + (((List.map (fun x => x + 1) μ).sum : Nat) : ℚ) -
            (1 / ((mi : ℚ) + 1)^r +
              (List.map (fun mi : Nat => 1 / (((mi : ℚ) + 1)^r)) μ).sum)
          ≤ ((mi : ℚ) + (μ.sum : ℚ)) * (2 - 1 / (2 : ℚ)^r)
      calc
        (mi : ℚ) + 1 + (((List.map (fun x => x + 1) μ).sum : Nat) : ℚ) -
            (1 / ((mi : ℚ) + 1)^r +
              (List.map (fun mi : Nat => 1 / (((mi : ℚ) + 1)^r)) μ).sum)
            =
          ((mi : ℚ) + 1 - 1 / ((mi : ℚ) + 1)^r) +
            ((((List.map (fun x : Nat => x + 1) μ).sum : Nat) : ℚ) -
              (List.map (fun mi : Nat => 1 / (((mi : ℚ) + 1)^r)) μ).sum) := by
            ring_nf
        _ ≤ (mi : ℚ) * (2 - 1 / (2 : ℚ)^r) +
            (μ.sum : ℚ) * (2 - 1 / (2 : ℚ)^r) :=
          add_le_add hterm' ih'
        _ = ((mi : ℚ) + (μ.sum : ℚ)) * (2 - 1 / (2 : ℚ)^r) := by
          ring

/-- The paper's simple upper bound
`h_r <= M (2 - 2^{-r}) c_r`, obtained by summing
`q_i - q_i^{-r} <= (q_i-1)(2-2^{-r})` over the partition. -/
theorem hCoeff_le_M_two_sub_twopow_c_of_partition {a : Nat} {μ : List Nat}
    (hμ : Prop51.IsPartitionOf μ (M a)) (r : Nat) :
    hCoeff μ r ≤
      ((M a : ℚ) * (2 - 1 / (2 : ℚ)^r)) * Prop51.c r := by
  unfold hCoeff
  obtain ⟨hsum, hpos⟩ := hμ
  have hD :
      (N μ : ℚ) - sPower μ r ≤ (M a : ℚ) * (2 - 1 / (2 : ℚ)^r) := by
    simpa [hsum] using
      N_sub_sPower_le_partition_mass_two_sub (μ := μ) hpos r
  have hc : 0 ≤ Prop51.c r := Prop51.c_nonneg r
  calc
    Prop51.c r * ((N μ : ℚ) - sPower μ r)
        ≤ Prop51.c r * ((M a : ℚ) * (2 - 1 / (2 : ℚ)^r)) :=
          mul_le_mul_of_nonneg_left hD hc
    _ = ((M a : ℚ) * (2 - 1 / (2 : ℚ)^r)) * Prop51.c r := by ring

private theorem markedWeight_term_le (mi r : Nat) :
    (mi : ℚ) / ((mi + 1 : Nat) : ℚ)^r ≤ (mi : ℚ) / (2 : ℚ)^r := by
  by_cases hmi : mi = 0
  · simp [hmi]
  · have hmi_pos : 1 ≤ mi := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hmi)
    have hq_ge_two : (2 : ℚ) ≤ ((mi + 1 : Nat) : ℚ) := by
      exact_mod_cast Nat.succ_le_succ hmi_pos
    have hpow_le : (2 : ℚ)^r ≤ (((mi + 1 : Nat) : ℚ)^r) :=
      pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 2) hq_ge_two r
    have hden_pos : (0 : ℚ) < (2 : ℚ)^r := by positivity
    have hfrac : (((mi + 1 : Nat) : ℚ)^r)⁻¹ ≤ ((2 : ℚ)^r)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hden_pos hpow_le
    simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hfrac (by positivity : 0 ≤ (mi : ℚ))

theorem markedWeight_nonneg_of_coeffs (μ : List Nat) (r : Nat) :
    0 ≤ markedWeight μ r := by
  unfold markedWeight
  refine List.sum_nonneg fun x hx => ?_
  simp only [List.mem_map] at hx
  obtain ⟨mi, _hmi, rfl⟩ := hx
  positivity

private theorem markedWeight_le_sum_div_two_pow (μ : List Nat) (r : Nat) :
    markedWeight μ r ≤ (μ.sum : ℚ) / (2 : ℚ)^r := by
  induction μ with
  | nil =>
      simp [markedWeight]
  | cons mi μ ih =>
      unfold markedWeight at ih ⊢
      simp only [List.map_cons, List.sum_cons, Nat.cast_add]
      have ih' :
          (List.map (fun mi : Nat => (mi : ℚ) / (((mi : ℚ) + 1)^r)) μ).sum
            ≤ (μ.sum : ℚ) / (2 : ℚ)^r := by
        simpa [Nat.cast_add, Nat.cast_one] using ih
      change
        (mi : ℚ) / (((mi : ℚ) + 1)^r) +
            (List.map
              (fun mi : Nat => (mi : ℚ) / (((mi : ℚ) + 1)^r)) μ).sum
          ≤ ((mi : ℚ) + (μ.sum : ℚ)) / (2 : ℚ)^r
      have hterm := markedWeight_term_le mi r
      have hterm' : (mi : ℚ) / (((mi : ℚ) + 1)^r) ≤ (mi : ℚ) / (2 : ℚ)^r := by
        simpa [Nat.cast_add, Nat.cast_one] using hterm
      have hmain :
          (mi : ℚ) / (((mi : ℚ) + 1)^r) +
              (List.map
                (fun mi : Nat => (mi : ℚ) / (((mi : ℚ) + 1)^r)) μ).sum
            ≤ (mi : ℚ) / (2 : ℚ)^r + (μ.sum : ℚ) / (2 : ℚ)^r :=
        add_le_add hterm' ih'
      calc
        (mi : ℚ) / (((mi : ℚ) + 1)^r) +
            (List.map
              (fun mi : Nat => (mi : ℚ) / (((mi : ℚ) + 1)^r)) μ).sum
            ≤ (mi : ℚ) / (2 : ℚ)^r + (μ.sum : ℚ) / (2 : ℚ)^r :=
          hmain
        _ = ((mi : ℚ) + (μ.sum : ℚ)) / (2 : ℚ)^r := by ring

theorem markedWeight_le_M_div_two_pow_of_partition {a : Nat} {μ : List Nat}
    (hμ : Prop51.IsPartitionOf μ (M a)) (r : Nat) :
    markedWeight μ r ≤ (M a : ℚ) / (2 : ℚ)^r := by
  obtain ⟨hsum, _hpos⟩ := hμ
  simpa [hsum] using markedWeight_le_sum_div_two_pow μ r

theorem kCoeff_nonneg (μ : List Nat) (r : Nat) :
    0 ≤ kCoeff μ r := by
  rcases r with _ | r
  · simp [kCoeff]
  rcases r with _ | r
  · simp [kCoeff, markedWeight_nonneg_of_coeffs]
  · simp [kCoeff]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (by positivity))
        (Prop51.c_nonneg (r + 1)))
      (markedWeight_nonneg_of_coeffs μ (r + 2))

theorem kCoeff_le_partition_marked_bound {a : Nat} {μ : List Nat}
    (hμ : Prop51.IsPartitionOf μ (M a)) (r : Nat) :
    kCoeff μ r ≤
      match r with
      | 0 => 0
      | 1 => 2 * ((M a : ℚ) / (2 : ℚ))
      | r + 2 =>
          12 * ((r + 1 : Nat) : ℚ) * Prop51.c (r + 1) *
            ((M a : ℚ) / (2 : ℚ)^(r + 2)) := by
  rcases r with _ | r
  · simp [kCoeff]
  rcases r with _ | r
  · simp [kCoeff]
    simpa using markedWeight_le_M_div_two_pow_of_partition (a := a) (μ := μ) hμ 1
  · simp [kCoeff]
    have hmw :=
      markedWeight_le_M_div_two_pow_of_partition (a := a) (μ := μ) hμ (r + 2)
    exact mul_le_mul_of_nonneg_left hmw
      (mul_nonneg (mul_nonneg (by norm_num) (by positivity))
        (Prop51.c_nonneg (r + 1)))

private theorem marked_summand_le_q_sub_inv_pow (mi r : Nat) :
    (mi : ℚ) / (((mi + 1 : Nat) : ℚ)^r) ≤
      ((mi + 1 : Nat) : ℚ) - 1 / (((mi + 1 : Nat) : ℚ)^r) := by
  let q : ℚ := ((mi + 1 : Nat) : ℚ)
  have hqpos : 0 < q := by
    dsimp [q]
    exact_mod_cast Nat.succ_pos mi
  have hq_ge_one : (1 : ℚ) ≤ q := by
    dsimp [q]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le mi)
  have hpow : q ≤ q^(r + 1) := by
    calc
      q = q^1 := by ring
      _ ≤ q^(r + 1) := pow_le_pow_right₀ hq_ge_one (by omega : 1 ≤ r + 1)
  have hnat : (mi : ℚ) ≤ q^(r + 1) - 1 := by
    have hq_minus : q - 1 = (mi : ℚ) := by
      dsimp [q]
      push_cast
      ring
    linarith
  rw [div_le_iff₀ (pow_pos hqpos r)]
  calc
    (mi : ℚ) ≤ q^(r + 1) - 1 := hnat
    _ = (q - 1 / q^r) * q^r := by
      field_simp [pow_ne_zero r hqpos.ne']
      ring

private theorem markedWeight_le_N_sub_sPower_of_coeffs
    (μ : List Nat) (r : Nat) :
    markedWeight μ r ≤ (N μ : ℚ) - sPower μ r := by
  induction μ with
  | nil =>
      simp [markedWeight, N, sPower]
  | cons mi μ ih =>
      unfold markedWeight N sPower at ih ⊢
      simp only [List.map_cons, List.sum_cons, Nat.cast_add]
      have hterm := marked_summand_le_q_sub_inv_pow mi r
      have hterm' :
          (mi : ℚ) / ((mi : ℚ) + 1)^r ≤
            (mi : ℚ) + 1 - 1 / ((mi : ℚ) + 1)^r := by
        simpa [Nat.cast_add, Nat.cast_one] using hterm
      change
        (mi : ℚ) / ((mi : ℚ) + 1)^r +
            (List.map (fun mi : Nat => (mi : ℚ) / (((mi : ℚ) + 1)^r)) μ).sum
          ≤
        (mi : ℚ) + 1 + (((List.map (fun x : Nat => x + 1) μ).sum : Nat) : ℚ) -
          (1 / ((mi : ℚ) + 1)^r +
            (List.map (fun mi : Nat => 1 / (((mi : ℚ) + 1)^r)) μ).sum)
      have ih' :
          (List.map (fun mi : Nat => (mi : ℚ) / (((mi : ℚ) + 1)^r)) μ).sum
            ≤
          (((List.map (fun x : Nat => x + 1) μ).sum : Nat) : ℚ) -
            (List.map (fun mi : Nat => 1 / (((mi : ℚ) + 1)^r)) μ).sum := by
        simpa [Nat.cast_add, Nat.cast_one] using ih
      calc
        (mi : ℚ) / ((mi : ℚ) + 1)^r +
            (List.map (fun mi : Nat => (mi : ℚ) / (((mi : ℚ) + 1)^r)) μ).sum
            ≤ ((mi : ℚ) + 1 - 1 / ((mi : ℚ) + 1)^r) +
              ((((List.map (fun x : Nat => x + 1) μ).sum : Nat) : ℚ) -
                (List.map (fun mi : Nat => 1 / (((mi : ℚ) + 1)^r)) μ).sum) :=
          add_le_add hterm' ih'
        _ =
          (mi : ℚ) + 1 + (((List.map (fun x : Nat => x + 1) μ).sum : Nat) : ℚ) -
            (1 / ((mi : ℚ) + 1)^r +
              (List.map (fun mi : Nat => 1 / (((mi : ℚ) + 1)^r)) μ).sum) := by
          ring

private theorem marked_summand_one_le_c_one_q_sub_inv (mi : Nat) :
    (mi : ℚ) / (((mi + 1 : Nat) : ℚ)) ≤
      Prop51.c 1 * (((mi + 1 : Nat) : ℚ) - 1 / (((mi + 1 : Nat) : ℚ))) := by
  let q : ℚ := ((mi + 1 : Nat) : ℚ)
  have hqpos : 0 < q := by
    dsimp [q]
    exact_mod_cast Nat.succ_pos mi
  have hq_ge_one : (1 : ℚ) ≤ q := by
    dsimp [q]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le mi)
  by_cases hmi : mi = 0
  · simp [hmi]
  · have hmi_pos : 1 ≤ mi := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hmi)
    rw [Prop51.c_one]
    have hnorm :
        (mi : ℚ) / ((mi : ℚ) + 1) ≤
          (5 / 6 : ℚ) * ((mi : ℚ) + 1 - 1 / ((mi : ℚ) + 1)) := by
      have hden : (0 : ℚ) < (mi : ℚ) + 1 := by positivity
      field_simp [hden.ne']
      have hmiQ : (1 : ℚ) ≤ mi := by exact_mod_cast hmi_pos
      nlinarith
    simpa [Nat.cast_add, Nat.cast_one] using hnorm

private theorem markedWeight_one_le_c_one_N_sub_sPower
    (μ : List Nat) :
    markedWeight μ 1 ≤ Prop51.c 1 * ((N μ : ℚ) - sPower μ 1) := by
  induction μ with
  | nil =>
      simp [markedWeight, N, sPower]
  | cons mi μ ih =>
      unfold markedWeight N sPower at ih ⊢
      simp only [List.map_cons, List.sum_cons, Nat.cast_add, pow_one]
      have hterm := marked_summand_one_le_c_one_q_sub_inv mi
      have hterm' :
          (mi : ℚ) / ((mi : ℚ) + 1) ≤
            Prop51.c 1 * ((mi : ℚ) + 1 - 1 / ((mi : ℚ) + 1)) := by
        simpa [Nat.cast_add, Nat.cast_one] using hterm
      have ih' :
          (List.map (fun mi : Nat => (mi : ℚ) / (((mi : ℚ) + 1))) μ).sum
            ≤ Prop51.c 1 *
              ((((List.map (fun x : Nat => x + 1) μ).sum : Nat) : ℚ) -
                (List.map (fun mi : Nat => 1 / (((mi : ℚ) + 1))) μ).sum) := by
        simpa [Nat.cast_add, Nat.cast_one] using ih
      change
        (mi : ℚ) / ((mi : ℚ) + 1) +
            (List.map (fun mi : Nat => (mi : ℚ) / (((mi : ℚ) + 1))) μ).sum
          ≤
        Prop51.c 1 *
          ((mi : ℚ) + 1 + (((List.map (fun x : Nat => x + 1) μ).sum : Nat) : ℚ) -
            (1 / ((mi : ℚ) + 1) +
              (List.map (fun mi : Nat => 1 / (((mi : ℚ) + 1))) μ).sum))
      calc
        (mi : ℚ) / ((mi : ℚ) + 1) +
            (List.map (fun mi : Nat => (mi : ℚ) / (((mi : ℚ) + 1))) μ).sum
            ≤ Prop51.c 1 * ((mi : ℚ) + 1 - 1 / ((mi : ℚ) + 1)) +
              Prop51.c 1 *
                ((((List.map (fun x : Nat => x + 1) μ).sum : Nat) : ℚ) -
                  (List.map (fun mi : Nat => 1 / (((mi : ℚ) + 1))) μ).sum) :=
          add_le_add hterm' ih'
        _ =
          Prop51.c 1 *
            ((mi : ℚ) + 1 + (((List.map (fun x : Nat => x + 1) μ).sum : Nat) : ℚ) -
              (1 / ((mi : ℚ) + 1) +
                (List.map (fun mi : Nat => 1 / (((mi : ℚ) + 1))) μ).sum)) := by
          ring

private theorem kCoeff_prefactor_le_two_c_succ_succ (r : Nat) :
    12 * ((r + 1 : Nat) : ℚ) * Prop51.c (r + 1) ≤
      2 * Prop51.c (r + 2) := by
  have hd := Prop51.d_mono (by omega : r + 1 ≤ r + 2)
  have hfac :
      (((r + 1).factorial : Nat) : ℚ) =
        ((r + 1 : Nat) : ℚ) * ((r.factorial : Nat) : ℚ) := by
    norm_num [Nat.factorial_succ]
  have hpow : (6 : ℚ)^(r + 2) = 6 * (6 : ℚ)^(r + 1) := by
    rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]
    ring
  calc
    12 * ((r + 1 : Nat) : ℚ) * Prop51.c (r + 1)
        =
      (2 * ((6 : ℚ)^(r + 2) * (((r + 1).factorial : Nat) : ℚ))) *
        Prop51.d (r + 1) := by
        rw [Prop51.c_eq_d (r + 1), show r + 1 - 1 = r by omega, hfac, hpow]
        ring
    _ ≤
      (2 * ((6 : ℚ)^(r + 2) * (((r + 1).factorial : Nat) : ℚ))) *
        Prop51.d (r + 2) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = 2 * Prop51.c (r + 2) := by
      rw [Prop51.c_eq_d (r + 2), show r + 2 - 1 = r + 1 by omega]
      ring

/-- Paper comparison `k_r <= 2 h_r` for the low-series coefficients.  The
`r = 1` head uses `c_1 = 5/6`; the higher coefficients use monotonicity of
`d_r = c_r/(6^r(r-1)!)`. -/
theorem kCoeff_le_two_hCoeff_of_partition {a : Nat} {μ : List Nat}
    (_hμ : Prop51.IsPartitionOf μ (M a)) (r : Nat) :
    kCoeff μ r ≤ 2 * hCoeff μ r := by
  rcases r with _ | r
  · simp [kCoeff, hCoeff]
  rcases r with _ | r
  · simp [kCoeff, hCoeff]
    have hhead := markedWeight_one_le_c_one_N_sub_sPower μ
    rw [Prop51.c_one] at hhead
    nlinarith
  · simp [kCoeff, hCoeff, Nat.cast_add, Nat.cast_one]
    have hpref := kCoeff_prefactor_le_two_c_succ_succ r
    have hpref' :
        12 * ((r : ℚ) + 1) * Prop51.c (r + 1) ≤
          2 * Prop51.c (r + 2) := by
      simpa [Nat.cast_add, Nat.cast_one] using hpref
    have hmw := markedWeight_le_N_sub_sPower_of_coeffs μ (r + 2)
    have hmw_nonneg := markedWeight_nonneg_of_coeffs μ (r + 2)
    have hD_nonneg : 0 ≤ (N μ : ℚ) - sPower μ (r + 2) := by
      exact sub_nonneg.mpr (sPower_le_N μ (r + 2))
    have hpref_nonneg :
        0 ≤ 12 * ((r : ℚ) + 1) * Prop51.c (r + 1) := by
      exact mul_nonneg
        (mul_nonneg (by norm_num) (by positivity))
        (Prop51.c_nonneg (r + 1))
    have hc_nonneg : 0 ≤ 2 * Prop51.c (r + 2) := by
      exact mul_nonneg (by norm_num) (Prop51.c_nonneg (r + 2))
    calc
      12 * ((r : ℚ) + 1) * Prop51.c (r + 1) *
          markedWeight μ (r + 2)
          ≤ (2 * Prop51.c (r + 2)) *
              ((N μ : ℚ) - sPower μ (r + 2)) :=
        mul_le_mul hpref' hmw hmw_nonneg hc_nonneg
      _ = 2 * (Prop51.c (r + 2) * ((N μ : ℚ) - sPower μ (r + 2))) := by
        ring

/-- Coefficients of the low polynomial `-L(t)` used to define
`E(t)=exp(-L(t))`. -/
def printedTailLowExpInput (μ : List Nat) (a r : Nat) : ℚ :=
  if r ≤ printedTailP a then -hCoeff μ r else 0

def printedTailHighExpInput (μ : List Nat) (a r : Nat) : ℚ :=
  if printedTailP a < r then -hCoeff μ r else 0

/-- The coefficient `e_s` of `E(t)=exp(-L(t))`. -/
def printedTailECoeff (μ : List Nat) (a s : Nat) : ℚ :=
  Prop51.expCoeff (printedTailLowExpInput μ a) s

noncomputable def printedTailESeries (μ : List Nat) (a : Nat) : ℚ⟦X⟧ :=
  Prop51.expSeries (printedTailLowExpInput μ a)

noncomputable def printedTailHighESeries (μ : List Nat) (a : Nat) : ℚ⟦X⟧ :=
  Prop51.expSeries (printedTailHighExpInput μ a)

noncomputable def printedTailLowJSeries (μ : List Nat) (a : Nat) : ℚ⟦X⟧ :=
  mk fun r => if 1 ≤ r ∧ r ≤ printedTailP a then kCoeff μ r else 0

noncomputable def printedTailHighKSeries (μ : List Nat) (a : Nat) : ℚ⟦X⟧ :=
  mk fun r => if printedTailP a < r then kCoeff μ r else 0

noncomputable def printedTailWSeries (μ : List Nat) (a : Nat) : ℚ⟦X⟧ :=
  printedTailESeries μ a * (1 - printedTailLowJSeries μ a)

/-- The coefficient `omega_s` of `W(t)=E(t)(1-J(t))`, written as a finite
convolution with the low marked numerator `J`. -/
def printedTailOmegaCoeff (μ : List Nat) (a s : Nat) : ℚ :=
  printedTailECoeff μ a s -
    ((List.range s).map fun j : Nat =>
      let r := j + 1
      if r ≤ printedTailP a then
        kCoeff μ r * printedTailECoeff μ a (s - r)
      else 0).sum

theorem coeff_printedTailESeries (μ : List Nat) (a s : Nat) :
    coeff s (printedTailESeries μ a) = printedTailECoeff μ a s := by
  simp [printedTailESeries, printedTailECoeff]

private theorem expCoeff_eq_zero_of_input_eq_zero_le (L : Nat → ℚ) :
    ∀ n : Nat, 1 ≤ n → (∀ r : Nat, 1 ≤ r → r ≤ n → L r = 0) →
      Prop51.expCoeff L n = 0
  | 0, hn, _ => by omega
  | n + 1, _hn, hzero => by
      have hrec := Prop51.expCoeff_succ_mul L n
      have hsum :
          (∑ t ∈ Finset.range (n + 1),
              ((t + 1 : Nat) : ℚ) * L (t + 1) * Prop51.expCoeff L (n - t)) =
            0 := by
        refine Finset.sum_eq_zero fun t ht => ?_
        have htlt : t < n + 1 := Finset.mem_range.mp ht
        have hz : L (t + 1) = 0 := hzero (t + 1) (by omega) (by omega)
        simp [hz]
      have hne : (((n + 1 : Nat) : ℚ) ≠ 0) := by
        exact_mod_cast Nat.succ_ne_zero n
      rw [hsum] at hrec
      exact (mul_eq_zero.mp hrec).resolve_left hne

private theorem expCoeff_eq_input_of_gap (L : Nat → ℚ) (p n : Nat)
    (hpn : p < n) (hnp : n ≤ 2 * p + 1)
    (hzero : ∀ r : Nat, 1 ≤ r → r ≤ p → L r = 0) :
    Prop51.expCoeff L n = L n := by
  rcases n with _ | n
  · omega
  have hrec := Prop51.expCoeff_succ_mul L n
  have hsum :
      (∑ t ∈ Finset.range (n + 1),
          ((t + 1 : Nat) : ℚ) * L (t + 1) * Prop51.expCoeff L (n - t)) =
        ((n + 1 : Nat) : ℚ) * L (n + 1) := by
    rw [Finset.sum_range_succ]
    have hprefix :
        (∑ t ∈ Finset.range n,
            ((t + 1 : Nat) : ℚ) * L (t + 1) * Prop51.expCoeff L (n - t)) =
          0 := by
      refine Finset.sum_eq_zero fun t ht => ?_
      have htlt : t < n := Finset.mem_range.mp ht
      by_cases htp : t + 1 ≤ p
      · have hz : L (t + 1) = 0 := hzero (t + 1) (by omega) htp
        simp [hz]
      · have hdeg_pos : 1 ≤ n - t := by omega
        have hdeg_le_p : n - t ≤ p := by omega
        have hE :
            Prop51.expCoeff L (n - t) = 0 :=
          expCoeff_eq_zero_of_input_eq_zero_le L (n - t) hdeg_pos
            (fun r hr1 hrle => hzero r hr1 (by omega))
        simp [hE]
    rw [hprefix]
    simp
  rw [hsum] at hrec
  have hne : (((n + 1 : Nat) : ℚ) ≠ 0) := by
    exact_mod_cast Nat.succ_ne_zero n
  exact mul_left_cancel₀ hne hrec

theorem coeff_printedTailHighESeries_eq_zero_of_le_p
    (μ : List Nat) (a s : Nat) (hs : 1 ≤ s) (hsp : s ≤ printedTailP a) :
    coeff s (printedTailHighESeries μ a) = 0 := by
  rw [printedTailHighESeries, Prop51.coeff_expSeries]
  refine expCoeff_eq_zero_of_input_eq_zero_le (printedTailHighExpInput μ a)
    s hs ?_
  intro r hr1 hrs
  unfold printedTailHighExpInput
  rw [if_neg (by omega)]

theorem coeff_printedTailHighESeries_eq_neg_hCoeff_of_gt_p_le_a
    (μ : List Nat) (a s : Nat) (hsp : printedTailP a < s) (hsa : s ≤ a) :
    coeff s (printedTailHighESeries μ a) = -hCoeff μ s := by
  rw [printedTailHighESeries, Prop51.coeff_expSeries]
  rw [expCoeff_eq_input_of_gap (printedTailHighExpInput μ a) (printedTailP a) s
    hsp (by unfold printedTailP at *; omega) ?_]
  · unfold printedTailHighExpInput
    rw [if_pos hsp]
  · intro r _hr1 hrp
    unfold printedTailHighExpInput
    rw [if_neg (by omega)]

theorem coeff_printedTailHighESeries_piecewise
    (μ : List Nat) (a s : Nat) (hsa : s ≤ a) :
    coeff s (printedTailHighESeries μ a) =
      if s = 0 then 1 else if printedTailP a < s then -hCoeff μ s else 0 := by
  by_cases hs0 : s = 0
  · subst hs0
    simp [printedTailHighESeries]
  · rw [if_neg hs0]
    by_cases hsp : printedTailP a < s
    · rw [if_pos hsp,
        coeff_printedTailHighESeries_eq_neg_hCoeff_of_gt_p_le_a μ a s hsp hsa]
    · have hspos : 1 ≤ s := by omega
      have hsle : s ≤ printedTailP a := by omega
      rw [if_neg hsp,
        coeff_printedTailHighESeries_eq_zero_of_le_p μ a s hspos hsle]

theorem coeff_printedTailLowJSeries (μ : List Nat) (a r : Nat) :
    coeff r (printedTailLowJSeries μ a) =
      if 1 ≤ r ∧ r ≤ printedTailP a then kCoeff μ r else 0 := by
  simp [printedTailLowJSeries]

theorem coeff_printedTailHighKSeries_eq_zero_of_le_p
    (μ : List Nat) (a s : Nat) (hs : s ≤ printedTailP a) :
    coeff s (printedTailHighKSeries μ a) = 0 := by
  simp [printedTailHighKSeries, hs]

theorem printedFullFSeries_eq_low_mul_high (μ : List Nat) (a : Nat) :
    printedFullFSeries μ = printedTailESeries μ a * printedTailHighESeries μ a := by
  rw [printedFullFSeries, printedTailESeries, printedTailHighESeries,
    Prop51.expSeries_mul]
  congr 1
  funext r
  unfold printedTailLowExpInput printedTailHighExpInput
  by_cases hr : r ≤ printedTailP a
  · rw [if_pos hr, if_neg (by omega)]
    ring
  · rw [if_neg hr, if_pos (by omega)]
    ring

theorem printedFullKSeries_eq_low_add_high (μ : List Nat) (a : Nat) :
    printedFullKSeries μ = printedTailLowJSeries μ a + printedTailHighKSeries μ a := by
  ext r
  simp only [printedFullKSeries, printedTailLowJSeries, printedTailHighKSeries,
    coeff_mk, map_add]
  rcases r with _ | r
  · simp [kCoeff]
  · by_cases hr : r + 1 ≤ printedTailP a
    · rw [if_pos ⟨by omega, hr⟩, if_neg (by omega)]
      ring
    · rw [if_neg (fun h => hr h.2), if_pos (by omega)]
      ring

theorem coeff_printedTail_series_split_eq_printedCoeff
    (μ : List Nat) (a : Nat) :
    coeff a
        (printedTailHighESeries μ a * printedTailWSeries μ a -
          printedTailESeries μ a * printedTailHighESeries μ a *
            printedTailHighKSeries μ a) =
      printedCoeff μ a := by
  rw [← coeff_printedFullSeries_eq_printedCoeff μ a]
  congr 1
  rw [printedFullFSeries_eq_low_mul_high,
    printedFullKSeries_eq_low_add_high]
  unfold printedTailWSeries
  ring

theorem coeff_printedTailESeries_mul_lowJSeries
    (μ : List Nat) (a s : Nat) :
    coeff s (printedTailESeries μ a * printedTailLowJSeries μ a) =
      ((List.range s).map fun j : Nat =>
        let r := j + 1
        if r ≤ printedTailP a then
          kCoeff μ r * printedTailECoeff μ a (s - r)
        else 0).sum := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_printedTailESeries, coeff_printedTailLowJSeries]
  rw [Finset.sum_range_succ]
  simp
  rw [Prop51.list_range_map_sum]
  rw [← Finset.sum_range_reflect (fun x : Nat =>
    if 1 ≤ s - x ∧ s ≤ printedTailP a + x then
      printedTailECoeff μ a x * kCoeff μ (s - x)
    else 0) s]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjlt : j < s := Finset.mem_range.mp hj
  have hs_sub : s - (s - 1 - j) = j + 1 := by omega
  have hs_sub' : s - (j + 1) = s - 1 - j := by omega
  have hcond :
      (1 ≤ s - (s - 1 - j) ∧ s ≤ printedTailP a + (s - 1 - j)) ↔
        j < printedTailP a := by
    constructor <;> intro h
    · omega
    · constructor <;> omega
  rw [hs_sub']
  by_cases hp : j < printedTailP a
  · have hc : 1 ≤ s - (s - 1 - j) ∧ s ≤ printedTailP a + (s - 1 - j) :=
      hcond.mpr hp
    rw [if_pos hc, if_pos hp, hs_sub]
    ring
  · have hc : ¬(1 ≤ s - (s - 1 - j) ∧ s ≤ printedTailP a + (s - 1 - j)) :=
      fun hc => hp (hcond.mp hc)
    rw [if_neg hc, if_neg hp]

theorem coeff_printedTailWSeries (μ : List Nat) (a s : Nat) :
    coeff s (printedTailWSeries μ a) = printedTailOmegaCoeff μ a s := by
  unfold printedTailWSeries printedTailOmegaCoeff
  rw [mul_sub, mul_one, map_sub, coeff_printedTailESeries,
    coeff_printedTailESeries_mul_lowJSeries]

theorem coeff_printedTailHighESeries_mul_W_eq_piecewiseSum
    (μ : List Nat) (a : Nat) :
    coeff a (printedTailHighESeries μ a * printedTailWSeries μ a) =
      ∑ x ∈ Finset.range (a + 1),
        (if x = 0 then printedTailOmegaCoeff μ a a
         else if printedTailP a < x then
           -hCoeff μ x * printedTailOmegaCoeff μ a (a - x)
         else 0) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_printedTailWSeries]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxle : x ≤ a := by
    have := Finset.mem_range.mp hx
    omega
  rw [coeff_printedTailHighESeries_piecewise μ a x hxle]
  by_cases hx0 : x = 0
  · subst hx0
    simp
  · rw [if_neg hx0]
    by_cases hpx : printedTailP a < x
    · rw [if_pos hpx]
      simp [hx0, hpx]
    · rw [if_neg hpx]
      simp [hx0, hpx]

theorem coeff_printedTailHighESeries_mul_highKSeries_eq_piecewise
    (μ : List Nat) (a s : Nat) (hsa : s ≤ a) :
    coeff s (printedTailHighESeries μ a * printedTailHighKSeries μ a) =
      if printedTailP a < s then kCoeff μ s else 0 := by
  have hale : a ≤ 2 * printedTailP a + 1 := by
    unfold printedTailP
    omega
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_range_succ']
  have htail :
      (∑ x ∈ Finset.range s,
          coeff (x + 1) (printedTailHighESeries μ a) *
            coeff (s - (x + 1)) (printedTailHighKSeries μ a)) = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    have hxlt : x < s := Finset.mem_range.mp hx
    by_cases hxlep : x + 1 ≤ printedTailP a
    · rw [coeff_printedTailHighESeries_eq_zero_of_le_p μ a (x + 1)
        (by omega) hxlep]
      simp
    · have hdeg_le_p : s - (x + 1) ≤ printedTailP a := by omega
      rw [coeff_printedTailHighKSeries_eq_zero_of_le_p μ a (s - (x + 1))
        hdeg_le_p]
      simp
  rw [htail]
  simp [printedTailHighESeries, printedTailHighKSeries]

theorem coeff_printedTailE_mul_highE_mul_highK_eq_piecewiseSum
    (μ : List Nat) (a : Nat) :
    coeff a
        (printedTailESeries μ a * printedTailHighESeries μ a *
          printedTailHighKSeries μ a) =
      ∑ s ∈ Finset.range (a + 1),
        (if printedTailP a < a - s then
          printedTailECoeff μ a s * kCoeff μ (a - s)
        else 0) := by
  rw [mul_assoc, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_printedTailESeries]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hsle : s ≤ a := by
    have := Finset.mem_range.mp hs
    omega
  rw [coeff_printedTailHighESeries_mul_highKSeries_eq_piecewise μ a (a - s)
    (by omega)]
  by_cases hsp : printedTailP a < a - s
  · simp [hsp]
  · simp [hsp]

/-- Integer-shape Gamma moment `Gamma(a-s)/(6^s Gamma(a))`, expressed as a
rational factorial ratio.  The large-tail proofs only use this for
`s <= printedTailR0 a`, where the subtractions do not underflow. -/
def gammaWeight (a s : Nat) : ℚ :=
  ((Nat.factorial (a - s - 1) : Nat) : ℚ) /
    ((6 : ℚ)^s * ((Nat.factorial (a - 1) : Nat) : ℚ))

def printedTailHRawSum (μ : List Nat) (a : Nat) : ℚ :=
  ((List.range (printedTailR0 a + 1)).map fun s : Nat =>
    hCoeff μ (a - s) * printedTailOmegaCoeff μ a s).sum

def printedTailKRawSum (μ : List Nat) (a : Nat) : ℚ :=
  ((List.range (printedTailR0 a + 1)).map fun s : Nat =>
    kCoeff μ (a - s) * printedTailECoeff μ a s).sum

private theorem sum_Ico_eq_sum_range_reverse_rat
    (F : Nat → ℚ) {lo hi : Nat} (hlohi : lo ≤ hi) :
    ∑ x ∈ Finset.Ico lo (hi + 1), F x =
      ∑ s ∈ Finset.range (hi + 1 - lo), F (hi - s) := by
  rw [Finset.sum_Ico_eq_sum_range]
  let K := hi + 1 - lo
  rw [← Finset.sum_range_reflect (fun j => F (lo + j)) K]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjK : j < K := Finset.mem_range.mp hj
  change F (lo + (K - 1 - j)) = F (hi - j)
  congr 1
  unfold K
  omega

theorem coeff_printedTailHighESeries_mul_W_eq_omega_sub_HRaw
    (μ : List Nat) (a : Nat) (ha : 1 ≤ a) :
    coeff a (printedTailHighESeries μ a * printedTailWSeries μ a) =
      printedTailOmegaCoeff μ a a - printedTailHRawSum μ a := by
  rw [coeff_printedTailHighESeries_mul_W_eq_piecewiseSum]
  unfold printedTailHRawSum
  rw [Prop51.list_range_map_sum]
  have hp_lt_a : printedTailP a < a := by
    unfold printedTailP
    omega
  have hlen : printedTailR0 a + 1 = a - printedTailP a := by
    unfold printedTailR0
    omega
  rw [hlen]
  let F : Nat → ℚ := fun x =>
    if x = 0 then printedTailOmegaCoeff μ a a
    else if printedTailP a < x then
      -hCoeff μ x * printedTailOmegaCoeff μ a (a - x)
    else 0
  change (∑ x ∈ Finset.range (a + 1), F x) =
    printedTailOmegaCoeff μ a a -
      ∑ s ∈ Finset.range (a - printedTailP a),
        hCoeff μ (a - s) * printedTailOmegaCoeff μ a s
  rw [Finset.range_eq_Ico]
  rw [← Finset.sum_Ico_consecutive F (by omega : 0 ≤ printedTailP a + 1)
    (by omega : printedTailP a + 1 ≤ a + 1)]
  rw [Nat.Ico_zero_eq_range]
  have hlow :
      (∑ x ∈ Finset.range (printedTailP a + 1), F x) =
        printedTailOmegaCoeff μ a a := by
    rw [Finset.sum_range_succ']
    have htail :
        (∑ x ∈ Finset.range (printedTailP a), F (x + 1)) = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      have hxlt : x < printedTailP a := Finset.mem_range.mp hx
      have hx0 : x + 1 ≠ 0 := by omega
      have hnot : ¬ printedTailP a < x + 1 := by omega
      simp [F, hnot]
    rw [htail]
    simp [F]
  have hhi :
      (∑ x ∈ Finset.Ico (printedTailP a + 1) (a + 1), F x) =
        -∑ s ∈ Finset.range (a - printedTailP a),
          hCoeff μ (a - s) * printedTailOmegaCoeff μ a s := by
    rw [sum_Ico_eq_sum_range_reverse_rat F (by omega : printedTailP a + 1 ≤ a)]
    have hlen' : a + 1 - (printedTailP a + 1) = a - printedTailP a := by omega
    rw [hlen']
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hslt : s < a - printedTailP a := Finset.mem_range.mp hs
    have hs_gt : printedTailP a < a - s := by omega
    have hs_ne : a - s ≠ 0 := by omega
    have hsub : a - (a - s) = s := by omega
    simp [F, hs_ne, hs_gt, hsub]
  rw [hlow, hhi]
  ring

theorem coeff_printedTailE_mul_highE_mul_highK_eq_KRaw
    (μ : List Nat) (a : Nat) (ha : 1 ≤ a) :
    coeff a
        (printedTailESeries μ a * printedTailHighESeries μ a *
          printedTailHighKSeries μ a) =
      printedTailKRawSum μ a := by
  rw [coeff_printedTailE_mul_highE_mul_highK_eq_piecewiseSum]
  unfold printedTailKRawSum
  rw [Prop51.list_range_map_sum]
  have hp_lt_a : printedTailP a < a := by
    unfold printedTailP
    omega
  have hlen : printedTailR0 a + 1 = a - printedTailP a := by
    unfold printedTailR0
    omega
  rw [hlen]
  let G : Nat → ℚ := fun s =>
    if printedTailP a < a - s then
      printedTailECoeff μ a s * kCoeff μ (a - s)
    else 0
  change (∑ s ∈ Finset.range (a + 1), G s) =
    ∑ s ∈ Finset.range (a - printedTailP a),
      kCoeff μ (a - s) * printedTailECoeff μ a s
  rw [Finset.range_eq_Ico]
  rw [← Finset.sum_Ico_consecutive G (by omega : 0 ≤ a - printedTailP a)
    (by omega : a - printedTailP a ≤ a + 1)]
  rw [Nat.Ico_zero_eq_range]
  have hlow :
      (∑ s ∈ Finset.range (a - printedTailP a), G s) =
        ∑ s ∈ Finset.range (a - printedTailP a),
          kCoeff μ (a - s) * printedTailECoeff μ a s := by
    refine Finset.sum_congr rfl fun s hs => ?_
    have hslt : s < a - printedTailP a := Finset.mem_range.mp hs
    have hactive : printedTailP a < a - s := by omega
    simp [G, hactive]
    ring
  have hhi :
      (∑ s ∈ Finset.Ico (a - printedTailP a) (a + 1), G s) = 0 := by
    refine Finset.sum_eq_zero fun s hs => ?_
    have hslo : a - printedTailP a ≤ s := (Finset.mem_Ico.mp hs).1
    have hnot : ¬ printedTailP a < a - s := by omega
    simp [G, hnot]
  rw [hlow, hhi, add_zero]

theorem printedCoeff_eq_tail_raw_split
    (μ : List Nat) (a : Nat) (ha : 1 ≤ a) :
    printedCoeff μ a =
      printedTailOmegaCoeff μ a a - printedTailHRawSum μ a -
        printedTailKRawSum μ a := by
  have hseries := coeff_printedTail_series_split_eq_printedCoeff μ a
  rw [map_sub, coeff_printedTailHighESeries_mul_W_eq_omega_sub_HRaw μ a ha,
    coeff_printedTailE_mul_highE_mul_highK_eq_KRaw μ a ha] at hseries
  exact hseries.symm

def printedTailMainSum (μ : List Nat) (a : Nat) : ℚ :=
  ((List.range (printedTailR0 a + 1)).map fun s : Nat =>
    gammaWeight a s * printedTailOmegaCoeff μ a s).sum

def printedTailDen (μ : List Nat) (a : Nat) : ℚ :=
  ((N μ : Nat) : ℚ) * Prop51.c a

def printedTailHNormSum (μ : List Nat) (a : Nat) : ℚ :=
  ((List.range (printedTailR0 a + 1)).map fun s : Nat =>
    hCoeff μ (a - s) * printedTailOmegaCoeff μ a s / printedTailDen μ a).sum

def printedTailKNormSum (μ : List Nat) (a : Nat) : ℚ :=
  ((List.range (printedTailR0 a + 1)).map fun s : Nat =>
    kCoeff μ (a - s) * printedTailECoeff μ a s).sum / printedTailDen μ a

def printedTailOmegaNorm (μ : List Nat) (a : Nat) : ℚ :=
  printedTailOmegaCoeff μ a a / printedTailDen μ a

def printedTailSplitRhs (μ : List Nat) (a : Nat) : ℚ :=
  printedTailHNormSum μ a + printedTailKNormSum μ a - printedTailOmegaNorm μ a

/-- Exact normalized split target corresponding to equation `(exact-split)` in
the printed proof. -/
def PrintedTailExactSplit : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      (-printedCoeff μ a) / printedTailDen μ a = printedTailSplitRhs μ a

theorem printedTailExactSplit_closed : PrintedTailExactSplit := by
  intro a ha μ _hμ
  have hraw := printedCoeff_eq_tail_raw_split μ a (by omega)
  have hHnorm :
      printedTailHNormSum μ a =
        printedTailHRawSum μ a / printedTailDen μ a := by
    unfold printedTailHNormSum printedTailHRawSum
    rw [Prop51.list_range_map_sum, Prop51.list_range_map_sum]
    rw [← Finset.sum_div]
  have hKnorm :
      printedTailKNormSum μ a =
        printedTailKRawSum μ a / printedTailDen μ a := by
    rfl
  unfold printedTailSplitRhs printedTailOmegaNorm
  rw [hHnorm, hKnorm]
  rw [hraw]
  ring

/-- The Gamma-margin plus truncation step, stated directly for the finite main
sum `sum gamma_s omega_s`. -/
def PrintedTailMainLowerBound : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      9 / (40 * ((a : ℚ) - 2)) - 1 / (a : ℚ)^2 ≤
        printedTailMainSum μ a

def printedTailHErrorBudget (a : Nat) : ℚ :=
  (86069 / 3125 : ℚ) / (a : ℚ)^2

/-- The `h_{a-s}` replacement error:
`86069/3125 = 36*(2304/3125)+1`. -/
def PrintedTailHErrorBound : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      |printedTailHNormSum μ a - printedTailMainSum μ a| ≤
        printedTailHErrorBudget a

/-- Positive coefficientwise majorant for the low exponential
`E(t)=exp(-L(t))`, using absolute logarithmic coefficients. -/
def printedTailEAbsCoeff (μ : List Nat) (a s : Nat) : ℚ :=
  Prop51.expCoeff (fun r => |printedTailLowExpInput μ a r|) s

/-- Positive coefficientwise majorant for
`W(t)=E(t)(1-J(t))`, namely `exp(|L|) * (1 + |J|)` at coefficient level. -/
def printedTailWAbsCoeff (μ : List Nat) (a s : Nat) : ℚ :=
  printedTailEAbsCoeff μ a s +
    ((List.range s).map fun j : Nat =>
      let r := j + 1
      |if r ≤ printedTailP a then
        kCoeff μ r * printedTailEAbsCoeff μ a (s - r)
      else 0|).sum

private theorem printedTailEAbsCoeff_nonneg (μ : List Nat) (a s : Nat) :
    0 ≤ printedTailEAbsCoeff μ a s := by
  unfold printedTailEAbsCoeff
  exact Prop51.expCoeff_nonneg (fun r => abs_nonneg _) s

theorem abs_printedTailECoeff_le_EAbsCoeff (μ : List Nat) (a s : Nat) :
    |printedTailECoeff μ a s| ≤ printedTailEAbsCoeff μ a s := by
  unfold printedTailECoeff printedTailEAbsCoeff
  exact Prop51.abs_expCoeff_le_of_abs_le (fun r => abs_nonneg _)
    (fun r => le_rfl) s

theorem abs_printedTailOmegaCoeff_le_WAbsCoeff
    (μ : List Nat) (a s : Nat) :
    |printedTailOmegaCoeff μ a s| ≤ printedTailWAbsCoeff μ a s := by
  unfold printedTailOmegaCoeff printedTailWAbsCoeff
  have hconv :
      |((List.range s).map fun j : Nat =>
          let r := j + 1
          if r ≤ printedTailP a then
            kCoeff μ r * printedTailECoeff μ a (s - r)
          else 0).sum|
        ≤
      ((List.range s).map fun j : Nat =>
          |let r := j + 1
          if r ≤ printedTailP a then
            kCoeff μ r * printedTailEAbsCoeff μ a (s - r)
          else 0|).sum := by
    rw [Prop51.list_range_map_sum, Prop51.list_range_map_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun j hj => ?_
    dsimp only
    by_cases hr : j + 1 ≤ printedTailP a
    · simp [hr]
      rw [abs_of_nonneg (printedTailEAbsCoeff_nonneg μ a (s - (j + 1)))]
      exact mul_le_mul_of_nonneg_left
        (abs_printedTailECoeff_le_EAbsCoeff μ a (s - (j + 1)))
        (abs_nonneg _)
    · simp [hr]
  calc
    |printedTailECoeff μ a s -
        ((List.range s).map fun j : Nat =>
          let r := j + 1
          if r ≤ printedTailP a then
            kCoeff μ r * printedTailECoeff μ a (s - r)
          else 0).sum|
        ≤
      |printedTailECoeff μ a s| +
        |((List.range s).map fun j : Nat =>
          let r := j + 1
          if r ≤ printedTailP a then
            kCoeff μ r * printedTailECoeff μ a (s - r)
          else 0).sum| := by
          calc
            |printedTailECoeff μ a s -
                ((List.range s).map fun j : Nat =>
                  let r := j + 1
                  if r ≤ printedTailP a then
                    kCoeff μ r * printedTailECoeff μ a (s - r)
                  else 0).sum|
                =
              |printedTailECoeff μ a s +
                -((List.range s).map fun j : Nat =>
                  let r := j + 1
                  if r ≤ printedTailP a then
                    kCoeff μ r * printedTailECoeff μ a (s - r)
                  else 0).sum| := by ring_nf
            _ ≤
              |printedTailECoeff μ a s| +
                |-((List.range s).map fun j : Nat =>
                  let r := j + 1
                  if r ≤ printedTailP a then
                    kCoeff μ r * printedTailECoeff μ a (s - r)
                  else 0).sum| := abs_add_le _ _
            _ =
              |printedTailECoeff μ a s| +
                |((List.range s).map fun j : Nat =>
                  let r := j + 1
                  if r ≤ printedTailP a then
                    kCoeff μ r * printedTailECoeff μ a (s - r)
                  else 0).sum| := by rw [abs_neg]
    _ ≤
      printedTailEAbsCoeff μ a s +
        ((List.range s).map fun j : Nat =>
          |let r := j + 1
          if r ≤ printedTailP a then
            kCoeff μ r * printedTailEAbsCoeff μ a (s - r)
          else 0|).sum := by
        exact add_le_add
          (abs_printedTailECoeff_le_EAbsCoeff μ a s) hconv

/-- The `W` majorant coefficientwise dominates the `E` majorant. -/
theorem printedTailEAbsCoeff_le_WAbsCoeff (μ : List Nat) (a s : Nat) :
    printedTailEAbsCoeff μ a s ≤ printedTailWAbsCoeff μ a s := by
  unfold printedTailWAbsCoeff
  have hsum_nonneg :
      0 ≤ ((List.range s).map fun j : Nat =>
        let r := j + 1
        |if r ≤ printedTailP a then
          kCoeff μ r * printedTailEAbsCoeff μ a (s - r)
        else 0|).sum := by
    refine List.sum_nonneg fun x hx => ?_
    simp only [List.mem_map] at hx
    obtain ⟨j, _hj, rfl⟩ := hx
    exact abs_nonneg _
  linarith

theorem printedTailWAbsCoeff_nonneg (μ : List Nat) (a s : Nat) :
    0 ≤ printedTailWAbsCoeff μ a s := by
  exact (printedTailEAbsCoeff_nonneg μ a s).trans
    (printedTailEAbsCoeff_le_WAbsCoeff μ a s)

private theorem coeff_pow_nonneg_of_nonneg {L : Nat → ℚ}
    (hL : ∀ r, 0 ≤ L r) :
    ∀ q s : Nat, 0 ≤ coeff s ((PowerSeries.mk L : ℚ⟦X⟧)^q)
  | 0, s => by
      by_cases hs : s = 0
      · subst s
        simp
      · simp [hs]
  | q + 1, s => by
      rw [pow_succ, coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      refine Finset.sum_nonneg fun t _ => ?_
      exact mul_nonneg (coeff_pow_nonneg_of_nonneg hL q t)
        (by simpa using hL (s - t))

private def printedTailTrianglePairs (m : Nat) : Finset (Nat × Nat) :=
  (Finset.range (m + 1)).biUnion fun t => Finset.antidiagonal t

private theorem mem_printedTailTrianglePairs {m : Nat} {ij : Nat × Nat} :
    ij ∈ printedTailTrianglePairs m ↔ ij.1 + ij.2 ≤ m := by
  unfold printedTailTrianglePairs
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨t, ht, hij⟩
    have ht' := Finset.mem_range.mp ht
    have hij' := Finset.mem_antidiagonal.mp hij
    omega
  · intro hsum
    refine ⟨ij.1 + ij.2, Finset.mem_range.mpr (by omega), ?_⟩
    exact Finset.mem_antidiagonal.mpr rfl

private theorem printedTail_antidiagonal_pairwiseDisjoint (m : Nat) :
    Set.PairwiseDisjoint (↑(Finset.range (m + 1)) : Set Nat)
      (fun t => Finset.antidiagonal t) := by
  intro a _ha b _hb hab
  exact Finset.disjoint_left.mpr (by
    intro ij hia hib
    have hia' := Finset.mem_antidiagonal.mp hia
    have hib' := Finset.mem_antidiagonal.mp hib
    exact hab (by omega))

private theorem coeff_mul_prefix_sum_le
    {F G : ℚ⟦X⟧} (hF : ∀ s, 0 ≤ coeff s F)
    (hG : ∀ s, 0 ≤ coeff s G) (m : Nat) :
    (∑ s ∈ Finset.range (m + 1), coeff s (F * G))
      ≤ (∑ i ∈ Finset.range (m + 1), coeff i F) *
          (∑ j ∈ Finset.range (m + 1), coeff j G) := by
  have hleft :
      (∑ s ∈ Finset.range (m + 1), coeff s (F * G)) =
        ∑ ij ∈ printedTailTrianglePairs m, coeff ij.1 F * coeff ij.2 G := by
    unfold printedTailTrianglePairs
    calc
      (∑ s ∈ Finset.range (m + 1), coeff s (F * G))
          =
        ∑ s ∈ Finset.range (m + 1),
          ∑ ij ∈ Finset.antidiagonal s, coeff ij.1 F * coeff ij.2 G := by
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [coeff_mul]
      _ = ∑ ij ∈ (Finset.range (m + 1)).biUnion
            (fun t => Finset.antidiagonal t),
          coeff ij.1 F * coeff ij.2 G := by
            rw [Finset.sum_biUnion (printedTail_antidiagonal_pairwiseDisjoint m)]
  rw [hleft]
  have hsubset :
      printedTailTrianglePairs m ⊆
        (Finset.range (m + 1)).product (Finset.range (m + 1)) := by
    intro ij hij
    have hsum := (mem_printedTailTrianglePairs (m := m)).mp hij
    exact (Finset.mem_product).mpr
      ⟨Finset.mem_range.mpr (by omega),
        Finset.mem_range.mpr (by omega)⟩
  calc
    (∑ ij ∈ printedTailTrianglePairs m, coeff ij.1 F * coeff ij.2 G)
        ≤ ∑ ij ∈ (Finset.range (m + 1)).product (Finset.range (m + 1)),
            coeff ij.1 F * coeff ij.2 G :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubset
            (fun ij _ _ => mul_nonneg (hF ij.1) (hG ij.2))
    _ = (∑ i ∈ Finset.range (m + 1), coeff i F) *
          (∑ j ∈ Finset.range (m + 1), coeff j G) := by
          change
            (∑ ij ∈ Finset.range (m + 1) ×ˢ Finset.range (m + 1),
              coeff ij.1 F * coeff ij.2 G) =
              (∑ i ∈ Finset.range (m + 1), coeff i F) *
                (∑ j ∈ Finset.range (m + 1), coeff j G)
          rw [Finset.sum_product]
          symm
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]

private theorem coeff_mul_weighted_prefix_sum_le
    {F G : ℚ⟦X⟧} (hF : ∀ s, 0 ≤ coeff s F)
    (hG : ∀ s, 0 ≤ coeff s G) (m : Nat) :
    (∑ s ∈ Finset.range (m + 1), (s : ℚ) * coeff s (F * G))
      ≤ (∑ i ∈ Finset.range (m + 1), (i : ℚ) * coeff i F) *
          (∑ j ∈ Finset.range (m + 1), coeff j G) +
        (∑ i ∈ Finset.range (m + 1), coeff i F) *
          (∑ j ∈ Finset.range (m + 1), (j : ℚ) * coeff j G) := by
  have hleft :
      (∑ s ∈ Finset.range (m + 1), (s : ℚ) * coeff s (F * G))
        =
        ∑ ij ∈ printedTailTrianglePairs m,
          (((ij.1 : Nat) : ℚ) + ((ij.2 : Nat) : ℚ)) *
            (coeff ij.1 F * coeff ij.2 G) := by
    unfold printedTailTrianglePairs
    calc
      (∑ s ∈ Finset.range (m + 1), (s : ℚ) * coeff s (F * G))
          =
        ∑ s ∈ Finset.range (m + 1),
          ∑ ij ∈ Finset.antidiagonal s,
            (((ij.1 : Nat) : ℚ) + ((ij.2 : Nat) : ℚ)) *
              (coeff ij.1 F * coeff ij.2 G) := by
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [coeff_mul, Finset.mul_sum]
            refine Finset.sum_congr rfl fun ij hij => ?_
            have hs : ij.1 + ij.2 = s := Finset.mem_antidiagonal.mp hij
            have hsQ : ((s : Nat) : ℚ) =
                ((ij.1 : Nat) : ℚ) + ((ij.2 : Nat) : ℚ) := by
              rw [← hs, Nat.cast_add]
            rw [hsQ]
      _ = ∑ ij ∈ (Finset.range (m + 1)).biUnion
            (fun t => Finset.antidiagonal t),
          (((ij.1 : Nat) : ℚ) + ((ij.2 : Nat) : ℚ)) *
            (coeff ij.1 F * coeff ij.2 G) := by
            rw [Finset.sum_biUnion (printedTail_antidiagonal_pairwiseDisjoint m)]
  rw [hleft]
  have hsubset :
      printedTailTrianglePairs m ⊆
        (Finset.range (m + 1)).product (Finset.range (m + 1)) := by
    intro ij hij
    have hsum := (mem_printedTailTrianglePairs (m := m)).mp hij
    exact (Finset.mem_product).mpr
      ⟨Finset.mem_range.mpr (by omega),
        Finset.mem_range.mpr (by omega)⟩
  calc
    (∑ ij ∈ printedTailTrianglePairs m,
        (((ij.1 : Nat) : ℚ) + ((ij.2 : Nat) : ℚ)) *
          (coeff ij.1 F * coeff ij.2 G))
        ≤ ∑ ij ∈ (Finset.range (m + 1)).product (Finset.range (m + 1)),
            (((ij.1 : Nat) : ℚ) + ((ij.2 : Nat) : ℚ)) *
              (coeff ij.1 F * coeff ij.2 G) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubset
            (fun ij _ _ => by
              exact mul_nonneg (add_nonneg (by positivity) (by positivity))
                (mul_nonneg (hF ij.1) (hG ij.2)))
    _ =
        (∑ i ∈ Finset.range (m + 1), (i : ℚ) * coeff i F) *
            (∑ j ∈ Finset.range (m + 1), coeff j G) +
          (∑ i ∈ Finset.range (m + 1), coeff i F) *
            (∑ j ∈ Finset.range (m + 1), (j : ℚ) * coeff j G) := by
          change
            (∑ ij ∈ Finset.range (m + 1) ×ˢ Finset.range (m + 1),
              (((ij.1 : Nat) : ℚ) + ((ij.2 : Nat) : ℚ)) *
                (coeff ij.1 F * coeff ij.2 G)) =
              (∑ i ∈ Finset.range (m + 1), (i : ℚ) * coeff i F) *
                  (∑ j ∈ Finset.range (m + 1), coeff j G) +
                (∑ i ∈ Finset.range (m + 1), coeff i F) *
                  (∑ j ∈ Finset.range (m + 1), (j : ℚ) * coeff j G)
          rw [Finset.sum_product]
          calc
            (∑ x ∈ Finset.range (m + 1),
              ∑ x_1 ∈ Finset.range (m + 1),
                (((x : Nat) : ℚ) + ((x_1 : Nat) : ℚ)) *
                  (coeff x F * coeff x_1 G))
                =
              (∑ x ∈ Finset.range (m + 1),
                ∑ x_1 ∈ Finset.range (m + 1),
                  ((x : ℚ) * coeff x F) * coeff x_1 G) +
              (∑ x ∈ Finset.range (m + 1),
                ∑ x_1 ∈ Finset.range (m + 1),
                  coeff x F * ((x_1 : ℚ) * coeff x_1 G)) := by
                rw [← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun j _ => ?_
                ring
            _ =
              (∑ i ∈ Finset.range (m + 1), (i : ℚ) * coeff i F) *
                  (∑ j ∈ Finset.range (m + 1), coeff j G) +
                (∑ i ∈ Finset.range (m + 1), coeff i F) *
                  (∑ j ∈ Finset.range (m + 1), (j : ℚ) * coeff j G) := by
                congr 1
                · symm
                  rw [Finset.sum_mul]
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [Finset.mul_sum]
                · symm
                  rw [Finset.sum_mul]
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [Finset.mul_sum]

private theorem coeff_pow_prefix_sum_le_total_pow {L : Nat → ℚ}
    (hL : ∀ r, 0 ≤ L r) (m q : Nat) :
    (∑ s ∈ Finset.range (m + 1),
        coeff s ((PowerSeries.mk L : ℚ⟦X⟧)^q))
      ≤ (∑ r ∈ Finset.range (m + 1), L r)^q := by
  induction q with
  | zero =>
      have hsum :
          (∑ s ∈ Finset.range (m + 1),
              coeff s ((PowerSeries.mk L : ℚ⟦X⟧)^0)) = 1 := by
        rw [pow_zero]
        rw [Finset.sum_eq_single (0 : Nat)]
        · simp
        · intro b _hb hb0
          simp [hb0]
        · intro h0
          simp at h0
      rw [hsum]
      simp
  | succ q ih =>
      let T : ℚ := ∑ r ∈ Finset.range (m + 1), L r
      have hT : 0 ≤ T := by
        dsimp [T]
        exact Finset.sum_nonneg fun r _ => hL r
      have hprod := coeff_mul_prefix_sum_le
        (F := (PowerSeries.mk L : ℚ⟦X⟧)^q)
        (G := PowerSeries.mk L)
        (fun s => coeff_pow_nonneg_of_nonneg hL q s)
        (fun s => by simpa using hL s) m
      calc
        (∑ s ∈ Finset.range (m + 1),
            coeff s ((PowerSeries.mk L : ℚ⟦X⟧)^(q + 1)))
            =
          ∑ s ∈ Finset.range (m + 1),
            coeff s (((PowerSeries.mk L : ℚ⟦X⟧)^q) *
              PowerSeries.mk L) := by
              rw [pow_succ]
        _ ≤ (∑ i ∈ Finset.range (m + 1),
              coeff i ((PowerSeries.mk L : ℚ⟦X⟧)^q)) *
              (∑ j ∈ Finset.range (m + 1), coeff j (PowerSeries.mk L : ℚ⟦X⟧)) :=
            hprod
        _ = (∑ i ∈ Finset.range (m + 1),
              coeff i ((PowerSeries.mk L : ℚ⟦X⟧)^q)) *
              (∑ j ∈ Finset.range (m + 1), L j) := by
            congr 1
            refine Finset.sum_congr rfl fun j _ => ?_
            simp
        _ ≤ T^q * T :=
            mul_le_mul_of_nonneg_right ih hT
        _ = T^(q + 1) := by
            rw [pow_succ]

private theorem expCoeff_scale_local (rho : ℚ) (L : Nat → ℚ) :
    ∀ m : Nat,
      Prop51.expCoeff (fun r => rho^r * L r) m =
        rho^m * Prop51.expCoeff L m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      cases m with
      | zero =>
          simp
      | succ n =>
          have hscaled := Prop51.expCoeff_succ_mul
            (fun r => rho^r * L r) n
          have hbase := Prop51.expCoeff_succ_mul L n
          have hsum :
              (∑ t ∈ Finset.range (n + 1),
                ((t + 1 : Nat) : ℚ) * (rho^(t + 1) * L (t + 1)) *
                  Prop51.expCoeff (fun r => rho^r * L r) (n - t))
                =
              rho^(n + 1) *
                ∑ t ∈ Finset.range (n + 1),
                  ((t + 1 : Nat) : ℚ) * L (t + 1) *
                    Prop51.expCoeff L (n - t) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun t ht => ?_
            have ht_le : t ≤ n := by
              have ht' := Finset.mem_range.mp ht
              omega
            have hpow : rho^(t + 1) * rho^(n - t) = rho^(n + 1) := by
              rw [← pow_add]
              congr 1
              omega
            rw [ih (n - t) (by omega)]
            calc
              ((t + 1 : Nat) : ℚ) * (rho^(t + 1) * L (t + 1)) *
                  (rho^(n - t) * Prop51.expCoeff L (n - t))
                  = rho^(t + 1) * rho^(n - t) *
                      (((t + 1 : Nat) : ℚ) * L (t + 1) *
                        Prop51.expCoeff L (n - t)) := by
                    ring
              _ = rho^(n + 1) *
                      (((t + 1 : Nat) : ℚ) * L (t + 1) *
                        Prop51.expCoeff L (n - t)) := by
                    rw [hpow]
          have hmul :
              ((n + 1 : Nat) : ℚ) *
                  Prop51.expCoeff (fun r => rho^r * L r) (n + 1)
                =
              ((n + 1 : Nat) : ℚ) *
                  (rho^(n + 1) * Prop51.expCoeff L (n + 1)) := by
            rw [hscaled, hsum, ← hbase]
            ring
          exact mul_left_cancel₀ (by positivity : ((n + 1 : Nat) : ℚ) ≠ 0) hmul

private def printedTailExpPrefix (y : ℚ) (m : Nat) : ℚ :=
  ∑ q ∈ Finset.range (m + 1), y^q / (q.factorial : ℚ)

private theorem printedTailExpPrefix_mono_arg {x y : ℚ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (m : Nat) :
    printedTailExpPrefix x m ≤ printedTailExpPrefix y m := by
  unfold printedTailExpPrefix
  refine Finset.sum_le_sum fun q _ => ?_
  exact div_le_div_of_nonneg_right
    (pow_le_pow_left₀ hx hxy q) (by positivity)

private theorem printedTailExpPrefix_le_203_50 {y : ℚ}
    (hy0 : 0 ≤ y) (hy : y ≤ 7 / 5) (m : Nat) :
    printedTailExpPrefix y m ≤ 203 / 50 := by
  have hmono := printedTailExpPrefix_mono_arg hy0 hy m
  have hupper := Prop51.sum_exp_le (7 / 5 : ℚ) 5
    (by norm_num) (by norm_num) (m + 1)
  have hconst :
      (∑ t ∈ Finset.range 5, (7 / 5 : ℚ)^t / (t.factorial : ℚ)) +
          ((7 / 5 : ℚ)^5 / (Nat.factorial 5 : ℚ)) *
            (1 / (1 - (7 / 5 : ℚ) / (5 : ℚ))) ≤ 203 / 50 := by
    norm_num
  exact hmono.trans (hupper.trans hconst)

private theorem printedTailExpPrefix_le_182 {y : ℚ}
    (hy0 : 0 ≤ y) (hy : y ≤ 26 / 5) (m : Nat) :
    printedTailExpPrefix y m ≤ 182 := by
  have hmono := printedTailExpPrefix_mono_arg hy0 hy m
  have hupper := Prop51.sum_exp_le (26 / 5 : ℚ) 11
    (by norm_num) (by norm_num) (m + 1)
  have hconst :
      (∑ t ∈ Finset.range 11, (26 / 5 : ℚ)^t / (t.factorial : ℚ)) +
          ((26 / 5 : ℚ)^11 / (Nat.factorial 11 : ℚ)) *
            (1 / (1 - (26 / 5 : ℚ) / (11 : ℚ))) ≤ 182 := by
    norm_num
  exact hmono.trans (hupper.trans hconst)

private theorem expCoeff_point_sum_le_expPrefix {L : Nat → ℚ}
    (hL0 : L 0 = 0) (hL : ∀ r, 0 ≤ L r)
    {x : ℚ} (hx : 0 ≤ x) (m : Nat) :
    (∑ s ∈ Finset.range (m + 1), Prop51.expCoeff L s * x^s)
      ≤ printedTailExpPrefix
          (∑ r ∈ Finset.range (m + 1), x^r * L r) m := by
  let Lx : Nat → ℚ := fun r => x^r * L r
  have hLx0 : Lx 0 = 0 := by
    dsimp [Lx]
    simp [hL0]
  have hLx_nonneg : ∀ r, 0 ≤ Lx r := by
    intro r
    dsimp [Lx]
    exact mul_nonneg (pow_nonneg hx r) (hL r)
  have hscale :
      (∑ s ∈ Finset.range (m + 1), Prop51.expCoeff L s * x^s)
        =
      ∑ s ∈ Finset.range (m + 1), Prop51.expCoeff Lx s := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [expCoeff_scale_local x L s]
    ring
  rw [hscale]
  unfold printedTailExpPrefix
  calc
    (∑ s ∈ Finset.range (m + 1), Prop51.expCoeff Lx s)
        =
      ∑ s ∈ Finset.range (m + 1),
        ∑ q ∈ Finset.range (s + 1),
          coeff s ((PowerSeries.mk Lx : ℚ⟦X⟧)^q) /
            (q.factorial : ℚ) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Prop51.expCoeff_eq_sum_pow Lx hLx0 s]
    _ ≤ ∑ s ∈ Finset.range (m + 1),
        ∑ q ∈ Finset.range (m + 1),
          coeff s ((PowerSeries.mk Lx : ℚ⟦X⟧)^q) /
            (q.factorial : ℚ) := by
          refine Finset.sum_le_sum fun s hs => ?_
          have hs_le : s ≤ m := by
            have hs' := Finset.mem_range.mp hs
            omega
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (fun q hq => by
              exact Finset.mem_range.mpr (by
                have hq' := Finset.mem_range.mp hq
                omega))
            (fun q _ _ => by
              exact div_nonneg
                (coeff_pow_nonneg_of_nonneg hLx_nonneg q s)
                (by positivity))
    _ = ∑ q ∈ Finset.range (m + 1),
        (∑ s ∈ Finset.range (m + 1),
          coeff s ((PowerSeries.mk Lx : ℚ⟦X⟧)^q)) /
            (q.factorial : ℚ) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [← Finset.sum_div]
    _ ≤ ∑ q ∈ Finset.range (m + 1),
        (∑ r ∈ Finset.range (m + 1), x^r * L r)^q /
          (q.factorial : ℚ) := by
          refine Finset.sum_le_sum fun q _ => ?_
          exact div_le_div_of_nonneg_right
            (coeff_pow_prefix_sum_le_total_pow hLx_nonneg m q)
            (by positivity)

private theorem expCoeff_deriv_point_sum_le_expPrefix {L : Nat → ℚ}
    (hL0 : L 0 = 0) (hL : ∀ r, 0 ≤ L r)
    {x : ℚ} (hx : 0 ≤ x) (m : Nat) :
    (∑ s ∈ Finset.range (m + 1),
        (s : ℚ) * Prop51.expCoeff L s * x^s)
      ≤ (∑ r ∈ Finset.range (m + 1),
          (r : ℚ) * (x^r * L r)) *
          printedTailExpPrefix
            (∑ r ∈ Finset.range (m + 1), x^r * L r) m := by
  let Lx : Nat → ℚ := fun r => x^r * L r
  let U : ℚ⟦X⟧ := PowerSeries.mk fun r => (r : ℚ) * Lx r
  let E : ℚ⟦X⟧ := Prop51.expSeries Lx
  have hLx0 : Lx 0 = 0 := by
    dsimp [Lx]
    simp [hL0]
  have hLx_nonneg : ∀ r, 0 ≤ Lx r := by
    intro r
    dsimp [Lx]
    exact mul_nonneg (pow_nonneg hx r) (hL r)
  have hscale :
      (∑ s ∈ Finset.range (m + 1),
          (s : ℚ) * Prop51.expCoeff L s * x^s)
        =
      ∑ s ∈ Finset.range (m + 1),
        (s : ℚ) * Prop51.expCoeff Lx s := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [expCoeff_scale_local x L s]
    ring
  have hcoeff :
      ∀ s : Nat, (s : ℚ) * Prop51.expCoeff Lx s = coeff s (U * E) := by
    intro s
    have h := congrArg (fun F : ℚ⟦X⟧ => coeff s F)
      (Prop51.theta_expSeries Lx)
    change coeff s (Prop51.theta (Prop51.expSeries Lx)) =
      coeff s ((PowerSeries.mk fun r => (r : ℚ) * Lx r) *
        Prop51.expSeries Lx) at h
    rw [Prop51.coeff_theta, Prop51.coeff_expSeries] at h
    simpa [U, E] using h
  have hEpoint :
      (∑ s ∈ Finset.range (m + 1), Prop51.expCoeff Lx s)
        ≤ printedTailExpPrefix
            (∑ r ∈ Finset.range (m + 1), x^r * L r) m := by
    have h := expCoeff_point_sum_le_expPrefix hLx0 hLx_nonneg
      (x := (1 : ℚ)) (by norm_num) m
    simpa [Lx] using h
  have hU_nonneg :
      0 ≤ ∑ r ∈ Finset.range (m + 1), (r : ℚ) * (x^r * L r) := by
    exact Finset.sum_nonneg fun r _ => by
      exact mul_nonneg (by positivity) (mul_nonneg (pow_nonneg hx r) (hL r))
  rw [hscale]
  calc
    (∑ s ∈ Finset.range (m + 1),
        (s : ℚ) * Prop51.expCoeff Lx s)
        = ∑ s ∈ Finset.range (m + 1), coeff s (U * E) := by
          refine Finset.sum_congr rfl fun s _ => hcoeff s
    _ ≤ (∑ r ∈ Finset.range (m + 1), coeff r U) *
          (∑ s ∈ Finset.range (m + 1), coeff s E) :=
        coeff_mul_prefix_sum_le
          (F := U) (G := E)
          (fun r => by
            dsimp [U]
            simp
            exact mul_nonneg (by positivity) (hLx_nonneg r))
          (fun s => by
            dsimp [E]
            simpa using Prop51.expCoeff_nonneg hLx_nonneg s)
          m
    _ = (∑ r ∈ Finset.range (m + 1), (r : ℚ) * (x^r * L r)) *
          (∑ s ∈ Finset.range (m + 1), Prop51.expCoeff Lx s) := by
          have hUsum :
              (∑ r ∈ Finset.range (m + 1), coeff r U) =
                ∑ r ∈ Finset.range (m + 1), (r : ℚ) * (x^r * L r) := by
            refine Finset.sum_congr rfl fun r _ => ?_
            simp [U, Lx]
          have hEsum :
              (∑ s ∈ Finset.range (m + 1), coeff s E) =
                ∑ s ∈ Finset.range (m + 1), Prop51.expCoeff Lx s := by
            refine Finset.sum_congr rfl fun s _ => ?_
            simp [E]
          rw [hUsum, hEsum]
    _ ≤ (∑ r ∈ Finset.range (m + 1), (r : ℚ) * (x^r * L r)) *
          printedTailExpPrefix
            (∑ r ∈ Finset.range (m + 1), x^r * L r) m :=
          mul_le_mul_of_nonneg_left hEpoint hU_nonneg

private def printedTailLowAbsInput (μ : List Nat) (a r : Nat) : ℚ :=
  |printedTailLowExpInput μ a r|

private noncomputable def printedTailEAbsPointSeries
    (μ : List Nat) (a : Nat) (x : ℚ) : ℚ⟦X⟧ :=
  mk fun s => printedTailEAbsCoeff μ a s * x^s

private def printedTailJAbsCoeff (μ : List Nat) (a r : Nat) : ℚ :=
  if 1 ≤ r ∧ r ≤ printedTailP a then kCoeff μ r else 0

private noncomputable def printedTailJAbsPointSeries
    (μ : List Nat) (a : Nat) (x : ℚ) : ℚ⟦X⟧ :=
  mk fun r => printedTailJAbsCoeff μ a r * x^r

private theorem coeff_printedTailEAbsPointSeries
    (μ : List Nat) (a : Nat) (x : ℚ) (s : Nat) :
    coeff s (printedTailEAbsPointSeries μ a x) =
      printedTailEAbsCoeff μ a s * x^s := by
  simp [printedTailEAbsPointSeries]

private theorem coeff_printedTailJAbsPointSeries
    (μ : List Nat) (a : Nat) (x : ℚ) (r : Nat) :
    coeff r (printedTailJAbsPointSeries μ a x) =
      printedTailJAbsCoeff μ a r * x^r := by
  simp [printedTailJAbsPointSeries]

private theorem printedTailLowAbsInput_zero
    (μ : List Nat) (a : Nat) :
    printedTailLowAbsInput μ a 0 = 0 := by
  simp [printedTailLowAbsInput, printedTailLowExpInput, hCoeff]

private theorem printedTailLowAbsInput_nonneg
    (μ : List Nat) (a r : Nat) :
    0 ≤ printedTailLowAbsInput μ a r := by
  unfold printedTailLowAbsInput
  exact abs_nonneg _

private theorem printedTailJAbsCoeff_nonneg
    (μ : List Nat) (a r : Nat) :
    0 ≤ printedTailJAbsCoeff μ a r := by
  unfold printedTailJAbsCoeff
  by_cases hr : 1 ≤ r ∧ r ≤ printedTailP a
  · simp [hr, kCoeff_nonneg μ r]
  · simp [hr]

private theorem coeff_printedTailEAbsPointSeries_mul_JAbsPointSeries
    (μ : List Nat) (a : Nat) (x : ℚ) (s : Nat) :
    coeff s (printedTailEAbsPointSeries μ a x *
        printedTailJAbsPointSeries μ a x) =
      ((List.range s).map fun j : Nat =>
        let r := j + 1
        (if r ≤ printedTailP a then
          kCoeff μ r * printedTailEAbsCoeff μ a (s - r)
        else 0) * x^s).sum := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_printedTailEAbsPointSeries,
    coeff_printedTailJAbsPointSeries, printedTailJAbsCoeff]
  rw [Finset.sum_range_succ]
  simp
  rw [Prop51.list_range_map_sum]
  rw [← Finset.sum_range_reflect (fun y : Nat =>
    if 1 ≤ s - y ∧ s ≤ printedTailP a + y then
      (printedTailEAbsCoeff μ a y * x^y) *
        (kCoeff μ (s - y) * x^(s - y))
    else 0) s]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjlt : j < s := Finset.mem_range.mp hj
  have hs_sub : s - (s - 1 - j) = j + 1 := by omega
  have hs_sub' : s - (j + 1) = s - 1 - j := by omega
  have hpow : x^(s - 1 - j) * x^(j + 1) = x^s := by
    rw [← pow_add]
    congr 1
    omega
  have hcond :
      (1 ≤ s - (s - 1 - j) ∧ s ≤ printedTailP a + (s - 1 - j)) ↔
        j < printedTailP a := by
    constructor <;> intro h
    · omega
    · constructor <;> omega
  rw [hs_sub']
  by_cases hp : j < printedTailP a
  · have hc : 1 ≤ s - (s - 1 - j) ∧
        s ≤ printedTailP a + (s - 1 - j) := hcond.mpr hp
    rw [if_pos hc, if_pos hp, hs_sub]
    calc
      (printedTailEAbsCoeff μ a (s - 1 - j) * x^(s - 1 - j)) *
          (kCoeff μ (j + 1) * x^(j + 1))
          =
        (kCoeff μ (j + 1) * printedTailEAbsCoeff μ a (s - 1 - j)) *
          (x^(s - 1 - j) * x^(j + 1)) := by ring
      _ =
        (kCoeff μ (j + 1) * printedTailEAbsCoeff μ a (s - 1 - j)) *
          x^s := by rw [hpow]
  · have hc : ¬(1 ≤ s - (s - 1 - j) ∧
        s ≤ printedTailP a + (s - 1 - j)) :=
      fun hc => hp (hcond.mp hc)
    rw [if_neg hc, if_neg hp]

private theorem printedTailWAbsCoeff_point_eq_coeff
    (μ : List Nat) (a : Nat) (x : ℚ) (s : Nat) :
    printedTailWAbsCoeff μ a s * x^s =
      coeff s (printedTailEAbsPointSeries μ a x +
        printedTailEAbsPointSeries μ a x *
          printedTailJAbsPointSeries μ a x) := by
  have hconv :
      ((List.range s).map fun j : Nat =>
        let r := j + 1
        |if r ≤ printedTailP a then
          kCoeff μ r * printedTailEAbsCoeff μ a (s - r)
        else 0|).sum * x^s =
      ((List.range s).map fun j : Nat =>
        let r := j + 1
        (if r ≤ printedTailP a then
          kCoeff μ r * printedTailEAbsCoeff μ a (s - r)
        else 0) * x^s).sum := by
    rw [Prop51.list_range_map_sum, Prop51.list_range_map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only
    by_cases hr : j + 1 ≤ printedTailP a
    · simp [hr, abs_of_nonneg
        (mul_nonneg (kCoeff_nonneg μ (j + 1))
          (printedTailEAbsCoeff_nonneg μ a (s - (j + 1))))]
    · simp [hr]
  calc
    printedTailWAbsCoeff μ a s * x^s
        =
      printedTailEAbsCoeff μ a s * x^s +
        ((List.range s).map fun j : Nat =>
          let r := j + 1
          |if r ≤ printedTailP a then
            kCoeff μ r * printedTailEAbsCoeff μ a (s - r)
          else 0|).sum * x^s := by
          unfold printedTailWAbsCoeff
          ring
    _ =
      printedTailEAbsCoeff μ a s * x^s +
        ((List.range s).map fun j : Nat =>
          let r := j + 1
          (if r ≤ printedTailP a then
            kCoeff μ r * printedTailEAbsCoeff μ a (s - r)
          else 0) * x^s).sum := by
          rw [hconv]
    _ =
      coeff s (printedTailEAbsPointSeries μ a x +
        printedTailEAbsPointSeries μ a x *
          printedTailJAbsPointSeries μ a x) := by
          rw [map_add, coeff_printedTailEAbsPointSeries,
            coeff_printedTailEAbsPointSeries_mul_JAbsPointSeries]

private theorem printedTailW_point_sum_le_product
    (μ : List Nat) (a : Nat) {x : ℚ} (hx : 0 ≤ x) (m : Nat) :
    (∑ s ∈ Finset.range (m + 1),
        printedTailWAbsCoeff μ a s * x^s)
      ≤ (∑ s ∈ Finset.range (m + 1),
          printedTailEAbsCoeff μ a s * x^s) *
        (1 + ∑ r ∈ Finset.range (m + 1),
          printedTailJAbsCoeff μ a r * x^r) := by
  let E := printedTailEAbsPointSeries μ a x
  let J := printedTailJAbsPointSeries μ a x
  have hE_nonneg : ∀ s : Nat, 0 ≤ coeff s E := by
    intro s
    dsimp [E]
    rw [coeff_printedTailEAbsPointSeries]
    exact mul_nonneg (printedTailEAbsCoeff_nonneg μ a s)
      (pow_nonneg hx s)
  have hJ_nonneg : ∀ r : Nat, 0 ≤ coeff r J := by
    intro r
    dsimp [J]
    rw [coeff_printedTailJAbsPointSeries]
    exact mul_nonneg (printedTailJAbsCoeff_nonneg μ a r)
      (pow_nonneg hx r)
  have hprod := coeff_mul_prefix_sum_le
    (F := E) (G := J) hE_nonneg hJ_nonneg m
  calc
    (∑ s ∈ Finset.range (m + 1),
        printedTailWAbsCoeff μ a s * x^s)
        =
      ∑ s ∈ Finset.range (m + 1), coeff s (E + E * J) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        exact printedTailWAbsCoeff_point_eq_coeff μ a x s
    _ =
      (∑ s ∈ Finset.range (m + 1), coeff s E) +
        ∑ s ∈ Finset.range (m + 1), coeff s (E * J) := by
        simp [map_add, Finset.sum_add_distrib]
    _ ≤
      (∑ s ∈ Finset.range (m + 1), coeff s E) +
        (∑ s ∈ Finset.range (m + 1), coeff s E) *
          (∑ r ∈ Finset.range (m + 1), coeff r J) := by
        linarith [hprod]
    _ =
      (∑ s ∈ Finset.range (m + 1),
          printedTailEAbsCoeff μ a s * x^s) *
        (1 + ∑ r ∈ Finset.range (m + 1),
          printedTailJAbsCoeff μ a r * x^r) := by
        simp [E, J, coeff_printedTailEAbsPointSeries,
          coeff_printedTailJAbsPointSeries]
        ring

private theorem printedTailW_deriv_point_sum_le_product
    (μ : List Nat) (a : Nat) {x : ℚ} (hx : 0 ≤ x) (m : Nat) :
    (∑ s ∈ Finset.range (m + 1),
        (s : ℚ) * printedTailWAbsCoeff μ a s * x^s)
      ≤ (∑ s ∈ Finset.range (m + 1),
          (s : ℚ) * printedTailEAbsCoeff μ a s * x^s) *
          (1 + ∑ r ∈ Finset.range (m + 1),
            printedTailJAbsCoeff μ a r * x^r) +
        (∑ s ∈ Finset.range (m + 1),
          printedTailEAbsCoeff μ a s * x^s) *
          (∑ r ∈ Finset.range (m + 1),
            (r : ℚ) * printedTailJAbsCoeff μ a r * x^r) := by
  let E := printedTailEAbsPointSeries μ a x
  let J := printedTailJAbsPointSeries μ a x
  have hE_nonneg : ∀ s : Nat, 0 ≤ coeff s E := by
    intro s
    dsimp [E]
    rw [coeff_printedTailEAbsPointSeries]
    exact mul_nonneg (printedTailEAbsCoeff_nonneg μ a s)
      (pow_nonneg hx s)
  have hJ_nonneg : ∀ r : Nat, 0 ≤ coeff r J := by
    intro r
    dsimp [J]
    rw [coeff_printedTailJAbsPointSeries]
    exact mul_nonneg (printedTailJAbsCoeff_nonneg μ a r)
      (pow_nonneg hx r)
  have hprod := coeff_mul_weighted_prefix_sum_le
    (F := E) (G := J) hE_nonneg hJ_nonneg m
  calc
    (∑ s ∈ Finset.range (m + 1),
        (s : ℚ) * printedTailWAbsCoeff μ a s * x^s)
        =
      ∑ s ∈ Finset.range (m + 1),
        (s : ℚ) * coeff s (E + E * J) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [← printedTailWAbsCoeff_point_eq_coeff μ a x s]
        ring
    _ =
      (∑ s ∈ Finset.range (m + 1), (s : ℚ) * coeff s E) +
        ∑ s ∈ Finset.range (m + 1), (s : ℚ) * coeff s (E * J) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [map_add]
        ring
    _ ≤
      (∑ s ∈ Finset.range (m + 1), (s : ℚ) * coeff s E) +
        ((∑ s ∈ Finset.range (m + 1), (s : ℚ) * coeff s E) *
            (∑ r ∈ Finset.range (m + 1), coeff r J) +
          (∑ s ∈ Finset.range (m + 1), coeff s E) *
            (∑ r ∈ Finset.range (m + 1), (r : ℚ) * coeff r J)) := by
        linarith [hprod]
    _ =
      (∑ s ∈ Finset.range (m + 1),
          (s : ℚ) * printedTailEAbsCoeff μ a s * x^s) *
          (1 + ∑ r ∈ Finset.range (m + 1),
            printedTailJAbsCoeff μ a r * x^r) +
        (∑ s ∈ Finset.range (m + 1),
          printedTailEAbsCoeff μ a s * x^s) *
          (∑ r ∈ Finset.range (m + 1),
            (r : ℚ) * printedTailJAbsCoeff μ a r * x^r) := by
        have hEw :
            (∑ s ∈ Finset.range (m + 1), (s : ℚ) * coeff s E) =
              ∑ s ∈ Finset.range (m + 1),
                (s : ℚ) * printedTailEAbsCoeff μ a s * x^s := by
          refine Finset.sum_congr rfl fun s _ => ?_
          simp [E, coeff_printedTailEAbsPointSeries]
          ring
        have hJw :
            (∑ r ∈ Finset.range (m + 1), (r : ℚ) * coeff r J) =
              ∑ r ∈ Finset.range (m + 1),
                (r : ℚ) * printedTailJAbsCoeff μ a r * x^r := by
          refine Finset.sum_congr rfl fun r _ => ?_
          simp [J, coeff_printedTailJAbsPointSeries]
          ring
        have hEp :
            (∑ s ∈ Finset.range (m + 1), coeff s E) =
              ∑ s ∈ Finset.range (m + 1),
                printedTailEAbsCoeff μ a s * x^s := by
          refine Finset.sum_congr rfl fun s _ => ?_
          simp [E, coeff_printedTailEAbsPointSeries]
        have hJp :
            (∑ r ∈ Finset.range (m + 1), coeff r J) =
              ∑ r ∈ Finset.range (m + 1),
                printedTailJAbsCoeff μ a r * x^r := by
          refine Finset.sum_congr rfl fun r _ => ?_
          simp [J, coeff_printedTailJAbsPointSeries]
        rw [hEw, hJw, hEp, hJp]
        ring

def printedTailX2 (a : Nat) : ℚ :=
  2 / (3 * (a : ℚ))

def printedTailX0 (a : Nat) : ℚ :=
  1 / (6 * ((a : ℚ) - 12))

def printedTailX1 (a : Nat) : ℚ :=
  1 / (3 * (a : ℚ))

/-- Certificate-facing finite point bound for the positive majorant
`\widehat W` at `x_2 = 2/(3a)`.  Since the coefficient to be extracted is
degree `a`, it suffices to bound the finite prefix through degree `a`; the
printed proof obtains this from the stronger analytic estimate
`\widehat W(x_2) < 920`. -/
def PrintedTailWPointBoundX2 : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      (∑ s ∈ Finset.range (a + 1),
        printedTailWAbsCoeff μ a s * (printedTailX2 a)^s) ≤ 920

/-- Finite point and logarithmic-derivative bounds for the positive majorant
`\widehat W` at `x_0 = 1/(6(a-12))` and `x_2 = 2/(3a)`.  These are the
finite-prefix versions of the printed bounds
`\widehat W(x_0)`, `x_0\widehat W'(x_0)`, `\widehat W(x_2)`, and
`x_2\widehat W'(x_2)`. -/
def PrintedTailWPointMomentBounds : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      (∑ s ∈ Finset.range (printedTailR0 a + 1),
        printedTailWAbsCoeff μ a s * (printedTailX0 a)^s ≤
          (203 / 50 : ℚ) * (21 / 10)) ∧
      (∑ s ∈ Finset.range (printedTailR0 a + 1),
        (s : ℚ) * printedTailWAbsCoeff μ a s * (printedTailX0 a)^s ≤
          (203 / 50 : ℚ) * (17 / 4)) ∧
      (∑ s ∈ Finset.range (printedTailR0 a + 1),
        printedTailWAbsCoeff μ a s * (printedTailX2 a)^s ≤
          (182 : ℚ) * (101 / 20)) ∧
      (∑ s ∈ Finset.range (printedTailR0 a + 1),
        (s : ℚ) * printedTailWAbsCoeff μ a s * (printedTailX2 a)^s ≤
          (182 : ℚ) * (255 / 8))

/-- Majorant moment estimates for `exp(|L|)*(1+|J|)`.
These are the coefficientwise-positive moment bounds that correspond most
directly to `\widehat W` in the printed proof; `\widehat E` is then dominated
coefficientwise by `\widehat W`. -/
def PrintedTailMajorantMomentBounds : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      (∑ s ∈ Finset.range (printedTailR0 a + 1),
          gammaWeight a s * printedTailWAbsCoeff μ a s ≤ 9) ∧
      (∑ s ∈ Finset.range (printedTailR0 a + 1),
          (s : ℚ) * gammaWeight a s * printedTailWAbsCoeff μ a s ≤ 18)

/-- The two absolute-moment estimates from the printed proof:
`sum gamma_s |omega_s| <= 9` and
`sum s gamma_s |omega_s| <= 18`.

This is intentionally stated in the same finite `s <= r_0` language as the
tail split above.  The following theorem proves that these two moments imply
the displayed `h`-replacement error, using only the already-formalized
`d`-ratio estimate and elementary partition bounds. -/
def PrintedTailAbsoluteMomentBounds : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      (∑ s ∈ Finset.range (printedTailR0 a + 1),
          gammaWeight a s * |printedTailOmegaCoeff μ a s| ≤ 9) ∧
      (∑ s ∈ Finset.range (printedTailR0 a + 1),
          (s : ℚ) * gammaWeight a s * |printedTailOmegaCoeff μ a s| ≤ 18)

private theorem gammaWeight_nonneg {a s : Nat} (_hs : s < a) :
    0 ≤ gammaWeight a s := by
  unfold gammaWeight
  positivity

private theorem gammaWeight_pos {a s : Nat} (_hs : s < a) :
    0 < gammaWeight a s := by
  unfold gammaWeight
  positivity

private theorem printedTail_range_lt_a {a s : Nat} (ha : 150 ≤ a)
    (hs : s ∈ Finset.range (printedTailR0 a + 1)) : s < a := by
  have hsle : s ≤ printedTailR0 a := by
    have := Finset.mem_range.mp hs
    omega
  unfold printedTailR0 printedTailP at hsle
  omega

private theorem printedTail_range_p_succ_le {a s : Nat} (ha : 150 ≤ a)
    (hs : s ∈ Finset.range (printedTailR0 a + 1)) :
    printedTailP a + 1 ≤ a - s := by
  have hp_lt_a : printedTailP a < a := by
    unfold printedTailP
    omega
  have hlen : printedTailR0 a + 1 = a - printedTailP a := by
    unfold printedTailR0
    omega
  have hslt : s < a - printedTailP a := by
    simpa [hlen] using Finset.mem_range.mp hs
  omega

private theorem printedTail_two_mul_sub_ge {a s : Nat} (ha : 150 ≤ a)
    (hs : s ∈ Finset.range (printedTailR0 a + 1)) :
    a ≤ 2 * (a - s) := by
  have hp := printedTail_range_p_succ_le (a := a) (s := s) ha hs
  unfold printedTailP at hp
  omega

private theorem printedTail_factorial_tail_mul_pow_le
    {a s : Nat} (hp : 1 ≤ a - s) :
    (((a - s - 1).factorial : Nat) : ℚ) *
        (((a - s : Nat) : ℚ)^s)
      ≤ ((a - 1).factorial : ℚ) := by
  have hnat :
      (a - s - 1).factorial * (a - s)^s ≤ (a - 1).factorial := by
    have hpow :
        (a - s)^s ≤ (a - s).ascFactorial s :=
      Nat.pow_succ_le_ascFactorial (a - s) s
    have hmul :=
      Nat.mul_le_mul_left (a - s - 1).factorial hpow
    have hfac :=
      Nat.factorial_mul_ascFactorial' (a - s) s (by omega : 0 < a - s)
    have hsum : a - s + s - 1 = a - 1 := by omega
    rw [hsum] at hfac
    exact hmul.trans_eq hfac
  exact_mod_cast hnat

private theorem printedTail_recip_six_mul_pow (A : ℚ) (hA : A ≠ 0)
    (s : Nat) :
    (1 / A^s) / (6 : ℚ)^s = (1 / (6 * A))^s := by
  have hApow : A^s ≠ 0 := pow_ne_zero _ hA
  have h6pow : (6 : ℚ)^s ≠ 0 :=
    pow_ne_zero _ (by norm_num : (6 : ℚ) ≠ 0)
  have h6A : 6 * A ≠ 0 := mul_ne_zero (by norm_num) hA
  field_simp [hApow, h6pow, h6A]
  rw [one_div, inv_pow]
  rw [← mul_pow]
  have hcomm : A * 6 = 6 * A := by ring
  rw [hcomm]
  field_simp [h6A]

private theorem gammaWeight_le_inv_six_sub_pow {a s : Nat}
    (hp : 1 ≤ a - s) :
    gammaWeight a s ≤ (1 / (6 * ((a - s : Nat) : ℚ)))^s := by
  unfold gammaWeight
  have hfac := printedTail_factorial_tail_mul_pow_le (a := a) (s := s) hp
  let A : ℚ := ((a - s : Nat) : ℚ)
  have hA_pos : 0 < A := by
    dsimp [A]
    exact_mod_cast hp
  have hA_ne : A ≠ 0 := hA_pos.ne'
  have hpow_pos : 0 < A^s := pow_pos hA_pos s
  have hfac_pos : 0 < (((a - 1).factorial : Nat) : ℚ) := by positivity
  have hnum_le :
      (((a - s - 1).factorial : Nat) : ℚ) ≤
        (((a - 1).factorial : Nat) : ℚ) / A^s := by
    rw [le_div_iff₀ hpow_pos]
    dsimp [A]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hfac
  have hdiv :
      (((a - s - 1).factorial : Nat) : ℚ) /
          (((a - 1).factorial : Nat) : ℚ) ≤
        1 / A^s := by
    calc
      (((a - s - 1).factorial : Nat) : ℚ) /
          (((a - 1).factorial : Nat) : ℚ)
          ≤ ((((a - 1).factorial : Nat) : ℚ) / A^s) /
              (((a - 1).factorial : Nat) : ℚ) :=
            div_le_div_of_nonneg_right hnum_le hfac_pos.le
      _ = 1 / A^s := by field_simp [hfac_pos.ne']
  calc
    (((a - s - 1).factorial : Nat) : ℚ) /
        ((6 : ℚ)^s * (((a - 1).factorial : Nat) : ℚ))
        = ((((a - s - 1).factorial : Nat) : ℚ) /
            (((a - 1).factorial : Nat) : ℚ)) / (6 : ℚ)^s := by ring
    _ ≤ (1 / A^s) / (6 : ℚ)^s :=
      div_le_div_of_nonneg_right hdiv (by positivity)
    _ = (1 / (6 * A))^s := printedTail_recip_six_mul_pow A hA_ne s
    _ = (1 / (6 * ((a - s : Nat) : ℚ)))^s := by rfl

private theorem printedTail_one_div_two_pow_mono {u v : Nat} (hvu : v ≤ u) :
    1 / (2 : ℚ)^u ≤ 1 / (2 : ℚ)^v := by
  have hpow : (2 : ℚ)^v ≤ (2 : ℚ)^u :=
    pow_le_pow_right₀ (by norm_num : (0 : ℚ) ≤ 2) hvu
  exact one_div_le_one_div_of_le (by positivity) hpow

private theorem gammaWeight_le_x0_pow {a s : Nat}
    (ha : 150 ≤ a) (hs12 : s ≤ 12) :
    gammaWeight a s ≤ (printedTailX0 a)^s := by
  have htail :=
    gammaWeight_le_inv_six_sub_pow (a := a) (s := s) (by omega : 1 ≤ a - s)
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hs12Q : (s : ℚ) ≤ 12 := by exact_mod_cast hs12
  have hbase_left_nonneg : 0 ≤ 1 / (6 * ((a - s : Nat) : ℚ)) := by
    positivity
  have hbase : 1 / (6 * ((a - s : Nat) : ℚ)) ≤ printedTailX0 a := by
    unfold printedTailX0
    have hdenle : 6 * ((a : ℚ) - 12) ≤ 6 * ((a - s : Nat) : ℚ) := by
      have hcast : ((a - s : Nat) : ℚ) = (a : ℚ) - s := by
        rw [Nat.cast_sub (by omega : s ≤ a)]
      rw [hcast]
      nlinarith
    have hdenpos : 0 < 6 * ((a : ℚ) - 12) := by nlinarith
    exact one_div_le_one_div_of_le hdenpos hdenle
  exact htail.trans (pow_le_pow_left₀ hbase_left_nonneg hbase s)

private theorem gammaWeight_le_x1_pow {a s : Nat}
    (ha : 150 ≤ a) (hrange : printedTailP a + 1 ≤ a - s) :
    gammaWeight a s ≤ (printedTailX1 a)^s := by
  have htail :=
    gammaWeight_le_inv_six_sub_pow (a := a) (s := s) (by omega : 1 ≤ a - s)
  have hbase_left_nonneg : 0 ≤ 1 / (6 * ((a - s : Nat) : ℚ)) := by
    positivity
  have hbase : 1 / (6 * ((a - s : Nat) : ℚ)) ≤ printedTailX1 a := by
    unfold printedTailX1
    have hdenle : 3 * (a : ℚ) ≤ 6 * ((a - s : Nat) : ℚ) := by
      have hnat : a ≤ 2 * (a - s) := by
        unfold printedTailP at hrange
        omega
      have hq : (a : ℚ) ≤ 2 * ((a - s : Nat) : ℚ) := by
        exact_mod_cast hnat
      nlinarith
    have hdenpos : 0 < 3 * (a : ℚ) := by
      exact mul_pos (by norm_num) (by exact_mod_cast
        (lt_of_lt_of_le (by norm_num : 0 < 150) ha))
    exact one_div_le_one_div_of_le hdenpos hdenle
  exact htail.trans (pow_le_pow_left₀ hbase_left_nonneg hbase s)

private theorem printedTailX1_pow_le_scaled_x2 {a s : Nat}
    (ha : 150 ≤ a) (hs13 : 13 ≤ s) :
    (printedTailX1 a)^s ≤ (1 / (2 : ℚ)^13) * (printedTailX2 a)^s := by
  unfold printedTailX1 printedTailX2
  have hden : 3 * (a : ℚ) ≠ 0 := by
    have ha_pos : (0 : ℚ) < a := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 150) ha)
    positivity
  have hx2_nonneg : 0 ≤ 2 / (3 * (a : ℚ)) := by positivity
  have hx1_eq :
      (1 / (3 * (a : ℚ))) =
        (1 / 2 : ℚ) * (2 / (3 * (a : ℚ))) := by
    field_simp [hden]
  rw [hx1_eq, mul_pow]
  have hpow : (1 / 2 : ℚ)^s ≤ (1 / (2 : ℚ)^13) := by
    have hrewrite : (1 / 2 : ℚ)^s = 1 / (2 : ℚ)^s := by
      rw [one_div_pow]
    rw [hrewrite]
    exact printedTail_one_div_two_pow_mono hs13
  exact mul_le_mul_of_nonneg_right hpow (pow_nonneg hx2_nonneg s)

private theorem gammaWeight_le_splitMajorant {a s : Nat}
    (ha : 150 ≤ a) (hs : s ∈ Finset.range (printedTailR0 a + 1)) :
    gammaWeight a s ≤
      (printedTailX0 a)^s + (1 / (2 : ℚ)^13) * (printedTailX2 a)^s := by
  by_cases hs12 : s ≤ 12
  · have h := gammaWeight_le_x0_pow (a := a) (s := s) ha hs12
    have hx2_nonneg : 0 ≤ printedTailX2 a := by
      unfold printedTailX2
      positivity
    exact h.trans
      (le_add_of_nonneg_right
        (mul_nonneg (by norm_num) (pow_nonneg hx2_nonneg s)))
  · have hs13 : 13 ≤ s := by omega
    have hrange := printedTail_range_p_succ_le (a := a) (s := s) ha hs
    have h :=
      (gammaWeight_le_x1_pow (a := a) (s := s) ha hrange).trans
        (printedTailX1_pow_le_scaled_x2 (a := a) (s := s) ha hs13)
    have hx0_nonneg : 0 ≤ printedTailX0 a := by
      unfold printedTailX0
      have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
      have hdenpos : 0 < 6 * ((a : ℚ) - 12) := by nlinarith
      exact (one_div_pos.mpr hdenpos).le
    exact h.trans (le_add_of_nonneg_left (pow_nonneg hx0_nonneg s))

theorem printedTailMajorantMomentBounds_of_wPointMomentBounds
    (hpoint : PrintedTailWPointMomentBounds) :
    PrintedTailMajorantMomentBounds := by
  intro a ha μ hμ
  have hp := hpoint a ha μ hμ
  constructor
  · have hterm :
      (∑ s ∈ Finset.range (printedTailR0 a + 1),
          gammaWeight a s * printedTailWAbsCoeff μ a s) ≤
        ∑ s ∈ Finset.range (printedTailR0 a + 1),
          (printedTailWAbsCoeff μ a s * (printedTailX0 a)^s +
            (1 / (2 : ℚ)^13) *
              (printedTailWAbsCoeff μ a s * (printedTailX2 a)^s)) := by
      refine Finset.sum_le_sum fun s hs => ?_
      have hW := printedTailWAbsCoeff_nonneg μ a s
      have hsplit := gammaWeight_le_splitMajorant (a := a) (s := s) ha hs
      calc
        gammaWeight a s * printedTailWAbsCoeff μ a s
            ≤ ((printedTailX0 a)^s +
                (1 / (2 : ℚ)^13) * (printedTailX2 a)^s) *
                printedTailWAbsCoeff μ a s :=
              mul_le_mul_of_nonneg_right hsplit hW
        _ = printedTailWAbsCoeff μ a s * (printedTailX0 a)^s +
              (1 / (2 : ℚ)^13) *
                (printedTailWAbsCoeff μ a s * (printedTailX2 a)^s) := by
              ring
    calc
      (∑ s ∈ Finset.range (printedTailR0 a + 1),
          gammaWeight a s * printedTailWAbsCoeff μ a s)
          ≤ ∑ s ∈ Finset.range (printedTailR0 a + 1),
            (printedTailWAbsCoeff μ a s * (printedTailX0 a)^s +
              (1 / (2 : ℚ)^13) *
                (printedTailWAbsCoeff μ a s * (printedTailX2 a)^s)) := hterm
      _ = (∑ s ∈ Finset.range (printedTailR0 a + 1),
            printedTailWAbsCoeff μ a s * (printedTailX0 a)^s) +
          (1 / (2 : ℚ)^13) *
            (∑ s ∈ Finset.range (printedTailR0 a + 1),
              printedTailWAbsCoeff μ a s * (printedTailX2 a)^s) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ (203 / 50 : ℚ) * (21 / 10) +
          (1 / (2 : ℚ)^13) * ((182 : ℚ) * (101 / 20)) := by
          exact add_le_add hp.1
            (mul_le_mul_of_nonneg_left hp.2.2.1 (by norm_num))
      _ ≤ 9 := by norm_num
  · have hterm :
      (∑ s ∈ Finset.range (printedTailR0 a + 1),
          (s : ℚ) * gammaWeight a s * printedTailWAbsCoeff μ a s) ≤
        ∑ s ∈ Finset.range (printedTailR0 a + 1),
          ((s : ℚ) * printedTailWAbsCoeff μ a s * (printedTailX0 a)^s +
            (1 / (2 : ℚ)^13) *
              ((s : ℚ) * printedTailWAbsCoeff μ a s *
                (printedTailX2 a)^s)) := by
      refine Finset.sum_le_sum fun s hs => ?_
      have hW := printedTailWAbsCoeff_nonneg μ a s
      have hscale_nonneg : 0 ≤ (s : ℚ) * printedTailWAbsCoeff μ a s :=
        mul_nonneg (by positivity) hW
      have hsplit := gammaWeight_le_splitMajorant (a := a) (s := s) ha hs
      calc
        (s : ℚ) * gammaWeight a s * printedTailWAbsCoeff μ a s
            ≤ ((printedTailX0 a)^s +
                (1 / (2 : ℚ)^13) * (printedTailX2 a)^s) *
                ((s : ℚ) * printedTailWAbsCoeff μ a s) := by
              nlinarith [mul_le_mul_of_nonneg_right hsplit hscale_nonneg]
        _ = (s : ℚ) * printedTailWAbsCoeff μ a s * (printedTailX0 a)^s +
              (1 / (2 : ℚ)^13) *
                ((s : ℚ) * printedTailWAbsCoeff μ a s *
                  (printedTailX2 a)^s) := by
              ring
    calc
      (∑ s ∈ Finset.range (printedTailR0 a + 1),
          (s : ℚ) * gammaWeight a s * printedTailWAbsCoeff μ a s)
          ≤ ∑ s ∈ Finset.range (printedTailR0 a + 1),
            ((s : ℚ) * printedTailWAbsCoeff μ a s * (printedTailX0 a)^s +
              (1 / (2 : ℚ)^13) *
                ((s : ℚ) * printedTailWAbsCoeff μ a s *
                  (printedTailX2 a)^s)) := hterm
      _ = (∑ s ∈ Finset.range (printedTailR0 a + 1),
            (s : ℚ) * printedTailWAbsCoeff μ a s * (printedTailX0 a)^s) +
          (1 / (2 : ℚ)^13) *
            (∑ s ∈ Finset.range (printedTailR0 a + 1),
              (s : ℚ) * printedTailWAbsCoeff μ a s *
                (printedTailX2 a)^s) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ (203 / 50 : ℚ) * (17 / 4) +
          (1 / (2 : ℚ)^13) * ((182 : ℚ) * (255 / 8)) := by
          exact add_le_add hp.2.1
            (mul_le_mul_of_nonneg_left hp.2.2.2 (by norm_num))
      _ ≤ 18 := by norm_num

theorem printedTailAbsoluteMomentBounds_of_majorant
    (hmaj : PrintedTailMajorantMomentBounds) :
    PrintedTailAbsoluteMomentBounds := by
  intro a ha μ hμ
  have hmajW0 := (hmaj a ha μ hμ).1
  have hmajW1 := (hmaj a ha μ hμ).2
  constructor
  · calc
      ∑ s ∈ Finset.range (printedTailR0 a + 1),
          gammaWeight a s * |printedTailOmegaCoeff μ a s|
          ≤
        ∑ s ∈ Finset.range (printedTailR0 a + 1),
          gammaWeight a s * printedTailWAbsCoeff μ a s := by
          refine Finset.sum_le_sum fun s hs => ?_
          have hslt := printedTail_range_lt_a (a := a) (s := s) ha hs
          exact mul_le_mul_of_nonneg_left
            (abs_printedTailOmegaCoeff_le_WAbsCoeff μ a s)
            (gammaWeight_nonneg hslt)
      _ ≤ 9 := hmajW0
  · calc
      ∑ s ∈ Finset.range (printedTailR0 a + 1),
          (s : ℚ) * gammaWeight a s * |printedTailOmegaCoeff μ a s|
          ≤
        ∑ s ∈ Finset.range (printedTailR0 a + 1),
          (s : ℚ) * gammaWeight a s * printedTailWAbsCoeff μ a s := by
          refine Finset.sum_le_sum fun s hs => ?_
          have hslt := printedTail_range_lt_a (a := a) (s := s) ha hs
          exact mul_le_mul_of_nonneg_left
            (abs_printedTailOmegaCoeff_le_WAbsCoeff μ a s)
            (mul_nonneg (by positivity) (gammaWeight_nonneg hslt))
      _ ≤ 18 := hmajW1

private theorem inv_q_pow_le_q_over_two_pow_succ {mi r : Nat}
    (hmi : 1 ≤ mi) :
    1 / (((mi + 1 : Nat) : ℚ)^r) ≤
      (((mi + 1 : Nat) : ℚ)) / (2 : ℚ)^(r + 1) := by
  let q : ℚ := ((mi + 1 : Nat) : ℚ)
  have hq2 : (2 : ℚ) ≤ q := by
    dsimp [q]
    exact_mod_cast (by omega : 2 ≤ mi + 1)
  have hqpos : 0 < q := by
    dsimp [q]
    exact_mod_cast Nat.succ_pos mi
  have hden1 : 0 < q^r := pow_pos hqpos r
  have hden2 : 0 < (2 : ℚ)^(r + 1) := by positivity
  have hpow : (2 : ℚ)^(r + 1) ≤ q^(r + 1) :=
    pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 2) hq2 (r + 1)
  rw [div_le_div_iff₀ hden1 hden2]
  calc
    (1 : ℚ) * (2 : ℚ)^(r + 1) ≤ q^(r + 1) := by simpa using hpow
    _ = q * q^r := by rw [pow_succ']

private theorem sum_q_div_const (μ : List Nat) {D : ℚ} :
    (μ.map fun mi : Nat => (((mi + 1 : Nat) : ℚ)) / D).sum =
      (((μ.map (· + 1)).sum : Nat) : ℚ) / D := by
  induction μ with
  | nil => simp
  | cons mi μ ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      push_cast
      ring

private theorem sPower_nonneg (μ : List Nat) (r : Nat) :
    0 ≤ sPower μ r := by
  unfold sPower
  refine List.sum_nonneg fun x hx => ?_
  simp only [List.mem_map] at hx
  obtain ⟨mi, _hmi, rfl⟩ := hx
  positivity

private theorem sPower_le_N_over_two_pow_succ
    {μ : List Nat} (hpos : ∀ m ∈ μ, 1 ≤ m) (r : Nat) :
    sPower μ r ≤ (N μ : ℚ) / (2 : ℚ)^(r + 1) := by
  unfold sPower N
  calc
    (μ.map fun mi : Nat => 1 / (((mi + 1 : Nat) : ℚ)^r)).sum
        ≤ (μ.map fun mi : Nat =>
            (((mi + 1 : Nat) : ℚ)) / (2 : ℚ)^(r + 1)).sum := by
          refine List.sum_le_sum fun mi hmi => ?_
          exact inv_q_pow_le_q_over_two_pow_succ (hpos mi hmi)
    _ = (((μ.map (· + 1)).sum : Nat) : ℚ) / (2 : ℚ)^(r + 1) :=
          sum_q_div_const μ

private theorem sPower_div_N_le_two_pow_succ
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) (r : Nat) :
    sPower μ r / (N μ : ℚ) ≤ 1 / (2 : ℚ)^(r + 1) := by
  have hμ_copy := hμ
  obtain ⟨_hsum, hpos⟩ := hμ
  have hNpos : (0 : ℚ) < (N μ : ℚ) := by
    have hNnat : 0 < N μ := printedTail_N_pos (a := a) (μ := μ) ha hμ_copy
    exact_mod_cast hNnat
  have hmain := sPower_le_N_over_two_pow_succ (μ := μ) hpos r
  rw [div_le_iff₀ hNpos]
  calc
    sPower μ r ≤ (N μ : ℚ) / (2 : ℚ)^(r + 1) := hmain
    _ = (1 / (2 : ℚ)^(r + 1)) * (N μ : ℚ) := by ring

private theorem one_div_two_pow_mono {u v : Nat} (hvu : v ≤ u) :
    1 / (2 : ℚ)^u ≤ 1 / (2 : ℚ)^v := by
  have hpow : (2 : ℚ)^v ≤ (2 : ℚ)^u :=
    pow_le_pow_right₀ (by norm_num : (0 : ℚ) ≤ 2) hvu
  exact one_div_le_one_div_of_le (by positivity) hpow

def printedTailPowBudgetRhs (a : Nat) : ℚ :=
  9 / (2 : ℚ)^(printedTailP a + 2)

def printedTailPowBudgetScaled (a : Nat) : ℚ :=
  (a : ℚ)^2 * printedTailPowBudgetRhs a

private theorem printedTailPowBudgetScaled_step8 (a : Nat) (ha : 150 ≤ a) :
    printedTailPowBudgetScaled (a + 8) ≤ printedTailPowBudgetScaled a := by
  unfold printedTailPowBudgetScaled printedTailPowBudgetRhs printedTailP
  have hdiv : (a + 8) / 2 = a / 2 + 4 := by
    simpa [show 8 = 4 * 2 by norm_num] using
      Nat.add_mul_div_right a 4 (by decide : 0 < 2)
  rw [hdiv]
  rw [show a / 2 + 4 + 2 = a / 2 + 2 + 4 by omega, pow_add]
  norm_num
  have hpoly : (((a + 8 : Nat) : ℚ)^2 / 16 ≤ (a : ℚ)^2) := by
    push_cast
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  have hnonneg : 0 ≤ 9 / (2 : ℚ) ^ (a / 2 + 2) := by positivity
  calc
    ((a : ℚ) + 8) ^ 2 *
        (9 / ((2 : ℚ) ^ (a / 2 + 2) * 16))
        = (((a + 8 : Nat) : ℚ)^2 / 16) *
            (9 / (2 : ℚ) ^ (a / 2 + 2)) := by
            push_cast
            ring
    _ ≤ (a : ℚ)^2 * (9 / (2 : ℚ) ^ (a / 2 + 2)) :=
        mul_le_mul_of_nonneg_right hpoly hnonneg

private theorem printedTailPowBudgetScaled_150 :
    printedTailPowBudgetScaled 150 < 1 := by native_decide
private theorem printedTailPowBudgetScaled_151 :
    printedTailPowBudgetScaled 151 < 1 := by native_decide
private theorem printedTailPowBudgetScaled_152 :
    printedTailPowBudgetScaled 152 < 1 := by native_decide
private theorem printedTailPowBudgetScaled_153 :
    printedTailPowBudgetScaled 153 < 1 := by native_decide
private theorem printedTailPowBudgetScaled_154 :
    printedTailPowBudgetScaled 154 < 1 := by native_decide
private theorem printedTailPowBudgetScaled_155 :
    printedTailPowBudgetScaled 155 < 1 := by native_decide
private theorem printedTailPowBudgetScaled_156 :
    printedTailPowBudgetScaled 156 < 1 := by native_decide
private theorem printedTailPowBudgetScaled_157 :
    printedTailPowBudgetScaled 157 < 1 := by native_decide

theorem printedTailPowBudget_bound (a : Nat) (ha : 150 ≤ a) :
    printedTailPowBudgetRhs a ≤ 1 / (a : ℚ)^2 := by
  have hscaled : printedTailPowBudgetScaled a < 1 := by
    refine Nat.strong_induction_on a ?_ ha
    intro a ih ha
    by_cases hle : a ≤ 157
    · interval_cases a <;> first
        | exact printedTailPowBudgetScaled_150
        | exact printedTailPowBudgetScaled_151
        | exact printedTailPowBudgetScaled_152
        | exact printedTailPowBudgetScaled_153
        | exact printedTailPowBudgetScaled_154
        | exact printedTailPowBudgetScaled_155
        | exact printedTailPowBudgetScaled_156
        | exact printedTailPowBudgetScaled_157
    · have hprev_ge : 150 ≤ a - 8 := by omega
      have hprev_lt : a - 8 < a := by omega
      have hprev : printedTailPowBudgetScaled (a - 8) < 1 :=
        ih (a - 8) hprev_lt hprev_ge
      have hstep :
          printedTailPowBudgetScaled ((a - 8) + 8) ≤
            printedTailPowBudgetScaled (a - 8) :=
        printedTailPowBudgetScaled_step8 (a - 8) hprev_ge
      have hadd : (a - 8) + 8 = a := by omega
      rw [hadd] at hstep
      exact lt_of_le_of_lt hstep hprev
  unfold printedTailPowBudgetScaled at hscaled
  have ha_sq_pos : (0 : ℚ) < (a : ℚ)^2 := by
    have ha_pos : (0 : ℚ) < (a : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 150) ha)
    positivity
  rw [le_div_iff₀ ha_sq_pos]
  nlinarith

private theorem hCoeff_div_den_eq_gammaWeight_mul
    {a s : Nat} {μ : List Nat} (hs : s < a) (hN : N μ ≠ 0) :
    hCoeff μ (a - s) / printedTailDen μ a =
      gammaWeight a s * (Prop51.d (a - s) / Prop51.d a) *
        (1 - sPower μ (a - s) / (N μ : ℚ)) := by
  have ha1 : 1 ≤ a := by omega
  have has1 : 1 ≤ a - s := by omega
  have hNq : ((N μ : Nat) : ℚ) ≠ 0 := by exact_mod_cast hN
  have hda : Prop51.d a ≠ 0 := (Prop51.d_pos a ha1).ne'
  have hdas : Prop51.d (a - s) ≠ 0 := (Prop51.d_pos (a - s) has1).ne'
  have hfac_a : (((a - 1).factorial : Nat) : ℚ) ≠ 0 := by positivity
  have hfac_as : ((((a - s - 1).factorial : Nat) : ℚ)) ≠ 0 := by positivity
  have hpow6 : (6 : ℚ)^a = (6 : ℚ)^(a - s) * (6 : ℚ)^s := by
    nth_rewrite 1 [show a = (a - s) + s by omega]
    rw [pow_add]
  unfold hCoeff printedTailDen gammaWeight
  rw [Prop51.c_eq_d (a - s), Prop51.c_eq_d a, hpow6]
  field_simp [hNq, hda, hdas, hfac_a, hfac_as]

private theorem hCoeff_div_den_sub_gammaWeight_abs_le
    {a s : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a))
    (hs : s ∈ Finset.range (printedTailR0 a + 1)) :
    |hCoeff μ (a - s) / printedTailDen μ a - gammaWeight a s| ≤
      (2 * (2304 / 3125 : ℚ) / (a : ℚ)^2) *
          ((s : ℚ) * gammaWeight a s) +
        (1 / (2 : ℚ)^(printedTailP a + 2)) * gammaWeight a s := by
  have hslt : s < a := printedTail_range_lt_a (a := a) (s := s) ha hs
  have hNpos_nat : 0 < N μ := printedTail_N_pos (a := a) (μ := μ) ha hμ
  have hNqpos : (0 : ℚ) < (N μ : ℚ) := by exact_mod_cast hNpos_nat
  have hgamma_nonneg : 0 ≤ gammaWeight a s := gammaWeight_nonneg hslt
  have hdpos_a : 0 < Prop51.d a := Prop51.d_pos a (by omega)
  have hdpos_as : 0 < Prop51.d (a - s) := Prop51.d_pos (a - s) (by omega)
  set R : ℚ := Prop51.d (a - s) / Prop51.d a with hR
  set x : ℚ := sPower μ (a - s) / (N μ : ℚ) with hx
  have hR_nonneg : 0 ≤ R := by
    rw [hR]
    exact div_nonneg hdpos_as.le hdpos_a.le
  have hR_le_one : R ≤ 1 := by
    rw [hR]
    rw [div_le_one₀ hdpos_a]
    exact Prop51.d_mono (Nat.sub_le a s)
  have hx_nonneg : 0 ≤ x := by
    rw [hx]
    exact div_nonneg (sPower_nonneg μ (a - s)) hNqpos.le
  have hrepr := hCoeff_div_den_eq_gammaWeight_mul
    (a := a) (s := s) (μ := μ) hslt (ne_of_gt hNpos_nat)
  rw [hrepr]
  change |gammaWeight a s * R * (1 - x) - gammaWeight a s| ≤
      (2 * (2304 / 3125 : ℚ) / (a : ℚ)^2) *
          ((s : ℚ) * gammaWeight a s) +
        (1 / (2 : ℚ)^(printedTailP a + 2)) * gammaWeight a s
  rw [show gammaWeight a s * R * (1 - x) - gammaWeight a s =
        gammaWeight a s * (R * (1 - x) - 1) by ring]
  rw [abs_mul, abs_of_nonneg hgamma_nonneg]
  have hmain_nonpos :
      R * (1 - x) - 1 ≤ 0 := by
    have : R * (1 - x) ≤ 1 := by
      calc
        R * (1 - x) ≤ R * 1 := by
          exact mul_le_mul_of_nonneg_left (by linarith : 1 - x ≤ 1) hR_nonneg
        _ ≤ 1 := by simpa using hR_le_one
    exact sub_nonpos.mpr this
  rw [abs_of_nonpos hmain_nonpos]
  have hdiff_decomp :
      -(R * (1 - x) - 1) = (1 - R) + R * x := by
    ring
  rw [hdiff_decomp]
  have hratio := Prop51.d_ratio_lb a s hslt
  have hR_drift :
      1 - R ≤
        (2304 / 3125 : ℚ) *
          ((s : ℚ) / ((a : ℚ) * ((a - s : Nat) : ℚ))) := by
    rw [hR]
    linarith
  have hsub_cast : ((a - s : Nat) : ℚ) = (a : ℚ) - (s : ℚ) := by
    rw [Nat.cast_sub hslt.le]
  have hfrac :
      (s : ℚ) / ((a : ℚ) * ((a - s : Nat) : ℚ))
        ≤ 2 * (s : ℚ) / (a : ℚ)^2 := by
    rw [hsub_cast]
    have haQ : (0 : ℚ) < a := by exact_mod_cast (by omega : 0 < a)
    have hsubQ : (0 : ℚ) < (a : ℚ) - (s : ℚ) := by
      rw [← hsub_cast]
      exact_mod_cast (by omega : 0 < a - s)
    have hs_nonneg : (0 : ℚ) ≤ s := by positivity
    have htwice : (a : ℚ) ≤ 2 * ((a : ℚ) - (s : ℚ)) := by
      have hnat := printedTail_two_mul_sub_ge (a := a) (s := s) ha hs
      rw [← hsub_cast]
      exact_mod_cast hnat
    have hrecip :
        1 / ((a : ℚ) * ((a : ℚ) - (s : ℚ)))
          ≤ 2 / (a : ℚ)^2 := by
      field_simp [haQ.ne', hsubQ.ne']
      nlinarith
    calc
      (s : ℚ) / ((a : ℚ) * ((a : ℚ) - (s : ℚ)))
          = (s : ℚ) * (1 / ((a : ℚ) * ((a : ℚ) - (s : ℚ)))) := by ring
      _ ≤ (s : ℚ) * (2 / (a : ℚ)^2) :=
          mul_le_mul_of_nonneg_left hrecip hs_nonneg
      _ = 2 * (s : ℚ) / (a : ℚ)^2 := by ring
  have hpow_succ :
      1 / (2 : ℚ)^(a - s + 1) ≤
        1 / (2 : ℚ)^(printedTailP a + 2) := by
    have hp := printedTail_range_p_succ_le (a := a) (s := s) ha hs
    exact one_div_two_pow_mono (by omega : printedTailP a + 2 ≤ a - s + 1)
  have hx_le :
      x ≤ 1 / (2 : ℚ)^(printedTailP a + 2) := by
    rw [hx]
    exact (sPower_div_N_le_two_pow_succ
      (a := a) (μ := μ) ha hμ (a - s)).trans hpow_succ
  calc
    gammaWeight a s * ((1 - R) + R * x)
        ≤ gammaWeight a s *
            (((2304 / 3125 : ℚ) *
                ((s : ℚ) / ((a : ℚ) * ((a - s : Nat) : ℚ)))) + x) := by
          have hRx_le_x : R * x ≤ x := by
            nlinarith [hR_nonneg, hR_le_one, hx_nonneg]
          have hsum :
              (1 - R) + R * x ≤
                ((2304 / 3125 : ℚ) *
                  ((s : ℚ) / ((a : ℚ) * ((a - s : Nat) : ℚ)))) + x := by
            nlinarith [hR_drift, hRx_le_x]
          exact mul_le_mul_of_nonneg_left hsum hgamma_nonneg
    _ ≤ gammaWeight a s *
            (((2304 / 3125 : ℚ) * (2 * (s : ℚ) / (a : ℚ)^2)) +
              1 / (2 : ℚ)^(printedTailP a + 2)) := by
          have hdrift :
              (2304 / 3125 : ℚ) *
                  ((s : ℚ) / ((a : ℚ) * ((a - s : Nat) : ℚ))) ≤
                (2304 / 3125 : ℚ) * (2 * (s : ℚ) / (a : ℚ)^2) :=
            mul_le_mul_of_nonneg_left hfrac (by norm_num)
          have hsum :
              ((2304 / 3125 : ℚ) *
                  ((s : ℚ) / ((a : ℚ) * ((a - s : Nat) : ℚ)))) + x ≤
                ((2304 / 3125 : ℚ) * (2 * (s : ℚ) / (a : ℚ)^2)) +
                  1 / (2 : ℚ)^(printedTailP a + 2) := by
            linarith
          exact mul_le_mul_of_nonneg_left hsum hgamma_nonneg
    _ =
      (2 * (2304 / 3125 : ℚ) / (a : ℚ)^2) *
          ((s : ℚ) * gammaWeight a s) +
        (1 / (2 : ℚ)^(printedTailP a + 2)) * gammaWeight a s := by ring

theorem printedTailHErrorBound_of_absoluteMoments
    (hmom : PrintedTailAbsoluteMomentBounds) :
    PrintedTailHErrorBound := by
  intro a ha μ hμ
  have hmom0 := (hmom a ha μ hμ).1
  have hmom1 := (hmom a ha μ hμ).2
  have hpowBudget := printedTailPowBudget_bound a ha
  unfold printedTailHNormSum printedTailMainSum
  rw [Prop51.list_range_map_sum, Prop51.list_range_map_sum]
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm :
      ∑ x ∈ Finset.range (printedTailR0 a + 1),
          |hCoeff μ (a - x) * printedTailOmegaCoeff μ a x /
              printedTailDen μ a -
            gammaWeight a x * printedTailOmegaCoeff μ a x|
        ≤
      (2 * (2304 / 3125 : ℚ) / (a : ℚ)^2) *
          (∑ x ∈ Finset.range (printedTailR0 a + 1),
            (x : ℚ) * gammaWeight a x * |printedTailOmegaCoeff μ a x|) +
        (1 / (2 : ℚ)^(printedTailP a + 2)) *
          (∑ x ∈ Finset.range (printedTailR0 a + 1),
            gammaWeight a x * |printedTailOmegaCoeff μ a x|) := by
    calc
      ∑ x ∈ Finset.range (printedTailR0 a + 1),
          |hCoeff μ (a - x) * printedTailOmegaCoeff μ a x /
              printedTailDen μ a -
            gammaWeight a x * printedTailOmegaCoeff μ a x|
          =
        ∑ x ∈ Finset.range (printedTailR0 a + 1),
          |(hCoeff μ (a - x) / printedTailDen μ a -
              gammaWeight a x) * printedTailOmegaCoeff μ a x| := by
            refine Finset.sum_congr rfl fun x hx => ?_
            congr 1
            ring
      _ ≤
        ∑ x ∈ Finset.range (printedTailR0 a + 1),
          ((2 * (2304 / 3125 : ℚ) / (a : ℚ)^2) *
              ((x : ℚ) * gammaWeight a x) +
            (1 / (2 : ℚ)^(printedTailP a + 2)) * gammaWeight a x) *
              |printedTailOmegaCoeff μ a x| := by
            refine Finset.sum_le_sum fun x hx => ?_
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right
              (hCoeff_div_den_sub_gammaWeight_abs_le
                (a := a) (s := x) (μ := μ) ha hμ hx)
              (abs_nonneg _)
      _ =
        (2 * (2304 / 3125 : ℚ) / (a : ℚ)^2) *
            (∑ x ∈ Finset.range (printedTailR0 a + 1),
              (x : ℚ) * gammaWeight a x * |printedTailOmegaCoeff μ a x|) +
          (1 / (2 : ℚ)^(printedTailP a + 2)) *
            (∑ x ∈ Finset.range (printedTailR0 a + 1),
              gammaWeight a x * |printedTailOmegaCoeff μ a x|) := by
            calc
              ∑ x ∈ Finset.range (printedTailR0 a + 1),
                  ((2 * (2304 / 3125 : ℚ) / (a : ℚ)^2) *
                      ((x : ℚ) * gammaWeight a x) +
                    (1 / (2 : ℚ)^(printedTailP a + 2)) * gammaWeight a x) *
                    |printedTailOmegaCoeff μ a x|
                  =
                ∑ x ∈ Finset.range (printedTailR0 a + 1),
                  ((2 * (2304 / 3125 : ℚ) / (a : ℚ)^2) *
                      ((x : ℚ) * gammaWeight a x *
                        |printedTailOmegaCoeff μ a x|) +
                    (1 / (2 : ℚ)^(printedTailP a + 2)) *
                      (gammaWeight a x *
                        |printedTailOmegaCoeff μ a x|)) := by
                    refine Finset.sum_congr rfl fun x hx => ?_
                    ring
              _ = _ := by
                    rw [Finset.sum_add_distrib, ← Finset.mul_sum,
                      ← Finset.mul_sum]
  calc
    ∑ x ∈ Finset.range (printedTailR0 a + 1),
        |hCoeff μ (a - x) * printedTailOmegaCoeff μ a x /
            printedTailDen μ a -
          gammaWeight a x * printedTailOmegaCoeff μ a x|
        ≤
      (2 * (2304 / 3125 : ℚ) / (a : ℚ)^2) *
          (∑ x ∈ Finset.range (printedTailR0 a + 1),
            (x : ℚ) * gammaWeight a x * |printedTailOmegaCoeff μ a x|) +
        (1 / (2 : ℚ)^(printedTailP a + 2)) *
          (∑ x ∈ Finset.range (printedTailR0 a + 1),
            gammaWeight a x * |printedTailOmegaCoeff μ a x|) := hterm
    _ ≤
      (2 * (2304 / 3125 : ℚ) / (a : ℚ)^2) * 18 +
        (1 / (2 : ℚ)^(printedTailP a + 2)) * 9 := by
          gcongr
    _ ≤
      (2 * (2304 / 3125 : ℚ) / (a : ℚ)^2) * 18 +
        1 / (a : ℚ)^2 := by
          have hpow9 :
              (1 / (2 : ℚ)^(printedTailP a + 2)) * 9
                ≤ 1 / (a : ℚ)^2 := by
            unfold printedTailPowBudgetRhs at hpowBudget
            convert hpowBudget using 1
            ring
          linarith
    _ = printedTailHErrorBudget a := by
          unfold printedTailHErrorBudget
          ring

def PrintedTailKErrorBound : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      |printedTailKNormSum μ a| ≤ 1 / (a : ℚ)^2

/-- The absolute moment needed for the `k`-error:
`sum gamma_s |e_s| <= 9`.  In the printed proof this is obtained from the
same coefficientwise majorant used for the `omega` absolute moments, since
`E` is dominated by the positive exponential majorant for `W`. -/
def PrintedTailEAbsoluteMomentBound : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      ∑ s ∈ Finset.range (printedTailR0 a + 1),
          gammaWeight a s * |printedTailECoeff μ a s| ≤ 9

theorem printedTailEAbsoluteMomentBound_of_majorant
    (hmaj : PrintedTailMajorantMomentBounds) :
    PrintedTailEAbsoluteMomentBound := by
  intro a ha μ hμ
  have hmajW0 := (hmaj a ha μ hμ).1
  calc
    ∑ s ∈ Finset.range (printedTailR0 a + 1),
        gammaWeight a s * |printedTailECoeff μ a s|
        ≤
      ∑ s ∈ Finset.range (printedTailR0 a + 1),
        gammaWeight a s * printedTailEAbsCoeff μ a s := by
        refine Finset.sum_le_sum fun s hs => ?_
        have hslt := printedTail_range_lt_a (a := a) (s := s) ha hs
        exact mul_le_mul_of_nonneg_left
          (abs_printedTailECoeff_le_EAbsCoeff μ a s)
          (gammaWeight_nonneg hslt)
    _ ≤
      ∑ s ∈ Finset.range (printedTailR0 a + 1),
        gammaWeight a s * printedTailWAbsCoeff μ a s := by
        refine Finset.sum_le_sum fun s hs => ?_
        have hslt := printedTail_range_lt_a (a := a) (s := s) ha hs
        exact mul_le_mul_of_nonneg_left
          (printedTailEAbsCoeff_le_WAbsCoeff μ a s)
          (gammaWeight_nonneg hslt)
    _ ≤ 9 := hmajW0

def printedTailKPowBudgetRhs (a : Nat) : ℚ :=
  9 / (2 : ℚ)^(printedTailP a)

def printedTailKPowBudgetScaled (a : Nat) : ℚ :=
  (a : ℚ)^2 * printedTailKPowBudgetRhs a

private theorem printedTailKPowBudgetScaled_step8 (a : Nat) (ha : 150 ≤ a) :
    printedTailKPowBudgetScaled (a + 8) ≤ printedTailKPowBudgetScaled a := by
  unfold printedTailKPowBudgetScaled printedTailKPowBudgetRhs printedTailP
  have hdiv : (a + 8) / 2 = a / 2 + 4 := by
    simpa [show 8 = 4 * 2 by norm_num] using
      Nat.add_mul_div_right a 4 (by decide : 0 < 2)
  rw [hdiv, pow_add]
  norm_num
  have hpoly : (((a + 8 : Nat) : ℚ)^2 / 16 ≤ (a : ℚ)^2) := by
    push_cast
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  have hnonneg : 0 ≤ 9 / (2 : ℚ) ^ (a / 2) := by positivity
  calc
    ((a : ℚ) + 8) ^ 2 *
        (9 / ((2 : ℚ) ^ (a / 2) * 16))
        = (((a + 8 : Nat) : ℚ)^2 / 16) *
            (9 / (2 : ℚ) ^ (a / 2)) := by
            push_cast
            ring
    _ ≤ (a : ℚ)^2 * (9 / (2 : ℚ) ^ (a / 2)) :=
        mul_le_mul_of_nonneg_right hpoly hnonneg

private theorem printedTailKPowBudgetScaled_150 :
    printedTailKPowBudgetScaled 150 < 1 := by native_decide
private theorem printedTailKPowBudgetScaled_151 :
    printedTailKPowBudgetScaled 151 < 1 := by native_decide
private theorem printedTailKPowBudgetScaled_152 :
    printedTailKPowBudgetScaled 152 < 1 := by native_decide
private theorem printedTailKPowBudgetScaled_153 :
    printedTailKPowBudgetScaled 153 < 1 := by native_decide
private theorem printedTailKPowBudgetScaled_154 :
    printedTailKPowBudgetScaled 154 < 1 := by native_decide
private theorem printedTailKPowBudgetScaled_155 :
    printedTailKPowBudgetScaled 155 < 1 := by native_decide
private theorem printedTailKPowBudgetScaled_156 :
    printedTailKPowBudgetScaled 156 < 1 := by native_decide
private theorem printedTailKPowBudgetScaled_157 :
    printedTailKPowBudgetScaled 157 < 1 := by native_decide

theorem printedTailKPowBudget_bound (a : Nat) (ha : 150 ≤ a) :
    printedTailKPowBudgetRhs a ≤ 1 / (a : ℚ)^2 := by
  have hscaled : printedTailKPowBudgetScaled a < 1 := by
    refine Nat.strong_induction_on a ?_ ha
    intro a ih ha
    by_cases hle : a ≤ 157
    · interval_cases a <;> first
        | exact printedTailKPowBudgetScaled_150
        | exact printedTailKPowBudgetScaled_151
        | exact printedTailKPowBudgetScaled_152
        | exact printedTailKPowBudgetScaled_153
        | exact printedTailKPowBudgetScaled_154
        | exact printedTailKPowBudgetScaled_155
        | exact printedTailKPowBudgetScaled_156
        | exact printedTailKPowBudgetScaled_157
    · have hprev_ge : 150 ≤ a - 8 := by omega
      have hprev_lt : a - 8 < a := by omega
      have hprev : printedTailKPowBudgetScaled (a - 8) < 1 :=
        ih (a - 8) hprev_lt hprev_ge
      have hstep :
          printedTailKPowBudgetScaled ((a - 8) + 8) ≤
            printedTailKPowBudgetScaled (a - 8) :=
        printedTailKPowBudgetScaled_step8 (a - 8) hprev_ge
      have hadd : (a - 8) + 8 = a := by omega
      rw [hadd] at hstep
      exact lt_of_le_of_lt hstep hprev
  unfold printedTailKPowBudgetScaled at hscaled
  have ha_sq_pos : (0 : ℚ) < (a : ℚ)^2 := by
    have ha_pos : (0 : ℚ) < (a : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 150) ha)
    positivity
  rw [le_div_iff₀ ha_sq_pos]
  nlinarith

private theorem marked_summand_le_q_over_two_pow {mi r : Nat} (hmi : 1 ≤ mi) :
    (mi : ℚ) / (((mi + 1 : Nat) : ℚ)^r) ≤
      (((mi + 1 : Nat) : ℚ)) / (2 : ℚ)^r := by
  let q : ℚ := ((mi + 1 : Nat) : ℚ)
  have hmiq : (mi : ℚ) ≤ q := by
    dsimp [q]
    exact_mod_cast (by omega : mi ≤ mi + 1)
  have hq2 : (2 : ℚ) ≤ q := by
    dsimp [q]
    exact_mod_cast (by omega : 2 ≤ mi + 1)
  have hqpos : 0 < q := by
    dsimp [q]
    exact_mod_cast Nat.succ_pos mi
  have hden1 : 0 < q^r := pow_pos hqpos r
  have hden2 : 0 < (2 : ℚ)^r := by positivity
  have hpow : (2 : ℚ)^r ≤ q^r :=
    pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 2) hq2 r
  rw [div_le_div_iff₀ hden1 hden2]
  exact mul_le_mul hmiq hpow hden2.le (by positivity)

private theorem markedWeight_le_N_over_two_pow
    (μ : List Nat) (hpos : ∀ m ∈ μ, 1 ≤ m) (r : Nat) :
    markedWeight μ r ≤ (N μ : ℚ) / (2 : ℚ)^r := by
  unfold markedWeight N
  calc
    (μ.map fun mi : Nat => (mi : ℚ) / (((mi + 1 : Nat) : ℚ)^r)).sum
        ≤ (μ.map fun mi : Nat =>
            (((mi + 1 : Nat) : ℚ)) / (2 : ℚ)^r).sum := by
          refine List.sum_le_sum fun mi hmi => ?_
          exact marked_summand_le_q_over_two_pow (hpos mi hmi)
    _ = (((μ.map (· + 1)).sum : Nat) : ℚ) / (2 : ℚ)^r :=
          sum_q_div_const μ

private theorem markedWeight_nonneg (μ : List Nat) (r : Nat) :
    0 ≤ markedWeight μ r := by
  unfold markedWeight
  refine List.sum_nonneg fun x hx => ?_
  simp only [List.mem_map] at hx
  obtain ⟨mi, _hmi, rfl⟩ := hx
  positivity

private theorem kCoeff_eq_of_two_le (μ : List Nat) {r : Nat} (hr : 2 ≤ r) :
    kCoeff μ r =
      12 * (((r - 1 : Nat) : ℚ)) * Prop51.c (r - 1) * markedWeight μ r := by
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 2 := ⟨r - 2, by omega⟩
  simp [kCoeff]

private theorem kCoeff_core_ratio_le_gamma {a s : Nat}
    (hs2 : 2 ≤ a - s) :
    12 * (((a - s - 1 : Nat) : ℚ)) * Prop51.c (a - s - 1) /
        Prop51.c a ≤
      2 * gammaWeight a s := by
  let t : Nat := a - s - 1
  have ht1 : 1 ≤ t := by
    dsimp [t]
    omega
  have hta : t ≤ a := by
    dsimp [t]
    omega
  have ha1 : 1 ≤ a := by omega
  have hca : Prop51.c a ≠ 0 := (Prop51.c_pos a ha1).ne'
  have hda : Prop51.d a ≠ 0 := (Prop51.d_pos a ha1).ne'
  have hdt : Prop51.d t ≠ 0 := (Prop51.d_pos t ht1).ne'
  have ht_fac : ((t : ℚ) * (((t - 1).factorial : Nat) : ℚ)) =
      ((t.factorial : Nat) : ℚ) := by
    exact_mod_cast Nat.mul_factorial_pred (by omega : t ≠ 0)
  have ht_eq : t = a - s - 1 := rfl
  have hpow6 : (6 : ℚ)^a = (6 : ℚ)^t * (6 : ℚ)^(s + 1) := by
    nth_rewrite 1 [show a = t + (s + 1) by dsimp [t]; omega]
    rw [pow_add]
  have hgamma_t :
      gammaWeight a s =
        ((t.factorial : Nat) : ℚ) /
          ((6 : ℚ)^s * ((Nat.factorial (a - 1) : Nat) : ℚ)) := by
    unfold gammaWeight
    rw [← ht_eq]
  have heq :
      12 * (((a - s - 1 : Nat) : ℚ)) * Prop51.c (a - s - 1) /
          Prop51.c a =
        2 * gammaWeight a s * (Prop51.d t / Prop51.d a) := by
    rw [← ht_eq, Prop51.c_eq_d t, Prop51.c_eq_d a, hpow6, hgamma_t]
    field_simp [hca, hda, hdt]
    rw [show (6 : ℚ)^(s + 1) = (6 : ℚ)^s * 6 by rw [pow_succ]]
    rw [← ht_fac]
    ring
  rw [heq]
  have hratio : Prop51.d t / Prop51.d a ≤ 1 := by
    rw [div_le_one₀ (Prop51.d_pos a ha1)]
    exact Prop51.d_mono hta
  have hgamma_nonneg : 0 ≤ gammaWeight a s := gammaWeight_nonneg (by omega : s < a)
  nlinarith

private theorem kCoeff_div_den_le_gamma_pow
    {a s : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a))
    (hs : s ∈ Finset.range (printedTailR0 a + 1)) :
    kCoeff μ (a - s) / printedTailDen μ a ≤
      (2 / (2 : ℚ)^(a - s)) * gammaWeight a s := by
  have hr_ge : printedTailP a + 1 ≤ a - s :=
    printedTail_range_p_succ_le (a := a) (s := s) ha hs
  have hr2 : 2 ≤ a - s := by
    unfold printedTailP at hr_ge
    omega
  have hNpos_nat : 0 < N μ := printedTail_N_pos (a := a) (μ := μ) ha hμ
  have hNpos : (0 : ℚ) < (N μ : ℚ) := by exact_mod_cast hNpos_nat
  have hcpos : 0 < Prop51.c a := Prop51.c_pos a (by omega)
  have hdenpos : 0 < printedTailDen μ a := by
    unfold printedTailDen
    exact mul_pos hNpos hcpos
  have hmw := markedWeight_le_N_over_two_pow μ hμ.2 (a - s)
  have hmw_nonneg := markedWeight_nonneg μ (a - s)
  have hk_eq := kCoeff_eq_of_two_le μ (r := a - s) hr2
  rw [hk_eq]
  have hcore := kCoeff_core_ratio_le_gamma (a := a) (s := s) hr2
  unfold printedTailDen
  calc
    (12 * (((a - s - 1 : Nat) : ℚ)) * Prop51.c (a - s - 1) *
          markedWeight μ (a - s)) /
        ((N μ : ℚ) * Prop51.c a)
        =
      (12 * (((a - s - 1 : Nat) : ℚ)) * Prop51.c (a - s - 1) /
          Prop51.c a) * (markedWeight μ (a - s) / (N μ : ℚ)) := by
        field_simp [hNpos.ne', hcpos.ne']
    _ ≤
      (2 * gammaWeight a s) * (1 / (2 : ℚ)^(a - s)) := by
        have hmw_div :
            markedWeight μ (a - s) / (N μ : ℚ) ≤
              1 / (2 : ℚ)^(a - s) := by
          rw [div_le_iff₀ hNpos]
          calc
            markedWeight μ (a - s) ≤
                (N μ : ℚ) / (2 : ℚ)^(a - s) := hmw
            _ = (1 / (2 : ℚ)^(a - s)) * (N μ : ℚ) := by ring
        have hmw_div_nonneg :
            0 ≤ markedWeight μ (a - s) / (N μ : ℚ) :=
          div_nonneg hmw_nonneg hNpos.le
        have hcore_rhs_nonneg : 0 ≤ 2 * gammaWeight a s :=
          mul_nonneg (by norm_num) (gammaWeight_nonneg
            (printedTail_range_lt_a (a := a) (s := s) ha hs))
        exact mul_le_mul hcore hmw_div hmw_div_nonneg hcore_rhs_nonneg
    _ = (2 / (2 : ℚ)^(a - s)) * gammaWeight a s := by ring

private theorem kCoeff_div_den_le_gamma_uniform
    {a s : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a))
    (hs : s ∈ Finset.range (printedTailR0 a + 1)) :
    kCoeff μ (a - s) / printedTailDen μ a ≤
      (1 / (2 : ℚ)^(printedTailP a)) * gammaWeight a s := by
  have hpoint := kCoeff_div_den_le_gamma_pow (a := a) (s := s) (μ := μ) ha hμ hs
  have hr_ge : printedTailP a + 1 ≤ a - s :=
    printedTail_range_p_succ_le (a := a) (s := s) ha hs
  have hpow :
      2 / (2 : ℚ)^(a - s) ≤ 1 / (2 : ℚ)^(printedTailP a) := by
    have hr1 : 1 ≤ a - s := by omega
    have hrewrite :
        2 / (2 : ℚ)^(a - s) = 1 / (2 : ℚ)^((a - s) - 1) := by
      have hsplit : (2 : ℚ)^(a - s) =
          (2 : ℚ)^((a - s) - 1) * 2 := by
        nth_rewrite 1 [show a - s = (a - s - 1) + 1 by omega]
        rw [pow_add]
        norm_num
      rw [hsplit]
      field_simp
    rw [hrewrite]
    exact one_div_two_pow_mono (by omega : printedTailP a ≤ (a - s) - 1)
  exact hpoint.trans (mul_le_mul_of_nonneg_right hpow (gammaWeight_nonneg
    (printedTail_range_lt_a (a := a) (s := s) ha hs)))

theorem printedTailKErrorBound_of_eAbsoluteMoment
    (he : PrintedTailEAbsoluteMomentBound) :
    PrintedTailKErrorBound := by
  intro a ha μ hμ
  have heMom := he a ha μ hμ
  have hbudget := printedTailKPowBudget_bound a ha
  have hdenpos : 0 < printedTailDen μ a := by
    unfold printedTailDen
    have hNpos : (0 : ℚ) < (N μ : ℚ) := by
      exact_mod_cast printedTail_N_pos (a := a) (μ := μ) ha hμ
    exact mul_pos hNpos (Prop51.c_pos a (by omega))
  unfold printedTailKNormSum
  rw [Prop51.list_range_map_sum]
  rw [abs_div]
  rw [abs_of_pos hdenpos]
  calc
    |∑ x ∈ Finset.range (printedTailR0 a + 1),
        kCoeff μ (a - x) * printedTailECoeff μ a x| / printedTailDen μ a
        ≤
      ∑ x ∈ Finset.range (printedTailR0 a + 1),
        |kCoeff μ (a - x) * printedTailECoeff μ a x / printedTailDen μ a|
        := by
          calc
            |∑ x ∈ Finset.range (printedTailR0 a + 1),
                kCoeff μ (a - x) * printedTailECoeff μ a x| /
                printedTailDen μ a
                ≤
              (∑ x ∈ Finset.range (printedTailR0 a + 1),
                |kCoeff μ (a - x) * printedTailECoeff μ a x|) /
                printedTailDen μ a :=
                  div_le_div_of_nonneg_right
                    (Finset.abs_sum_le_sum_abs _ _) hdenpos.le
            _ =
              ∑ x ∈ Finset.range (printedTailR0 a + 1),
                |kCoeff μ (a - x) * printedTailECoeff μ a x /
                  printedTailDen μ a| := by
                  rw [Finset.sum_div]
                  refine Finset.sum_congr rfl fun x hx => ?_
                  rw [abs_div, abs_of_pos hdenpos]
    _ ≤
      ∑ x ∈ Finset.range (printedTailR0 a + 1),
        (1 / (2 : ℚ)^(printedTailP a)) *
          (gammaWeight a x * |printedTailECoeff μ a x|) := by
        refine Finset.sum_le_sum fun x hx => ?_
        have hkgamma :=
          kCoeff_div_den_le_gamma_uniform (a := a) (s := x) (μ := μ) ha hμ hx
        have hk_nonneg :
            0 ≤ kCoeff μ (a - x) / printedTailDen μ a := by
          have hr_ge := printedTail_range_p_succ_le (a := a) (s := x) ha hx
          have hr2 : 2 ≤ a - x := by unfold printedTailP at hr_ge; omega
          rw [kCoeff_eq_of_two_le μ (r := a - x) hr2]
          exact div_nonneg
            (mul_nonneg
              (mul_nonneg (mul_nonneg (by norm_num) (by positivity))
                (Prop51.c_pos (a - x - 1) (by omega)).le)
              (markedWeight_nonneg μ (a - x)))
            hdenpos.le
        rw [abs_div, abs_mul, abs_of_pos hdenpos]
        have hrewrite :
            |kCoeff μ (a - x)| / printedTailDen μ a =
              kCoeff μ (a - x) / printedTailDen μ a := by
          have hk_num_nonneg : 0 ≤ kCoeff μ (a - x) := by
            have hmul := mul_nonneg hk_nonneg hdenpos.le
            rwa [div_mul_cancel₀ _ hdenpos.ne'] at hmul
          rw [abs_of_nonneg hk_num_nonneg]
        calc
          |kCoeff μ (a - x)| * |printedTailECoeff μ a x| /
              printedTailDen μ a
              =
            (|kCoeff μ (a - x)| / printedTailDen μ a) *
              |printedTailECoeff μ a x| := by ring
          _ = kCoeff μ (a - x) / printedTailDen μ a *
              |printedTailECoeff μ a x| := by rw [hrewrite]
          _ ≤
            ((1 / (2 : ℚ)^(printedTailP a)) * gammaWeight a x) *
              |printedTailECoeff μ a x|
              := mul_le_mul_of_nonneg_right hkgamma (abs_nonneg _)
          _ = (1 / (2 : ℚ)^(printedTailP a)) *
              (gammaWeight a x * |printedTailECoeff μ a x|) := by ring
    _ =
      (1 / (2 : ℚ)^(printedTailP a)) *
        (∑ x ∈ Finset.range (printedTailR0 a + 1),
          gammaWeight a x * |printedTailECoeff μ a x|) := by
        rw [Finset.mul_sum]
    _ ≤ (1 / (2 : ℚ)^(printedTailP a)) * 9 := by
        exact mul_le_mul_of_nonneg_left heMom (by positivity)
    _ = printedTailKPowBudgetRhs a := by
        unfold printedTailKPowBudgetRhs
        ring
    _ ≤ 1 / (a : ℚ)^2 := hbudget

/-- The printed pointwise coefficient budget
`|\omega_a| <= 920 (3a/2)^a`.  The remaining theorem in this block proves
that this budget implies the normalized `1/a^2` omega error. -/
def printedTailOmegaCoeffBudget (a : Nat) : ℚ :=
  920 * ((3 * (a : ℚ)) / 2)^a

/-- Certificate-facing pointwise omega-coefficient majorant from the printed
proof.  This is the output expected from the `\widehat W(x_2) < 920` majorant
evaluation. -/
def PrintedTailOmegaCoeffMajorant : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      |printedTailOmegaCoeff μ a a| ≤ printedTailOmegaCoeffBudget a

private theorem printedTailOmegaCoeffBudget_eq_x2 (a : Nat) (ha : 150 ≤ a) :
    920 / (printedTailX2 a)^a = printedTailOmegaCoeffBudget a := by
  let x : ℚ := printedTailX2 a
  let y : ℚ := (3 * (a : ℚ)) / 2
  have ha_pos : (0 : ℚ) < a := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 150) ha)
  have hxpos : 0 < x := by
    dsimp [x, printedTailX2]
    positivity
  have hxy : x * y = 1 := by
    dsimp [x, y, printedTailX2]
    field_simp [(by positivity : (3 * (a : ℚ)) ≠ 0)]
  have hxypow : x^a * y^a = 1 := by
    rw [← mul_pow, hxy, one_pow]
  have hxpow_ne : x^a ≠ 0 := pow_ne_zero _ hxpos.ne'
  have hy : y^a = 1 / x^a := by
    calc
      y^a = (x^a * y^a) / x^a := by field_simp [hxpow_ne]
      _ = 1 / x^a := by rw [hxypow]
  dsimp [x, y, printedTailX2] at hy ⊢
  unfold printedTailOmegaCoeffBudget
  rw [hy]
  ring

theorem printedTailOmegaCoeffMajorant_of_wPointBoundX2
    (hpoint : PrintedTailWPointBoundX2) :
    PrintedTailOmegaCoeffMajorant := by
  intro a ha μ hμ
  have hx2pos : 0 < printedTailX2 a := by
    unfold printedTailX2
    have ha_pos : (0 : ℚ) < a := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 150) ha)
    positivity
  have hx2pow_nonneg : 0 ≤ (printedTailX2 a)^a :=
    pow_nonneg hx2pos.le a
  have hx2pow_pos : 0 < (printedTailX2 a)^a := pow_pos hx2pos a
  have hterm_le_sum :
      printedTailWAbsCoeff μ a a * (printedTailX2 a)^a ≤
        ∑ s ∈ Finset.range (a + 1),
          printedTailWAbsCoeff μ a s * (printedTailX2 a)^s := by
    refine Finset.single_le_sum
      (s := Finset.range (a + 1))
      (f := fun s : Nat =>
        printedTailWAbsCoeff μ a s * (printedTailX2 a)^s)
      ?hf ?hmem
    · intro s _hs
      exact mul_nonneg (printedTailWAbsCoeff_nonneg μ a s)
        (pow_nonneg hx2pos.le s)
    · simp
  have homega_x2 :
      |printedTailOmegaCoeff μ a a| * (printedTailX2 a)^a ≤ 920 := by
    calc
      |printedTailOmegaCoeff μ a a| * (printedTailX2 a)^a
          ≤ printedTailWAbsCoeff μ a a * (printedTailX2 a)^a :=
            mul_le_mul_of_nonneg_right
              (abs_printedTailOmegaCoeff_le_WAbsCoeff μ a a) hx2pow_nonneg
      _ ≤ ∑ s ∈ Finset.range (a + 1),
            printedTailWAbsCoeff μ a s * (printedTailX2 a)^s := hterm_le_sum
      _ ≤ 920 := hpoint a ha μ hμ
  have hcoeff_le_div :
      |printedTailOmegaCoeff μ a a| ≤ 920 / (printedTailX2 a)^a := by
    rw [le_div_iff₀ hx2pow_pos]
    exact homega_x2
  rw [printedTailOmegaCoeffBudget_eq_x2 a ha] at hcoeff_le_div
  exact hcoeff_le_div

def printedTailOmegaExpBudgetRhs (a : Nat) : ℚ :=
  (1656 / 5 : ℚ) * (19 / 25 : ℚ)^(a - 1)

def printedTailOmegaExpBudgetScaled (a : Nat) : ℚ :=
  (a : ℚ)^2 * printedTailOmegaExpBudgetRhs a

private theorem printedTailOmega_den_lower {a : Nat} {μ : List Nat}
    (ha : 150 ≤ a) (hμ : Prop51.IsPartitionOf μ (M a)) :
    (5 * (a : ℚ)) *
        ((5 / 36 : ℚ) * ((6 : ℚ)^a *
          ((Nat.factorial (a - 1) : Nat) : ℚ))) ≤
      printedTailDen μ a := by
  unfold printedTailDen
  have hN : (5 * (a : ℚ) : ℚ) ≤ (N μ : ℚ) := by
    have hNnat := printedTail_N_ge_five_mul (a := a) (μ := μ) ha hμ
    norm_num at hNnat ⊢
    exact_mod_cast hNnat
  have hc := Prop51.c_lb a (by omega : 1 ≤ a)
  have hc_nonneg :
      0 ≤ (5 / 36 : ℚ) *
        ((6 : ℚ)^a * ((Nat.factorial (a - 1) : Nat) : ℚ)) := by
    positivity
  have hN_nonneg : 0 ≤ (N μ : ℚ) := by positivity
  exact mul_le_mul hN hc hc_nonneg hN_nonneg

private theorem printedTail_factorial_weaker_lower (a : Nat) (ha : 150 ≤ a) :
    (((a : ℚ) - 1) / 3)^(a - 1) ≤
      ((Nat.factorial (a - 1) : Nat) : ℚ) := by
  have hfac := Prop51.factorial_lb (a - 1)
  have hsub_cast : ((a - 1 : Nat) : ℚ) = (a : ℚ) - 1 := by
    norm_num [Nat.cast_sub (by omega : 1 ≤ a)]
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hbase_nonneg : 0 ≤ ((a : ℚ) - 1) / 3 := by nlinarith
  have hbase_le : ((a : ℚ) - 1) / 3 ≤
      25 * ((a - 1 : Nat) : ℚ) / 68 := by
    rw [hsub_cast]
    nlinarith
  exact (pow_le_pow_left₀ hbase_nonneg hbase_le (a - 1)).trans hfac

private theorem printedTailOmega_den_weaker_lower {a : Nat} {μ : List Nat}
    (ha : 150 ≤ a) (hμ : Prop51.IsPartitionOf μ (M a)) :
    (5 * (a : ℚ)) *
        ((5 / 36 : ℚ) *
          ((6 : ℚ)^a * (((a : ℚ) - 1) / 3)^(a - 1))) ≤
      printedTailDen μ a := by
  have hfac := printedTail_factorial_weaker_lower a ha
  have hfacDen :
      (5 * (a : ℚ)) *
          ((5 / 36 : ℚ) *
            ((6 : ℚ)^a * (((a : ℚ) - 1) / 3)^(a - 1))) ≤
        (5 * (a : ℚ)) *
          ((5 / 36 : ℚ) *
            ((6 : ℚ)^a * ((Nat.factorial (a - 1) : Nat) : ℚ))) := by
    have hnonneg :
        0 ≤ (5 * (a : ℚ)) * ((5 / 36 : ℚ) * (6 : ℚ)^a) := by
      positivity
    calc
      (5 * (a : ℚ)) *
          ((5 / 36 : ℚ) *
            ((6 : ℚ)^a * (((a : ℚ) - 1) / 3)^(a - 1)))
          = ((5 * (a : ℚ)) * ((5 / 36 : ℚ) * (6 : ℚ)^a)) *
              (((a : ℚ) - 1) / 3)^(a - 1) := by ring
      _ ≤ ((5 * (a : ℚ)) * ((5 / 36 : ℚ) * (6 : ℚ)^a)) *
              ((Nat.factorial (a - 1) : Nat) : ℚ) :=
          mul_le_mul_of_nonneg_left hfac hnonneg
      _ =
        (5 * (a : ℚ)) *
          ((5 / 36 : ℚ) *
            ((6 : ℚ)^a * ((Nat.factorial (a - 1) : Nat) : ℚ))) := by
          ring
  exact hfacDen.trans (printedTailOmega_den_lower (a := a) (μ := μ) ha hμ)

private theorem printedTailOmegaCoeffBudget_div_denLower_eq
    (a : Nat) (ha : 150 ≤ a) :
    printedTailOmegaCoeffBudget a /
      ((5 * (a : ℚ)) *
        ((5 / 36 : ℚ) * ((6 : ℚ)^a *
          (((a : ℚ) - 1) / 3)^(a - 1)))) =
      (1656 / 5 : ℚ) *
        ((3 * (a : ℚ)) / (4 * ((a : ℚ) - 1)))^(a - 1) := by
  unfold printedTailOmegaCoeffBudget
  have ha_pos : (0 : ℚ) < a := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 150) ha)
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have ham1_pos : (0 : ℚ) < (a : ℚ) - 1 := by nlinarith
  have hpow3a2 :
      ((3 * (a : ℚ)) / 2)^a =
        ((3 * (a : ℚ)) / 2) * ((3 * (a : ℚ)) / 2)^(a - 1) := by
    rw [← pow_succ']
    congr
    omega
  have hpow6 : (6 : ℚ)^a = 6 * (6 : ℚ)^(a - 1) := by
    rw [← pow_succ']
    congr
    omega
  field_simp [ha_pos.ne', ham1_pos.ne']
  rw [hpow3a2, hpow6]
  have hprod_base :
      (6 : ℚ) * (((a : ℚ) - 1) / 3) *
        ((3 * (a : ℚ)) / (((a : ℚ) - 1) * 4)) =
          (3 * (a : ℚ)) / 2 := by
    field_simp [ham1_pos.ne']
    ring
  have hprod :
      (6 : ℚ)^(a - 1) * (((a : ℚ) - 1) / 3)^(a - 1) *
        ((3 * (a : ℚ)) / (((a : ℚ) - 1) * 4))^(a - 1) =
          ((3 * (a : ℚ)) / 2)^(a - 1) := by
    rw [← mul_pow, ← mul_pow, hprod_base]
  rw [← hprod]
  ring

private theorem printedTailOmegaExpBudget_base_le (a : Nat) (ha : 150 ≤ a) :
    (1656 / 5 : ℚ) *
        ((3 * (a : ℚ)) / (4 * ((a : ℚ) - 1)))^(a - 1) ≤
      printedTailOmegaExpBudgetRhs a := by
  unfold printedTailOmegaExpBudgetRhs
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hdenpos : 0 < 4 * ((a : ℚ) - 1) := by nlinarith
  have hbase_nonneg :
      0 ≤ (3 * (a : ℚ)) / (4 * ((a : ℚ) - 1)) := by positivity
  have hbase_le :
      (3 * (a : ℚ)) / (4 * ((a : ℚ) - 1)) ≤ 19 / 25 := by
    rw [div_le_iff₀ hdenpos]
    nlinarith
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hbase_nonneg hbase_le (a - 1)) (by norm_num)

private theorem printedTailOmegaExpBudgetScaled_step (a : Nat)
    (ha : 150 ≤ a) :
    printedTailOmegaExpBudgetScaled (a + 1) ≤
      printedTailOmegaExpBudgetScaled a := by
  unfold printedTailOmegaExpBudgetScaled printedTailOmegaExpBudgetRhs
  have hpow : (19 / 25 : ℚ) ^ ((a + 1) - 1) =
      (19 / 25 : ℚ) ^ (a - 1) * (19 / 25 : ℚ) := by
    have hidx : (a + 1) - 1 = (a - 1) + 1 := by omega
    rw [hidx, pow_add]
    ring
  rw [hpow]
  have hpoly :
      (((a + 1 : Nat) : ℚ)^2 * (19 / 25 : ℚ) ≤ (a : ℚ)^2) := by
    push_cast
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  have hnonneg :
      0 ≤ (1656 / 5 : ℚ) * (19 / 25 : ℚ) ^ (a - 1) := by
    positivity
  calc
    ((a + 1 : Nat) : ℚ)^2 * ((1656 / 5 : ℚ) *
        ((19 / 25 : ℚ) ^ (a - 1) * (19 / 25 : ℚ)))
        = (((a + 1 : Nat) : ℚ)^2 * (19 / 25 : ℚ)) *
            ((1656 / 5 : ℚ) * (19 / 25 : ℚ) ^ (a - 1)) := by
            ring
    _ ≤ (a : ℚ)^2 *
          ((1656 / 5 : ℚ) * (19 / 25 : ℚ) ^ (a - 1)) :=
        mul_le_mul_of_nonneg_right hpoly hnonneg

private theorem printedTailOmegaExpBudgetScaled_150 :
    printedTailOmegaExpBudgetScaled 150 < 1 := by native_decide

theorem printedTailOmegaExpBudget_bound (a : Nat) (ha : 150 ≤ a) :
    printedTailOmegaExpBudgetRhs a ≤ 1 / (a : ℚ)^2 := by
  have hscaled_lt : printedTailOmegaExpBudgetScaled a < 1 := by
    exact Nat.le_induction
      (P := fun n _ => printedTailOmegaExpBudgetScaled n < 1)
      printedTailOmegaExpBudgetScaled_150
      (fun n hn ih =>
        lt_of_le_of_lt (printedTailOmegaExpBudgetScaled_step n hn) ih) a ha
  have ha_sq_pos : 0 < (a : ℚ)^2 := by positivity
  rw [le_div_iff₀ ha_sq_pos]
  unfold printedTailOmegaExpBudgetScaled at hscaled_lt
  linarith

def PrintedTailOmegaErrorBound : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      |printedTailOmegaNorm μ a| ≤ 1 / (a : ℚ)^2

theorem printedTailOmegaErrorBound_of_coeffMajorant
    (hcoeffMajorant : PrintedTailOmegaCoeffMajorant) :
    PrintedTailOmegaErrorBound := by
  intro a ha μ hμ
  unfold printedTailOmegaNorm
  have hdenpos := printedTail_den_pos (a := a) (μ := μ) ha hμ
  have hdenposDen : 0 < printedTailDen μ a := by
    unfold printedTailDen
    exact hdenpos
  have hdenlower :=
    printedTailOmega_den_weaker_lower (a := a) (μ := μ) ha hμ
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hbase_pos : 0 < ((a : ℚ) - 1) / 3 := by nlinarith
  have hdenlower_pos :
      0 < (5 * (a : ℚ)) *
        ((5 / 36 : ℚ) *
          ((6 : ℚ)^a * (((a : ℚ) - 1) / 3)^(a - 1))) := by
    positivity
  have hbudget_nonneg : 0 ≤ printedTailOmegaCoeffBudget a := by
    unfold printedTailOmegaCoeffBudget
    positivity
  rw [abs_div, abs_of_pos hdenposDen]
  have hnorm_le_budget :
      |printedTailOmegaCoeff μ a a| / printedTailDen μ a ≤
        printedTailOmegaExpBudgetRhs a := by
    calc
      |printedTailOmegaCoeff μ a a| / printedTailDen μ a
          ≤ printedTailOmegaCoeffBudget a / printedTailDen μ a :=
            div_le_div_of_nonneg_right (hcoeffMajorant a ha μ hμ) hdenposDen.le
      _ ≤ printedTailOmegaCoeffBudget a /
          ((5 * (a : ℚ)) *
            ((5 / 36 : ℚ) *
              ((6 : ℚ)^a * (((a : ℚ) - 1) / 3)^(a - 1)))) :=
            div_le_div_of_nonneg_left hbudget_nonneg hdenlower_pos hdenlower
      _ =
        (1656 / 5 : ℚ) *
          ((3 * (a : ℚ)) / (4 * ((a : ℚ) - 1)))^(a - 1) :=
            printedTailOmegaCoeffBudget_div_denLower_eq a ha
      _ ≤ printedTailOmegaExpBudgetRhs a :=
            printedTailOmegaExpBudget_base_le a ha
  exact hnorm_le_budget.trans (printedTailOmegaExpBudget_bound a ha)

/-- Final normalized large-tail assembly from the exact split and the three
finite error estimates. -/
theorem printedTailNormalizedLowerBound_of_split_errorBounds
    (hsplit : PrintedTailExactSplit)
    (hmain : PrintedTailMainLowerBound)
    (hh : PrintedTailHErrorBound)
    (hk : PrintedTailKErrorBound)
    (homega : PrintedTailOmegaErrorBound) :
    PrintedTailNormalizedLowerBound := by
  intro a ha μ hμ
  change printedLargeMargin a ≤ (-printedCoeff μ a) / printedTailDen μ a
  rw [hsplit a ha μ hμ]
  have hmain_lb := hmain a ha μ hμ
  have hh_abs := abs_le.mp (hh a ha μ hμ)
  have hk_abs := abs_le.mp (hk a ha μ hμ)
  have homega_abs := abs_le.mp (homega a ha μ hμ)
  have hmargin_decomp :
      printedLargeMargin a =
        9 / (40 * ((a : ℚ) - 2)) - 1 / (a : ℚ)^2 -
          printedTailHErrorBudget a - 1 / (a : ℚ)^2 -
          1 / (a : ℚ)^2 := by
    unfold printedLargeMargin printedTailHErrorBudget
    ring
  unfold printedTailSplitRhs
  rw [hmargin_decomp]
  nlinarith [hh_abs.1, hk_abs.1, homega_abs.2]

theorem printedCoeffNegativityTail_of_split_errorBounds
    (hsplit : PrintedTailExactSplit)
    (hmain : PrintedTailMainLowerBound)
    (hh : PrintedTailHErrorBound)
    (hk : PrintedTailKErrorBound)
    (homega : PrintedTailOmegaErrorBound) :
    PrintedCoeffNegativityTail :=
  printedCoeffNegativityTail_of_normalizedLowerBound
    (printedTailNormalizedLowerBound_of_split_errorBounds
      hsplit hmain hh hk homega)

theorem printedTailNormalizedLowerBound_of_errorBounds
    (hmain : PrintedTailMainLowerBound)
    (hh : PrintedTailHErrorBound)
    (hk : PrintedTailKErrorBound)
    (homega : PrintedTailOmegaErrorBound) :
    PrintedTailNormalizedLowerBound :=
  printedTailNormalizedLowerBound_of_split_errorBounds
    printedTailExactSplit_closed hmain hh hk homega

theorem printedCoeffNegativityTail_of_errorBounds
    (hmain : PrintedTailMainLowerBound)
    (hh : PrintedTailHErrorBound)
    (hk : PrintedTailKErrorBound)
    (homega : PrintedTailOmegaErrorBound) :
    PrintedCoeffNegativityTail :=
  printedCoeffNegativityTail_of_split_errorBounds
    printedTailExactSplit_closed hmain hh hk homega

/-! ## Gamma-margin arithmetic -/

def gammaExponentBound (a : Nat) : ℚ :=
  5 / 4 + 5 / (2 * ((a : ℚ) - 3)) +
    96 * (a : ℚ)^2 / (25 * ((a : ℚ) - 5)^3)

private theorem gammaExponentBound_poly_pos (a : Nat) (ha : 150 ≤ a) :
    0 < 100 * (a : ℚ)^4 - 14480 * (a : ℚ)^3 + 110040 * (a : ℚ)^2 -
      410000 * (a : ℚ) + 662500 := by
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hshift : 0 ≤ (a : ℚ) - 150 := by nlinarith
  have hsq : 0 ≤ ((a : ℚ) - 150)^2 := sq_nonneg _
  have hcube : 0 ≤ ((a : ℚ) - 150)^3 := by positivity
  have hfour : 0 ≤ ((a : ℚ) - 150)^4 := by positivity
  have hdecomp :
      100 * (a : ℚ)^4 - 14480 * (a : ℚ)^3 + 110040 * (a : ℚ)^2 -
          410000 * (a : ℚ) + 662500 =
        100 * ((a : ℚ) - 150)^4 + 45520 * ((a : ℚ) - 150)^3 +
          7094040 * ((a : ℚ) - 150)^2 + 405202000 * ((a : ℚ) - 150) +
          4170062500 := by
    ring
  rw [hdecomp]
  nlinarith

/-- The rational endpoint in the Gamma-margin proof is uniformly below
`13/10` for all `a >= 150`. -/
theorem gammaExponentBound_lt (a : Nat) (ha : 150 ≤ a) :
    gammaExponentBound a < 13 / 10 := by
  unfold gammaExponentBound
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have h3 : (0 : ℚ) < (a : ℚ) - 3 := by nlinarith
  have h5 : (0 : ℚ) < (a : ℚ) - 5 := by nlinarith
  have hpoly := gammaExponentBound_poly_pos a ha
  field_simp [h3.ne', h5.ne']
  ring_nf
  nlinarith

/-! ## Exact factorial-gas constants

The following declarations mirror the first block of
`verify_prop52_tail_constants.py`.  They certify the four finite prefix sums
over `4 <= r <= 75` and the elementary geometric-tail budgets starting at
`r = 76`.
-/

def factorialGasPrefixTerm (base r : Nat) (weighted : Bool) : ℚ :=
  (((Nat.factorial (r - 1) * base^r * 150^4 : Nat) : ℚ) / (150 : ℚ)^r) *
    if weighted then (r : ℚ) else 1

def factorialGasPrefix (base : Nat) (weighted : Bool) : ℚ :=
  ((List.range 72).map fun i : Nat => factorialGasPrefixTerm base (i + 4) weighted).sum

theorem factorialGas_prefix_base4 :
    factorialGasPrefix 4 false < 1727 := by
  native_decide

theorem factorialGas_prefix_base4_weighted :
    factorialGasPrefix 4 true < 7128 := by
  native_decide

theorem factorialGas_prefix_base2 :
    factorialGasPrefix 2 false < 102 := by
  native_decide

theorem factorialGas_prefix_base2_weighted :
    factorialGasPrefix 2 true < 412 := by
  native_decide

theorem factorialGas_tail_base4_first :
    (((48 * 76^4 * 3^76 : Nat) : ℚ) / (4 : ℚ)^76) < 3 / 5 := by
  native_decide

theorem factorialGas_tail_base4_ratio :
    (((3 * 77^4 : Nat) : ℚ) / ((4 * 76^4 : Nat) : ℚ)) < 4 / 5 := by
  native_decide

theorem factorialGas_tail_base4_weighted_first :
    (((48 * 76^5 * 3^76 : Nat) : ℚ) / (4 : ℚ)^76) < 39 := by
  native_decide

theorem factorialGas_tail_base4_weighted_ratio :
    (((3 * 77^5 : Nat) : ℚ) / ((4 * 76^5 : Nat) : ℚ)) < 13 / 16 := by
  native_decide

theorem factorialGas_tail_base2_first :
    (((48 * 76^4 * 3^76 : Nat) : ℚ) / (8 : ℚ)^76) < 1 / 2 := by
  native_decide

theorem factorialGas_tail_base2_ratio :
    (((3 * 77^4 : Nat) : ℚ) / ((8 * 76^4 : Nat) : ℚ)) < 1 / 2 := by
  native_decide

theorem factorialGas_tail_base2_weighted_first :
    (((48 * 76^5 * 3^76 : Nat) : ℚ) / (8 : ℚ)^76) < 1 / 2 := by
  native_decide

theorem factorialGas_tail_base2_weighted_ratio :
    (((3 * 77^5 : Nat) : ℚ) / ((8 * 76^5 : Nat) : ℚ)) < 1 / 2 := by
  native_decide

theorem factorialGas_prefix_tail_base4 :
    factorialGasPrefix 4 false + 3 < 1730 := by
  native_decide

theorem factorialGas_prefix_tail_base4_weighted :
    factorialGasPrefix 4 true + 208 < 7340 := by
  native_decide

theorem factorialGas_prefix_tail_base2 :
    factorialGasPrefix 2 false + 1 < 103 := by
  native_decide

theorem factorialGas_prefix_tail_base2_weighted :
    factorialGasPrefix 2 true + 1 < 413 := by
  native_decide

private theorem choose_three_cast {n : Nat} (hn : 3 ≤ n) :
    ((n.choose 3 : Nat) : ℚ) =
      (n : ℚ) * (n - 1 : Nat) * (n - 2 : Nat) / 6 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 3 + m - 1 = m + 2 by omega,
    show 3 + m - 2 = m + 1 by omega]
  have h := Nat.choose_mul_factorial_mul_factorial
    (n := 3 + m) (k := 3) (by omega : 3 ≤ 3 + m)
  norm_num at h
  have hq :
      (((3 + m).choose 3 * 6 * m.factorial : Nat) : ℚ) =
        (((3 + m).factorial : Nat) : ℚ) := by
    exact_mod_cast h
  have hfac :
      (((3 + m).factorial : Nat) : ℚ) =
        ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) *
          ((m.factorial : Nat) : ℚ) := by
    rw [show 3 + m = (m + 2) + 1 by omega, Nat.factorial_succ]
    rw [show m + 2 = (m + 1) + 1 by omega, Nat.factorial_succ]
    rw [show m + 1 = m + 1 by rfl, Nat.factorial_succ]
    norm_num
    ring
  rw [Nat.cast_mul, Nat.cast_mul, hfac] at hq
  have hfac_ne : (((m.factorial : Nat) : ℚ)) ≠ 0 := by positivity
  field_simp [hfac_ne] at hq ⊢
  push_cast
  ring_nf at hq ⊢
  exact hq

private theorem eight_thirds_le_one_add_inv_pow_succ
    (r : Nat) (hr : 1 ≤ r) :
    (8 / 3 : ℚ) ≤ (1 + 1 / (r : ℚ))^(r + 1) := by
  rcases Nat.eq_or_lt_of_le hr with rfl | hrgt
  · norm_num
  have hrpos : (0 : ℚ) < (r : ℚ) := by
    exact_mod_cast (by omega : 0 < r)
  let y : ℚ := 1 / (r : ℚ)
  let T : Nat → ℚ := fun m =>
    y^m * 1^(r + 1 - m) * ((r + 1).choose m : ℚ)
  have hfull :
      (1 + 1 / (r : ℚ))^(r + 1) =
        ∑ m ∈ Finset.range (r + 2), T m := by
    dsimp [T, y]
    calc
      (1 + 1 / (r : ℚ))^(r + 1)
          = (1 / (r : ℚ) + 1)^(r + 1) := by ring_nf
      _ = ∑ m ∈ Finset.range (r + 1 + 1),
            (1 / (r : ℚ))^m * 1^(r + 1 - m) *
              ((r + 1).choose m : ℚ) := by
            exact add_pow (1 / (r : ℚ)) (1 : ℚ) (r + 1)
      _ = ∑ m ∈ Finset.range (r + 2),
            (1 / (r : ℚ))^m * 1^(r + 1 - m) *
              ((r + 1).choose m : ℚ) := by
            rw [show r + 1 + 1 = r + 2 by omega]
  have hprefix_le :
      (∑ m ∈ Finset.range 4, T m) ≤
        ∑ m ∈ Finset.range (r + 2), T m := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?hsub ?hnonneg
    · intro m hm
      simp only [Finset.mem_range] at hm ⊢
      omega
    · intro m _hm _hnot
      dsimp [T, y]
      positivity
  have hprefix :
      (∑ m ∈ Finset.range 4, T m) =
        8 / 3 + 3 / (2 * (r : ℚ)) - 1 / (6 * (r : ℚ)^2) := by
    dsimp [T, y]
    norm_num [Finset.sum_range_succ, Nat.choose_one_right,
      Nat.cast_choose_two ℚ, choose_three_cast (by omega : 3 ≤ r + 1)]
    rw [show r + 1 - 2 = r - 1 by omega]
    rw [Nat.cast_sub (by omega : 1 ≤ r)]
    field_simp [hrpos.ne']
    ring_nf
  have hprefix_ge : (8 / 3 : ℚ) ≤ ∑ m ∈ Finset.range 4, T m := by
    rw [hprefix]
    have hpos :
        0 ≤ 3 / (2 * (r : ℚ)) - 1 / (6 * (r : ℚ)^2) := by
      have hnum : 0 ≤ 9 * (r : ℚ) - 1 := by
        have hrQ : (1 : ℚ) ≤ r := by exact_mod_cast hr
        nlinarith
      have hden : 0 < 6 * (r : ℚ)^2 := by positivity
      have hrepr :
          3 / (2 * (r : ℚ)) - 1 / (6 * (r : ℚ)^2) =
            (9 * (r : ℚ) - 1) / (6 * (r : ℚ)^2) := by
        field_simp [hrpos.ne', pow_ne_zero 2 hrpos.ne']
        ring
      rw [hrepr]
      exact div_nonneg hnum hden.le
    linarith
  rw [hfull]
  exact hprefix_ge.trans hprefix_le

private theorem factorial_pred_le_rational_stirling
    (r : Nat) (hr : 1 ≤ r) :
    (((r - 1).factorial : Nat) : ℚ) ≤
      3 * (r : ℚ)^r * (3 / 8 : ℚ)^r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
      have hrpos : (0 : ℚ) < (r : ℚ) := by
        exact_mod_cast (by omega : 0 < r)
      have hpowratio0 :
          (8 / 3 : ℚ) ≤ (1 + 1 / (r : ℚ))^(r + 1) :=
        eight_thirds_le_one_add_inv_pow_succ r hr
      have hpowratio :
          (8 / 3 : ℚ) * (r : ℚ)^(r + 1) ≤
            ((r + 1 : Nat) : ℚ)^(r + 1) := by
        have hmul := mul_le_mul_of_nonneg_right hpowratio0
          (pow_nonneg hrpos.le (r + 1))
        have hbase :
            1 + 1 / (r : ℚ) = ((r + 1 : Nat) : ℚ) / (r : ℚ) := by
          field_simp [hrpos.ne']
          push_cast
          ring
        rw [hbase] at hmul
        calc
          (8 / 3 : ℚ) * (r : ℚ)^(r + 1)
              ≤ (((r + 1 : Nat) : ℚ) / (r : ℚ))^(r + 1) *
                  (r : ℚ)^(r + 1) := hmul
          _ = ((r + 1 : Nat) : ℚ)^(r + 1) := by
              rw [div_pow]
              field_simp [pow_ne_zero (r + 1) hrpos.ne']
      have hcore :
          (r : ℚ)^(r + 1) ≤
            (3 / 8 : ℚ) * (((r + 1 : Nat) : ℚ)^(r + 1)) := by
        nlinarith [hpowratio]
      have hfac :
          (((r + 1 - 1).factorial : Nat) : ℚ) =
            (r : ℚ) * (((r - 1).factorial : Nat) : ℚ) := by
        rw [show r + 1 - 1 = r by omega]
        rw [show r = (r - 1) + 1 by omega, Nat.factorial_succ]
        norm_num
      rw [hfac]
      calc
        (r : ℚ) * (((r - 1).factorial : Nat) : ℚ)
            ≤ (r : ℚ) * (3 * (r : ℚ)^r * (3 / 8 : ℚ)^r) :=
              mul_le_mul_of_nonneg_left ih hrpos.le
        _ = 3 * (r : ℚ)^(r + 1) * (3 / 8 : ℚ)^r := by ring
        _ ≤ 3 * (((r + 1 : Nat) : ℚ)^(r + 1)) *
              (3 / 8 : ℚ)^(r + 1) := by
          calc
            3 * (r : ℚ)^(r + 1) * (3 / 8 : ℚ)^r
                ≤ 3 * ((3 / 8 : ℚ) *
                    ((r + 1 : Nat) : ℚ)^(r + 1)) *
                    (3 / 8 : ℚ)^r :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hcore
                      (by norm_num : (0 : ℚ) ≤ 3))
                    (pow_nonneg (by norm_num) r)
            _ = 3 * (((r + 1 : Nat) : ℚ)^(r + 1)) *
                  (3 / 8 : ℚ)^(r + 1) := by
                rw [pow_succ]
                ring

private theorem factorialGasPrefix_scale_le
    {a base r : Nat} (ha : 150 ≤ a) (hr : 4 ≤ r) :
    (((r - 1).factorial : Nat) : ℚ) * (base : ℚ)^r / (a : ℚ)^r
      ≤ factorialGasPrefixTerm base r false / (a : ℚ)^4 := by
  let A : ℚ := a
  have hApos : 0 < A := by
    dsimp [A]
    exact_mod_cast (by omega : 0 < a)
  have h150pos : (0 : ℚ) < 150 := by norm_num
  have hpow150_le : (150 : ℚ)^(r - 4) ≤ A^(r - 4) := by
    dsimp [A]
    exact pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 150)
      (by exact_mod_cast ha) (r - 4)
  have hinv_le : 1 / A^(r - 4) ≤ 1 / (150 : ℚ)^(r - 4) :=
    one_div_le_one_div_of_le (pow_pos h150pos (r - 4)) hpow150_le
  calc
    (((r - 1).factorial : Nat) : ℚ) * (base : ℚ)^r / (a : ℚ)^r
        = ((((r - 1).factorial : Nat) : ℚ) * (base : ℚ)^r / A^4) *
            (1 / A^(r - 4)) := by
          dsimp [A]
          rw [show r = 4 + (r - 4) by omega, pow_add]
          field_simp [hApos.ne', pow_ne_zero 4 hApos.ne',
            pow_ne_zero (r - 4) hApos.ne']
          rw [show 4 + (r - 4) - 4 = r - 4 by omega]
          ring
    _ ≤ ((((r - 1).factorial : Nat) : ℚ) * (base : ℚ)^r / A^4) *
          (1 / (150 : ℚ)^(r - 4)) :=
          mul_le_mul_of_nonneg_left hinv_le (by positivity)
    _ = factorialGasPrefixTerm base r false / A^4 := by
          unfold factorialGasPrefixTerm
          simp
          rw [show r = 4 + (r - 4) by omega, pow_add]
          field_simp [hApos.ne', pow_ne_zero 4 h150pos.ne',
            pow_ne_zero (r - 4) h150pos.ne']
          norm_num
          ring

private theorem factorialGasPrefix_weighted_scale_le
    {a base r : Nat} (ha : 150 ≤ a) (hr : 4 ≤ r) :
    (r : ℚ) * ((((r - 1).factorial : Nat) : ℚ) *
        (base : ℚ)^r / (a : ℚ)^r)
      ≤ factorialGasPrefixTerm base r true / (a : ℚ)^4 := by
  have hbase := factorialGasPrefix_scale_le
    (a := a) (base := base) (r := r) ha hr
  have hr_nonneg : 0 ≤ (r : ℚ) := by positivity
  calc
    (r : ℚ) * ((((r - 1).factorial : Nat) : ℚ) *
        (base : ℚ)^r / (a : ℚ)^r)
        ≤ (r : ℚ) * (factorialGasPrefixTerm base r false / (a : ℚ)^4) :=
          mul_le_mul_of_nonneg_left hbase hr_nonneg
    _ = factorialGasPrefixTerm base r true / (a : ℚ)^4 := by
          unfold factorialGasPrefixTerm
          simp
          ring

private theorem factorialGasBase4_tail_term_le
    {a r : Nat} (hr : 4 ≤ r) (hra : 2 * r ≤ a) :
    (((r - 1).factorial : Nat) : ℚ) * (4 : ℚ)^r / (a : ℚ)^r
      ≤ (48 * (r : ℚ)^4 * (3 / 4 : ℚ)^r) / (a : ℚ)^4 := by
  let R : ℚ := r
  let A : ℚ := a
  have hRpos : 0 < R := by
    dsimp [R]
    exact_mod_cast (by omega : 0 < r)
  have hApos : 0 < A := by
    dsimp [A]
    exact_mod_cast (by omega : 0 < a)
  have hratio : R / A ≤ (1 / 2 : ℚ) := by
    dsimp [R, A]
    rw [div_le_iff₀ hApos]
    have hq : (2 : ℚ) * (r : ℚ) ≤ (a : ℚ) := by exact_mod_cast hra
    nlinarith
  have hratio_nonneg : 0 ≤ R / A := by positivity
  have hpow_ratio :
      (R / A)^(r - 4) ≤ (1 / 2 : ℚ)^(r - 4) :=
    pow_le_pow_left₀ hratio_nonneg hratio (r - 4)
  have hfac := factorial_pred_le_rational_stirling r (by omega : 1 ≤ r)
  have hbase :
      (((r - 1).factorial : Nat) : ℚ) * (4 : ℚ)^r / A^r
        ≤ (3 * R^r * (3 / 8 : ℚ)^r) * (4 : ℚ)^r / A^r := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hfac (pow_nonneg (by norm_num) r))
      (pow_nonneg hApos.le r)
  have hRpow : R^r = R^4 * R^(r - 4) := by
    conv_lhs => rw [show r = 4 + (r - 4) by omega]
    rw [pow_add]
  have hApow : A^r = A^4 * A^(r - 4) := by
    conv_lhs => rw [show r = 4 + (r - 4) by omega]
    rw [pow_add]
  have h384 : (3 / 8 : ℚ)^r * (4 : ℚ)^r = (3 / 2 : ℚ)^r := by
    rw [← mul_pow]
    norm_num
  have h12_32 :
      (1 / 2 : ℚ)^(r - 4) * (3 / 2 : ℚ)^(r - 4) =
        (3 / 4 : ℚ)^(r - 4) := by
    rw [← mul_pow]
    norm_num
  have h34pow :
      (3 / 4 : ℚ)^r = (3 / 4 : ℚ)^4 * (3 / 4 : ℚ)^(r - 4) := by
    conv_lhs => rw [show r = 4 + (r - 4) by omega]
    rw [pow_add]
  have h32pow :
      (3 / 2 : ℚ)^r = (3 / 2 : ℚ)^4 * (3 / 2 : ℚ)^(r - 4) := by
    conv_lhs => rw [show r = 4 + (r - 4) by omega]
    rw [pow_add]
  calc
    (((r - 1).factorial : Nat) : ℚ) * (4 : ℚ)^r / (a : ℚ)^r
        = (((r - 1).factorial : Nat) : ℚ) * (4 : ℚ)^r / A^r := by rfl
    _ ≤ (3 * R^r * (3 / 8 : ℚ)^r) * (4 : ℚ)^r / A^r := hbase
    _ = 3 * (R^4 / A^4) * (R / A)^(r - 4) * (3 / 2 : ℚ)^r := by
      rw [hRpow, hApow]
      calc
        (3 * (R^4 * R^(r - 4)) * (3 / 8 : ℚ)^r) * (4 : ℚ)^r /
            (A^4 * A^(r - 4))
            = 3 * (R^4 * R^(r - 4)) *
                ((3 / 8 : ℚ)^r * (4 : ℚ)^r) /
                (A^4 * A^(r - 4)) := by ring
        _ = 3 * (R^4 * R^(r - 4)) * (3 / 2 : ℚ)^r /
              (A^4 * A^(r - 4)) := by rw [h384]
        _ = 3 * (R^4 / A^4) * (R^(r - 4) / A^(r - 4)) *
              (3 / 2 : ℚ)^r := by
            field_simp [hApos.ne', pow_ne_zero 4 hApos.ne',
              pow_ne_zero (r - 4) hApos.ne']
        _ = 3 * (R^4 / A^4) * (R / A)^(r - 4) *
              (3 / 2 : ℚ)^r := by
            rw [← div_pow R A (r - 4)]
    _ ≤ 3 * (R^4 / A^4) * (1 / 2 : ℚ)^(r - 4) *
          (3 / 2 : ℚ)^r := by
      have hnonneg : 0 ≤ 3 * (R^4 / A^4) := by positivity
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow_ratio hnonneg)
        (pow_nonneg (by norm_num) r)
    _ = (48 * R^4 * (3 / 4 : ℚ)^r) / A^4 := by
      rw [h34pow, h32pow]
      calc
        3 * (R^4 / A^4) * (1 / 2 : ℚ)^(r - 4) *
            ((3 / 2 : ℚ)^4 * (3 / 2 : ℚ)^(r - 4))
            = 3 * (R^4 / A^4) *
                ((1 / 2 : ℚ)^(r - 4) * (3 / 2 : ℚ)^(r - 4)) *
                (3 / 2 : ℚ)^4 := by ring
        _ = 3 * (R^4 / A^4) * (3 / 4 : ℚ)^(r - 4) *
              (3 / 2 : ℚ)^4 := by rw [h12_32]
        _ = (48 * R^4 * ((3 / 4 : ℚ)^4 * (3 / 4 : ℚ)^(r - 4))) /
              A^4 := by
            field_simp [hApos.ne', pow_ne_zero 4 hApos.ne']
            norm_num
    _ = (48 * (r : ℚ)^4 * (3 / 4 : ℚ)^r) / (a : ℚ)^4 := by rfl

private theorem factorialGasBase2_tail_term_le
    {a r : Nat} (hr : 4 ≤ r) (hra : 2 * r ≤ a) :
    (((r - 1).factorial : Nat) : ℚ) * (2 : ℚ)^r / (a : ℚ)^r
      ≤ (48 * (r : ℚ)^4 * (3 / 8 : ℚ)^r) / (a : ℚ)^4 := by
  let R : ℚ := r
  let A : ℚ := a
  have hRpos : 0 < R := by
    dsimp [R]
    exact_mod_cast (by omega : 0 < r)
  have hApos : 0 < A := by
    dsimp [A]
    exact_mod_cast (by omega : 0 < a)
  have hratio : R / A ≤ (1 / 2 : ℚ) := by
    dsimp [R, A]
    rw [div_le_iff₀ hApos]
    have hq : (2 : ℚ) * (r : ℚ) ≤ (a : ℚ) := by exact_mod_cast hra
    nlinarith
  have hratio_nonneg : 0 ≤ R / A := by positivity
  have hpow_ratio :
      (R / A)^(r - 4) ≤ (1 / 2 : ℚ)^(r - 4) :=
    pow_le_pow_left₀ hratio_nonneg hratio (r - 4)
  have hfac := factorial_pred_le_rational_stirling r (by omega : 1 ≤ r)
  have hbase :
      (((r - 1).factorial : Nat) : ℚ) * (2 : ℚ)^r / A^r
        ≤ (3 * R^r * (3 / 8 : ℚ)^r) * (2 : ℚ)^r / A^r := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hfac (pow_nonneg (by norm_num) r))
      (pow_nonneg hApos.le r)
  have hRpow : R^r = R^4 * R^(r - 4) := by
    conv_lhs => rw [show r = 4 + (r - 4) by omega]
    rw [pow_add]
  have hApow : A^r = A^4 * A^(r - 4) := by
    conv_lhs => rw [show r = 4 + (r - 4) by omega]
    rw [pow_add]
  have h382 : (3 / 8 : ℚ)^r * (2 : ℚ)^r = (3 / 4 : ℚ)^r := by
    rw [← mul_pow]
    norm_num
  have h12_34 :
      (1 / 2 : ℚ)^(r - 4) * (3 / 4 : ℚ)^(r - 4) =
        (3 / 8 : ℚ)^(r - 4) := by
    rw [← mul_pow]
    norm_num
  have h38pow :
      (3 / 8 : ℚ)^r = (3 / 8 : ℚ)^4 * (3 / 8 : ℚ)^(r - 4) := by
    conv_lhs => rw [show r = 4 + (r - 4) by omega]
    rw [pow_add]
  have h34pow :
      (3 / 4 : ℚ)^r = (3 / 4 : ℚ)^4 * (3 / 4 : ℚ)^(r - 4) := by
    conv_lhs => rw [show r = 4 + (r - 4) by omega]
    rw [pow_add]
  calc
    (((r - 1).factorial : Nat) : ℚ) * (2 : ℚ)^r / (a : ℚ)^r
        = (((r - 1).factorial : Nat) : ℚ) * (2 : ℚ)^r / A^r := by rfl
    _ ≤ (3 * R^r * (3 / 8 : ℚ)^r) * (2 : ℚ)^r / A^r := hbase
    _ = 3 * (R^4 / A^4) * (R / A)^(r - 4) * (3 / 4 : ℚ)^r := by
      rw [hRpow, hApow]
      calc
        (3 * (R^4 * R^(r - 4)) * (3 / 8 : ℚ)^r) * (2 : ℚ)^r /
            (A^4 * A^(r - 4))
            = 3 * (R^4 * R^(r - 4)) *
                ((3 / 8 : ℚ)^r * (2 : ℚ)^r) /
                (A^4 * A^(r - 4)) := by ring
        _ = 3 * (R^4 * R^(r - 4)) * (3 / 4 : ℚ)^r /
              (A^4 * A^(r - 4)) := by rw [h382]
        _ = 3 * (R^4 / A^4) * (R^(r - 4) / A^(r - 4)) *
              (3 / 4 : ℚ)^r := by
            field_simp [hApos.ne', pow_ne_zero 4 hApos.ne',
              pow_ne_zero (r - 4) hApos.ne']
        _ = 3 * (R^4 / A^4) * (R / A)^(r - 4) *
              (3 / 4 : ℚ)^r := by
            rw [← div_pow R A (r - 4)]
    _ ≤ 3 * (R^4 / A^4) * (1 / 2 : ℚ)^(r - 4) *
          (3 / 4 : ℚ)^r := by
      have hnonneg : 0 ≤ 3 * (R^4 / A^4) := by positivity
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow_ratio hnonneg)
        (pow_nonneg (by norm_num) r)
    _ = (48 * R^4 * (3 / 8 : ℚ)^r) / A^4 := by
      rw [h38pow, h34pow]
      calc
        3 * (R^4 / A^4) * (1 / 2 : ℚ)^(r - 4) *
            ((3 / 4 : ℚ)^4 * (3 / 4 : ℚ)^(r - 4))
            = 3 * (R^4 / A^4) *
                ((1 / 2 : ℚ)^(r - 4) * (3 / 4 : ℚ)^(r - 4)) *
                (3 / 4 : ℚ)^4 := by ring
        _ = 3 * (R^4 / A^4) * (3 / 8 : ℚ)^(r - 4) *
              (3 / 4 : ℚ)^4 := by rw [h12_34]
        _ = (48 * R^4 * ((3 / 8 : ℚ)^4 * (3 / 8 : ℚ)^(r - 4))) /
              A^4 := by
            field_simp [hApos.ne', pow_ne_zero 4 hApos.ne']
            norm_num
    _ = (48 * (r : ℚ)^4 * (3 / 8 : ℚ)^r) / (a : ℚ)^4 := by rfl

private theorem factorialGasBase4_weighted_tail_term_le
    {a r : Nat} (hr : 4 ≤ r) (hra : 2 * r ≤ a) :
    (r : ℚ) * ((((r - 1).factorial : Nat) : ℚ) *
        (4 : ℚ)^r / (a : ℚ)^r)
      ≤ (48 * (r : ℚ)^5 * (3 / 4 : ℚ)^r) / (a : ℚ)^4 := by
  have h := factorialGasBase4_tail_term_le (a := a) (r := r) hr hra
  have hr_nonneg : 0 ≤ (r : ℚ) := by positivity
  calc
    (r : ℚ) * ((((r - 1).factorial : Nat) : ℚ) *
        (4 : ℚ)^r / (a : ℚ)^r)
        ≤ (r : ℚ) * ((48 * (r : ℚ)^4 * (3 / 4 : ℚ)^r) /
            (a : ℚ)^4) := mul_le_mul_of_nonneg_left h hr_nonneg
    _ = (48 * (r : ℚ)^5 * (3 / 4 : ℚ)^r) / (a : ℚ)^4 := by
          ring

private theorem factorialGasBase2_weighted_tail_term_le
    {a r : Nat} (hr : 4 ≤ r) (hra : 2 * r ≤ a) :
    (r : ℚ) * ((((r - 1).factorial : Nat) : ℚ) *
        (2 : ℚ)^r / (a : ℚ)^r)
      ≤ (48 * (r : ℚ)^5 * (3 / 8 : ℚ)^r) / (a : ℚ)^4 := by
  have h := factorialGasBase2_tail_term_le (a := a) (r := r) hr hra
  have hr_nonneg : 0 ≤ (r : ℚ) := by positivity
  calc
    (r : ℚ) * ((((r - 1).factorial : Nat) : ℚ) *
        (2 : ℚ)^r / (a : ℚ)^r)
        ≤ (r : ℚ) * ((48 * (r : ℚ)^4 * (3 / 8 : ℚ)^r) /
            (a : ℚ)^4) := mul_le_mul_of_nonneg_left h hr_nonneg
    _ = (48 * (r : ℚ)^5 * (3 / 8 : ℚ)^r) / (a : ℚ)^4 := by
          ring

private def factorialGasTailBase4Term (r : Nat) : ℚ :=
  48 * (r : ℚ)^4 * (3 / 4 : ℚ)^r

private def factorialGasTailBase4WeightedTerm (r : Nat) : ℚ :=
  48 * (r : ℚ)^5 * (3 / 4 : ℚ)^r

private def factorialGasTailBase2Term (r : Nat) : ℚ :=
  48 * (r : ℚ)^4 * (3 / 8 : ℚ)^r

private def factorialGasTailBase2WeightedTerm (r : Nat) : ℚ :=
  48 * (r : ℚ)^5 * (3 / 8 : ℚ)^r

private theorem factorialGasTailBase4Term_nonneg (r : Nat) :
    0 ≤ factorialGasTailBase4Term r := by
  unfold factorialGasTailBase4Term
  positivity

private theorem factorialGasTailBase4WeightedTerm_nonneg (r : Nat) :
    0 ≤ factorialGasTailBase4WeightedTerm r := by
  unfold factorialGasTailBase4WeightedTerm
  positivity

private theorem factorialGasTailBase2Term_nonneg (r : Nat) :
    0 ≤ factorialGasTailBase2Term r := by
  unfold factorialGasTailBase2Term
  positivity

private theorem factorialGasTailBase2WeightedTerm_nonneg (r : Nat) :
    0 ≤ factorialGasTailBase2WeightedTerm r := by
  unfold factorialGasTailBase2WeightedTerm
  positivity

private theorem factorialGasTailBase4Term_succ_le
    (r : Nat) (hr : 76 ≤ r) :
    factorialGasTailBase4Term (r + 1) ≤
      factorialGasTailBase4Term r * (4 / 5 : ℚ) := by
  have hrpos : (0 : ℚ) < (r : ℚ) := by
    exact_mod_cast (by omega : 0 < r)
  have hfrac :
      (((r + 1 : Nat) : ℚ) / (r : ℚ)) ≤ (77 / 76 : ℚ) := by
    rw [div_le_iff₀ hrpos]
    have hrQ : (76 : ℚ) ≤ r := by exact_mod_cast hr
    norm_num
    nlinarith
  have hpow :
      (((r + 1 : Nat) : ℚ) / (r : ℚ))^4 ≤ (77 / 76 : ℚ)^4 :=
    pow_le_pow_left₀ (by positivity) hfrac 4
  have hratio_bound :
      (3 / 4 : ℚ) *
          ((((r + 1 : Nat) : ℚ) / (r : ℚ))^4) ≤ 4 / 5 := by
    calc
      (3 / 4 : ℚ) * ((((r + 1 : Nat) : ℚ) / (r : ℚ))^4)
          ≤ (3 / 4 : ℚ) * (77 / 76 : ℚ)^4 :=
            mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ = (((3 * 77^4 : Nat) : ℚ) / ((4 * 76^4 : Nat) : ℚ)) := by
            norm_num
      _ ≤ 4 / 5 := le_of_lt factorialGas_tail_base4_ratio
  have hsucc :
      factorialGasTailBase4Term (r + 1) =
        factorialGasTailBase4Term r *
          ((3 / 4 : ℚ) *
            ((((r + 1 : Nat) : ℚ) / (r : ℚ))^4)) := by
    unfold factorialGasTailBase4Term
    rw [pow_succ]
    field_simp [hrpos.ne']
    ring
  rw [hsucc]
  exact mul_le_mul_of_nonneg_left hratio_bound
    (factorialGasTailBase4Term_nonneg r)

private theorem factorialGasTailBase4WeightedTerm_succ_le
    (r : Nat) (hr : 76 ≤ r) :
    factorialGasTailBase4WeightedTerm (r + 1) ≤
      factorialGasTailBase4WeightedTerm r * (13 / 16 : ℚ) := by
  have hrpos : (0 : ℚ) < (r : ℚ) := by
    exact_mod_cast (by omega : 0 < r)
  have hfrac :
      (((r + 1 : Nat) : ℚ) / (r : ℚ)) ≤ (77 / 76 : ℚ) := by
    rw [div_le_iff₀ hrpos]
    have hrQ : (76 : ℚ) ≤ r := by exact_mod_cast hr
    norm_num
    nlinarith
  have hpow :
      (((r + 1 : Nat) : ℚ) / (r : ℚ))^5 ≤ (77 / 76 : ℚ)^5 :=
    pow_le_pow_left₀ (by positivity) hfrac 5
  have hratio_bound :
      (3 / 4 : ℚ) *
          ((((r + 1 : Nat) : ℚ) / (r : ℚ))^5) ≤ 13 / 16 := by
    calc
      (3 / 4 : ℚ) * ((((r + 1 : Nat) : ℚ) / (r : ℚ))^5)
          ≤ (3 / 4 : ℚ) * (77 / 76 : ℚ)^5 :=
            mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ = (((3 * 77^5 : Nat) : ℚ) / ((4 * 76^5 : Nat) : ℚ)) := by
            norm_num
      _ ≤ 13 / 16 := le_of_lt factorialGas_tail_base4_weighted_ratio
  have hsucc :
      factorialGasTailBase4WeightedTerm (r + 1) =
        factorialGasTailBase4WeightedTerm r *
          ((3 / 4 : ℚ) *
            ((((r + 1 : Nat) : ℚ) / (r : ℚ))^5)) := by
    unfold factorialGasTailBase4WeightedTerm
    rw [pow_succ]
    field_simp [hrpos.ne']
    ring
  rw [hsucc]
  exact mul_le_mul_of_nonneg_left hratio_bound
    (factorialGasTailBase4WeightedTerm_nonneg r)

private theorem factorialGasTailBase2Term_succ_le
    (r : Nat) (hr : 76 ≤ r) :
    factorialGasTailBase2Term (r + 1) ≤
      factorialGasTailBase2Term r * (1 / 2 : ℚ) := by
  have hrpos : (0 : ℚ) < (r : ℚ) := by
    exact_mod_cast (by omega : 0 < r)
  have hfrac :
      (((r + 1 : Nat) : ℚ) / (r : ℚ)) ≤ (77 / 76 : ℚ) := by
    rw [div_le_iff₀ hrpos]
    have hrQ : (76 : ℚ) ≤ r := by exact_mod_cast hr
    norm_num
    nlinarith
  have hpow :
      (((r + 1 : Nat) : ℚ) / (r : ℚ))^4 ≤ (77 / 76 : ℚ)^4 :=
    pow_le_pow_left₀ (by positivity) hfrac 4
  have hratio_bound :
      (3 / 8 : ℚ) *
          ((((r + 1 : Nat) : ℚ) / (r : ℚ))^4) ≤ 1 / 2 := by
    calc
      (3 / 8 : ℚ) * ((((r + 1 : Nat) : ℚ) / (r : ℚ))^4)
          ≤ (3 / 8 : ℚ) * (77 / 76 : ℚ)^4 :=
            mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ = (((3 * 77^4 : Nat) : ℚ) / ((8 * 76^4 : Nat) : ℚ)) := by
            norm_num
      _ ≤ 1 / 2 := le_of_lt factorialGas_tail_base2_ratio
  have hsucc :
      factorialGasTailBase2Term (r + 1) =
        factorialGasTailBase2Term r *
          ((3 / 8 : ℚ) *
            ((((r + 1 : Nat) : ℚ) / (r : ℚ))^4)) := by
    unfold factorialGasTailBase2Term
    rw [pow_succ]
    field_simp [hrpos.ne']
    ring
  rw [hsucc]
  exact mul_le_mul_of_nonneg_left hratio_bound
    (factorialGasTailBase2Term_nonneg r)

private theorem factorialGasTailBase2WeightedTerm_succ_le
    (r : Nat) (hr : 76 ≤ r) :
    factorialGasTailBase2WeightedTerm (r + 1) ≤
      factorialGasTailBase2WeightedTerm r * (1 / 2 : ℚ) := by
  have hrpos : (0 : ℚ) < (r : ℚ) := by
    exact_mod_cast (by omega : 0 < r)
  have hfrac :
      (((r + 1 : Nat) : ℚ) / (r : ℚ)) ≤ (77 / 76 : ℚ) := by
    rw [div_le_iff₀ hrpos]
    have hrQ : (76 : ℚ) ≤ r := by exact_mod_cast hr
    norm_num
    nlinarith
  have hpow :
      (((r + 1 : Nat) : ℚ) / (r : ℚ))^5 ≤ (77 / 76 : ℚ)^5 :=
    pow_le_pow_left₀ (by positivity) hfrac 5
  have hratio_bound :
      (3 / 8 : ℚ) *
          ((((r + 1 : Nat) : ℚ) / (r : ℚ))^5) ≤ 1 / 2 := by
    calc
      (3 / 8 : ℚ) * ((((r + 1 : Nat) : ℚ) / (r : ℚ))^5)
          ≤ (3 / 8 : ℚ) * (77 / 76 : ℚ)^5 :=
            mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ = (((3 * 77^5 : Nat) : ℚ) / ((8 * 76^5 : Nat) : ℚ)) := by
            norm_num
      _ ≤ 1 / 2 := le_of_lt factorialGas_tail_base2_weighted_ratio
  have hsucc :
      factorialGasTailBase2WeightedTerm (r + 1) =
        factorialGasTailBase2WeightedTerm r *
          ((3 / 8 : ℚ) *
            ((((r + 1 : Nat) : ℚ) / (r : ℚ))^5)) := by
    unfold factorialGasTailBase2WeightedTerm
    rw [pow_succ]
    field_simp [hrpos.ne']
    ring
  rw [hsucc]
  exact mul_le_mul_of_nonneg_left hratio_bound
    (factorialGasTailBase2WeightedTerm_nonneg r)

private theorem factorialGas_geom_chain_bound_from
    (F : Nat → ℚ) {q : ℚ} (hq0 : 0 ≤ q)
    {a K : Nat}
    (hstep : ∀ j, j + 1 < K → F (a + j + 1) ≤ F (a + j) * q) :
    ∀ j, j < K → F (a + j) ≤ F a * q^j := by
  intro j hj
  induction j with
  | zero =>
      simp
  | succ j ih =>
      calc
        F (a + (j + 1)) = F (a + j + 1) := by rw [Nat.add_assoc]
        _ ≤ F (a + j) * q := hstep j hj
        _ ≤ (F a * q^j) * q := by
            exact mul_le_mul_of_nonneg_right (ih (Nat.lt_of_succ_lt hj)) hq0
        _ = F a * q^(j + 1) := by
            rw [pow_succ]
            ring

private theorem factorialGas_geom_chain_sum_from_le
    (F : Nat → ℚ) {q : ℚ} (hq0 : 0 ≤ q)
    {a K : Nat}
    (hstep : ∀ j, j + 1 < K → F (a + j + 1) ≤ F (a + j) * q) :
    ∑ j ∈ Finset.range K, F (a + j)
      ≤ F a * ∑ j ∈ Finset.range K, q^j := by
  calc
    ∑ j ∈ Finset.range K, F (a + j)
        ≤ ∑ j ∈ Finset.range K, F a * q^j := by
          refine Finset.sum_le_sum fun j hj => ?_
          exact factorialGas_geom_chain_bound_from F hq0 hstep j
            (Finset.mem_range.mp hj)
    _ = F a * ∑ j ∈ Finset.range K, q^j := by
          rw [Finset.mul_sum]

private theorem factorialGasTailBase4_sum_le (p : Nat) :
    (∑ r ∈ Finset.Ico 76 (p + 1), factorialGasTailBase4Term r) ≤ 3 := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hfirst : factorialGasTailBase4Term 76 < 3 / 5 := by
    native_decide
  have hgeom :
      (∑ j ∈ Finset.range (p + 1 - 76), factorialGasTailBase4Term (76 + j))
        ≤ factorialGasTailBase4Term 76 *
            ∑ j ∈ Finset.range (p + 1 - 76), (4 / 5 : ℚ)^j := by
    refine factorialGas_geom_chain_sum_from_le
      (fun r => factorialGasTailBase4Term r)
      (by norm_num : (0 : ℚ) ≤ 4 / 5) ?_
    intro j hj
    exact factorialGasTailBase4Term_succ_le (76 + j) (by omega)
  calc
    (∑ j ∈ Finset.range (p + 1 - 76), factorialGasTailBase4Term (76 + j))
        ≤ factorialGasTailBase4Term 76 *
            ∑ j ∈ Finset.range (p + 1 - 76), (4 / 5 : ℚ)^j := hgeom
    _ ≤ (3 / 5 : ℚ) * (1 / (1 - (4 / 5 : ℚ))) := by
          exact mul_le_mul
            (le_of_lt hfirst)
            (Prop51.geom_sum_le_inv_one_sub (4 / 5 : ℚ)
              (by norm_num) (by norm_num) _)
            (by positivity)
            (by norm_num)
    _ = 3 := by norm_num

private theorem factorialGasTailBase4Weighted_sum_le (p : Nat) :
    (∑ r ∈ Finset.Ico 76 (p + 1), factorialGasTailBase4WeightedTerm r) ≤
      208 := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hfirst : factorialGasTailBase4WeightedTerm 76 < 39 := by
    native_decide
  have hgeom :
      (∑ j ∈ Finset.range (p + 1 - 76),
          factorialGasTailBase4WeightedTerm (76 + j))
        ≤ factorialGasTailBase4WeightedTerm 76 *
            ∑ j ∈ Finset.range (p + 1 - 76), (13 / 16 : ℚ)^j := by
    refine factorialGas_geom_chain_sum_from_le
      (fun r => factorialGasTailBase4WeightedTerm r)
      (by norm_num : (0 : ℚ) ≤ 13 / 16) ?_
    intro j hj
    exact factorialGasTailBase4WeightedTerm_succ_le (76 + j) (by omega)
  calc
    (∑ j ∈ Finset.range (p + 1 - 76),
        factorialGasTailBase4WeightedTerm (76 + j))
        ≤ factorialGasTailBase4WeightedTerm 76 *
            ∑ j ∈ Finset.range (p + 1 - 76), (13 / 16 : ℚ)^j := hgeom
    _ ≤ (39 : ℚ) * (1 / (1 - (13 / 16 : ℚ))) := by
          exact mul_le_mul
            (le_of_lt hfirst)
            (Prop51.geom_sum_le_inv_one_sub (13 / 16 : ℚ)
              (by norm_num) (by norm_num) _)
            (by positivity)
            (by norm_num)
    _ = 208 := by norm_num

private theorem factorialGasTailBase2_sum_le (p : Nat) :
    (∑ r ∈ Finset.Ico 76 (p + 1), factorialGasTailBase2Term r) ≤ 1 := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hfirst : factorialGasTailBase2Term 76 < 1 / 2 := by
    native_decide
  have hgeom :
      (∑ j ∈ Finset.range (p + 1 - 76), factorialGasTailBase2Term (76 + j))
        ≤ factorialGasTailBase2Term 76 *
            ∑ j ∈ Finset.range (p + 1 - 76), (1 / 2 : ℚ)^j := by
    refine factorialGas_geom_chain_sum_from_le
      (fun r => factorialGasTailBase2Term r)
      (by norm_num : (0 : ℚ) ≤ 1 / 2) ?_
    intro j hj
    exact factorialGasTailBase2Term_succ_le (76 + j) (by omega)
  calc
    (∑ j ∈ Finset.range (p + 1 - 76), factorialGasTailBase2Term (76 + j))
        ≤ factorialGasTailBase2Term 76 *
            ∑ j ∈ Finset.range (p + 1 - 76), (1 / 2 : ℚ)^j := hgeom
    _ ≤ (1 / 2 : ℚ) * (1 / (1 - (1 / 2 : ℚ))) := by
          exact mul_le_mul
            (le_of_lt hfirst)
            (Prop51.geom_sum_le_inv_one_sub (1 / 2 : ℚ)
              (by norm_num) (by norm_num) _)
            (by positivity)
            (by norm_num)
    _ = 1 := by norm_num

private theorem factorialGasTailBase2Weighted_sum_le (p : Nat) :
    (∑ r ∈ Finset.Ico 76 (p + 1), factorialGasTailBase2WeightedTerm r) ≤
      1 := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hfirst : factorialGasTailBase2WeightedTerm 76 < 1 / 2 := by
    native_decide
  have hgeom :
      (∑ j ∈ Finset.range (p + 1 - 76),
          factorialGasTailBase2WeightedTerm (76 + j))
        ≤ factorialGasTailBase2WeightedTerm 76 *
            ∑ j ∈ Finset.range (p + 1 - 76), (1 / 2 : ℚ)^j := by
    refine factorialGas_geom_chain_sum_from_le
      (fun r => factorialGasTailBase2WeightedTerm r)
      (by norm_num : (0 : ℚ) ≤ 1 / 2) ?_
    intro j hj
    exact factorialGasTailBase2WeightedTerm_succ_le (76 + j) (by omega)
  calc
    (∑ j ∈ Finset.range (p + 1 - 76),
        factorialGasTailBase2WeightedTerm (76 + j))
        ≤ factorialGasTailBase2WeightedTerm 76 *
            ∑ j ∈ Finset.range (p + 1 - 76), (1 / 2 : ℚ)^j := hgeom
    _ ≤ (1 / 2 : ℚ) * (1 / (1 - (1 / 2 : ℚ))) := by
          exact mul_le_mul
            (le_of_lt hfirst)
            (Prop51.geom_sum_le_inv_one_sub (1 / 2 : ℚ)
              (by norm_num) (by norm_num) _)
            (by positivity)
            (by norm_num)
    _ = 1 := by norm_num

private theorem factorialGasPrefix_sum_eq (base : Nat) (weighted : Bool) :
    (∑ r ∈ Finset.Ico (4 : Nat) 76, factorialGasPrefixTerm base r weighted) =
      factorialGasPrefix base weighted := by
  unfold factorialGasPrefix
  rw [Prop51.list_range_map_sum]
  rw [Finset.sum_Ico_eq_sum_range]
  norm_num
  refine Finset.sum_congr rfl fun i _hi => ?_
  rw [show 4 + i = i + 4 by omega]

private theorem factorialGasBase4_x2_sum_le (a : Nat) (ha : 150 ≤ a) :
    (∑ r ∈ Finset.Ico (4 : Nat) (printedTailP a + 1),
      (((r - 1).factorial : Nat) : ℚ) * (4 : ℚ)^r / (a : ℚ)^r)
      ≤ 1730 / (a : ℚ)^4 := by
  let F : Nat → ℚ := fun r =>
    (((r - 1).factorial : Nat) : ℚ) * (4 : ℚ)^r / (a : ℚ)^r
  let G : Nat → ℚ := fun r => factorialGasTailBase4Term r
  have ha_pos : (0 : ℚ) < (a : ℚ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 150) ha)
  have hp76 : 76 ≤ printedTailP a + 1 := by
    unfold printedTailP
    omega
  have hsplit := Finset.sum_Ico_consecutive F
    (by norm_num : 4 ≤ 76) hp76
  have hprefix :
      (∑ r ∈ Finset.Ico 4 76, F r) ≤
        factorialGasPrefix 4 false / (a : ℚ)^4 := by
    calc
      (∑ r ∈ Finset.Ico 4 76, F r)
          ≤ ∑ r ∈ Finset.Ico 4 76,
              factorialGasPrefixTerm 4 r false / (a : ℚ)^4 := by
            refine Finset.sum_le_sum fun r hr => ?_
            have hmem := Finset.mem_Ico.mp hr
            dsimp [F]
            exact factorialGasPrefix_scale_le
              (a := a) (base := 4) (r := r) ha hmem.1
      _ = factorialGasPrefix 4 false / (a : ℚ)^4 := by
            rw [← Finset.sum_div]
            rw [factorialGasPrefix_sum_eq]
  have htail :
      (∑ r ∈ Finset.Ico 76 (printedTailP a + 1), F r) ≤
        3 / (a : ℚ)^4 := by
    calc
      (∑ r ∈ Finset.Ico 76 (printedTailP a + 1), F r)
          ≤ ∑ r ∈ Finset.Ico 76 (printedTailP a + 1),
              G r / (a : ℚ)^4 := by
            refine Finset.sum_le_sum fun r hr => ?_
            have hmem := Finset.mem_Ico.mp hr
            have hr_le_p : r ≤ printedTailP a := by omega
            have hra : 2 * r ≤ a := by
              unfold printedTailP at hr_le_p
              omega
            dsimp [F, G]
            exact factorialGasBase4_tail_term_le
              (a := a) (r := r) (by omega : 4 ≤ r) hra
      _ = (∑ r ∈ Finset.Ico 76 (printedTailP a + 1), G r) /
            (a : ℚ)^4 := by
            rw [← Finset.sum_div]
      _ ≤ 3 / (a : ℚ)^4 :=
            div_le_div_of_nonneg_right
              (factorialGasTailBase4_sum_le (printedTailP a))
              (pow_nonneg ha_pos.le 4)
  change (∑ r ∈ Finset.Ico (4 : Nat) (printedTailP a + 1), F r)
    ≤ 1730 / (a : ℚ)^4
  rw [← hsplit]
  calc
    (∑ r ∈ Finset.Ico (4 : Nat) 76, F r) +
        ∑ r ∈ Finset.Ico (76 : Nat) (printedTailP a + 1), F r
        ≤ factorialGasPrefix 4 false / (a : ℚ)^4 + 3 / (a : ℚ)^4 :=
          add_le_add hprefix htail
    _ = (factorialGasPrefix 4 false + 3) / (a : ℚ)^4 := by ring
    _ ≤ 1730 / (a : ℚ)^4 :=
          div_le_div_of_nonneg_right
            (le_of_lt factorialGas_prefix_tail_base4)
            (pow_nonneg ha_pos.le 4)

private theorem factorialGasBase4_weighted_x2_sum_le
    (a : Nat) (ha : 150 ≤ a) :
    (∑ r ∈ Finset.Ico (4 : Nat) (printedTailP a + 1),
      (r : ℚ) *
        ((((r - 1).factorial : Nat) : ℚ) * (4 : ℚ)^r / (a : ℚ)^r))
      ≤ 7340 / (a : ℚ)^4 := by
  let F : Nat → ℚ := fun r =>
    (r : ℚ) *
      ((((r - 1).factorial : Nat) : ℚ) * (4 : ℚ)^r / (a : ℚ)^r)
  let G : Nat → ℚ := fun r => factorialGasTailBase4WeightedTerm r
  have ha_pos : (0 : ℚ) < (a : ℚ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 150) ha)
  have hp76 : 76 ≤ printedTailP a + 1 := by
    unfold printedTailP
    omega
  have hsplit := Finset.sum_Ico_consecutive F
    (by norm_num : 4 ≤ 76) hp76
  have hprefix :
      (∑ r ∈ Finset.Ico 4 76, F r) ≤
        factorialGasPrefix 4 true / (a : ℚ)^4 := by
    calc
      (∑ r ∈ Finset.Ico 4 76, F r)
          ≤ ∑ r ∈ Finset.Ico 4 76,
              factorialGasPrefixTerm 4 r true / (a : ℚ)^4 := by
            refine Finset.sum_le_sum fun r hr => ?_
            have hmem := Finset.mem_Ico.mp hr
            dsimp [F]
            exact factorialGasPrefix_weighted_scale_le
              (a := a) (base := 4) (r := r) ha hmem.1
      _ = factorialGasPrefix 4 true / (a : ℚ)^4 := by
            rw [← Finset.sum_div]
            rw [factorialGasPrefix_sum_eq]
  have htail :
      (∑ r ∈ Finset.Ico 76 (printedTailP a + 1), F r) ≤
        208 / (a : ℚ)^4 := by
    calc
      (∑ r ∈ Finset.Ico 76 (printedTailP a + 1), F r)
          ≤ ∑ r ∈ Finset.Ico 76 (printedTailP a + 1),
              G r / (a : ℚ)^4 := by
            refine Finset.sum_le_sum fun r hr => ?_
            have hmem := Finset.mem_Ico.mp hr
            have hr_le_p : r ≤ printedTailP a := by omega
            have hra : 2 * r ≤ a := by
              unfold printedTailP at hr_le_p
              omega
            dsimp [F, G]
            exact factorialGasBase4_weighted_tail_term_le
              (a := a) (r := r) (by omega : 4 ≤ r) hra
      _ = (∑ r ∈ Finset.Ico 76 (printedTailP a + 1), G r) /
            (a : ℚ)^4 := by
            rw [← Finset.sum_div]
      _ ≤ 208 / (a : ℚ)^4 :=
            div_le_div_of_nonneg_right
              (factorialGasTailBase4Weighted_sum_le (printedTailP a))
              (pow_nonneg ha_pos.le 4)
  change (∑ r ∈ Finset.Ico (4 : Nat) (printedTailP a + 1), F r)
    ≤ 7340 / (a : ℚ)^4
  rw [← hsplit]
  calc
    (∑ r ∈ Finset.Ico (4 : Nat) 76, F r) +
        ∑ r ∈ Finset.Ico (76 : Nat) (printedTailP a + 1), F r
        ≤ factorialGasPrefix 4 true / (a : ℚ)^4 +
            208 / (a : ℚ)^4 := add_le_add hprefix htail
    _ = (factorialGasPrefix 4 true + 208) / (a : ℚ)^4 := by ring
    _ ≤ 7340 / (a : ℚ)^4 :=
          div_le_div_of_nonneg_right
            (le_of_lt factorialGas_prefix_tail_base4_weighted)
            (pow_nonneg ha_pos.le 4)

private theorem factorialGasBase2_x2_sum_le (a : Nat) (ha : 150 ≤ a) :
    (∑ r ∈ Finset.Ico (4 : Nat) (printedTailP a + 1),
      (((r - 1).factorial : Nat) : ℚ) * (2 : ℚ)^r / (a : ℚ)^r)
      ≤ 103 / (a : ℚ)^4 := by
  let F : Nat → ℚ := fun r =>
    (((r - 1).factorial : Nat) : ℚ) * (2 : ℚ)^r / (a : ℚ)^r
  let G : Nat → ℚ := fun r => factorialGasTailBase2Term r
  have ha_pos : (0 : ℚ) < (a : ℚ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 150) ha)
  have hp76 : 76 ≤ printedTailP a + 1 := by
    unfold printedTailP
    omega
  have hsplit := Finset.sum_Ico_consecutive F
    (by norm_num : 4 ≤ 76) hp76
  have hprefix :
      (∑ r ∈ Finset.Ico 4 76, F r) ≤
        factorialGasPrefix 2 false / (a : ℚ)^4 := by
    calc
      (∑ r ∈ Finset.Ico 4 76, F r)
          ≤ ∑ r ∈ Finset.Ico 4 76,
              factorialGasPrefixTerm 2 r false / (a : ℚ)^4 := by
            refine Finset.sum_le_sum fun r hr => ?_
            have hmem := Finset.mem_Ico.mp hr
            dsimp [F]
            exact factorialGasPrefix_scale_le
              (a := a) (base := 2) (r := r) ha hmem.1
      _ = factorialGasPrefix 2 false / (a : ℚ)^4 := by
            rw [← Finset.sum_div]
            rw [factorialGasPrefix_sum_eq]
  have htail :
      (∑ r ∈ Finset.Ico 76 (printedTailP a + 1), F r) ≤
        1 / (a : ℚ)^4 := by
    calc
      (∑ r ∈ Finset.Ico 76 (printedTailP a + 1), F r)
          ≤ ∑ r ∈ Finset.Ico 76 (printedTailP a + 1),
              G r / (a : ℚ)^4 := by
            refine Finset.sum_le_sum fun r hr => ?_
            have hmem := Finset.mem_Ico.mp hr
            have hr_le_p : r ≤ printedTailP a := by omega
            have hra : 2 * r ≤ a := by
              unfold printedTailP at hr_le_p
              omega
            dsimp [F, G]
            exact factorialGasBase2_tail_term_le
              (a := a) (r := r) (by omega : 4 ≤ r) hra
      _ = (∑ r ∈ Finset.Ico 76 (printedTailP a + 1), G r) /
            (a : ℚ)^4 := by
            rw [← Finset.sum_div]
      _ ≤ 1 / (a : ℚ)^4 :=
            div_le_div_of_nonneg_right
              (factorialGasTailBase2_sum_le (printedTailP a))
              (pow_nonneg ha_pos.le 4)
  change (∑ r ∈ Finset.Ico (4 : Nat) (printedTailP a + 1), F r)
    ≤ 103 / (a : ℚ)^4
  rw [← hsplit]
  calc
    (∑ r ∈ Finset.Ico (4 : Nat) 76, F r) +
        ∑ r ∈ Finset.Ico (76 : Nat) (printedTailP a + 1), F r
        ≤ factorialGasPrefix 2 false / (a : ℚ)^4 + 1 / (a : ℚ)^4 :=
          add_le_add hprefix htail
    _ = (factorialGasPrefix 2 false + 1) / (a : ℚ)^4 := by ring
    _ ≤ 103 / (a : ℚ)^4 :=
          div_le_div_of_nonneg_right
            (le_of_lt factorialGas_prefix_tail_base2)
            (pow_nonneg ha_pos.le 4)

private theorem factorialGasBase2_weighted_x2_sum_le
    (a : Nat) (ha : 150 ≤ a) :
    (∑ r ∈ Finset.Ico (4 : Nat) (printedTailP a + 1),
      (r : ℚ) *
        ((((r - 1).factorial : Nat) : ℚ) * (2 : ℚ)^r / (a : ℚ)^r))
      ≤ 413 / (a : ℚ)^4 := by
  let F : Nat → ℚ := fun r =>
    (r : ℚ) *
      ((((r - 1).factorial : Nat) : ℚ) * (2 : ℚ)^r / (a : ℚ)^r)
  let G : Nat → ℚ := fun r => factorialGasTailBase2WeightedTerm r
  have ha_pos : (0 : ℚ) < (a : ℚ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 150) ha)
  have hp76 : 76 ≤ printedTailP a + 1 := by
    unfold printedTailP
    omega
  have hsplit := Finset.sum_Ico_consecutive F
    (by norm_num : 4 ≤ 76) hp76
  have hprefix :
      (∑ r ∈ Finset.Ico 4 76, F r) ≤
        factorialGasPrefix 2 true / (a : ℚ)^4 := by
    calc
      (∑ r ∈ Finset.Ico 4 76, F r)
          ≤ ∑ r ∈ Finset.Ico 4 76,
              factorialGasPrefixTerm 2 r true / (a : ℚ)^4 := by
            refine Finset.sum_le_sum fun r hr => ?_
            have hmem := Finset.mem_Ico.mp hr
            dsimp [F]
            exact factorialGasPrefix_weighted_scale_le
              (a := a) (base := 2) (r := r) ha hmem.1
      _ = factorialGasPrefix 2 true / (a : ℚ)^4 := by
            rw [← Finset.sum_div]
            rw [factorialGasPrefix_sum_eq]
  have htail :
      (∑ r ∈ Finset.Ico 76 (printedTailP a + 1), F r) ≤
        1 / (a : ℚ)^4 := by
    calc
      (∑ r ∈ Finset.Ico 76 (printedTailP a + 1), F r)
          ≤ ∑ r ∈ Finset.Ico 76 (printedTailP a + 1),
              G r / (a : ℚ)^4 := by
            refine Finset.sum_le_sum fun r hr => ?_
            have hmem := Finset.mem_Ico.mp hr
            have hr_le_p : r ≤ printedTailP a := by omega
            have hra : 2 * r ≤ a := by
              unfold printedTailP at hr_le_p
              omega
            dsimp [F, G]
            exact factorialGasBase2_weighted_tail_term_le
              (a := a) (r := r) (by omega : 4 ≤ r) hra
      _ = (∑ r ∈ Finset.Ico 76 (printedTailP a + 1), G r) /
            (a : ℚ)^4 := by
            rw [← Finset.sum_div]
      _ ≤ 1 / (a : ℚ)^4 :=
            div_le_div_of_nonneg_right
              (factorialGasTailBase2Weighted_sum_le (printedTailP a))
              (pow_nonneg ha_pos.le 4)
  change (∑ r ∈ Finset.Ico (4 : Nat) (printedTailP a + 1), F r)
    ≤ 413 / (a : ℚ)^4
  rw [← hsplit]
  calc
    (∑ r ∈ Finset.Ico (4 : Nat) 76, F r) +
        ∑ r ∈ Finset.Ico (76 : Nat) (printedTailP a + 1), F r
        ≤ factorialGasPrefix 2 true / (a : ℚ)^4 +
            1 / (a : ℚ)^4 := add_le_add hprefix htail
    _ = (factorialGasPrefix 2 true + 1) / (a : ℚ)^4 := by ring
    _ ≤ 413 / (a : ℚ)^4 :=
          div_le_div_of_nonneg_right
            (le_of_lt factorialGas_prefix_tail_base2_weighted)
            (pow_nonneg ha_pos.le 4)

/-! ## Taylor--Gamma truncation arithmetic -/

def truncationResidueRhs (a : Nat) : ℚ :=
  let p := a / 2
  let r0 := a - p - 1
  let S := a / 8
  920 / (2 : ℚ)^(r0 + 1) +
    2 * (5 / 6 : ℚ)^a +
    9 * (9 / 10 : ℚ)^(a - S) +
    920 * (a : ℚ) * (3 / 10 : ℚ)^(S + 1)

theorem truncationResidue_150 :
    truncationResidueRhs 150 < 1 / (150 : ℚ)^2 := by native_decide

theorem truncationResidue_151 :
    truncationResidueRhs 151 < 1 / (151 : ℚ)^2 := by native_decide

theorem truncationResidue_152 :
    truncationResidueRhs 152 < 1 / (152 : ℚ)^2 := by native_decide

theorem truncationResidue_153 :
    truncationResidueRhs 153 < 1 / (153 : ℚ)^2 := by native_decide

theorem truncationResidue_154 :
    truncationResidueRhs 154 < 1 / (154 : ℚ)^2 := by native_decide

theorem truncationResidue_155 :
    truncationResidueRhs 155 < 1 / (155 : ℚ)^2 := by native_decide

theorem truncationResidue_156 :
    truncationResidueRhs 156 < 1 / (156 : ℚ)^2 := by native_decide

theorem truncationResidue_157 :
    truncationResidueRhs 157 < 1 / (157 : ℚ)^2 := by native_decide

def truncationResidueScaled (a : Nat) : ℚ :=
  (a : ℚ)^2 * truncationResidueRhs a

private def truncationResidueScaledTerm1 (a : Nat) : ℚ :=
  (a : ℚ)^2 * (920 / (2 : ℚ)^(a - a/2))

private def truncationResidueScaledTerm2 (a : Nat) : ℚ :=
  (a : ℚ)^2 * (2 * (5/6 : ℚ)^a)

private def truncationResidueScaledTerm3 (a : Nat) : ℚ :=
  (a : ℚ)^2 * (9 * (9/10 : ℚ)^(a - a/8))

private def truncationResidueScaledTerm4 (a : Nat) : ℚ :=
  (a : ℚ)^2 * (920 * (a : ℚ) * (3/10 : ℚ)^(a/8 + 1))

private theorem truncationResidueScaled_eq_terms (a : Nat) (ha : 150 ≤ a) :
    truncationResidueScaled a =
      truncationResidueScaledTerm1 a +
      truncationResidueScaledTerm2 a +
      truncationResidueScaledTerm3 a +
      truncationResidueScaledTerm4 a := by
  unfold truncationResidueScaled truncationResidueRhs
    truncationResidueScaledTerm1 truncationResidueScaledTerm2
    truncationResidueScaledTerm3 truncationResidueScaledTerm4
  dsimp only
  have hr0 : a - a / 2 - 1 + 1 = a - a / 2 := by omega
  rw [hr0]
  ring_nf

private theorem truncationResidueScaledTerm1_step8 (a : Nat) (ha : 150 ≤ a) :
    truncationResidueScaledTerm1 (a + 8) ≤ truncationResidueScaledTerm1 a := by
  unfold truncationResidueScaledTerm1
  have hdiv : (a + 8) / 2 = a / 2 + 4 := by
    simpa [show 8 = 4 * 2 by norm_num] using
      Nat.add_mul_div_right a 4 (by decide : 0 < 2)
  have hexp : a + 8 - (a + 8) / 2 = (a - a/2) + 4 := by
    rw [hdiv]
    omega
  rw [hexp, pow_add]
  norm_num
  have hpoly : (((a + 8 : Nat) : ℚ)^2 / 16 ≤ (a : ℚ)^2) := by
    push_cast
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  have hnonneg : 0 ≤ 920 / (2 : ℚ) ^ (a - a / 2) := by positivity
  calc
    ((a : ℚ) + 8) ^ 2 * (920 / ((2 : ℚ) ^ (a - a / 2) * 16))
        = (((a + 8 : Nat) : ℚ)^2 / 16) *
            (920 / (2 : ℚ) ^ (a - a / 2)) := by
            push_cast
            ring
    _ ≤ (a : ℚ)^2 * (920 / (2 : ℚ) ^ (a - a / 2)) :=
      mul_le_mul_of_nonneg_right hpoly hnonneg

private theorem truncationResidueScaledTerm2_step8 (a : Nat) (ha : 150 ≤ a) :
    truncationResidueScaledTerm2 (a + 8) ≤ truncationResidueScaledTerm2 a := by
  unfold truncationResidueScaledTerm2
  rw [pow_add]
  norm_num
  have hpoly :
      (((a + 8 : Nat) : ℚ)^2 * (390625 / 839808 : ℚ) ≤ (a : ℚ)^2 * 2) := by
    push_cast
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  have hnonneg : 0 ≤ (5 / 6 : ℚ) ^ a := by positivity
  calc
    ((a : ℚ) + 8) ^ 2 * (2 * ((5 / 6 : ℚ) ^ a * (390625 / 1679616)))
        = (((a + 8 : Nat) : ℚ)^2 * (390625 / 839808 : ℚ)) *
            (5 / 6 : ℚ) ^ a := by
            push_cast
            ring
    _ ≤ ((a : ℚ)^2 * 2) * (5 / 6 : ℚ) ^ a :=
      mul_le_mul_of_nonneg_right hpoly hnonneg
    _ = (a : ℚ)^2 * (2 * (5 / 6 : ℚ) ^ a) := by ring

private theorem truncationResidueScaledTerm3_step8 (a : Nat) (ha : 150 ≤ a) :
    truncationResidueScaledTerm3 (a + 8) ≤ truncationResidueScaledTerm3 a := by
  unfold truncationResidueScaledTerm3
  have hdiv : (a + 8) / 8 = a / 8 + 1 := by
    simpa only [one_mul] using Nat.add_mul_div_right a 1 (by decide : 0 < 8)
  have hexp : a + 8 - (a + 8) / 8 = (a - a/8) + 7 := by
    rw [hdiv]
    omega
  rw [hexp, pow_add]
  norm_num
  have hpoly : (((a + 8 : Nat) : ℚ)^2 * ((9/10 : ℚ)^7) ≤ (a : ℚ)^2) := by
    norm_num
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  have hnonneg : 0 ≤ 9 * (9 / 10 : ℚ) ^ (a - a / 8) := by positivity
  calc
    ((a : ℚ) + 8) ^ 2 *
        (9 * ((9 / 10 : ℚ) ^ (a - a / 8) * (4782969 / 10000000)))
        = (((a + 8 : Nat) : ℚ)^2 * ((9/10 : ℚ)^7)) *
            (9 * (9 / 10 : ℚ) ^ (a - a / 8)) := by
            push_cast
            norm_num
            ring
    _ ≤ (a : ℚ)^2 * (9 * (9 / 10 : ℚ) ^ (a - a / 8)) :=
      mul_le_mul_of_nonneg_right hpoly hnonneg

private theorem truncationResidueScaledTerm4_step8 (a : Nat) (ha : 150 ≤ a) :
    truncationResidueScaledTerm4 (a + 8) ≤ truncationResidueScaledTerm4 a := by
  unfold truncationResidueScaledTerm4
  have hdiv : (a + 8) / 8 = a / 8 + 1 := by
    simpa only [one_mul] using Nat.add_mul_div_right a 1 (by decide : 0 < 8)
  rw [hdiv]
  rw [show a / 8 + 1 + 1 = a / 8 + 2 by omega, pow_succ]
  ring_nf
  have hpoly : (((a + 8 : Nat) : ℚ)^3 * (3/10 : ℚ) ≤ (a : ℚ)^3) := by
    push_cast
    ring_nf
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  have hnonneg : 0 ≤ 276 * (3 / 10 : ℚ) ^ (a / 8) := by positivity
  calc
    ((8 + a : Nat) : ℚ) ^ 3 * (3 / 10 : ℚ) ^ (a / 8) * (414 / 5)
        = (((a + 8 : Nat) : ℚ)^3 * (3 / 10 : ℚ)) *
            (276 * (3 / 10 : ℚ) ^ (a / 8)) := by
            push_cast
            ring
    _ ≤ (a : ℚ)^3 * (276 * (3 / 10 : ℚ) ^ (a / 8)) :=
      mul_le_mul_of_nonneg_right hpoly hnonneg
    _ = (a : ℚ)^3 * (3 / 10 : ℚ) ^ (a / 8) * 276 := by ring

/-- The scaled truncation residue decreases when `a` is increased by eight.

This is the formal version of the paper's parity/mod-eight monotonicity
argument for the four exponential tail terms. -/
theorem truncationResidueScaled_step8 (a : Nat) (ha : 150 ≤ a) :
    truncationResidueScaled (a + 8) ≤ truncationResidueScaled a := by
  rw [truncationResidueScaled_eq_terms (a + 8) (by omega),
    truncationResidueScaled_eq_terms a ha]
  nlinarith [truncationResidueScaledTerm1_step8 a ha,
    truncationResidueScaledTerm2_step8 a ha,
    truncationResidueScaledTerm3_step8 a ha,
    truncationResidueScaledTerm4_step8 a ha]

private theorem truncationResidueScaled_150 : truncationResidueScaled 150 < 1 := by
  unfold truncationResidueScaled
  norm_num
  nlinarith [truncationResidue_150]

private theorem truncationResidueScaled_151 : truncationResidueScaled 151 < 1 := by
  unfold truncationResidueScaled
  norm_num
  nlinarith [truncationResidue_151]

private theorem truncationResidueScaled_152 : truncationResidueScaled 152 < 1 := by
  unfold truncationResidueScaled
  norm_num
  nlinarith [truncationResidue_152]

private theorem truncationResidueScaled_153 : truncationResidueScaled 153 < 1 := by
  unfold truncationResidueScaled
  norm_num
  nlinarith [truncationResidue_153]

private theorem truncationResidueScaled_154 : truncationResidueScaled 154 < 1 := by
  unfold truncationResidueScaled
  norm_num
  nlinarith [truncationResidue_154]

private theorem truncationResidueScaled_155 : truncationResidueScaled 155 < 1 := by
  unfold truncationResidueScaled
  norm_num
  nlinarith [truncationResidue_155]

private theorem truncationResidueScaled_156 : truncationResidueScaled 156 < 1 := by
  unfold truncationResidueScaled
  norm_num
  nlinarith [truncationResidue_156]

private theorem truncationResidueScaled_157 : truncationResidueScaled 157 < 1 := by
  unfold truncationResidueScaled
  norm_num
  nlinarith [truncationResidue_157]

/-- Uniform truncation-residue bound for every `a >= 150`, assembled from the
eight endpoint checks and the mod-eight monotonicity step. -/
theorem truncationResidue_bound (a : Nat) (ha : 150 ≤ a) :
    truncationResidueRhs a < 1 / (a : ℚ)^2 := by
  have hscaled : truncationResidueScaled a < 1 := by
    refine Nat.strong_induction_on a ?_ ha
    intro a ih ha
    by_cases hle : a ≤ 157
    · interval_cases a <;> first
        | exact truncationResidueScaled_150
        | exact truncationResidueScaled_151
        | exact truncationResidueScaled_152
        | exact truncationResidueScaled_153
        | exact truncationResidueScaled_154
        | exact truncationResidueScaled_155
        | exact truncationResidueScaled_156
        | exact truncationResidueScaled_157
    · have hprev_ge : 150 ≤ a - 8 := by omega
      have hprev_lt : a - 8 < a := by omega
      have hprev : truncationResidueScaled (a - 8) < 1 :=
        ih (a - 8) hprev_lt hprev_ge
      have hstep :
          truncationResidueScaled ((a - 8) + 8) ≤ truncationResidueScaled (a - 8) :=
        truncationResidueScaled_step8 (a - 8) hprev_ge
      have hadd : (a - 8) + 8 = a := by omega
      rw [hadd] at hstep
      exact lt_of_le_of_lt hstep hprev
  unfold truncationResidueScaled at hscaled
  have ha_sq_pos : (0 : ℚ) < (a : ℚ)^2 := by
    have ha_pos : (0 : ℚ) < (a : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 150) ha)
    positivity
  rw [lt_div_iff₀ ha_sq_pos]
  nlinarith

/-! ## Main Gamma-margin interface -/

/-- The untruncated Gamma/integral lower estimate from the printed proof,
stated after moving the Taylor--Gamma truncation residue to the right-hand
side.  The theorem below combines this with `truncationResidue_bound` to recover
the finite main-sum lower bound consumed by the exact split assembly. -/
def PrintedTailGammaIntegralLowerBound : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      9 / (40 * ((a : ℚ) - 2)) ≤
        printedTailMainSum μ a + truncationResidueRhs a

/-- Convert the Gamma/integral lower estimate plus the formal truncation
residue bound into the finite main-sum lower bound used by the tail assembly. -/
theorem printedTailMainLowerBound_of_gammaIntegralLowerBound
    (hgamma : PrintedTailGammaIntegralLowerBound) :
    PrintedTailMainLowerBound := by
  intro a ha μ hμ
  have hg := hgamma a ha μ hμ
  have hres := truncationResidue_bound a ha
  nlinarith

/-! ## Uniform endpoint arithmetic for the `x₀` and `x₂` majorants -/

def printedTailMrat (a : Nat) : ℚ :=
  6 * (a : ℚ) - 6

def printedTailX0Bound1 (a : Nat) : ℚ :=
  (5 * printedTailMrat a) / (24 * ((a : ℚ) - 12)) +
    (88 * printedTailMrat a) / (125 * ((a : ℚ) - 12)^2)

def printedTailX0Bound2 (a : Nat) : ℚ :=
  (5 * printedTailMrat a) / (24 * ((a : ℚ) - 12)) +
    (36 * printedTailMrat a) / (25 * ((a : ℚ) - 12)^2)

def printedTailX0Bound3 (a : Nat) : ℚ :=
  printedTailMrat a / (6 * ((a : ℚ) - 12)) +
    (11 * printedTailMrat a) / (100 * ((a : ℚ) - 12)^2)

def printedTailX0Bound4 (a : Nat) : ℚ :=
  printedTailMrat a / (6 * ((a : ℚ) - 12)) +
    (72 * printedTailMrat a) / (325 * ((a : ℚ) - 12)^2)

theorem printedTailX0Bound1_lt (a : Nat) (ha : 150 ≤ a) :
    printedTailX0Bound1 a < 7 / 5 := by
  unfold printedTailX0Bound1 printedTailMrat
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hn_pos : (0 : ℚ) < (a : ℚ) - 12 := by nlinarith
  field_simp [hn_pos.ne']
  nlinarith

theorem printedTailX0Bound2_lt (a : Nat) (ha : 150 ≤ a) :
    printedTailX0Bound2 a < 3 / 2 := by
  unfold printedTailX0Bound2 printedTailMrat
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hn_pos : (0 : ℚ) < (a : ℚ) - 12 := by nlinarith
  field_simp [hn_pos.ne']
  nlinarith

theorem printedTailX0Bound3_lt (a : Nat) (ha : 150 ≤ a) :
    printedTailX0Bound3 a < 11 / 10 := by
  unfold printedTailX0Bound3 printedTailMrat
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hn_pos : (0 : ℚ) < (a : ℚ) - 12 := by nlinarith
  field_simp [hn_pos.ne']
  nlinarith

theorem printedTailX0Bound4_lt (a : Nat) (ha : 150 ≤ a) :
    printedTailX0Bound4 a < 11 / 10 := by
  unfold printedTailX0Bound4 printedTailMrat
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hn_pos : (0 : ℚ) < (a : ℚ) - 12 := by nlinarith
  field_simp [hn_pos.ne']
  nlinarith

/-! ## Low-polynomial point bounds at `x₀`

The printed proof bounds `L(x₀)`, `x₀L'(x₀)`, `J(x₀)`, and `x₀J'(x₀)`.
The constants below are slightly coarser than the displayed rational
`printedTailX0Bound*` constants, but they still imply the same endpoint
thresholds used by the `\widehat W` moment argument.
-/

def printedTailLPointSum (μ : List Nat) (a : Nat) (x : ℚ) : ℚ :=
  ∑ r ∈ Finset.range (printedTailP a + 1), hCoeff μ r * x^r

def printedTailLDerivPointSum (μ : List Nat) (a : Nat) (x : ℚ) : ℚ :=
  ∑ r ∈ Finset.range (printedTailP a + 1),
    (r : ℚ) * hCoeff μ r * x^r

def printedTailJPointSum (μ : List Nat) (a : Nat) (x : ℚ) : ℚ :=
  ∑ r ∈ Finset.range (printedTailP a + 1), kCoeff μ r * x^r

def printedTailJDerivPointSum (μ : List Nat) (a : Nat) (x : ℚ) : ℚ :=
  ∑ r ∈ Finset.range (printedTailP a + 1),
    (r : ℚ) * kCoeff μ r * x^r

private theorem factorial_pred_le_pow_of_le (p : Nat) :
    ∀ r : Nat, 2 ≤ r → r ≤ p → (r - 1).factorial ≤ p^(r - 2)
  | 0, hr, _ => by omega
  | 1, hr, _ => by omega
  | 2, _hr, _hrp => by simp
  | r + 3, _hr, hrp => by
      have ih := factorial_pred_le_pow_of_le p (r + 2) (by omega) (by omega)
      rw [show r + 3 - 1 = r + 2 by omega,
        show r + 3 - 2 = r + 1 by omega, Nat.factorial_succ,
        pow_succ']
      exact Nat.mul_le_mul (by omega : r + 2 ≤ p) ih

private theorem factorial_le_two_mul_pow_of_le (p : Nat) :
    ∀ r : Nat, 2 ≤ r → r ≤ p → r.factorial ≤ 2 * p^(r - 2)
  | 0, hr, _ => by omega
  | 1, hr, _ => by omega
  | 2, _hr, _hrp => by simp
  | r + 3, _hr, hrp => by
      have ih := factorial_le_two_mul_pow_of_le p (r + 2) (by omega) (by omega)
      rw [show r + 3 - 2 = r + 1 by omega, Nat.factorial_succ,
        pow_succ']
      calc
        (r + 3) * (r + 2).factorial
            ≤ p * (2 * p^r) := Nat.mul_le_mul (by omega : r + 3 ≤ p) ih
        _ = 2 * (p * p^r) := by ring

private theorem printedTailP_div_x0Den_le_three_fifths
    (a : Nat) (ha : 150 ≤ a) :
    ((printedTailP a : ℚ) / ((a : ℚ) - 12)) ≤ 3 / 5 := by
  unfold printedTailP
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hden : (0 : ℚ) < (a : ℚ) - 12 := by nlinarith
  have hdiv_nat : a / 2 * 2 ≤ a := Nat.div_mul_le_self a 2
  have hdiv : ((a / 2 : Nat) : ℚ) * 2 ≤ (a : ℚ) := by exact_mod_cast hdiv_nat
  rw [div_le_iff₀ hden]
  nlinarith

private theorem printedTailP_div_two_x0Den_le_three_tenths
    (a : Nat) (ha : 150 ≤ a) :
    ((printedTailP a : ℚ) / (2 * ((a : ℚ) - 12))) ≤ 3 / 10 := by
  have h := printedTailP_div_x0Den_le_three_fifths a ha
  have hden : (0 : ℚ) < (a : ℚ) - 12 := by
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  calc
    ((printedTailP a : ℚ) / (2 * ((a : ℚ) - 12)))
        = (1 / 2 : ℚ) * ((printedTailP a : ℚ) / ((a : ℚ) - 12)) := by
          field_simp [hden.ne']
    _ ≤ (1 / 2 : ℚ) * (3 / 5) :=
          mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 3 / 10 := by norm_num

private theorem factorial_pred_x0_tail_term_le
    {a r : Nat} (ha : 150 ≤ a) (hr2 : 2 ≤ r)
    (hrp : r ≤ printedTailP a) :
    (((r - 1).factorial : Nat) : ℚ) / (((a : ℚ) - 12)^r)
      ≤ (1 / ((a : ℚ) - 12)^2) * (3 / 5 : ℚ)^(r - 2) := by
  let A : ℚ := (a : ℚ) - 12
  have hApos : 0 < A := by
    dsimp [A]
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  have hfacNat :=
    factorial_pred_le_pow_of_le (printedTailP a) r hr2 hrp
  have hfac :
      (((r - 1).factorial : Nat) : ℚ) ≤
        ((printedTailP a : Nat) : ℚ)^(r - 2) := by
    exact_mod_cast hfacNat
  have hpA := printedTailP_div_x0Den_le_three_fifths a ha
  have hpA_nonneg : 0 ≤ ((printedTailP a : ℚ) / A) := by
    positivity
  calc
    (((r - 1).factorial : Nat) : ℚ) / A^r
        ≤ ((printedTailP a : ℚ)^(r - 2)) / A^r :=
          div_le_div_of_nonneg_right hfac (pow_nonneg hApos.le r)
    _ = (1 / A^2) * (((printedTailP a : ℚ) / A)^(r - 2)) := by
          rw [show r = (r - 2) + 2 by omega, pow_add, div_pow]
          field_simp [hApos.ne', pow_ne_zero (r - 2) hApos.ne']
          rw [show r - 2 + 2 - 2 = r - 2 by omega]
    _ ≤ (1 / A^2) * (3 / 5 : ℚ)^(r - 2) :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hpA_nonneg hpA (r - 2)) (by positivity)

private theorem factorial_x0_tail_term_le
    {a r : Nat} (ha : 150 ≤ a) (hr2 : 2 ≤ r)
    (hrp : r ≤ printedTailP a) :
    ((r.factorial : Nat) : ℚ) / (((a : ℚ) - 12)^r)
      ≤ (2 / ((a : ℚ) - 12)^2) * (3 / 5 : ℚ)^(r - 2) := by
  let A : ℚ := (a : ℚ) - 12
  have hApos : 0 < A := by
    dsimp [A]
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  have hfacNat :=
    factorial_le_two_mul_pow_of_le (printedTailP a) r hr2 hrp
  have hfac :
      ((r.factorial : Nat) : ℚ) ≤
        2 * ((printedTailP a : Nat) : ℚ)^(r - 2) := by
    exact_mod_cast hfacNat
  have hpA := printedTailP_div_x0Den_le_three_fifths a ha
  have hpA_nonneg : 0 ≤ ((printedTailP a : ℚ) / A) := by
    positivity
  calc
    ((r.factorial : Nat) : ℚ) / A^r
        ≤ (2 * (printedTailP a : ℚ)^(r - 2)) / A^r :=
          div_le_div_of_nonneg_right hfac (pow_nonneg hApos.le r)
    _ = (2 / A^2) * (((printedTailP a : ℚ) / A)^(r - 2)) := by
          rw [show r = (r - 2) + 2 by omega, pow_add, div_pow]
          field_simp [hApos.ne', pow_ne_zero (r - 2) hApos.ne']
          rw [show r - 2 + 2 - 2 = r - 2 by omega]
    _ ≤ (2 / A^2) * (3 / 5 : ℚ)^(r - 2) :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hpA_nonneg hpA (r - 2)) (by positivity)

private theorem factorial_pred_x0_halved_tail_term_le
    {a r : Nat} (ha : 150 ≤ a) (hr2 : 2 ≤ r)
    (hrp : r ≤ printedTailP a) :
    (((r - 1).factorial : Nat) : ℚ) /
        ((2 : ℚ)^r * ((a : ℚ) - 12)^r)
      ≤ (1 / (4 * ((a : ℚ) - 12)^2)) *
          (3 / 10 : ℚ)^(r - 2) := by
  let A : ℚ := (a : ℚ) - 12
  have hApos : 0 < A := by
    dsimp [A]
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  have hbase := factorial_pred_x0_tail_term_le
    (a := a) (r := r) ha hr2 hrp
  have hscale : 0 ≤ (1 / (2 : ℚ)^r) := by positivity
  calc
    (((r - 1).factorial : Nat) : ℚ) / ((2 : ℚ)^r * A^r)
        = (1 / (2 : ℚ)^r) *
            ((((r - 1).factorial : Nat) : ℚ) / A^r) := by
          field_simp [pow_ne_zero r (by norm_num : (2 : ℚ) ≠ 0)]
    _ ≤ (1 / (2 : ℚ)^r) *
          ((1 / A^2) * (3 / 5 : ℚ)^(r - 2)) :=
          mul_le_mul_of_nonneg_left hbase hscale
    _ = (1 / (4 * A^2)) * (3 / 10 : ℚ)^(r - 2) := by
          have hpow :
              (3 / 5 : ℚ)^(r - 2) =
                (2 : ℚ)^(r - 2) * (3 / 10 : ℚ)^(r - 2) := by
            rw [← mul_pow]
            norm_num
          rw [show r = (r - 2) + 2 by omega, pow_add]
          field_simp [hApos.ne', pow_ne_zero (r - 2)
            (by norm_num : (2 : ℚ) ≠ 0)]
          rw [show r - 2 + 2 - 2 = r - 2 by omega, hpow]
          norm_num
          ring

private theorem factorial_x0_halved_tail_term_le
    {a r : Nat} (ha : 150 ≤ a) (hr2 : 2 ≤ r)
    (hrp : r ≤ printedTailP a) :
    ((r.factorial : Nat) : ℚ) /
        ((2 : ℚ)^r * ((a : ℚ) - 12)^r)
      ≤ (1 / (2 * ((a : ℚ) - 12)^2)) *
          (3 / 10 : ℚ)^(r - 2) := by
  let A : ℚ := (a : ℚ) - 12
  have hApos : 0 < A := by
    dsimp [A]
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  have hbase := factorial_x0_tail_term_le
    (a := a) (r := r) ha hr2 hrp
  have hscale : 0 ≤ (1 / (2 : ℚ)^r) := by positivity
  calc
    ((r.factorial : Nat) : ℚ) / ((2 : ℚ)^r * A^r)
        = (1 / (2 : ℚ)^r) * (((r.factorial : Nat) : ℚ) / A^r) := by
          field_simp [pow_ne_zero r (by norm_num : (2 : ℚ) ≠ 0)]
    _ ≤ (1 / (2 : ℚ)^r) *
          ((2 / A^2) * (3 / 5 : ℚ)^(r - 2)) :=
          mul_le_mul_of_nonneg_left hbase hscale
    _ = (1 / (2 * A^2)) * (3 / 10 : ℚ)^(r - 2) := by
          have hpow :
              (3 / 5 : ℚ)^(r - 2) =
                (2 : ℚ)^(r - 2) * (3 / 10 : ℚ)^(r - 2) := by
            rw [← mul_pow]
            norm_num
          rw [show r = (r - 2) + 2 by omega, pow_add]
          field_simp [hApos.ne', pow_ne_zero (r - 2)
            (by norm_num : (2 : ℚ) ≠ 0)]
          rw [show r - 2 + 2 - 2 = r - 2 by omega, hpow]

private theorem factorial_pred_x0_tail_sum_le
    (a : Nat) (ha : 150 ≤ a) :
    (∑ r ∈ Finset.Ico 2 (printedTailP a + 1),
      (((r - 1).factorial : Nat) : ℚ) / (((a : ℚ) - 12)^r))
      ≤ (5 / (2 * ((a : ℚ) - 12)^2) : ℚ) := by
  let A : ℚ := (a : ℚ) - 12
  have hApos : 0 < A := by
    dsimp [A]
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  calc
    (∑ r ∈ Finset.Ico 2 (printedTailP a + 1),
      (((r - 1).factorial : Nat) : ℚ) / A^r)
        ≤ ∑ r ∈ Finset.Ico 2 (printedTailP a + 1),
            (1 / A^2) * (3 / 5 : ℚ)^(r - 2) := by
          refine Finset.sum_le_sum fun r hr => ?_
          have hmem := Finset.mem_Ico.mp hr
          exact factorial_pred_x0_tail_term_le (a := a) (r := r)
            ha hmem.1 (by omega)
    _ = (1 / A^2) *
          ∑ j ∈ Finset.range (printedTailP a + 1 - 2),
            (3 / 5 : ℚ)^j := by
          rw [Finset.sum_Ico_eq_sum_range]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j hj => ?_
          simp
    _ ≤ (1 / A^2) * (1 / (1 - (3 / 5 : ℚ))) :=
          mul_le_mul_of_nonneg_left
            (Prop51.geom_sum_le_inv_one_sub (3 / 5 : ℚ)
              (by norm_num) (by norm_num) _) (by positivity)
    _ = 5 / (2 * A^2) := by ring_nf

private theorem factorial_x0_tail_sum_le
    (a : Nat) (ha : 150 ≤ a) :
    (∑ r ∈ Finset.Ico 2 (printedTailP a + 1),
      ((r.factorial : Nat) : ℚ) / (((a : ℚ) - 12)^r))
      ≤ (5 / ((a : ℚ) - 12)^2 : ℚ) := by
  let A : ℚ := (a : ℚ) - 12
  have hApos : 0 < A := by
    dsimp [A]
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  calc
    (∑ r ∈ Finset.Ico 2 (printedTailP a + 1),
      ((r.factorial : Nat) : ℚ) / A^r)
        ≤ ∑ r ∈ Finset.Ico 2 (printedTailP a + 1),
            (2 / A^2) * (3 / 5 : ℚ)^(r - 2) := by
          refine Finset.sum_le_sum fun r hr => ?_
          have hmem := Finset.mem_Ico.mp hr
          exact factorial_x0_tail_term_le (a := a) (r := r)
            ha hmem.1 (by omega)
    _ = (2 / A^2) *
          ∑ j ∈ Finset.range (printedTailP a + 1 - 2),
            (3 / 5 : ℚ)^j := by
          rw [Finset.sum_Ico_eq_sum_range]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j hj => ?_
          simp
    _ ≤ (2 / A^2) * (1 / (1 - (3 / 5 : ℚ))) :=
          mul_le_mul_of_nonneg_left
            (Prop51.geom_sum_le_inv_one_sub (3 / 5 : ℚ)
              (by norm_num) (by norm_num) _) (by positivity)
    _ = 5 / A^2 := by ring_nf

private theorem factorial_pred_x0_halved_tail_sum_le
    (a : Nat) (ha : 150 ≤ a) :
    (∑ r ∈ Finset.Ico 2 (printedTailP a + 1),
      (((r - 1).factorial : Nat) : ℚ) /
        ((2 : ℚ)^r * ((a : ℚ) - 12)^r))
      ≤ (5 / (14 * ((a : ℚ) - 12)^2) : ℚ) := by
  let A : ℚ := (a : ℚ) - 12
  have hApos : 0 < A := by
    dsimp [A]
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  calc
    (∑ r ∈ Finset.Ico 2 (printedTailP a + 1),
      (((r - 1).factorial : Nat) : ℚ) / ((2 : ℚ)^r * A^r))
        ≤ ∑ r ∈ Finset.Ico 2 (printedTailP a + 1),
            (1 / (4 * A^2)) * (3 / 10 : ℚ)^(r - 2) := by
          refine Finset.sum_le_sum fun r hr => ?_
          have hmem := Finset.mem_Ico.mp hr
          exact factorial_pred_x0_halved_tail_term_le
            (a := a) (r := r) ha hmem.1 (by omega)
    _ = (1 / (4 * A^2)) *
          ∑ j ∈ Finset.range (printedTailP a + 1 - 2),
            (3 / 10 : ℚ)^j := by
          rw [Finset.sum_Ico_eq_sum_range]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j hj => ?_
          simp
    _ ≤ (1 / (4 * A^2)) * (1 / (1 - (3 / 10 : ℚ))) :=
          mul_le_mul_of_nonneg_left
            (Prop51.geom_sum_le_inv_one_sub (3 / 10 : ℚ)
              (by norm_num) (by norm_num) _) (by positivity)
    _ = 5 / (14 * A^2) := by ring_nf

private theorem factorial_x0_halved_tail_sum_le
    (a : Nat) (ha : 150 ≤ a) :
    (∑ r ∈ Finset.Ico 2 (printedTailP a + 1),
      ((r.factorial : Nat) : ℚ) /
        ((2 : ℚ)^r * ((a : ℚ) - 12)^r))
      ≤ (5 / (7 * ((a : ℚ) - 12)^2) : ℚ) := by
  let A : ℚ := (a : ℚ) - 12
  have hApos : 0 < A := by
    dsimp [A]
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  calc
    (∑ r ∈ Finset.Ico 2 (printedTailP a + 1),
      ((r.factorial : Nat) : ℚ) / ((2 : ℚ)^r * A^r))
        ≤ ∑ r ∈ Finset.Ico 2 (printedTailP a + 1),
            (1 / (2 * A^2)) * (3 / 10 : ℚ)^(r - 2) := by
          refine Finset.sum_le_sum fun r hr => ?_
          have hmem := Finset.mem_Ico.mp hr
          exact factorial_x0_halved_tail_term_le
            (a := a) (r := r) ha hmem.1 (by omega)
    _ = (1 / (2 * A^2)) *
          ∑ j ∈ Finset.range (printedTailP a + 1 - 2),
            (3 / 10 : ℚ)^j := by
          rw [Finset.sum_Ico_eq_sum_range]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j hj => ?_
          simp
    _ ≤ (1 / (2 * A^2)) * (1 / (1 - (3 / 10 : ℚ))) :=
          mul_le_mul_of_nonneg_left
            (Prop51.geom_sum_le_inv_one_sub (3 / 10 : ℚ)
              (by norm_num) (by norm_num) _) (by positivity)
    _ = 5 / (7 * A^2) := by ring_nf

private theorem sum_range_eq_zero_one_add_Ico
    (F : Nat → ℚ) {p : Nat} (hp : 1 ≤ p) :
    ∑ r ∈ Finset.range (p + 1), F r =
      F 0 + F 1 + ∑ r ∈ Finset.Ico 2 (p + 1), F r := by
  have hsplit := (Finset.sum_range_add_sum_Ico F (by omega : 2 ≤ p + 1)).symm
  rw [hsplit]
  norm_num [Finset.sum_range_succ]

private theorem sum_Ico_two_three_add_Ico
    (F : Nat → ℚ) {p : Nat} (hp : 3 ≤ p) :
    ∑ r ∈ Finset.Ico 2 (p + 1), F r =
      F 2 + F 3 + ∑ r ∈ Finset.Ico 4 (p + 1), F r := by
  have hsplit := Finset.sum_Ico_consecutive F
    (by norm_num : 2 ≤ 4) (by omega : 4 ≤ p + 1)
  rw [← hsplit]
  have hsmall : (∑ r ∈ Finset.Ico 2 4, F r) = F 2 + F 3 := by
    have hIco : Finset.Ico (2 : Nat) 4 = ({2, 3} : Finset Nat) := by
      decide
    rw [hIco]
    simp
  rw [hsmall]

private theorem hCoeff_x0_tail_term_le {a r : Nat} {μ : List Nat}
    (ha : 150 ≤ a) (hμ : Prop51.IsPartitionOf μ (M a))
    (hr : 2 ≤ r) :
    hCoeff μ r * (printedTailX0 a)^r
      ≤ (8 * (M a : ℚ) / 25) *
          ((((r - 1).factorial : Nat) : ℚ) / (((a : ℚ) - 12)^r)) := by
  let A : ℚ := (a : ℚ) - 12
  have hApos : 0 < A := by
    dsimp [A]
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  have hMnonneg : 0 ≤ (M a : ℚ) := by positivity
  have hx0_nonneg : 0 ≤ printedTailX0 a := by
    unfold printedTailX0
    positivity
  have hcoeff := hCoeff_le_M_two_sub_twopow_c_of_partition
    (a := a) (μ := μ) hμ r
  have hfactor_nonneg :
      0 ≤ (M a : ℚ) * (2 - 1 / (2 : ℚ)^r) := by
    have hpow_ge_one : (1 : ℚ) ≤ (2 : ℚ)^r :=
      one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 2)
    have hinv_le_one : 1 / (2 : ℚ)^r ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 1) hpow_ge_one
    nlinarith
  have hfactor_le :
      (M a : ℚ) * (2 - 1 / (2 : ℚ)^r) ≤ (M a : ℚ) * 2 := by
    have hinv_nonneg : 0 ≤ 1 / (2 : ℚ)^r := by positivity
    nlinarith
  have hcub := Prop51.c_ub r (by omega : 1 ≤ r)
  have hc_nonneg := Prop51.c_nonneg r
  have hright_nonneg :
      0 ≤ (4 / 25 : ℚ) *
        ((6 : ℚ)^r * (((r - 1).factorial : Nat) : ℚ)) := by
    positivity
  have hprod :
      ((M a : ℚ) * (2 - 1 / (2 : ℚ)^r)) * Prop51.c r
        ≤ ((M a : ℚ) * 2) *
            ((4 / 25 : ℚ) *
              ((6 : ℚ)^r * (((r - 1).factorial : Nat) : ℚ))) :=
    mul_le_mul hfactor_le hcub hc_nonneg
      (mul_nonneg hMnonneg (by norm_num))
  calc
    hCoeff μ r * (printedTailX0 a)^r
        ≤ (((M a : ℚ) * (2 - 1 / (2 : ℚ)^r)) * Prop51.c r) *
            (printedTailX0 a)^r :=
          mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hx0_nonneg r)
    _ ≤ (((M a : ℚ) * 2) *
            ((4 / 25 : ℚ) *
              ((6 : ℚ)^r * (((r - 1).factorial : Nat) : ℚ)))) *
            (printedTailX0 a)^r :=
          mul_le_mul_of_nonneg_right hprod (pow_nonneg hx0_nonneg r)
    _ = (8 * (M a : ℚ) / 25) *
          ((((r - 1).factorial : Nat) : ℚ) / A^r) := by
          change (((M a : ℚ) * 2) *
              ((4 / 25 : ℚ) *
                ((6 : ℚ)^r * (((r - 1).factorial : Nat) : ℚ)))) *
              (1 / (6 * A))^r =
            (8 * (M a : ℚ) / 25) *
              ((((r - 1).factorial : Nat) : ℚ) / A^r)
          dsimp [A]
          rw [one_div_pow, mul_pow]
          field_simp [hApos.ne', pow_ne_zero r hApos.ne',
            pow_ne_zero r (by norm_num : (6 : ℚ) ≠ 0)]
          ring_nf

private theorem kCoeff_x0_tail_term_le {a r : Nat} {μ : List Nat}
    (ha : 150 ≤ a) (hμ : Prop51.IsPartitionOf μ (M a))
    (hr : 2 ≤ r) :
    kCoeff μ r * (printedTailX0 a)^r
      ≤ (8 * (M a : ℚ) / 25) *
          ((((r - 1).factorial : Nat) : ℚ) /
            ((2 : ℚ)^r * ((a : ℚ) - 12)^r)) := by
  let A : ℚ := (a : ℚ) - 12
  rcases r with _ | r'
  · omega
  rcases r' with _ | n
  · omega
  have hApos : 0 < A := by
    dsimp [A]
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  have hx0_nonneg : 0 ≤ printedTailX0 a := by
    unfold printedTailX0
    positivity
  have hmw := markedWeight_le_M_div_two_pow_of_partition
    (a := a) (μ := μ) hμ (n + 2)
  have hmw_nonneg := markedWeight_nonneg_of_coeffs μ (n + 2)
  have hpref_nonneg :
      0 ≤ 12 * ((n : ℚ) + 1) * Prop51.c (n + 1) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (by positivity))
      (Prop51.c_nonneg (n + 1))
  have hcub := Prop51.c_ub (n + 1) (by omega : 1 ≤ n + 1)
  have hright_nonneg :
      0 ≤ (4 / 25 : ℚ) *
        ((6 : ℚ)^(n + 1) * (((n + 1 - 1).factorial : Nat) : ℚ)) := by
    positivity
  have hpref :
      12 * ((n : ℚ) + 1) * Prop51.c (n + 1)
        ≤ 12 * ((n : ℚ) + 1) *
            ((4 / 25 : ℚ) *
              ((6 : ℚ)^(n + 1) *
                (((n + 1 - 1).factorial : Nat) : ℚ))) := by
    exact mul_le_mul_of_nonneg_left hcub
      (mul_nonneg (by norm_num) (by positivity))
  have hcoeff :
      kCoeff μ (n + 2)
        ≤ (12 * ((n : ℚ) + 1) * Prop51.c (n + 1)) *
            ((M a : ℚ) / (2 : ℚ)^(n + 2)) := by
    simpa [kCoeff, Nat.cast_add, Nat.cast_one] using
      mul_le_mul_of_nonneg_left hmw hpref_nonneg
  have hcoeff' :
      kCoeff μ (n + 2)
        ≤ (12 * ((n : ℚ) + 1) *
            ((4 / 25 : ℚ) *
              ((6 : ℚ)^(n + 1) *
                (((n + 1 - 1).factorial : Nat) : ℚ)))) *
            ((M a : ℚ) / (2 : ℚ)^(n + 2)) := by
    exact hcoeff.trans
      (mul_le_mul_of_nonneg_right hpref
        (div_nonneg (by positivity) (pow_nonneg (by norm_num) _)))
  calc
    kCoeff μ (n + 2) * (printedTailX0 a)^(n + 2)
        ≤ ((12 * ((n : ℚ) + 1) *
            ((4 / 25 : ℚ) *
              ((6 : ℚ)^(n + 1) *
                (((n + 1 - 1).factorial : Nat) : ℚ)))) *
            ((M a : ℚ) / (2 : ℚ)^(n + 2))) *
            (printedTailX0 a)^(n + 2) :=
          mul_le_mul_of_nonneg_right hcoeff'
            (pow_nonneg hx0_nonneg (n + 2))
    _ = (8 * (M a : ℚ) / 25) *
          ((((n + 2 - 1).factorial : Nat) : ℚ) /
            ((2 : ℚ)^(n + 2) * A^(n + 2))) := by
          rw [show n + 1 - 1 = n by omega,
            show n + 2 - 1 = n + 1 by omega, Nat.factorial_succ]
          change ((12 * ((n : ℚ) + 1) *
              ((4 / 25 : ℚ) *
                ((6 : ℚ)^(n + 1) * ((n.factorial : Nat) : ℚ)))) *
              ((M a : ℚ) / (2 : ℚ)^(n + 2))) *
              (1 / (6 * A))^(n + 2) =
            (8 * (M a : ℚ) / 25) *
              (((((n + 1).factorial : Nat) : ℚ)) /
                ((2 : ℚ)^(n + 2) * A^(n + 2)))
          dsimp [A]
          rw [one_div_pow, mul_pow]
          field_simp [hApos.ne', pow_ne_zero (n + 2) hApos.ne',
            pow_ne_zero (n + 2) (by norm_num : (6 : ℚ) ≠ 0),
            pow_ne_zero (n + 2) (by norm_num : (2 : ℚ) ≠ 0)]
          have hfacCast :
              (((n + 1).factorial : Nat) : ℚ) =
                ((n : ℚ) + 1) * (((n.factorial : Nat) : ℚ)) := by
            exact_mod_cast (Nat.factorial_succ n)
          rw [hfacCast]
          ring_nf

private theorem printedTailLPoint_x0_budget (a : Nat) (ha : 150 ≤ a) :
    5 * (M a : ℚ) / (24 * ((a : ℚ) - 12)) +
        (8 * (M a : ℚ) / 25) * (5 / (2 * ((a : ℚ) - 12)^2)) ≤
      7 / 5 := by
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hApos : 0 < (a : ℚ) - 12 := by nlinarith
  have hdenpos : 0 < 120 * ((a : ℚ) - 12)^2 := by positivity
  have hpoly :
      0 ≤ 18 * (a : ℚ)^2 - 2658 * (a : ℚ) + 22968 := by
    have hshift : 0 ≤ (a : ℚ) - 150 := by nlinarith
    have hsq : 0 ≤ ((a : ℚ) - 150)^2 := sq_nonneg _
    have hdecomp :
        18 * (a : ℚ)^2 - 2658 * (a : ℚ) + 22968 =
          18 * ((a : ℚ) - 150)^2 +
            2742 * ((a : ℚ) - 150) + 29268 := by ring
    rw [hdecomp]
    nlinarith
  apply sub_nonneg.mp
  have hdiff :
      7 / 5 -
          (5 * (M a : ℚ) / (24 * ((a : ℚ) - 12)) +
            (8 * (M a : ℚ) / 25) * (5 / (2 * ((a : ℚ) - 12)^2))) =
        (18 * (a : ℚ)^2 - 2658 * (a : ℚ) + 22968) /
          (120 * ((a : ℚ) - 12)^2) := by
    unfold M
    rw [Nat.cast_sub (by omega : 6 ≤ 6 * a), Nat.cast_mul]
    field_simp [hApos.ne', pow_ne_zero 2 hApos.ne']
    ring
  rw [hdiff]
  exact div_nonneg hpoly hdenpos.le

private theorem printedTailLDeriv_x0_budget (a : Nat) (ha : 150 ≤ a) :
    5 * (M a : ℚ) / (24 * ((a : ℚ) - 12)) +
        (8 * (M a : ℚ) / 25) * (5 / ((a : ℚ) - 12)^2) ≤
      3 / 2 := by
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hApos : 0 < (a : ℚ) - 12 := by nlinarith
  have hdenpos : 0 < 120 * ((a : ℚ) - 12)^2 := by positivity
  have hpoly :
      0 ≤ 30 * (a : ℚ)^2 - 3522 * (a : ℚ) + 25272 := by
    have hshift : 0 ≤ (a : ℚ) - 150 := by nlinarith
    have hsq : 0 ≤ ((a : ℚ) - 150)^2 := sq_nonneg _
    have hdecomp :
        30 * (a : ℚ)^2 - 3522 * (a : ℚ) + 25272 =
          30 * ((a : ℚ) - 150)^2 +
            5478 * ((a : ℚ) - 150) + 171972 := by ring
    rw [hdecomp]
    nlinarith
  apply sub_nonneg.mp
  have hdiff :
      3 / 2 -
          (5 * (M a : ℚ) / (24 * ((a : ℚ) - 12)) +
            (8 * (M a : ℚ) / 25) * (5 / ((a : ℚ) - 12)^2)) =
        (30 * (a : ℚ)^2 - 3522 * (a : ℚ) + 25272) /
          (120 * ((a : ℚ) - 12)^2) := by
    unfold M
    rw [Nat.cast_sub (by omega : 6 ≤ 6 * a), Nat.cast_mul]
    field_simp [hApos.ne', pow_ne_zero 2 hApos.ne']
    ring
  rw [hdiff]
  exact div_nonneg hpoly hdenpos.le

private theorem printedTailJPoint_x0_budget (a : Nat) (ha : 150 ≤ a) :
    (M a : ℚ) / (6 * ((a : ℚ) - 12)) +
        (8 * (M a : ℚ) / 25) * (5 / (14 * ((a : ℚ) - 12)^2)) ≤
      11 / 10 := by
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hApos : 0 < (a : ℚ) - 12 := by nlinarith
  have hdenpos : 0 < 210 * ((a : ℚ) - 12)^2 := by positivity
  have hpoly :
      0 ≤ 21 * (a : ℚ)^2 - 2958 * (a : ℚ) + 30888 := by
    have hshift : 0 ≤ (a : ℚ) - 150 := by nlinarith
    have hsq : 0 ≤ ((a : ℚ) - 150)^2 := sq_nonneg _
    have hdecomp :
        21 * (a : ℚ)^2 - 2958 * (a : ℚ) + 30888 =
          21 * ((a : ℚ) - 150)^2 +
            3342 * ((a : ℚ) - 150) + 59688 := by ring
    rw [hdecomp]
    nlinarith
  apply sub_nonneg.mp
  have hdiff :
      11 / 10 -
          ((M a : ℚ) / (6 * ((a : ℚ) - 12)) +
            (8 * (M a : ℚ) / 25) *
              (5 / (14 * ((a : ℚ) - 12)^2))) =
        (21 * (a : ℚ)^2 - 2958 * (a : ℚ) + 30888) /
          (210 * ((a : ℚ) - 12)^2) := by
    unfold M
    rw [Nat.cast_sub (by omega : 6 ≤ 6 * a), Nat.cast_mul]
    field_simp [hApos.ne', pow_ne_zero 2 hApos.ne']
    ring
  rw [hdiff]
  exact div_nonneg hpoly hdenpos.le

private theorem printedTailJDeriv_x0_budget (a : Nat) (ha : 150 ≤ a) :
    (M a : ℚ) / (6 * ((a : ℚ) - 12)) +
        (8 * (M a : ℚ) / 25) * (5 / (7 * ((a : ℚ) - 12)^2)) ≤
      11 / 10 := by
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hApos : 0 < (a : ℚ) - 12 := by nlinarith
  have hdenpos : 0 < 210 * ((a : ℚ) - 12)^2 := by positivity
  have hpoly :
      0 ≤ 21 * (a : ℚ)^2 - 3102 * (a : ℚ) + 31032 := by
    have hshift : 0 ≤ (a : ℚ) - 150 := by nlinarith
    have hsq : 0 ≤ ((a : ℚ) - 150)^2 := sq_nonneg _
    have hdecomp :
        21 * (a : ℚ)^2 - 3102 * (a : ℚ) + 31032 =
          21 * ((a : ℚ) - 150)^2 +
            3198 * ((a : ℚ) - 150) + 38232 := by ring
    rw [hdecomp]
    nlinarith
  apply sub_nonneg.mp
  have hdiff :
      11 / 10 -
          ((M a : ℚ) / (6 * ((a : ℚ) - 12)) +
            (8 * (M a : ℚ) / 25) *
              (5 / (7 * ((a : ℚ) - 12)^2))) =
        (21 * (a : ℚ)^2 - 3102 * (a : ℚ) + 31032) /
          (210 * ((a : ℚ) - 12)^2) := by
    unfold M
    rw [Nat.cast_sub (by omega : 6 ≤ 6 * a), Nat.cast_mul]
    field_simp [hApos.ne', pow_ne_zero 2 hApos.ne']
    ring
  rw [hdiff]
  exact div_nonneg hpoly hdenpos.le

theorem printedTailLPointSum_x0_le
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    printedTailLPointSum μ a (printedTailX0 a) ≤ 7 / 5 := by
  let A : ℚ := (a : ℚ) - 12
  have hApos : 0 < A := by
    dsimp [A]
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  have hp : 1 ≤ printedTailP a := by
    unfold printedTailP
    omega
  let F : Nat → ℚ := fun r => hCoeff μ r * (printedTailX0 a)^r
  have hsplit := sum_range_eq_zero_one_add_Ico F (p := printedTailP a) hp
  have hzero : F 0 = 0 := by
    simp [F, hCoeff]
  have hone : F 1 ≤ 5 * (M a : ℚ) / (24 * A) := by
    have hcoeff := hCoeff_le_M_two_sub_twopow_c_of_partition
      (a := a) (μ := μ) hμ 1
    have hx0_nonneg : 0 ≤ printedTailX0 a := by
      unfold printedTailX0
      positivity
    calc
      F 1 ≤ (((M a : ℚ) * (2 - 1 / (2 : ℚ)^1)) * Prop51.c 1) *
          printedTailX0 a := by
            dsimp [F]
            simpa using mul_le_mul_of_nonneg_right hcoeff hx0_nonneg
      _ = 5 * (M a : ℚ) / (24 * A) := by
            unfold printedTailX0
            rw [Prop51.c_one]
            dsimp [A]
            field_simp [hApos.ne']
            ring_nf
  have htail :
      (∑ r ∈ Finset.Ico 2 (printedTailP a + 1), F r)
        ≤ (8 * (M a : ℚ) / 25) * (5 / (2 * A^2)) := by
    calc
      (∑ r ∈ Finset.Ico 2 (printedTailP a + 1), F r)
          ≤ ∑ r ∈ Finset.Ico 2 (printedTailP a + 1),
              (8 * (M a : ℚ) / 25) *
                ((((r - 1).factorial : Nat) : ℚ) / A^r) := by
            refine Finset.sum_le_sum fun r hr => ?_
            have hmem := Finset.mem_Ico.mp hr
            exact hCoeff_x0_tail_term_le (a := a) (μ := μ)
              ha hμ hmem.1
      _ = (8 * (M a : ℚ) / 25) *
            ∑ r ∈ Finset.Ico 2 (printedTailP a + 1),
              (((r - 1).factorial : Nat) : ℚ) / A^r := by
            rw [Finset.mul_sum]
      _ ≤ (8 * (M a : ℚ) / 25) * (5 / (2 * A^2)) :=
            mul_le_mul_of_nonneg_left
              (factorial_pred_x0_tail_sum_le a ha) (by positivity)
  rw [printedTailLPointSum, hsplit]
  calc
    F 0 + F 1 + ∑ r ∈ Finset.Ico 2 (printedTailP a + 1), F r
        ≤ 0 + 5 * (M a : ℚ) / (24 * A) +
            (8 * (M a : ℚ) / 25) * (5 / (2 * A^2)) := by
          nlinarith
    _ ≤ 7 / 5 := by
          simpa [A] using printedTailLPoint_x0_budget a ha

theorem printedTailLDerivPointSum_x0_le
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    printedTailLDerivPointSum μ a (printedTailX0 a) ≤ 3 / 2 := by
  let A : ℚ := (a : ℚ) - 12
  have hApos : 0 < A := by
    dsimp [A]
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  have hp : 1 ≤ printedTailP a := by
    unfold printedTailP
    omega
  let F : Nat → ℚ := fun r =>
    (r : ℚ) * hCoeff μ r * (printedTailX0 a)^r
  have hsplit := sum_range_eq_zero_one_add_Ico F (p := printedTailP a) hp
  have hzero : F 0 = 0 := by
    simp [F]
  have hone : F 1 ≤ 5 * (M a : ℚ) / (24 * A) := by
    have hcoeff := hCoeff_le_M_two_sub_twopow_c_of_partition
      (a := a) (μ := μ) hμ 1
    have hx0_nonneg : 0 ≤ printedTailX0 a := by
      unfold printedTailX0
      positivity
    calc
      F 1 ≤ (((M a : ℚ) * (2 - 1 / (2 : ℚ)^1)) * Prop51.c 1) *
          printedTailX0 a := by
            dsimp [F]
            simpa using mul_le_mul_of_nonneg_right hcoeff hx0_nonneg
      _ = 5 * (M a : ℚ) / (24 * A) := by
            unfold printedTailX0
            rw [Prop51.c_one]
            dsimp [A]
            field_simp [hApos.ne']
            ring_nf
  have htail :
      (∑ r ∈ Finset.Ico 2 (printedTailP a + 1), F r)
        ≤ (8 * (M a : ℚ) / 25) * (5 / A^2) := by
    calc
      (∑ r ∈ Finset.Ico 2 (printedTailP a + 1), F r)
          ≤ ∑ r ∈ Finset.Ico 2 (printedTailP a + 1),
              (8 * (M a : ℚ) / 25) *
                (((r.factorial : Nat) : ℚ) / A^r) := by
            refine Finset.sum_le_sum fun r hr => ?_
            have hmem := Finset.mem_Ico.mp hr
            have hbase := hCoeff_x0_tail_term_le (a := a) (μ := μ)
              ha hμ hmem.1
            have hr_nonneg : 0 ≤ (r : ℚ) := by positivity
            have hrewrite :
                (r : ℚ) *
                    ((8 * (M a : ℚ) / 25) *
                      ((((r - 1).factorial : Nat) : ℚ) / A^r))
                  =
                (8 * (M a : ℚ) / 25) *
                  (((r.factorial : Nat) : ℚ) / A^r) := by
              have hfac :
                  ((r.factorial : Nat) : ℚ) =
                    (r : ℚ) * (((r - 1).factorial : Nat) : ℚ) := by
                exact_mod_cast (Nat.mul_factorial_pred (by omega : r ≠ 0)).symm
              rw [hfac]
              ring
            calc
              F r = (r : ℚ) * (hCoeff μ r * (printedTailX0 a)^r) := by
                dsimp [F]
                ring
              _ ≤ (r : ℚ) *
                    ((8 * (M a : ℚ) / 25) *
                      ((((r - 1).factorial : Nat) : ℚ) / A^r)) :=
                    mul_le_mul_of_nonneg_left hbase hr_nonneg
              _ = (8 * (M a : ℚ) / 25) *
                    (((r.factorial : Nat) : ℚ) / A^r) := hrewrite
      _ = (8 * (M a : ℚ) / 25) *
            ∑ r ∈ Finset.Ico 2 (printedTailP a + 1),
              ((r.factorial : Nat) : ℚ) / A^r := by
            rw [Finset.mul_sum]
      _ ≤ (8 * (M a : ℚ) / 25) * (5 / A^2) :=
            mul_le_mul_of_nonneg_left
              (factorial_x0_tail_sum_le a ha) (by positivity)
  rw [printedTailLDerivPointSum, hsplit]
  calc
    F 0 + F 1 + ∑ r ∈ Finset.Ico 2 (printedTailP a + 1), F r
        ≤ 0 + 5 * (M a : ℚ) / (24 * A) +
            (8 * (M a : ℚ) / 25) * (5 / A^2) := by
          nlinarith
    _ ≤ 3 / 2 := by
          simpa [A] using printedTailLDeriv_x0_budget a ha

theorem printedTailJPointSum_x0_le
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    printedTailJPointSum μ a (printedTailX0 a) ≤ 11 / 10 := by
  let A : ℚ := (a : ℚ) - 12
  have hApos : 0 < A := by
    dsimp [A]
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  have hp : 1 ≤ printedTailP a := by
    unfold printedTailP
    omega
  let F : Nat → ℚ := fun r => kCoeff μ r * (printedTailX0 a)^r
  have hsplit := sum_range_eq_zero_one_add_Ico F (p := printedTailP a) hp
  have hzero : F 0 = 0 := by
    simp [F, kCoeff]
  have hone : F 1 ≤ (M a : ℚ) / (6 * A) := by
    have hcoeff := kCoeff_le_partition_marked_bound
      (a := a) (μ := μ) hμ 1
    have hcoeff' : kCoeff μ 1 ≤ (M a : ℚ) := by
      have hcoeff0 : kCoeff μ 1 ≤ 2 * ((M a : ℚ) / 2) := by
        simpa using hcoeff
      linarith
    have hx0_nonneg : 0 ≤ printedTailX0 a := by
      unfold printedTailX0
      positivity
    calc
      F 1 ≤ (M a : ℚ) * printedTailX0 a := by
            dsimp [F]
            simpa using mul_le_mul_of_nonneg_right hcoeff' hx0_nonneg
      _ = (M a : ℚ) / (6 * A) := by
            unfold printedTailX0
            dsimp [A]
            field_simp [hApos.ne']
  have htail :
      (∑ r ∈ Finset.Ico 2 (printedTailP a + 1), F r)
        ≤ (8 * (M a : ℚ) / 25) * (5 / (14 * A^2)) := by
    calc
      (∑ r ∈ Finset.Ico 2 (printedTailP a + 1), F r)
          ≤ ∑ r ∈ Finset.Ico 2 (printedTailP a + 1),
              (8 * (M a : ℚ) / 25) *
                ((((r - 1).factorial : Nat) : ℚ) /
                  ((2 : ℚ)^r * A^r)) := by
            refine Finset.sum_le_sum fun r hr => ?_
            have hmem := Finset.mem_Ico.mp hr
            exact kCoeff_x0_tail_term_le (a := a) (μ := μ)
              ha hμ hmem.1
      _ = (8 * (M a : ℚ) / 25) *
            ∑ r ∈ Finset.Ico 2 (printedTailP a + 1),
              (((r - 1).factorial : Nat) : ℚ) /
                ((2 : ℚ)^r * A^r) := by
            rw [Finset.mul_sum]
      _ ≤ (8 * (M a : ℚ) / 25) * (5 / (14 * A^2)) :=
            mul_le_mul_of_nonneg_left
              (factorial_pred_x0_halved_tail_sum_le a ha) (by positivity)
  rw [printedTailJPointSum, hsplit]
  calc
    F 0 + F 1 + ∑ r ∈ Finset.Ico 2 (printedTailP a + 1), F r
        ≤ 0 + (M a : ℚ) / (6 * A) +
            (8 * (M a : ℚ) / 25) * (5 / (14 * A^2)) := by
          nlinarith
    _ ≤ 11 / 10 := by
          simpa [A] using printedTailJPoint_x0_budget a ha

theorem printedTailJDerivPointSum_x0_le
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    printedTailJDerivPointSum μ a (printedTailX0 a) ≤ 11 / 10 := by
  let A : ℚ := (a : ℚ) - 12
  have hApos : 0 < A := by
    dsimp [A]
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  have hp : 1 ≤ printedTailP a := by
    unfold printedTailP
    omega
  let F : Nat → ℚ := fun r =>
    (r : ℚ) * kCoeff μ r * (printedTailX0 a)^r
  have hsplit := sum_range_eq_zero_one_add_Ico F (p := printedTailP a) hp
  have hzero : F 0 = 0 := by
    simp [F]
  have hone : F 1 ≤ (M a : ℚ) / (6 * A) := by
    have hcoeff := kCoeff_le_partition_marked_bound
      (a := a) (μ := μ) hμ 1
    have hcoeff' : kCoeff μ 1 ≤ (M a : ℚ) := by
      have hcoeff0 : kCoeff μ 1 ≤ 2 * ((M a : ℚ) / 2) := by
        simpa using hcoeff
      linarith
    have hx0_nonneg : 0 ≤ printedTailX0 a := by
      unfold printedTailX0
      positivity
    calc
      F 1 ≤ (M a : ℚ) * printedTailX0 a := by
            dsimp [F]
            simpa using mul_le_mul_of_nonneg_right hcoeff' hx0_nonneg
      _ = (M a : ℚ) / (6 * A) := by
            unfold printedTailX0
            dsimp [A]
            field_simp [hApos.ne']
  have htail :
      (∑ r ∈ Finset.Ico 2 (printedTailP a + 1), F r)
        ≤ (8 * (M a : ℚ) / 25) * (5 / (7 * A^2)) := by
    calc
      (∑ r ∈ Finset.Ico 2 (printedTailP a + 1), F r)
          ≤ ∑ r ∈ Finset.Ico 2 (printedTailP a + 1),
              (8 * (M a : ℚ) / 25) *
                (((r.factorial : Nat) : ℚ) /
                  ((2 : ℚ)^r * A^r)) := by
            refine Finset.sum_le_sum fun r hr => ?_
            have hmem := Finset.mem_Ico.mp hr
            have hbase := kCoeff_x0_tail_term_le (a := a) (μ := μ)
              ha hμ hmem.1
            have hr_nonneg : 0 ≤ (r : ℚ) := by positivity
            have hrewrite :
                (r : ℚ) *
                    ((8 * (M a : ℚ) / 25) *
                      ((((r - 1).factorial : Nat) : ℚ) /
                        ((2 : ℚ)^r * A^r)))
                  =
                (8 * (M a : ℚ) / 25) *
                  (((r.factorial : Nat) : ℚ) /
                    ((2 : ℚ)^r * A^r)) := by
              have hfac :
                  ((r.factorial : Nat) : ℚ) =
                    (r : ℚ) * (((r - 1).factorial : Nat) : ℚ) := by
                exact_mod_cast (Nat.mul_factorial_pred (by omega : r ≠ 0)).symm
              rw [hfac]
              ring
            calc
              F r = (r : ℚ) * (kCoeff μ r * (printedTailX0 a)^r) := by
                dsimp [F]
                ring
              _ ≤ (r : ℚ) *
                    ((8 * (M a : ℚ) / 25) *
                      ((((r - 1).factorial : Nat) : ℚ) /
                        ((2 : ℚ)^r * A^r))) :=
                    mul_le_mul_of_nonneg_left hbase hr_nonneg
              _ = (8 * (M a : ℚ) / 25) *
                    (((r.factorial : Nat) : ℚ) /
                      ((2 : ℚ)^r * A^r)) := hrewrite
      _ = (8 * (M a : ℚ) / 25) *
            ∑ r ∈ Finset.Ico 2 (printedTailP a + 1),
              ((r.factorial : Nat) : ℚ) / ((2 : ℚ)^r * A^r) := by
            rw [Finset.mul_sum]
      _ ≤ (8 * (M a : ℚ) / 25) * (5 / (7 * A^2)) :=
            mul_le_mul_of_nonneg_left
              (factorial_x0_halved_tail_sum_le a ha) (by positivity)
  rw [printedTailJDerivPointSum, hsplit]
  calc
    F 0 + F 1 + ∑ r ∈ Finset.Ico 2 (printedTailP a + 1), F r
        ≤ 0 + (M a : ℚ) / (6 * A) +
            (8 * (M a : ℚ) / 25) * (5 / (7 * A^2)) := by
          nlinarith
    _ ≤ 11 / 10 := by
          simpa [A] using printedTailJDeriv_x0_budget a ha

/-! ## Low-polynomial term bounds at `x₂`

These are the coefficientwise estimates whose finite sums are controlled by
the factorial-gas certificates above.  They isolate the algebraic reduction
from the concrete generated prefix/tail constants.
-/

private theorem hCoeff_one_x2_le
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    hCoeff μ 1 * printedTailX2 a ≤ 5 * ((a : ℚ) - 1) / (a : ℚ) := by
  have hcoeff := hCoeff_le_M_two_sub_twopow_c_of_partition
    (a := a) (μ := μ) hμ 1
  have hx2_nonneg : 0 ≤ printedTailX2 a := by
    unfold printedTailX2
    positivity
  have ha_pos : (0 : ℚ) < (a : ℚ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 150) ha)
  calc
    hCoeff μ 1 * printedTailX2 a
        ≤ (((M a : ℚ) * (2 - 1 / (2 : ℚ)^1)) * Prop51.c 1) *
            printedTailX2 a :=
          mul_le_mul_of_nonneg_right hcoeff hx2_nonneg
    _ = 5 * ((a : ℚ) - 1) / (a : ℚ) := by
          unfold printedTailX2 M
          rw [Prop51.c_one, Nat.cast_sub (by omega : 6 ≤ 6 * a), Nat.cast_mul]
          field_simp [ha_pos.ne']
          ring

private theorem kCoeff_one_x2_le
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    kCoeff μ 1 * printedTailX2 a ≤ 4 * ((a : ℚ) - 1) / (a : ℚ) := by
  have hcoeff := kCoeff_le_partition_marked_bound
    (a := a) (μ := μ) hμ 1
  have hcoeff' : kCoeff μ 1 ≤ (M a : ℚ) := by
    have hcoeff0 : kCoeff μ 1 ≤ 2 * ((M a : ℚ) / 2) := by
      simpa using hcoeff
    linarith
  have hx2_nonneg : 0 ≤ printedTailX2 a := by
    unfold printedTailX2
    positivity
  have ha_pos : (0 : ℚ) < (a : ℚ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 150) ha)
  calc
    kCoeff μ 1 * printedTailX2 a
        ≤ (M a : ℚ) * printedTailX2 a :=
          mul_le_mul_of_nonneg_right hcoeff' hx2_nonneg
    _ = 4 * ((a : ℚ) - 1) / (a : ℚ) := by
          unfold printedTailX2 M
          rw [Nat.cast_sub (by omega : 6 ≤ 6 * a), Nat.cast_mul]
          field_simp [ha_pos.ne']
          ring

private theorem hCoeff_x2_tail_term_le {a r : Nat} {μ : List Nat}
    (ha : 150 ≤ a) (hμ : Prop51.IsPartitionOf μ (M a))
    (hr : 2 ≤ r) :
    hCoeff μ r * (printedTailX2 a)^r
      ≤ (8 * (M a : ℚ) / 25) *
          ((((r - 1).factorial : Nat) : ℚ) * (4 : ℚ)^r / (a : ℚ)^r) := by
  let A : ℚ := (a : ℚ)
  have hApos : 0 < A := by
    dsimp [A]
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 150) ha)
  have hMnonneg : 0 ≤ (M a : ℚ) := by positivity
  have hx2_nonneg : 0 ≤ printedTailX2 a := by
    unfold printedTailX2
    positivity
  have hcoeff := hCoeff_le_M_two_sub_twopow_c_of_partition
    (a := a) (μ := μ) hμ r
  have hfactor_le :
      (M a : ℚ) * (2 - 1 / (2 : ℚ)^r) ≤ (M a : ℚ) * 2 := by
    have hinv_nonneg : 0 ≤ 1 / (2 : ℚ)^r := by positivity
    nlinarith
  have hcub := Prop51.c_ub r (by omega : 1 ≤ r)
  have hc_nonneg := Prop51.c_nonneg r
  have hprod :
      ((M a : ℚ) * (2 - 1 / (2 : ℚ)^r)) * Prop51.c r
        ≤ ((M a : ℚ) * 2) *
            ((4 / 25 : ℚ) *
              ((6 : ℚ)^r * (((r - 1).factorial : Nat) : ℚ))) :=
    mul_le_mul hfactor_le hcub hc_nonneg
      (mul_nonneg hMnonneg (by norm_num))
  calc
    hCoeff μ r * (printedTailX2 a)^r
        ≤ (((M a : ℚ) * (2 - 1 / (2 : ℚ)^r)) * Prop51.c r) *
            (printedTailX2 a)^r :=
          mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hx2_nonneg r)
    _ ≤ (((M a : ℚ) * 2) *
            ((4 / 25 : ℚ) *
              ((6 : ℚ)^r * (((r - 1).factorial : Nat) : ℚ)))) *
            (printedTailX2 a)^r :=
          mul_le_mul_of_nonneg_right hprod (pow_nonneg hx2_nonneg r)
    _ = (8 * (M a : ℚ) / 25) *
          ((((r - 1).factorial : Nat) : ℚ) * (4 : ℚ)^r / A^r) := by
          change (((M a : ℚ) * 2) *
              ((4 / 25 : ℚ) *
                ((6 : ℚ)^r * (((r - 1).factorial : Nat) : ℚ)))) *
              (2 / (3 * A))^r =
            (8 * (M a : ℚ) / 25) *
              ((((r - 1).factorial : Nat) : ℚ) * (4 : ℚ)^r / A^r)
          dsimp [A]
          rw [div_pow, mul_pow]
          field_simp [hApos.ne', pow_ne_zero r hApos.ne',
            pow_ne_zero r (by norm_num : (3 : ℚ) ≠ 0)]
          have hpow : (2 : ℚ)^r * 6^r = 3^r * 4^r := by
            rw [← mul_pow, ← mul_pow]
            norm_num
          have hpow' : (6 : ℚ)^r * 2^r = 3^r * 4^r := by
            rw [mul_comm, hpow]
          calc
            (M a : ℚ) * 2 * 4 * 6^r * 2^r
                = (M a : ℚ) * 8 * (6^r * 2^r) := by ring
            _ = (M a : ℚ) * 8 * (3^r * 4^r) := by rw [hpow']
            _ = (M a : ℚ) * 3^r * 8 * 4^r := by ring

private theorem kCoeff_x2_tail_term_le {a r : Nat} {μ : List Nat}
    (ha : 150 ≤ a) (hμ : Prop51.IsPartitionOf μ (M a))
    (hr : 2 ≤ r) :
    kCoeff μ r * (printedTailX2 a)^r
      ≤ (8 * (M a : ℚ) / 25) *
          ((((r - 1).factorial : Nat) : ℚ) * (2 : ℚ)^r / (a : ℚ)^r) := by
  let A : ℚ := (a : ℚ)
  rcases r with _ | r'
  · omega
  rcases r' with _ | n
  · omega
  have hApos : 0 < A := by
    dsimp [A]
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 150) ha)
  have hx2_nonneg : 0 ≤ printedTailX2 a := by
    unfold printedTailX2
    positivity
  have hmw := markedWeight_le_M_div_two_pow_of_partition
    (a := a) (μ := μ) hμ (n + 2)
  have hpref_nonneg :
      0 ≤ 12 * ((n : ℚ) + 1) * Prop51.c (n + 1) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (by positivity))
      (Prop51.c_nonneg (n + 1))
  have hcub := Prop51.c_ub (n + 1) (by omega : 1 ≤ n + 1)
  have hpref :
      12 * ((n : ℚ) + 1) * Prop51.c (n + 1)
        ≤ 12 * ((n : ℚ) + 1) *
            ((4 / 25 : ℚ) *
              ((6 : ℚ)^(n + 1) *
                (((n + 1 - 1).factorial : Nat) : ℚ))) := by
    exact mul_le_mul_of_nonneg_left hcub
      (mul_nonneg (by norm_num) (by positivity))
  have hcoeff :
      kCoeff μ (n + 2)
        ≤ (12 * ((n : ℚ) + 1) * Prop51.c (n + 1)) *
            ((M a : ℚ) / (2 : ℚ)^(n + 2)) := by
    simpa [kCoeff, Nat.cast_add, Nat.cast_one] using
      mul_le_mul_of_nonneg_left hmw hpref_nonneg
  have hcoeff' :
      kCoeff μ (n + 2)
        ≤ (12 * ((n : ℚ) + 1) *
            ((4 / 25 : ℚ) *
              ((6 : ℚ)^(n + 1) *
                (((n + 1 - 1).factorial : Nat) : ℚ)))) *
            ((M a : ℚ) / (2 : ℚ)^(n + 2)) := by
    exact hcoeff.trans
      (mul_le_mul_of_nonneg_right hpref
        (div_nonneg (by positivity) (pow_nonneg (by norm_num) _)))
  calc
    kCoeff μ (n + 2) * (printedTailX2 a)^(n + 2)
        ≤ ((12 * ((n : ℚ) + 1) *
            ((4 / 25 : ℚ) *
              ((6 : ℚ)^(n + 1) *
                (((n + 1 - 1).factorial : Nat) : ℚ)))) *
            ((M a : ℚ) / (2 : ℚ)^(n + 2))) *
            (printedTailX2 a)^(n + 2) :=
          mul_le_mul_of_nonneg_right hcoeff'
            (pow_nonneg hx2_nonneg (n + 2))
    _ = (8 * (M a : ℚ) / 25) *
          ((((n + 2 - 1).factorial : Nat) : ℚ) *
            (2 : ℚ)^(n + 2) / A^(n + 2)) := by
          rw [show n + 1 - 1 = n by omega,
            show n + 2 - 1 = n + 1 by omega, Nat.factorial_succ]
          change ((12 * ((n : ℚ) + 1) *
              ((4 / 25 : ℚ) *
                ((6 : ℚ)^(n + 1) * ((n.factorial : Nat) : ℚ)))) *
              ((M a : ℚ) / (2 : ℚ)^(n + 2))) *
              (2 / (3 * A))^(n + 2) =
            (8 * (M a : ℚ) / 25) *
              (((((n + 1).factorial : Nat) : ℚ)) *
                (2 : ℚ)^(n + 2) / A^(n + 2))
          dsimp [A]
          rw [div_pow, mul_pow]
          field_simp [hApos.ne', pow_ne_zero (n + 2) hApos.ne',
            pow_ne_zero (n + 2) (by norm_num : (2 : ℚ) ≠ 0),
            pow_ne_zero (n + 2) (by norm_num : (3 : ℚ) ≠ 0)]
          have hfacCast :
              (((n + 1).factorial : Nat) : ℚ) =
                ((n : ℚ) + 1) * (((n.factorial : Nat) : ℚ)) := by
            exact_mod_cast (Nat.factorial_succ n)
          rw [hfacCast]
          have hpow : (2 : ℚ)^(n + 2) * 3^(n + 2) = 6^(n + 2) := by
            rw [← mul_pow]
            norm_num
          have h6 :
              (6 : ℚ)^(n + 2) = 6^(n + 1) * 6 := by
            rw [show n + 2 = n + 1 + 1 by omega, pow_succ]
          calc
            12 * ((n : ℚ) + 1) * 4 * 6^(n + 1) *
                  ((n.factorial : Nat) : ℚ) * (M a : ℚ)
                =
              (M a : ℚ) * (6^(n + 1) * 6) * 8 *
                (((n : ℚ) + 1) * ((n.factorial : Nat) : ℚ)) := by ring
            _ =
              (M a : ℚ) * 6^(n + 2) * 8 *
                (((n : ℚ) + 1) * ((n.factorial : Nat) : ℚ)) := by
                rw [h6]
            _ =
              (M a : ℚ) * (2^(n + 2) * 3^(n + 2)) * 8 *
                (((n : ℚ) + 1) * ((n.factorial : Nat) : ℚ)) := by
                rw [← hpow]
            _ =
              (M a : ℚ) * 2^(n + 2) * 3^(n + 2) * 8 *
                (((n : ℚ) + 1) * ((n.factorial : Nat) : ℚ)) := by ring

private theorem hCoeff_x2_weighted_tail_term_le {a r : Nat} {μ : List Nat}
    (ha : 150 ≤ a) (hμ : Prop51.IsPartitionOf μ (M a))
    (hr : 2 ≤ r) :
    (r : ℚ) * hCoeff μ r * (printedTailX2 a)^r
      ≤ (8 * (M a : ℚ) / 25) *
          ((r : ℚ) *
            ((((r - 1).factorial : Nat) : ℚ) *
              (4 : ℚ)^r / (a : ℚ)^r)) := by
  have hbase := hCoeff_x2_tail_term_le (a := a) (r := r)
    (μ := μ) ha hμ hr
  have hr_nonneg : 0 ≤ (r : ℚ) := by positivity
  calc
    (r : ℚ) * hCoeff μ r * (printedTailX2 a)^r
        = (r : ℚ) * (hCoeff μ r * (printedTailX2 a)^r) := by ring
    _ ≤ (r : ℚ) *
          ((8 * (M a : ℚ) / 25) *
            ((((r - 1).factorial : Nat) : ℚ) *
              (4 : ℚ)^r / (a : ℚ)^r)) :=
          mul_le_mul_of_nonneg_left hbase hr_nonneg
    _ = (8 * (M a : ℚ) / 25) *
          ((r : ℚ) *
            ((((r - 1).factorial : Nat) : ℚ) *
              (4 : ℚ)^r / (a : ℚ)^r)) := by
          ring

private theorem kCoeff_x2_weighted_tail_term_le {a r : Nat} {μ : List Nat}
    (ha : 150 ≤ a) (hμ : Prop51.IsPartitionOf μ (M a))
    (hr : 2 ≤ r) :
    (r : ℚ) * kCoeff μ r * (printedTailX2 a)^r
      ≤ (8 * (M a : ℚ) / 25) *
          ((r : ℚ) *
            ((((r - 1).factorial : Nat) : ℚ) *
              (2 : ℚ)^r / (a : ℚ)^r)) := by
  have hbase := kCoeff_x2_tail_term_le (a := a) (r := r)
    (μ := μ) ha hμ hr
  have hr_nonneg : 0 ≤ (r : ℚ) := by positivity
  calc
    (r : ℚ) * kCoeff μ r * (printedTailX2 a)^r
        = (r : ℚ) * (kCoeff μ r * (printedTailX2 a)^r) := by ring
    _ ≤ (r : ℚ) *
          ((8 * (M a : ℚ) / 25) *
            ((((r - 1).factorial : Nat) : ℚ) *
              (2 : ℚ)^r / (a : ℚ)^r)) :=
          mul_le_mul_of_nonneg_left hbase hr_nonneg
    _ = (8 * (M a : ℚ) / 25) *
          ((r : ℚ) *
            ((((r - 1).factorial : Nat) : ℚ) *
              (2 : ℚ)^r / (a : ℚ)^r)) := by
          ring

def printedTailX2Bound1 (a : Nat) : ℚ :=
  5 * ((a : ℚ) - 1) / (a : ℚ) +
    (8 * printedTailMrat a / 25) *
      (16 / (a : ℚ)^2 + 128 / (a : ℚ)^3 + 1730 / (a : ℚ)^4)

def printedTailX2Bound2 (a : Nat) : ℚ :=
  5 * ((a : ℚ) - 1) / (a : ℚ) +
    (8 * printedTailMrat a / 25) *
      (32 / (a : ℚ)^2 + 384 / (a : ℚ)^3 + 7340 / (a : ℚ)^4)

def printedTailX2Bound3 (a : Nat) : ℚ :=
  4 * ((a : ℚ) - 1) / (a : ℚ) +
    (8 * printedTailMrat a / 25) *
      (4 / (a : ℚ)^2 + 16 / (a : ℚ)^3 + 103 / (a : ℚ)^4)

def printedTailX2Bound4 (a : Nat) : ℚ :=
  4 * ((a : ℚ) - 1) / (a : ℚ) +
    (8 * printedTailMrat a / 25) *
      (8 / (a : ℚ)^2 + 48 / (a : ℚ)^3 + 413 / (a : ℚ)^4)

private theorem printedTailX2Bound1_poly_pos (a : Nat) (ha : 150 ≤ a) :
    0 < 25 * (a : ℚ)^4 - 3215 * (a : ℚ)^3 - 26880 * (a : ℚ)^2 -
      384480 * (a : ℚ) + 415200 := by
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hshift : 0 ≤ (a : ℚ) - 150 := by nlinarith
  have hsq : 0 ≤ ((a : ℚ) - 150)^2 := sq_nonneg _
  have hcube : 0 ≤ ((a : ℚ) - 150)^3 := by positivity
  have hfour : 0 ≤ ((a : ℚ) - 150)^4 := by positivity
  have hdecomp :
      25 * (a : ℚ)^4 - 3215 * (a : ℚ)^3 - 26880 * (a : ℚ)^2 -
          384480 * (a : ℚ) + 415200 =
        25 * ((a : ℚ) - 150)^4 + 11785 * ((a : ℚ) - 150)^3 +
          1901370 * ((a : ℚ) - 150)^2 + 112039020 * ((a : ℚ) - 150) +
          1143568200 := by
    ring
  rw [hdecomp]
  nlinarith

private theorem printedTailX2Bound2_poly_pos (a : Nat) (ha : 150 ≤ a) :
    0 < 25 * (a : ℚ)^4 - 2822 * (a : ℚ)^3 - 33792 * (a : ℚ)^2 -
      667776 * (a : ℚ) + 704640 := by
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hshift : 0 ≤ (a : ℚ) - 150 := by nlinarith
  have hsq : 0 ≤ ((a : ℚ) - 150)^2 := sq_nonneg _
  have hcube : 0 ≤ ((a : ℚ) - 150)^3 := by positivity
  have hfour : 0 ≤ ((a : ℚ) - 150)^4 := by positivity
  have hdecomp :
      25 * (a : ℚ)^4 - 2822 * (a : ℚ)^3 - 33792 * (a : ℚ)^2 -
          667776 * (a : ℚ) + 704640 =
        25 * ((a : ℚ) - 150)^4 + 12178 * ((a : ℚ) - 150)^3 +
          2071308 * ((a : ℚ) - 150)^2 + 136209624 * ((a : ℚ) - 150) +
          2272218240 := by
    ring
  rw [hdecomp]
  nlinarith

private theorem printedTailX2Bound3_poly_pos (a : Nat) (ha : 150 ≤ a) :
    0 < 25 * (a : ℚ)^4 - 1840 * (a : ℚ)^3 - 11520 * (a : ℚ)^2 -
      83520 * (a : ℚ) + 98880 := by
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hshift : 0 ≤ (a : ℚ) - 150 := by nlinarith
  have hsq : 0 ≤ ((a : ℚ) - 150)^2 := sq_nonneg _
  have hcube : 0 ≤ ((a : ℚ) - 150)^3 := by positivity
  have hfour : 0 ≤ ((a : ℚ) - 150)^4 := by positivity
  have hdecomp :
      25 * (a : ℚ)^4 - 1840 * (a : ℚ)^3 - 11520 * (a : ℚ)^2 -
          83520 * (a : ℚ) + 98880 =
        25 * ((a : ℚ) - 150)^4 + 13160 * ((a : ℚ) - 150)^3 +
          2535480 * ((a : ℚ) - 150)^2 + 209760480 * ((a : ℚ) - 150) +
          6174620880 := by
    ring
  rw [hdecomp]
  nlinarith

private theorem printedTailX2Bound4_poly_pos (a : Nat) (ha : 150 ≤ a) :
    0 < 25 * (a : ℚ)^4 - 2840 * (a : ℚ)^3 - 19200 * (a : ℚ)^2 -
      175200 * (a : ℚ) + 198240 := by
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hshift : 0 ≤ (a : ℚ) - 150 := by nlinarith
  have hsq : 0 ≤ ((a : ℚ) - 150)^2 := sq_nonneg _
  have hcube : 0 ≤ ((a : ℚ) - 150)^3 := by positivity
  have hfour : 0 ≤ ((a : ℚ) - 150)^4 := by positivity
  have hdecomp :
      25 * (a : ℚ)^4 - 2840 * (a : ℚ)^3 - 19200 * (a : ℚ)^2 -
          175200 * (a : ℚ) + 198240 =
        25 * ((a : ℚ) - 150)^4 + 12160 * ((a : ℚ) - 150)^3 +
          2077800 * ((a : ℚ) - 150)^2 + 139864800 * ((a : ℚ) - 150) +
          2613168240 := by
    ring
  rw [hdecomp]
  nlinarith

theorem printedTailX2Bound1_lt (a : Nat) (ha : 150 ≤ a) :
    printedTailX2Bound1 a < 26 / 5 := by
  unfold printedTailX2Bound1 printedTailMrat
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have ha_pos : (0 : ℚ) < (a : ℚ) := by nlinarith
  have hpoly := printedTailX2Bound1_poly_pos a ha
  field_simp [ha_pos.ne']
  ring_nf
  nlinarith

theorem printedTailX2Bound2_lt (a : Nat) (ha : 150 ≤ a) :
    printedTailX2Bound2 a < 11 / 2 := by
  unfold printedTailX2Bound2 printedTailMrat
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have ha_pos : (0 : ℚ) < (a : ℚ) := by nlinarith
  have hpoly := printedTailX2Bound2_poly_pos a ha
  field_simp [ha_pos.ne']
  ring_nf
  nlinarith

theorem printedTailX2Bound3_lt (a : Nat) (ha : 150 ≤ a) :
    printedTailX2Bound3 a < 81 / 20 := by
  unfold printedTailX2Bound3 printedTailMrat
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have ha_pos : (0 : ℚ) < (a : ℚ) := by nlinarith
  have hpoly := printedTailX2Bound3_poly_pos a ha
  field_simp [ha_pos.ne']
  ring_nf
  nlinarith

theorem printedTailX2Bound4_lt (a : Nat) (ha : 150 ≤ a) :
    printedTailX2Bound4 a < 41 / 10 := by
  unfold printedTailX2Bound4 printedTailMrat
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have ha_pos : (0 : ℚ) < (a : ℚ) := by nlinarith
  have hpoly := printedTailX2Bound4_poly_pos a ha
  field_simp [ha_pos.ne']
  ring_nf
  nlinarith

theorem printedTailLPointSum_x2_le
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    printedTailLPointSum μ a (printedTailX2 a) ≤ 26 / 5 := by
  have hp : 1 ≤ printedTailP a := by
    unfold printedTailP
    omega
  have hp3 : 3 ≤ printedTailP a := by
    unfold printedTailP
    omega
  have hMrat : printedTailMrat a = (M a : ℚ) := by
    unfold printedTailMrat M
    rw [Nat.cast_sub (by omega : 6 ≤ 6 * a), Nat.cast_mul]
    ring
  let F : Nat → ℚ := fun r => hCoeff μ r * (printedTailX2 a)^r
  have hsplit := sum_range_eq_zero_one_add_Ico F (p := printedTailP a) hp
  have hzero : F 0 = 0 := by
    simp [F, hCoeff]
  have hone : F 1 ≤ 5 * ((a : ℚ) - 1) / (a : ℚ) := by
    simpa [F] using hCoeff_one_x2_le (a := a) (μ := μ) ha hμ
  have htail4 :
      (∑ r ∈ Finset.Ico (4 : Nat) (printedTailP a + 1), F r)
        ≤ (8 * (M a : ℚ) / 25) * (1730 / (a : ℚ)^4) := by
    calc
      (∑ r ∈ Finset.Ico (4 : Nat) (printedTailP a + 1), F r)
          ≤ ∑ r ∈ Finset.Ico (4 : Nat) (printedTailP a + 1),
              (8 * (M a : ℚ) / 25) *
                ((((r - 1).factorial : Nat) : ℚ) *
                  (4 : ℚ)^r / (a : ℚ)^r) := by
            refine Finset.sum_le_sum fun r hr => ?_
            have hmem := Finset.mem_Ico.mp hr
            simpa [F] using hCoeff_x2_tail_term_le (a := a) (r := r)
              (μ := μ) ha hμ (by omega : 2 ≤ r)
      _ = (8 * (M a : ℚ) / 25) *
            ∑ r ∈ Finset.Ico (4 : Nat) (printedTailP a + 1),
              (((r - 1).factorial : Nat) : ℚ) *
                (4 : ℚ)^r / (a : ℚ)^r := by
            rw [Finset.mul_sum]
      _ ≤ (8 * (M a : ℚ) / 25) * (1730 / (a : ℚ)^4) :=
            mul_le_mul_of_nonneg_left
              (factorialGasBase4_x2_sum_le a ha) (by positivity)
  have h2 : F 2 ≤ (8 * (M a : ℚ) / 25) * (16 / (a : ℚ)^2) := by
    calc
      F 2
          ≤ (8 * (M a : ℚ) / 25) *
              ((((2 - 1).factorial : Nat) : ℚ) *
                (4 : ℚ)^2 / (a : ℚ)^2) := by
            simpa [F] using hCoeff_x2_tail_term_le (a := a) (r := 2)
              (μ := μ) ha hμ (by norm_num : 2 ≤ 2)
      _ = (8 * (M a : ℚ) / 25) * (16 / (a : ℚ)^2) := by
            norm_num
  have h3 : F 3 ≤ (8 * (M a : ℚ) / 25) * (128 / (a : ℚ)^3) := by
    calc
      F 3
          ≤ (8 * (M a : ℚ) / 25) *
              ((((3 - 1).factorial : Nat) : ℚ) *
                (4 : ℚ)^3 / (a : ℚ)^3) := by
            simpa [F] using hCoeff_x2_tail_term_le (a := a) (r := 3)
              (μ := μ) ha hμ (by norm_num : 2 ≤ 3)
      _ = (8 * (M a : ℚ) / 25) * (128 / (a : ℚ)^3) := by
            norm_num
  have htail :
      (∑ r ∈ Finset.Ico (2 : Nat) (printedTailP a + 1), F r)
        ≤ (8 * (M a : ℚ) / 25) *
            (16 / (a : ℚ)^2 + 128 / (a : ℚ)^3 +
              1730 / (a : ℚ)^4) := by
    have hsplit_tail :=
      sum_Ico_two_three_add_Ico F (p := printedTailP a) hp3
    rw [hsplit_tail]
    calc
      F 2 + F 3 + ∑ r ∈ Finset.Ico (4 : Nat) (printedTailP a + 1), F r
          ≤ (8 * (M a : ℚ) / 25) * (16 / (a : ℚ)^2) +
              (8 * (M a : ℚ) / 25) * (128 / (a : ℚ)^3) +
              (8 * (M a : ℚ) / 25) * (1730 / (a : ℚ)^4) := by
            nlinarith
      _ = (8 * (M a : ℚ) / 25) *
            (16 / (a : ℚ)^2 + 128 / (a : ℚ)^3 +
              1730 / (a : ℚ)^4) := by
            ring
  rw [printedTailLPointSum, hsplit]
  calc
    F 0 + F 1 + ∑ r ∈ Finset.Ico (2 : Nat) (printedTailP a + 1), F r
        ≤ 0 + 5 * ((a : ℚ) - 1) / (a : ℚ) +
            (8 * (M a : ℚ) / 25) *
              (16 / (a : ℚ)^2 + 128 / (a : ℚ)^3 +
                1730 / (a : ℚ)^4) := by
          nlinarith
    _ = printedTailX2Bound1 a := by
          unfold printedTailX2Bound1
          rw [hMrat]
          ring
    _ ≤ 26 / 5 := le_of_lt (printedTailX2Bound1_lt a ha)

theorem printedTailLDerivPointSum_x2_le
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    printedTailLDerivPointSum μ a (printedTailX2 a) ≤ 11 / 2 := by
  have hp : 1 ≤ printedTailP a := by
    unfold printedTailP
    omega
  have hp3 : 3 ≤ printedTailP a := by
    unfold printedTailP
    omega
  have hMrat : printedTailMrat a = (M a : ℚ) := by
    unfold printedTailMrat M
    rw [Nat.cast_sub (by omega : 6 ≤ 6 * a), Nat.cast_mul]
    ring
  let F : Nat → ℚ := fun r => (r : ℚ) * hCoeff μ r * (printedTailX2 a)^r
  have hsplit := sum_range_eq_zero_one_add_Ico F (p := printedTailP a) hp
  have hzero : F 0 = 0 := by
    simp [F]
  have hone : F 1 ≤ 5 * ((a : ℚ) - 1) / (a : ℚ) := by
    simpa [F] using hCoeff_one_x2_le (a := a) (μ := μ) ha hμ
  have htail4 :
      (∑ r ∈ Finset.Ico (4 : Nat) (printedTailP a + 1), F r)
        ≤ (8 * (M a : ℚ) / 25) * (7340 / (a : ℚ)^4) := by
    calc
      (∑ r ∈ Finset.Ico (4 : Nat) (printedTailP a + 1), F r)
          ≤ ∑ r ∈ Finset.Ico (4 : Nat) (printedTailP a + 1),
              (8 * (M a : ℚ) / 25) *
                ((r : ℚ) *
                  ((((r - 1).factorial : Nat) : ℚ) *
                    (4 : ℚ)^r / (a : ℚ)^r)) := by
            refine Finset.sum_le_sum fun r hr => ?_
            have hmem := Finset.mem_Ico.mp hr
            simpa [F] using hCoeff_x2_weighted_tail_term_le (a := a)
              (r := r) (μ := μ) ha hμ (by omega : 2 ≤ r)
      _ = (8 * (M a : ℚ) / 25) *
            ∑ r ∈ Finset.Ico (4 : Nat) (printedTailP a + 1),
              (r : ℚ) *
                ((((r - 1).factorial : Nat) : ℚ) *
                  (4 : ℚ)^r / (a : ℚ)^r) := by
            rw [Finset.mul_sum]
      _ ≤ (8 * (M a : ℚ) / 25) * (7340 / (a : ℚ)^4) :=
            mul_le_mul_of_nonneg_left
              (factorialGasBase4_weighted_x2_sum_le a ha) (by positivity)
  have h2 : F 2 ≤ (8 * (M a : ℚ) / 25) * (32 / (a : ℚ)^2) := by
    calc
      F 2
          ≤ (8 * (M a : ℚ) / 25) *
            ((2 : ℚ) *
              ((((2 - 1).factorial : Nat) : ℚ) *
                (4 : ℚ)^2 / (a : ℚ)^2)) := by
            simpa [F] using hCoeff_x2_weighted_tail_term_le (a := a)
              (r := 2) (μ := μ) ha hμ (by norm_num : 2 ≤ 2)
      _ = (8 * (M a : ℚ) / 25) * (32 / (a : ℚ)^2) := by
            ring
  have h3 : F 3 ≤ (8 * (M a : ℚ) / 25) * (384 / (a : ℚ)^3) := by
    calc
      F 3
          ≤ (8 * (M a : ℚ) / 25) *
            ((3 : ℚ) *
              ((((3 - 1).factorial : Nat) : ℚ) *
                (4 : ℚ)^3 / (a : ℚ)^3)) := by
            simpa [F] using hCoeff_x2_weighted_tail_term_le (a := a)
              (r := 3) (μ := μ) ha hμ (by norm_num : 2 ≤ 3)
      _ = (8 * (M a : ℚ) / 25) * (384 / (a : ℚ)^3) := by
            ring
  have htail :
      (∑ r ∈ Finset.Ico (2 : Nat) (printedTailP a + 1), F r)
        ≤ (8 * (M a : ℚ) / 25) *
            (32 / (a : ℚ)^2 + 384 / (a : ℚ)^3 +
              7340 / (a : ℚ)^4) := by
    have hsplit_tail :=
      sum_Ico_two_three_add_Ico F (p := printedTailP a) hp3
    rw [hsplit_tail]
    calc
      F 2 + F 3 + ∑ r ∈ Finset.Ico (4 : Nat) (printedTailP a + 1), F r
          ≤ (8 * (M a : ℚ) / 25) * (32 / (a : ℚ)^2) +
              (8 * (M a : ℚ) / 25) * (384 / (a : ℚ)^3) +
              (8 * (M a : ℚ) / 25) * (7340 / (a : ℚ)^4) := by
            nlinarith
      _ = (8 * (M a : ℚ) / 25) *
            (32 / (a : ℚ)^2 + 384 / (a : ℚ)^3 +
              7340 / (a : ℚ)^4) := by
            ring
  rw [printedTailLDerivPointSum, hsplit]
  calc
    F 0 + F 1 + ∑ r ∈ Finset.Ico (2 : Nat) (printedTailP a + 1), F r
        ≤ 0 + 5 * ((a : ℚ) - 1) / (a : ℚ) +
            (8 * (M a : ℚ) / 25) *
              (32 / (a : ℚ)^2 + 384 / (a : ℚ)^3 +
                7340 / (a : ℚ)^4) := by
          nlinarith
    _ = printedTailX2Bound2 a := by
          unfold printedTailX2Bound2
          rw [hMrat]
          ring
    _ ≤ 11 / 2 := le_of_lt (printedTailX2Bound2_lt a ha)

theorem printedTailJPointSum_x2_le
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    printedTailJPointSum μ a (printedTailX2 a) ≤ 81 / 20 := by
  have hp : 1 ≤ printedTailP a := by
    unfold printedTailP
    omega
  have hp3 : 3 ≤ printedTailP a := by
    unfold printedTailP
    omega
  have hMrat : printedTailMrat a = (M a : ℚ) := by
    unfold printedTailMrat M
    rw [Nat.cast_sub (by omega : 6 ≤ 6 * a), Nat.cast_mul]
    ring
  let F : Nat → ℚ := fun r => kCoeff μ r * (printedTailX2 a)^r
  have hsplit := sum_range_eq_zero_one_add_Ico F (p := printedTailP a) hp
  have hzero : F 0 = 0 := by
    simp [F, kCoeff]
  have hone : F 1 ≤ 4 * ((a : ℚ) - 1) / (a : ℚ) := by
    simpa [F] using kCoeff_one_x2_le (a := a) (μ := μ) ha hμ
  have htail4 :
      (∑ r ∈ Finset.Ico (4 : Nat) (printedTailP a + 1), F r)
        ≤ (8 * (M a : ℚ) / 25) * (103 / (a : ℚ)^4) := by
    calc
      (∑ r ∈ Finset.Ico (4 : Nat) (printedTailP a + 1), F r)
          ≤ ∑ r ∈ Finset.Ico (4 : Nat) (printedTailP a + 1),
              (8 * (M a : ℚ) / 25) *
                ((((r - 1).factorial : Nat) : ℚ) *
                  (2 : ℚ)^r / (a : ℚ)^r) := by
            refine Finset.sum_le_sum fun r hr => ?_
            have hmem := Finset.mem_Ico.mp hr
            simpa [F] using kCoeff_x2_tail_term_le (a := a) (r := r)
              (μ := μ) ha hμ (by omega : 2 ≤ r)
      _ = (8 * (M a : ℚ) / 25) *
            ∑ r ∈ Finset.Ico (4 : Nat) (printedTailP a + 1),
              (((r - 1).factorial : Nat) : ℚ) *
                (2 : ℚ)^r / (a : ℚ)^r := by
            rw [Finset.mul_sum]
      _ ≤ (8 * (M a : ℚ) / 25) * (103 / (a : ℚ)^4) :=
            mul_le_mul_of_nonneg_left
              (factorialGasBase2_x2_sum_le a ha) (by positivity)
  have h2 : F 2 ≤ (8 * (M a : ℚ) / 25) * (4 / (a : ℚ)^2) := by
    calc
      F 2
          ≤ (8 * (M a : ℚ) / 25) *
              ((((2 - 1).factorial : Nat) : ℚ) *
                (2 : ℚ)^2 / (a : ℚ)^2) := by
            simpa [F] using kCoeff_x2_tail_term_le (a := a) (r := 2)
              (μ := μ) ha hμ (by norm_num : 2 ≤ 2)
      _ = (8 * (M a : ℚ) / 25) * (4 / (a : ℚ)^2) := by
            norm_num
  have h3 : F 3 ≤ (8 * (M a : ℚ) / 25) * (16 / (a : ℚ)^3) := by
    calc
      F 3
          ≤ (8 * (M a : ℚ) / 25) *
              ((((3 - 1).factorial : Nat) : ℚ) *
                (2 : ℚ)^3 / (a : ℚ)^3) := by
            simpa [F] using kCoeff_x2_tail_term_le (a := a) (r := 3)
              (μ := μ) ha hμ (by norm_num : 2 ≤ 3)
      _ = (8 * (M a : ℚ) / 25) * (16 / (a : ℚ)^3) := by
            norm_num
  have htail :
      (∑ r ∈ Finset.Ico (2 : Nat) (printedTailP a + 1), F r)
        ≤ (8 * (M a : ℚ) / 25) *
            (4 / (a : ℚ)^2 + 16 / (a : ℚ)^3 +
              103 / (a : ℚ)^4) := by
    have hsplit_tail :=
      sum_Ico_two_three_add_Ico F (p := printedTailP a) hp3
    rw [hsplit_tail]
    calc
      F 2 + F 3 + ∑ r ∈ Finset.Ico (4 : Nat) (printedTailP a + 1), F r
          ≤ (8 * (M a : ℚ) / 25) * (4 / (a : ℚ)^2) +
              (8 * (M a : ℚ) / 25) * (16 / (a : ℚ)^3) +
              (8 * (M a : ℚ) / 25) * (103 / (a : ℚ)^4) := by
            nlinarith
      _ = (8 * (M a : ℚ) / 25) *
            (4 / (a : ℚ)^2 + 16 / (a : ℚ)^3 +
              103 / (a : ℚ)^4) := by
            ring
  rw [printedTailJPointSum, hsplit]
  calc
    F 0 + F 1 + ∑ r ∈ Finset.Ico (2 : Nat) (printedTailP a + 1), F r
        ≤ 0 + 4 * ((a : ℚ) - 1) / (a : ℚ) +
            (8 * (M a : ℚ) / 25) *
              (4 / (a : ℚ)^2 + 16 / (a : ℚ)^3 +
                103 / (a : ℚ)^4) := by
          nlinarith
    _ = printedTailX2Bound3 a := by
          unfold printedTailX2Bound3
          rw [hMrat]
          ring
    _ ≤ 81 / 20 := le_of_lt (printedTailX2Bound3_lt a ha)

theorem printedTailJDerivPointSum_x2_le
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    printedTailJDerivPointSum μ a (printedTailX2 a) ≤ 41 / 10 := by
  have hp : 1 ≤ printedTailP a := by
    unfold printedTailP
    omega
  have hp3 : 3 ≤ printedTailP a := by
    unfold printedTailP
    omega
  have hMrat : printedTailMrat a = (M a : ℚ) := by
    unfold printedTailMrat M
    rw [Nat.cast_sub (by omega : 6 ≤ 6 * a), Nat.cast_mul]
    ring
  let F : Nat → ℚ := fun r => (r : ℚ) * kCoeff μ r * (printedTailX2 a)^r
  have hsplit := sum_range_eq_zero_one_add_Ico F (p := printedTailP a) hp
  have hzero : F 0 = 0 := by
    simp [F]
  have hone : F 1 ≤ 4 * ((a : ℚ) - 1) / (a : ℚ) := by
    simpa [F] using kCoeff_one_x2_le (a := a) (μ := μ) ha hμ
  have htail4 :
      (∑ r ∈ Finset.Ico (4 : Nat) (printedTailP a + 1), F r)
        ≤ (8 * (M a : ℚ) / 25) * (413 / (a : ℚ)^4) := by
    calc
      (∑ r ∈ Finset.Ico (4 : Nat) (printedTailP a + 1), F r)
          ≤ ∑ r ∈ Finset.Ico (4 : Nat) (printedTailP a + 1),
              (8 * (M a : ℚ) / 25) *
                ((r : ℚ) *
                  ((((r - 1).factorial : Nat) : ℚ) *
                    (2 : ℚ)^r / (a : ℚ)^r)) := by
            refine Finset.sum_le_sum fun r hr => ?_
            have hmem := Finset.mem_Ico.mp hr
            simpa [F] using kCoeff_x2_weighted_tail_term_le (a := a)
              (r := r) (μ := μ) ha hμ (by omega : 2 ≤ r)
      _ = (8 * (M a : ℚ) / 25) *
            ∑ r ∈ Finset.Ico (4 : Nat) (printedTailP a + 1),
              (r : ℚ) *
                ((((r - 1).factorial : Nat) : ℚ) *
                  (2 : ℚ)^r / (a : ℚ)^r) := by
            rw [Finset.mul_sum]
      _ ≤ (8 * (M a : ℚ) / 25) * (413 / (a : ℚ)^4) :=
            mul_le_mul_of_nonneg_left
              (factorialGasBase2_weighted_x2_sum_le a ha) (by positivity)
  have h2 : F 2 ≤ (8 * (M a : ℚ) / 25) * (8 / (a : ℚ)^2) := by
    calc
      F 2
          ≤ (8 * (M a : ℚ) / 25) *
            ((2 : ℚ) *
              ((((2 - 1).factorial : Nat) : ℚ) *
                (2 : ℚ)^2 / (a : ℚ)^2)) := by
            simpa [F] using kCoeff_x2_weighted_tail_term_le (a := a)
              (r := 2) (μ := μ) ha hμ (by norm_num : 2 ≤ 2)
      _ = (8 * (M a : ℚ) / 25) * (8 / (a : ℚ)^2) := by
            ring
  have h3 : F 3 ≤ (8 * (M a : ℚ) / 25) * (48 / (a : ℚ)^3) := by
    calc
      F 3
          ≤ (8 * (M a : ℚ) / 25) *
            ((3 : ℚ) *
              ((((3 - 1).factorial : Nat) : ℚ) *
                (2 : ℚ)^3 / (a : ℚ)^3)) := by
            simpa [F] using kCoeff_x2_weighted_tail_term_le (a := a)
              (r := 3) (μ := μ) ha hμ (by norm_num : 2 ≤ 3)
      _ = (8 * (M a : ℚ) / 25) * (48 / (a : ℚ)^3) := by
            ring
  have htail :
      (∑ r ∈ Finset.Ico (2 : Nat) (printedTailP a + 1), F r)
        ≤ (8 * (M a : ℚ) / 25) *
            (8 / (a : ℚ)^2 + 48 / (a : ℚ)^3 +
              413 / (a : ℚ)^4) := by
    have hsplit_tail :=
      sum_Ico_two_three_add_Ico F (p := printedTailP a) hp3
    rw [hsplit_tail]
    calc
      F 2 + F 3 + ∑ r ∈ Finset.Ico (4 : Nat) (printedTailP a + 1), F r
          ≤ (8 * (M a : ℚ) / 25) * (8 / (a : ℚ)^2) +
              (8 * (M a : ℚ) / 25) * (48 / (a : ℚ)^3) +
              (8 * (M a : ℚ) / 25) * (413 / (a : ℚ)^4) := by
            nlinarith
      _ = (8 * (M a : ℚ) / 25) *
            (8 / (a : ℚ)^2 + 48 / (a : ℚ)^3 +
              413 / (a : ℚ)^4) := by
            ring
  rw [printedTailJDerivPointSum, hsplit]
  calc
    F 0 + F 1 + ∑ r ∈ Finset.Ico (2 : Nat) (printedTailP a + 1), F r
        ≤ 0 + 4 * ((a : ℚ) - 1) / (a : ℚ) +
            (8 * (M a : ℚ) / 25) *
              (8 / (a : ℚ)^2 + 48 / (a : ℚ)^3 +
                413 / (a : ℚ)^4) := by
          nlinarith
    _ = printedTailX2Bound4 a := by
          unfold printedTailX2Bound4
          rw [hMrat]
          ring
    _ ≤ 41 / 10 := le_of_lt (printedTailX2Bound4_lt a ha)

private theorem printedTailR0_le_P (a : Nat) :
    printedTailR0 a ≤ printedTailP a := by
  unfold printedTailR0 printedTailP
  omega

private theorem printedTailX0_nonneg {a : Nat} (ha : 150 ≤ a) :
    0 ≤ printedTailX0 a := by
  unfold printedTailX0
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hden : 0 < 6 * ((a : ℚ) - 12) := by nlinarith
  positivity

private theorem printedTailX2_nonneg {a : Nat} (ha : 150 ≤ a) :
    0 ≤ printedTailX2 a := by
  unfold printedTailX2
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hden : 0 < 3 * (a : ℚ) := by nlinarith
  positivity

private theorem printedTailExpPrefix_nonneg {y : ℚ}
    (hy : 0 ≤ y) (m : Nat) :
    0 ≤ printedTailExpPrefix y m := by
  unfold printedTailExpPrefix
  exact Finset.sum_nonneg fun q _ =>
    div_nonneg (pow_nonneg hy q) (by positivity)

private theorem printedTailLowAbsInput_point_prefix_le_LPointSum
    {a : Nat} {μ : List Nat} {x : ℚ} {m : Nat}
    (hμ : Prop51.IsPartitionOf μ (M a)) (hx : 0 ≤ x)
    (hm : m ≤ printedTailP a) :
    (∑ r ∈ Finset.range (m + 1), x^r * printedTailLowAbsInput μ a r)
      ≤ printedTailLPointSum μ a x := by
  have hsubset :
      Finset.range (m + 1) ⊆ Finset.range (printedTailP a + 1) := by
    intro r hr
    exact Finset.mem_range.mpr (by
      have hr' := Finset.mem_range.mp hr
      omega)
  have hsum_eq :
      (∑ r ∈ Finset.range (m + 1), x^r * printedTailLowAbsInput μ a r)
        =
      ∑ r ∈ Finset.range (m + 1), hCoeff μ r * x^r := by
    refine Finset.sum_congr rfl fun r hr => ?_
    have hrp : r ≤ printedTailP a := by
      have hr' := Finset.mem_range.mp hr
      omega
    unfold printedTailLowAbsInput printedTailLowExpInput
    rw [if_pos hrp, abs_neg,
      abs_of_nonneg (hCoeff_nonneg_of_partition hμ r)]
    ring
  rw [hsum_eq, printedTailLPointSum]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun r _ _ => mul_nonneg (hCoeff_nonneg_of_partition hμ r)
      (pow_nonneg hx r))

private theorem printedTailLowAbsInput_deriv_prefix_le_LDerivPointSum
    {a : Nat} {μ : List Nat} {x : ℚ} {m : Nat}
    (hμ : Prop51.IsPartitionOf μ (M a)) (hx : 0 ≤ x)
    (hm : m ≤ printedTailP a) :
    (∑ r ∈ Finset.range (m + 1),
        (r : ℚ) * (x^r * printedTailLowAbsInput μ a r))
      ≤ printedTailLDerivPointSum μ a x := by
  have hsubset :
      Finset.range (m + 1) ⊆ Finset.range (printedTailP a + 1) := by
    intro r hr
    exact Finset.mem_range.mpr (by
      have hr' := Finset.mem_range.mp hr
      omega)
  have hsum_eq :
      (∑ r ∈ Finset.range (m + 1),
          (r : ℚ) * (x^r * printedTailLowAbsInput μ a r))
        =
      ∑ r ∈ Finset.range (m + 1),
        (r : ℚ) * hCoeff μ r * x^r := by
    refine Finset.sum_congr rfl fun r hr => ?_
    have hrp : r ≤ printedTailP a := by
      have hr' := Finset.mem_range.mp hr
      omega
    unfold printedTailLowAbsInput printedTailLowExpInput
    rw [if_pos hrp, abs_neg,
      abs_of_nonneg (hCoeff_nonneg_of_partition hμ r)]
    ring
  rw [hsum_eq, printedTailLDerivPointSum]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun r _ _ => by
      exact mul_nonneg
        (mul_nonneg (by positivity) (hCoeff_nonneg_of_partition hμ r))
        (pow_nonneg hx r))

private theorem printedTailJAbsCoeff_point_prefix_le_JPointSum
    {a : Nat} {μ : List Nat} {x : ℚ} {m : Nat}
    (hx : 0 ≤ x) (hm : m ≤ printedTailP a) :
    (∑ r ∈ Finset.range (m + 1),
        printedTailJAbsCoeff μ a r * x^r)
      ≤ printedTailJPointSum μ a x := by
  have hsubset :
      Finset.range (m + 1) ⊆ Finset.range (printedTailP a + 1) := by
    intro r hr
    exact Finset.mem_range.mpr (by
      have hr' := Finset.mem_range.mp hr
      omega)
  have hsum_eq :
      (∑ r ∈ Finset.range (m + 1),
          printedTailJAbsCoeff μ a r * x^r)
        =
      ∑ r ∈ Finset.range (m + 1), kCoeff μ r * x^r := by
    refine Finset.sum_congr rfl fun r hr => ?_
    have hrp : r ≤ printedTailP a := by
      have hr' := Finset.mem_range.mp hr
      omega
    by_cases hr0 : r = 0
    · subst r
      simp [printedTailJAbsCoeff, kCoeff]
    · have hr1 : 1 ≤ r := by omega
      simp [printedTailJAbsCoeff, hr1, hrp]
  rw [hsum_eq, printedTailJPointSum]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun r _ _ => mul_nonneg (kCoeff_nonneg μ r) (pow_nonneg hx r))

private theorem printedTailJAbsCoeff_deriv_prefix_le_JDerivPointSum
    {a : Nat} {μ : List Nat} {x : ℚ} {m : Nat}
    (hx : 0 ≤ x) (hm : m ≤ printedTailP a) :
    (∑ r ∈ Finset.range (m + 1),
        (r : ℚ) * printedTailJAbsCoeff μ a r * x^r)
      ≤ printedTailJDerivPointSum μ a x := by
  have hsubset :
      Finset.range (m + 1) ⊆ Finset.range (printedTailP a + 1) := by
    intro r hr
    exact Finset.mem_range.mpr (by
      have hr' := Finset.mem_range.mp hr
      omega)
  have hsum_eq :
      (∑ r ∈ Finset.range (m + 1),
          (r : ℚ) * printedTailJAbsCoeff μ a r * x^r)
        =
      ∑ r ∈ Finset.range (m + 1),
        (r : ℚ) * kCoeff μ r * x^r := by
    refine Finset.sum_congr rfl fun r hr => ?_
    have hrp : r ≤ printedTailP a := by
      have hr' := Finset.mem_range.mp hr
      omega
    by_cases hr0 : r = 0
    · subst r
      simp [printedTailJAbsCoeff, kCoeff]
    · have hr1 : 1 ≤ r := by omega
      simp [printedTailJAbsCoeff, hr1, hrp]
  rw [hsum_eq, printedTailJDerivPointSum]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun r _ _ => by
      exact mul_nonneg (mul_nonneg (by positivity) (kCoeff_nonneg μ r))
        (pow_nonneg hx r))

private theorem printedTailLowAbsInput_point_prefix_le_LPointSum_of_P_le
    {a : Nat} {μ : List Nat} {x : ℚ} {m : Nat}
    (hμ : Prop51.IsPartitionOf μ (M a)) (hpm : printedTailP a ≤ m) :
    (∑ r ∈ Finset.range (m + 1), x^r * printedTailLowAbsInput μ a r)
      ≤ printedTailLPointSum μ a x := by
  have hsubset :
      Finset.range (printedTailP a + 1) ⊆ Finset.range (m + 1) := by
    intro r hr
    exact Finset.mem_range.mpr (by
      have hr' := Finset.mem_range.mp hr
      omega)
  have hzero :
      ∀ r ∈ Finset.range (m + 1), r ∉ Finset.range (printedTailP a + 1) →
        x^r * printedTailLowAbsInput μ a r = 0 := by
    intro r _hr hnot
    have hpr : printedTailP a < r := by
      have hnot' : ¬ r < printedTailP a + 1 := by
        intro hrange
        exact hnot (Finset.mem_range.mpr hrange)
      omega
    unfold printedTailLowAbsInput printedTailLowExpInput
    rw [if_neg (by omega : ¬ r ≤ printedTailP a)]
    simp
  have hbig_small :
      (∑ r ∈ Finset.range (m + 1), x^r * printedTailLowAbsInput μ a r)
        =
      ∑ r ∈ Finset.range (printedTailP a + 1),
        x^r * printedTailLowAbsInput μ a r :=
    (Finset.sum_subset hsubset hzero).symm
  rw [hbig_small, printedTailLPointSum]
  refine le_of_eq ?_
  refine Finset.sum_congr rfl fun r hr => ?_
  have hrp : r ≤ printedTailP a := by
    have hr' := Finset.mem_range.mp hr
    omega
  unfold printedTailLowAbsInput printedTailLowExpInput
  rw [if_pos hrp, abs_neg,
    abs_of_nonneg (hCoeff_nonneg_of_partition hμ r)]
  ring

private theorem printedTailJAbsCoeff_point_prefix_le_JPointSum_of_P_le
    {a : Nat} {μ : List Nat} {x : ℚ} {m : Nat}
    (hpm : printedTailP a ≤ m) :
    (∑ r ∈ Finset.range (m + 1), printedTailJAbsCoeff μ a r * x^r)
      ≤ printedTailJPointSum μ a x := by
  have hsubset :
      Finset.range (printedTailP a + 1) ⊆ Finset.range (m + 1) := by
    intro r hr
    exact Finset.mem_range.mpr (by
      have hr' := Finset.mem_range.mp hr
      omega)
  have hzero :
      ∀ r ∈ Finset.range (m + 1), r ∉ Finset.range (printedTailP a + 1) →
        printedTailJAbsCoeff μ a r * x^r = 0 := by
    intro r _hr hnot
    have hpr : printedTailP a < r := by
      have hnot' : ¬ r < printedTailP a + 1 := by
        intro hrange
        exact hnot (Finset.mem_range.mpr hrange)
      omega
    unfold printedTailJAbsCoeff
    rw [if_neg (by omega : ¬(1 ≤ r ∧ r ≤ printedTailP a))]
    simp
  have hbig_small :
      (∑ r ∈ Finset.range (m + 1), printedTailJAbsCoeff μ a r * x^r)
        =
      ∑ r ∈ Finset.range (printedTailP a + 1),
        printedTailJAbsCoeff μ a r * x^r :=
    (Finset.sum_subset hsubset hzero).symm
  rw [hbig_small, printedTailJPointSum]
  refine le_of_eq ?_
  refine Finset.sum_congr rfl fun r hr => ?_
  have hrp : r ≤ printedTailP a := by
    have hr' := Finset.mem_range.mp hr
    omega
  by_cases hr0 : r = 0
  · subst r
    simp [printedTailJAbsCoeff, kCoeff]
  · have hr1 : 1 ≤ r := by omega
    simp [printedTailJAbsCoeff, hr1, hrp]

private theorem printedTailEAbsPointPrefix_nonneg
    (μ : List Nat) (a : Nat) {x : ℚ} (hx : 0 ≤ x) (m : Nat) :
    0 ≤ ∑ s ∈ Finset.range (m + 1),
      printedTailEAbsCoeff μ a s * x^s := by
  exact Finset.sum_nonneg fun s _ =>
    mul_nonneg (printedTailEAbsCoeff_nonneg μ a s) (pow_nonneg hx s)

private theorem printedTailEAbsDerivPrefix_nonneg
    (μ : List Nat) (a : Nat) {x : ℚ} (hx : 0 ≤ x) (m : Nat) :
    0 ≤ ∑ s ∈ Finset.range (m + 1),
      (s : ℚ) * printedTailEAbsCoeff μ a s * x^s := by
  exact Finset.sum_nonneg fun s _ =>
    mul_nonneg
      (mul_nonneg (by positivity) (printedTailEAbsCoeff_nonneg μ a s))
      (pow_nonneg hx s)

private theorem printedTailJAbsPointPrefix_nonneg
    (μ : List Nat) (a : Nat) {x : ℚ} (hx : 0 ≤ x) (m : Nat) :
    0 ≤ ∑ r ∈ Finset.range (m + 1),
      printedTailJAbsCoeff μ a r * x^r := by
  exact Finset.sum_nonneg fun r _ =>
    mul_nonneg (printedTailJAbsCoeff_nonneg μ a r) (pow_nonneg hx r)

private theorem printedTailJAbsDerivPrefix_nonneg
    (μ : List Nat) (a : Nat) {x : ℚ} (hx : 0 ≤ x) (m : Nat) :
    0 ≤ ∑ r ∈ Finset.range (m + 1),
      (r : ℚ) * printedTailJAbsCoeff μ a r * x^r := by
  exact Finset.sum_nonneg fun r _ =>
    mul_nonneg
      (mul_nonneg (by positivity) (printedTailJAbsCoeff_nonneg μ a r))
      (pow_nonneg hx r)

private theorem printedTailEAbsPointSum_x0_le
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    (∑ s ∈ Finset.range (printedTailR0 a + 1),
      printedTailEAbsCoeff μ a s * (printedTailX0 a)^s) ≤
        203 / 50 := by
  let m := printedTailR0 a
  let x := printedTailX0 a
  have hx : 0 ≤ x := by simpa [x] using printedTailX0_nonneg ha
  have hm : m ≤ printedTailP a := by
    simpa [m] using printedTailR0_le_P a
  have hLprefix :=
    printedTailLowAbsInput_point_prefix_le_LPointSum
      (a := a) (μ := μ) (x := x) (m := m) hμ hx hm
  have hLbd :
      (∑ r ∈ Finset.range (m + 1), x^r * printedTailLowAbsInput μ a r)
        ≤ 7 / 5 :=
    hLprefix.trans (by
      simpa [x] using
        (printedTailLPointSum_x0_le (a := a) (μ := μ) ha hμ))
  have hLnonneg :
      0 ≤ ∑ r ∈ Finset.range (m + 1), x^r * printedTailLowAbsInput μ a r := by
    exact Finset.sum_nonneg fun r _ =>
      mul_nonneg (pow_nonneg hx r)
        (printedTailLowAbsInput_nonneg μ a r)
  have hE := expCoeff_point_sum_le_expPrefix
    (L := printedTailLowAbsInput μ a)
    (printedTailLowAbsInput_zero μ a)
    (printedTailLowAbsInput_nonneg μ a) (x := x) hx m
  have hE' :
      (∑ s ∈ Finset.range (m + 1),
        printedTailEAbsCoeff μ a s * x^s)
        ≤ printedTailExpPrefix
            (∑ r ∈ Finset.range (m + 1),
              x^r * printedTailLowAbsInput μ a r) m := by
    simpa [printedTailEAbsCoeff, printedTailLowAbsInput] using hE
  have hExp := printedTailExpPrefix_le_203_50 hLnonneg hLbd m
  simpa [m, x] using hE'.trans hExp

private theorem printedTailEAbsDerivPointSum_x0_le
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    (∑ s ∈ Finset.range (printedTailR0 a + 1),
      (s : ℚ) * printedTailEAbsCoeff μ a s * (printedTailX0 a)^s) ≤
        (203 / 50 : ℚ) * (3 / 2) := by
  let m := printedTailR0 a
  let x := printedTailX0 a
  have hx : 0 ≤ x := by simpa [x] using printedTailX0_nonneg ha
  have hm : m ≤ printedTailP a := by
    simpa [m] using printedTailR0_le_P a
  have hLprefix :=
    printedTailLowAbsInput_point_prefix_le_LPointSum
      (a := a) (μ := μ) (x := x) (m := m) hμ hx hm
  have hLbd :
      (∑ r ∈ Finset.range (m + 1), x^r * printedTailLowAbsInput μ a r)
        ≤ 7 / 5 :=
    hLprefix.trans (by
      simpa [x] using
        (printedTailLPointSum_x0_le (a := a) (μ := μ) ha hμ))
  have hLnonneg :
      0 ≤ ∑ r ∈ Finset.range (m + 1), x^r * printedTailLowAbsInput μ a r := by
    exact Finset.sum_nonneg fun r _ =>
      mul_nonneg (pow_nonneg hx r)
        (printedTailLowAbsInput_nonneg μ a r)
  have hDprefix :=
    printedTailLowAbsInput_deriv_prefix_le_LDerivPointSum
      (a := a) (μ := μ) (x := x) (m := m) hμ hx hm
  have hDbd :
      (∑ r ∈ Finset.range (m + 1),
        (r : ℚ) * (x^r * printedTailLowAbsInput μ a r)) ≤ 3 / 2 :=
    hDprefix.trans (by
      simpa [x] using
        (printedTailLDerivPointSum_x0_le (a := a) (μ := μ) ha hμ))
  have hExpbd := printedTailExpPrefix_le_203_50 hLnonneg hLbd m
  have hExpnonneg := printedTailExpPrefix_nonneg hLnonneg m
  have hD := expCoeff_deriv_point_sum_le_expPrefix
    (L := printedTailLowAbsInput μ a)
    (printedTailLowAbsInput_zero μ a)
    (printedTailLowAbsInput_nonneg μ a) (x := x) hx m
  have hD' :
      (∑ s ∈ Finset.range (m + 1),
        (s : ℚ) * printedTailEAbsCoeff μ a s * x^s)
        ≤ (∑ r ∈ Finset.range (m + 1),
            (r : ℚ) * (x^r * printedTailLowAbsInput μ a r)) *
          printedTailExpPrefix
            (∑ r ∈ Finset.range (m + 1),
              x^r * printedTailLowAbsInput μ a r) m := by
    simpa [printedTailEAbsCoeff, printedTailLowAbsInput] using hD
  calc
    (∑ s ∈ Finset.range (printedTailR0 a + 1),
      (s : ℚ) * printedTailEAbsCoeff μ a s * (printedTailX0 a)^s)
        =
      ∑ s ∈ Finset.range (m + 1),
        (s : ℚ) * printedTailEAbsCoeff μ a s * x^s := by simp [m, x]
    _ ≤ (∑ r ∈ Finset.range (m + 1),
            (r : ℚ) * (x^r * printedTailLowAbsInput μ a r)) *
          printedTailExpPrefix
            (∑ r ∈ Finset.range (m + 1),
              x^r * printedTailLowAbsInput μ a r) m := hD'
    _ ≤ (3 / 2 : ℚ) * (203 / 50) :=
          mul_le_mul hDbd hExpbd hExpnonneg (by norm_num)
    _ = (203 / 50 : ℚ) * (3 / 2) := by ring

private theorem printedTailEAbsPointSum_x2_le
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    (∑ s ∈ Finset.range (printedTailR0 a + 1),
      printedTailEAbsCoeff μ a s * (printedTailX2 a)^s) ≤
        182 := by
  let m := printedTailR0 a
  let x := printedTailX2 a
  have hx : 0 ≤ x := by simpa [x] using printedTailX2_nonneg ha
  have hm : m ≤ printedTailP a := by
    simpa [m] using printedTailR0_le_P a
  have hLprefix :=
    printedTailLowAbsInput_point_prefix_le_LPointSum
      (a := a) (μ := μ) (x := x) (m := m) hμ hx hm
  have hLbd :
      (∑ r ∈ Finset.range (m + 1), x^r * printedTailLowAbsInput μ a r)
        ≤ 26 / 5 :=
    hLprefix.trans (by
      simpa [x] using
        (printedTailLPointSum_x2_le (a := a) (μ := μ) ha hμ))
  have hLnonneg :
      0 ≤ ∑ r ∈ Finset.range (m + 1), x^r * printedTailLowAbsInput μ a r := by
    exact Finset.sum_nonneg fun r _ =>
      mul_nonneg (pow_nonneg hx r)
        (printedTailLowAbsInput_nonneg μ a r)
  have hE := expCoeff_point_sum_le_expPrefix
    (L := printedTailLowAbsInput μ a)
    (printedTailLowAbsInput_zero μ a)
    (printedTailLowAbsInput_nonneg μ a) (x := x) hx m
  have hE' :
      (∑ s ∈ Finset.range (m + 1),
        printedTailEAbsCoeff μ a s * x^s)
        ≤ printedTailExpPrefix
            (∑ r ∈ Finset.range (m + 1),
              x^r * printedTailLowAbsInput μ a r) m := by
    simpa [printedTailEAbsCoeff, printedTailLowAbsInput] using hE
  have hExp := printedTailExpPrefix_le_182 hLnonneg hLbd m
  simpa [m, x] using hE'.trans hExp

private theorem printedTailEAbsPointSum_x2_prefix_le_of_P_le
    {a : Nat} {μ : List Nat} {m : Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) (hpm : printedTailP a ≤ m) :
    (∑ s ∈ Finset.range (m + 1),
      printedTailEAbsCoeff μ a s * (printedTailX2 a)^s) ≤
        182 := by
  let x := printedTailX2 a
  have hx : 0 ≤ x := by simpa [x] using printedTailX2_nonneg ha
  have hLprefix :=
    printedTailLowAbsInput_point_prefix_le_LPointSum_of_P_le
      (a := a) (μ := μ) (x := x) (m := m) hμ hpm
  have hLbd :
      (∑ r ∈ Finset.range (m + 1), x^r * printedTailLowAbsInput μ a r)
        ≤ 26 / 5 :=
    hLprefix.trans (by
      simpa [x] using
        (printedTailLPointSum_x2_le (a := a) (μ := μ) ha hμ))
  have hLnonneg :
      0 ≤ ∑ r ∈ Finset.range (m + 1), x^r * printedTailLowAbsInput μ a r := by
    exact Finset.sum_nonneg fun r _ =>
      mul_nonneg (pow_nonneg hx r)
        (printedTailLowAbsInput_nonneg μ a r)
  have hE := expCoeff_point_sum_le_expPrefix
    (L := printedTailLowAbsInput μ a)
    (printedTailLowAbsInput_zero μ a)
    (printedTailLowAbsInput_nonneg μ a) (x := x) hx m
  have hE' :
      (∑ s ∈ Finset.range (m + 1),
        printedTailEAbsCoeff μ a s * x^s)
        ≤ printedTailExpPrefix
            (∑ r ∈ Finset.range (m + 1),
              x^r * printedTailLowAbsInput μ a r) m := by
    simpa [printedTailEAbsCoeff, printedTailLowAbsInput] using hE
  have hExp := printedTailExpPrefix_le_182 hLnonneg hLbd m
  simpa [x] using hE'.trans hExp

private theorem printedTailEAbsDerivPointSum_x2_le
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    (∑ s ∈ Finset.range (printedTailR0 a + 1),
      (s : ℚ) * printedTailEAbsCoeff μ a s * (printedTailX2 a)^s) ≤
        (182 : ℚ) * (11 / 2) := by
  let m := printedTailR0 a
  let x := printedTailX2 a
  have hx : 0 ≤ x := by simpa [x] using printedTailX2_nonneg ha
  have hm : m ≤ printedTailP a := by
    simpa [m] using printedTailR0_le_P a
  have hLprefix :=
    printedTailLowAbsInput_point_prefix_le_LPointSum
      (a := a) (μ := μ) (x := x) (m := m) hμ hx hm
  have hLbd :
      (∑ r ∈ Finset.range (m + 1), x^r * printedTailLowAbsInput μ a r)
        ≤ 26 / 5 :=
    hLprefix.trans (by
      simpa [x] using
        (printedTailLPointSum_x2_le (a := a) (μ := μ) ha hμ))
  have hLnonneg :
      0 ≤ ∑ r ∈ Finset.range (m + 1), x^r * printedTailLowAbsInput μ a r := by
    exact Finset.sum_nonneg fun r _ =>
      mul_nonneg (pow_nonneg hx r)
        (printedTailLowAbsInput_nonneg μ a r)
  have hDprefix :=
    printedTailLowAbsInput_deriv_prefix_le_LDerivPointSum
      (a := a) (μ := μ) (x := x) (m := m) hμ hx hm
  have hDbd :
      (∑ r ∈ Finset.range (m + 1),
        (r : ℚ) * (x^r * printedTailLowAbsInput μ a r)) ≤ 11 / 2 :=
    hDprefix.trans (by
      simpa [x] using
        (printedTailLDerivPointSum_x2_le (a := a) (μ := μ) ha hμ))
  have hExpbd := printedTailExpPrefix_le_182 hLnonneg hLbd m
  have hExpnonneg := printedTailExpPrefix_nonneg hLnonneg m
  have hD := expCoeff_deriv_point_sum_le_expPrefix
    (L := printedTailLowAbsInput μ a)
    (printedTailLowAbsInput_zero μ a)
    (printedTailLowAbsInput_nonneg μ a) (x := x) hx m
  have hD' :
      (∑ s ∈ Finset.range (m + 1),
        (s : ℚ) * printedTailEAbsCoeff μ a s * x^s)
        ≤ (∑ r ∈ Finset.range (m + 1),
            (r : ℚ) * (x^r * printedTailLowAbsInput μ a r)) *
          printedTailExpPrefix
            (∑ r ∈ Finset.range (m + 1),
              x^r * printedTailLowAbsInput μ a r) m := by
    simpa [printedTailEAbsCoeff, printedTailLowAbsInput] using hD
  calc
    (∑ s ∈ Finset.range (printedTailR0 a + 1),
      (s : ℚ) * printedTailEAbsCoeff μ a s * (printedTailX2 a)^s)
        =
      ∑ s ∈ Finset.range (m + 1),
        (s : ℚ) * printedTailEAbsCoeff μ a s * x^s := by simp [m, x]
    _ ≤ (∑ r ∈ Finset.range (m + 1),
            (r : ℚ) * (x^r * printedTailLowAbsInput μ a r)) *
          printedTailExpPrefix
            (∑ r ∈ Finset.range (m + 1),
              x^r * printedTailLowAbsInput μ a r) m := hD'
    _ ≤ (11 / 2 : ℚ) * 182 :=
          mul_le_mul hDbd hExpbd hExpnonneg (by norm_num)
    _ = (182 : ℚ) * (11 / 2) := by ring

theorem printedTailWPointMomentBounds_closed :
    PrintedTailWPointMomentBounds := by
  intro a ha μ hμ
  let m := printedTailR0 a
  let x0 := printedTailX0 a
  let x2 := printedTailX2 a
  have hm : m ≤ printedTailP a := by
    simpa [m] using printedTailR0_le_P a
  have hx0 : 0 ≤ x0 := by simpa [x0] using printedTailX0_nonneg ha
  have hx2 : 0 ≤ x2 := by simpa [x2] using printedTailX2_nonneg ha
  have hE0 :
      (∑ s ∈ Finset.range (m + 1),
        printedTailEAbsCoeff μ a s * x0^s) ≤ 203 / 50 := by
    simpa [m, x0] using printedTailEAbsPointSum_x0_le
      (a := a) (μ := μ) ha hμ
  have hEd0 :
      (∑ s ∈ Finset.range (m + 1),
        (s : ℚ) * printedTailEAbsCoeff μ a s * x0^s) ≤
          (203 / 50 : ℚ) * (3 / 2) := by
    simpa [m, x0] using printedTailEAbsDerivPointSum_x0_le
      (a := a) (μ := μ) ha hμ
  have hJ0 :
      (∑ r ∈ Finset.range (m + 1),
        printedTailJAbsCoeff μ a r * x0^r) ≤ 11 / 10 := by
    exact (printedTailJAbsCoeff_point_prefix_le_JPointSum
      (a := a) (μ := μ) (x := x0) (m := m) hx0 hm).trans
        (by
          simpa [x0] using
            (printedTailJPointSum_x0_le (a := a) (μ := μ) ha hμ))
  have hJd0 :
      (∑ r ∈ Finset.range (m + 1),
        (r : ℚ) * printedTailJAbsCoeff μ a r * x0^r) ≤ 11 / 10 := by
    exact (printedTailJAbsCoeff_deriv_prefix_le_JDerivPointSum
      (a := a) (μ := μ) (x := x0) (m := m) hx0 hm).trans
        (by
          simpa [x0] using
            (printedTailJDerivPointSum_x0_le (a := a) (μ := μ) ha hμ))
  have hE2 :
      (∑ s ∈ Finset.range (m + 1),
        printedTailEAbsCoeff μ a s * x2^s) ≤ 182 := by
    simpa [m, x2] using printedTailEAbsPointSum_x2_le
      (a := a) (μ := μ) ha hμ
  have hEd2 :
      (∑ s ∈ Finset.range (m + 1),
        (s : ℚ) * printedTailEAbsCoeff μ a s * x2^s) ≤
          (182 : ℚ) * (11 / 2) := by
    simpa [m, x2] using printedTailEAbsDerivPointSum_x2_le
      (a := a) (μ := μ) ha hμ
  have hJ2 :
      (∑ r ∈ Finset.range (m + 1),
        printedTailJAbsCoeff μ a r * x2^r) ≤ 81 / 20 := by
    exact (printedTailJAbsCoeff_point_prefix_le_JPointSum
      (a := a) (μ := μ) (x := x2) (m := m) hx2 hm).trans
        (by
          simpa [x2] using
            (printedTailJPointSum_x2_le (a := a) (μ := μ) ha hμ))
  have hJd2 :
      (∑ r ∈ Finset.range (m + 1),
        (r : ℚ) * printedTailJAbsCoeff μ a r * x2^r) ≤ 41 / 10 := by
    exact (printedTailJAbsCoeff_deriv_prefix_le_JDerivPointSum
      (a := a) (μ := μ) (x := x2) (m := m) hx2 hm).trans
        (by
          simpa [x2] using
            (printedTailJDerivPointSum_x2_le (a := a) (μ := μ) ha hμ))
  have hE0_nonneg := printedTailEAbsPointPrefix_nonneg μ a hx0 m
  have hEd0_nonneg := printedTailEAbsDerivPrefix_nonneg μ a hx0 m
  have hJ0_nonneg := printedTailJAbsPointPrefix_nonneg μ a hx0 m
  have hJd0_nonneg := printedTailJAbsDerivPrefix_nonneg μ a hx0 m
  have hE2_nonneg := printedTailEAbsPointPrefix_nonneg μ a hx2 m
  have hEd2_nonneg := printedTailEAbsDerivPrefix_nonneg μ a hx2 m
  have hJ2_nonneg := printedTailJAbsPointPrefix_nonneg μ a hx2 m
  have hJd2_nonneg := printedTailJAbsDerivPrefix_nonneg μ a hx2 m
  have hJ0_factor_nonneg :
      0 ≤ 1 + ∑ r ∈ Finset.range (m + 1),
        printedTailJAbsCoeff μ a r * x0^r := by linarith
  have hJ2_factor_nonneg :
      0 ≤ 1 + ∑ r ∈ Finset.range (m + 1),
        printedTailJAbsCoeff μ a r * x2^r := by linarith
  have hJ0_factor_le :
      1 + ∑ r ∈ Finset.range (m + 1),
        printedTailJAbsCoeff μ a r * x0^r ≤ 1 + 11 / 10 := by
    linarith
  have hJ2_factor_le :
      1 + ∑ r ∈ Finset.range (m + 1),
        printedTailJAbsCoeff μ a r * x2^r ≤ 1 + 81 / 20 := by
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hW := printedTailW_point_sum_le_product μ a (x := x0) hx0 m
    have hprod :
        (∑ s ∈ Finset.range (m + 1),
          printedTailEAbsCoeff μ a s * x0^s) *
            (1 + ∑ r ∈ Finset.range (m + 1),
              printedTailJAbsCoeff μ a r * x0^r)
          ≤ (203 / 50 : ℚ) * (1 + 11 / 10) :=
      mul_le_mul hE0 hJ0_factor_le hJ0_factor_nonneg (by norm_num)
    calc
      (∑ s ∈ Finset.range (printedTailR0 a + 1),
        printedTailWAbsCoeff μ a s * (printedTailX0 a)^s)
          =
        ∑ s ∈ Finset.range (m + 1),
          printedTailWAbsCoeff μ a s * x0^s := by simp [m, x0]
      _ ≤ (∑ s ∈ Finset.range (m + 1),
          printedTailEAbsCoeff μ a s * x0^s) *
          (1 + ∑ r ∈ Finset.range (m + 1),
            printedTailJAbsCoeff μ a r * x0^r) := hW
      _ ≤ (203 / 50 : ℚ) * (1 + 11 / 10) := hprod
      _ = (203 / 50 : ℚ) * (21 / 10) := by norm_num
  · have hW := printedTailW_deriv_point_sum_le_product μ a (x := x0) hx0 m
    have hterm1 :
        (∑ s ∈ Finset.range (m + 1),
          (s : ℚ) * printedTailEAbsCoeff μ a s * x0^s) *
            (1 + ∑ r ∈ Finset.range (m + 1),
              printedTailJAbsCoeff μ a r * x0^r)
          ≤ ((203 / 50 : ℚ) * (3 / 2)) * (1 + 11 / 10) :=
      mul_le_mul hEd0 hJ0_factor_le hJ0_factor_nonneg (by norm_num)
    have hterm2 :
        (∑ s ∈ Finset.range (m + 1),
          printedTailEAbsCoeff μ a s * x0^s) *
            (∑ r ∈ Finset.range (m + 1),
              (r : ℚ) * printedTailJAbsCoeff μ a r * x0^r)
          ≤ (203 / 50 : ℚ) * (11 / 10) :=
      mul_le_mul hE0 hJd0 hJd0_nonneg (by norm_num)
    calc
      (∑ s ∈ Finset.range (printedTailR0 a + 1),
        (s : ℚ) * printedTailWAbsCoeff μ a s * (printedTailX0 a)^s)
          =
        ∑ s ∈ Finset.range (m + 1),
          (s : ℚ) * printedTailWAbsCoeff μ a s * x0^s := by simp [m, x0]
      _ ≤ (∑ s ∈ Finset.range (m + 1),
          (s : ℚ) * printedTailEAbsCoeff μ a s * x0^s) *
            (1 + ∑ r ∈ Finset.range (m + 1),
              printedTailJAbsCoeff μ a r * x0^r) +
          (∑ s ∈ Finset.range (m + 1),
            printedTailEAbsCoeff μ a s * x0^s) *
            (∑ r ∈ Finset.range (m + 1),
              (r : ℚ) * printedTailJAbsCoeff μ a r * x0^r) := hW
      _ ≤ ((203 / 50 : ℚ) * (3 / 2)) * (1 + 11 / 10) +
          (203 / 50 : ℚ) * (11 / 10) := add_le_add hterm1 hterm2
      _ = (203 / 50 : ℚ) * (17 / 4) := by norm_num
  · have hW := printedTailW_point_sum_le_product μ a (x := x2) hx2 m
    have hprod :
        (∑ s ∈ Finset.range (m + 1),
          printedTailEAbsCoeff μ a s * x2^s) *
            (1 + ∑ r ∈ Finset.range (m + 1),
              printedTailJAbsCoeff μ a r * x2^r)
          ≤ (182 : ℚ) * (1 + 81 / 20) :=
      mul_le_mul hE2 hJ2_factor_le hJ2_factor_nonneg (by norm_num)
    calc
      (∑ s ∈ Finset.range (printedTailR0 a + 1),
        printedTailWAbsCoeff μ a s * (printedTailX2 a)^s)
          =
        ∑ s ∈ Finset.range (m + 1),
          printedTailWAbsCoeff μ a s * x2^s := by simp [m, x2]
      _ ≤ (∑ s ∈ Finset.range (m + 1),
          printedTailEAbsCoeff μ a s * x2^s) *
          (1 + ∑ r ∈ Finset.range (m + 1),
            printedTailJAbsCoeff μ a r * x2^r) := hW
      _ ≤ (182 : ℚ) * (1 + 81 / 20) := hprod
      _ = (182 : ℚ) * (101 / 20) := by norm_num
  · have hW := printedTailW_deriv_point_sum_le_product μ a (x := x2) hx2 m
    have hterm1 :
        (∑ s ∈ Finset.range (m + 1),
          (s : ℚ) * printedTailEAbsCoeff μ a s * x2^s) *
            (1 + ∑ r ∈ Finset.range (m + 1),
              printedTailJAbsCoeff μ a r * x2^r)
          ≤ ((182 : ℚ) * (11 / 2)) * (1 + 81 / 20) :=
      mul_le_mul hEd2 hJ2_factor_le hJ2_factor_nonneg (by norm_num)
    have hterm2 :
        (∑ s ∈ Finset.range (m + 1),
          printedTailEAbsCoeff μ a s * x2^s) *
            (∑ r ∈ Finset.range (m + 1),
              (r : ℚ) * printedTailJAbsCoeff μ a r * x2^r)
          ≤ (182 : ℚ) * (41 / 10) :=
      mul_le_mul hE2 hJd2 hJd2_nonneg (by norm_num)
    calc
      (∑ s ∈ Finset.range (printedTailR0 a + 1),
        (s : ℚ) * printedTailWAbsCoeff μ a s * (printedTailX2 a)^s)
          =
        ∑ s ∈ Finset.range (m + 1),
          (s : ℚ) * printedTailWAbsCoeff μ a s * x2^s := by simp [m, x2]
      _ ≤ (∑ s ∈ Finset.range (m + 1),
          (s : ℚ) * printedTailEAbsCoeff μ a s * x2^s) *
            (1 + ∑ r ∈ Finset.range (m + 1),
              printedTailJAbsCoeff μ a r * x2^r) +
          (∑ s ∈ Finset.range (m + 1),
            printedTailEAbsCoeff μ a s * x2^s) *
            (∑ r ∈ Finset.range (m + 1),
              (r : ℚ) * printedTailJAbsCoeff μ a r * x2^r) := hW
      _ ≤ ((182 : ℚ) * (11 / 2)) * (1 + 81 / 20) +
          (182 : ℚ) * (41 / 10) := add_le_add hterm1 hterm2
      _ = (182 : ℚ) * (255 / 8) := by norm_num

theorem printedTailWPointBoundX2_closed :
    PrintedTailWPointBoundX2 := by
  intro a ha μ hμ
  let x := printedTailX2 a
  have hx : 0 ≤ x := by simpa [x] using printedTailX2_nonneg ha
  have hpa : printedTailP a ≤ a := by
    unfold printedTailP
    omega
  have hE :
      (∑ s ∈ Finset.range (a + 1),
        printedTailEAbsCoeff μ a s * x^s) ≤ 182 := by
    simpa [x] using printedTailEAbsPointSum_x2_prefix_le_of_P_le
      (a := a) (μ := μ) (m := a) ha hμ hpa
  have hJ :
      (∑ r ∈ Finset.range (a + 1),
        printedTailJAbsCoeff μ a r * x^r) ≤ 81 / 20 := by
    exact (printedTailJAbsCoeff_point_prefix_le_JPointSum_of_P_le
      (a := a) (μ := μ) (x := x) (m := a) hpa).trans
        (by
          simpa [x] using
            (printedTailJPointSum_x2_le (a := a) (μ := μ) ha hμ))
  have hJ_nonneg := printedTailJAbsPointPrefix_nonneg μ a hx a
  have hJ_factor_nonneg :
      0 ≤ 1 + ∑ r ∈ Finset.range (a + 1),
        printedTailJAbsCoeff μ a r * x^r := by linarith
  have hJ_factor_le :
      1 + ∑ r ∈ Finset.range (a + 1),
        printedTailJAbsCoeff μ a r * x^r ≤ 1 + 81 / 20 := by
    linarith
  have hW := printedTailW_point_sum_le_product μ a (x := x) hx a
  have hprod :
      (∑ s ∈ Finset.range (a + 1),
        printedTailEAbsCoeff μ a s * x^s) *
          (1 + ∑ r ∈ Finset.range (a + 1),
            printedTailJAbsCoeff μ a r * x^r)
        ≤ (182 : ℚ) * (1 + 81 / 20) :=
    mul_le_mul hE hJ_factor_le hJ_factor_nonneg (by norm_num)
  calc
    (∑ s ∈ Finset.range (a + 1),
      printedTailWAbsCoeff μ a s * (printedTailX2 a)^s)
        =
      ∑ s ∈ Finset.range (a + 1),
        printedTailWAbsCoeff μ a s * x^s := by simp [x]
    _ ≤ (∑ s ∈ Finset.range (a + 1),
        printedTailEAbsCoeff μ a s * x^s) *
        (1 + ∑ r ∈ Finset.range (a + 1),
          printedTailJAbsCoeff μ a r * x^r) := hW
    _ ≤ (182 : ℚ) * (1 + 81 / 20) := hprod
    _ ≤ 920 := by norm_num

/-- Final rational arithmetic for the first absolute-moment budget:
`exp(7/5) < 203/50` and `exp(26/5) < 182` reduce the displayed bound below
`9`. -/
theorem printedTailAbsoluteMoment0_budget :
    (203 / 50 : ℚ) * (21 / 10) +
        (182 : ℚ) * (101 / 20) / (2 : ℚ)^13 < 9 := by
  norm_num

/-- Final rational arithmetic for the weighted absolute-moment budget,
reduced below `18`. -/
theorem printedTailAbsoluteMoment1_budget :
    (203 / 50 : ℚ) * (17 / 4) +
        (182 : ℚ) * (255 / 8) / (2 : ℚ)^13 < 18 := by
  norm_num

/-! ## Endpoint arithmetic for the `x₀` and `x₂` majorants -/

def endpointM : Nat := 6 * 150 - 6

def endpointN : Nat := 150 - 12

def x0Endpoint1 : ℚ :=
  (5 * (endpointM : ℚ)) / (24 * endpointN) +
    (88 * (endpointM : ℚ)) / (125 * endpointN^2)

def x0Endpoint2 : ℚ :=
  (5 * (endpointM : ℚ)) / (24 * endpointN) +
    (36 * (endpointM : ℚ)) / (25 * endpointN^2)

def x0Endpoint3 : ℚ :=
  (endpointM : ℚ) / (6 * endpointN) +
    (11 * (endpointM : ℚ)) / (100 * endpointN^2)

def x0Endpoint4 : ℚ :=
  (endpointM : ℚ) / (6 * endpointN) +
    (72 * (endpointM : ℚ)) / (325 * endpointN^2)

theorem x0Endpoint1_lt : x0Endpoint1 < 7 / 5 := by native_decide

theorem x0Endpoint2_lt : x0Endpoint2 < 3 / 2 := by native_decide

theorem x0Endpoint3_lt : x0Endpoint3 < 11 / 10 := by native_decide

theorem x0Endpoint4_lt : x0Endpoint4 < 11 / 10 := by native_decide

def x2Endpoint1 : ℚ :=
  5 * (149 : ℚ) / 150 +
    (8 * (endpointM : ℚ) / 25) *
      (16 / (150 : ℚ)^2 + 128 / (150 : ℚ)^3 + 1730 / (150 : ℚ)^4)

def x2Endpoint2 : ℚ :=
  5 * (149 : ℚ) / 150 +
    (8 * (endpointM : ℚ) / 25) *
      (32 / (150 : ℚ)^2 + 384 / (150 : ℚ)^3 + 7340 / (150 : ℚ)^4)

def x2Endpoint3 : ℚ :=
  4 * (149 : ℚ) / 150 +
    (8 * (endpointM : ℚ) / 25) *
      (4 / (150 : ℚ)^2 + 16 / (150 : ℚ)^3 + 103 / (150 : ℚ)^4)

def x2Endpoint4 : ℚ :=
  4 * (149 : ℚ) / 150 +
    (8 * (endpointM : ℚ) / 25) *
      (8 / (150 : ℚ)^2 + 48 / (150 : ℚ)^3 + 413 / (150 : ℚ)^4)

theorem x2Endpoint1_lt : x2Endpoint1 < 26 / 5 := by native_decide

theorem x2Endpoint2_lt : x2Endpoint2 < 11 / 2 := by native_decide

theorem x2Endpoint3_lt : x2Endpoint3 < 81 / 20 := by native_decide

theorem x2Endpoint4_lt : x2Endpoint4 < 41 / 10 := by native_decide

end Prop52
