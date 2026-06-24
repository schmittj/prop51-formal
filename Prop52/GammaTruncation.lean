/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Taylor--Gamma truncation bridge for Proposition 5.2

This file collects the finite algebraic pieces of the comparison between the
Gamma expectation in `GammaMeasure.lean` and the printed finite sum
`printedTailMainSum`.  The analytic event estimates live in `GammaTail.lean`;
the coefficient and Gamma-weight estimates live in `GammaMoment.lean`.
-/

import Prop52.GammaTail
import Prop52.GammaMoment

namespace Prop52

open Finset
open MeasureTheory Set
open scoped ENNReal

/-- Finite Taylor polynomial of
`W(t)=E(t)(1-J(t))`, evaluated at `t = 1/(6y)`. -/
noncomputable def printedTailWTruncReal
    (μ : List Nat) (a R : Nat) (y : ℝ) : ℝ :=
  ∑ s ∈ Finset.range (R + 1),
    (printedTailOmegaCoeff μ a s : ℝ) * (1 / (6 * y))^s

theorem integrable_printedTailWTruncReal
    {a R : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hR : R ≤ printedTailP a + 1) :
    Integrable (printedTailWTruncReal μ a R) (gammaFullMeasure a) := by
  unfold printedTailWTruncReal
  refine MeasureTheory.integrable_finset_sum _ ?_
  intro s hs
  have hsle : s ≤ printedTailP a + 1 := by
    have hsR : s < R + 1 := Finset.mem_range.mp hs
    omega
  exact (integrable_invPow_gammaFullMeasure
    (a := a) (r := s) ha hsle).const_mul _

/-- The Gamma expectation of the finite `W`-Taylor polynomial is exactly the
corresponding finite `gammaWeight` sum. -/
theorem integral_printedTailWTruncReal_eq_sum_gammaWeight
    {a R : Nat} (μ : List Nat) (ha : 150 ≤ a)
    (hR : R ≤ printedTailP a + 1) :
    (∫ y, printedTailWTruncReal μ a R y ∂ gammaFullMeasure a) =
      ((∑ s ∈ Finset.range (R + 1),
        gammaWeight a s * printedTailOmegaCoeff μ a s : ℚ) : ℝ) := by
  unfold printedTailWTruncReal
  rw [MeasureTheory.integral_finset_sum]
  · rw [Rat.cast_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hsle : s ≤ printedTailP a + 1 := by
      have hsR : s < R + 1 := Finset.mem_range.mp hs
      omega
    rw [MeasureTheory.integral_const_mul]
    rw [integral_invPow_gammaFullMeasure_eq_gammaMonomialMoment
      (a := a) (r := s) ha hsle]
    rw [gammaMonomialMoment_eq_gammaWeight]
    rw [Rat.cast_mul]
    ring
  · intro s hs
    have hsle : s ≤ printedTailP a + 1 := by
      have hsR : s < R + 1 := Finset.mem_range.mp hs
      omega
    exact (integrable_invPow_gammaFullMeasure
      (a := a) (r := s) ha hsle).const_mul _

/-- Specialization of the finite `W`-polynomial expectation to the prefix
appearing in `printedTailMainSum`. -/
theorem integral_printedTailWTruncReal_R0_eq_mainSum
    {a : Nat} (μ : List Nat) (ha : 150 ≤ a) :
    (∫ y, printedTailWTruncReal μ a (printedTailR0 a) y
        ∂ gammaFullMeasure a) =
      (printedTailMainSum μ a : ℝ) := by
  have hR : printedTailR0 a ≤ printedTailP a + 1 := by
    unfold printedTailR0 printedTailP
    omega
  rw [integral_printedTailWTruncReal_eq_sum_gammaWeight
    (μ := μ) (a := a) (R := printedTailR0 a) ha hR]
  unfold printedTailMainSum
  rw [Prop51.list_range_map_sum]

/-- Termwise absolute majorant for the finite Taylor polynomial of `W`,
valid at any nonnegative evaluation point. -/
theorem abs_printedTailWTruncReal_le_WAbsCoeff_sum
    (μ : List Nat) (a R : Nat) {y : ℝ}
    (hy : 0 ≤ 1 / (6 * y)) :
    |printedTailWTruncReal μ a R y| ≤
      ∑ s ∈ Finset.range (R + 1),
        (printedTailWAbsCoeff μ a s : ℝ) * (1 / (6 * y))^s := by
  unfold printedTailWTruncReal
  calc
    |∑ s ∈ Finset.range (R + 1),
        (printedTailOmegaCoeff μ a s : ℝ) * (1 / (6 * y))^s|
        ≤ ∑ s ∈ Finset.range (R + 1),
            |(printedTailOmegaCoeff μ a s : ℝ) * (1 / (6 * y))^s| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ Finset.range (R + 1),
          (printedTailWAbsCoeff μ a s : ℝ) * (1 / (6 * y))^s := by
        refine Finset.sum_le_sum fun s _hs => ?_
        have homega :
            |(printedTailOmegaCoeff μ a s : ℝ)| ≤
              (printedTailWAbsCoeff μ a s : ℝ) := by
          exact_mod_cast abs_printedTailOmegaCoeff_le_WAbsCoeff μ a s
        have hpow_nonneg : 0 ≤ (1 / (6 * y))^s :=
          pow_nonneg hy s
        have hW_nonneg :
            0 ≤ (printedTailWAbsCoeff μ a s : ℝ) := by
          exact_mod_cast printedTailWAbsCoeff_nonneg μ a s
        rw [abs_mul, abs_of_nonneg hpow_nonneg]
        exact mul_le_mul homega le_rfl hpow_nonneg hW_nonneg

/-- Termwise absolute bound for the finite Taylor polynomial of `W`, keeping
the actual `|omega_s|` coefficients.  This is the form used by the lower-tail
Gamma moment estimates. -/
theorem abs_printedTailWTruncReal_le_absOmega_sum
    (μ : List Nat) (a R : Nat) {y : ℝ}
    (hy : 0 ≤ 1 / (6 * y)) :
    |printedTailWTruncReal μ a R y| ≤
      ∑ s ∈ Finset.range (R + 1),
        (|printedTailOmegaCoeff μ a s| : ℚ) * (1 / (6 * y))^s := by
  unfold printedTailWTruncReal
  calc
    |∑ s ∈ Finset.range (R + 1),
        (printedTailOmegaCoeff μ a s : ℝ) * (1 / (6 * y))^s|
        ≤ ∑ s ∈ Finset.range (R + 1),
            |(printedTailOmegaCoeff μ a s : ℝ) * (1 / (6 * y))^s| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s ∈ Finset.range (R + 1),
          (|printedTailOmegaCoeff μ a s| : ℚ) * (1 / (6 * y))^s := by
        refine Finset.sum_congr rfl fun s _hs => ?_
        have hpow_nonneg : 0 ≤ (1 / (6 * y))^s :=
          pow_nonneg hy s
        rw [abs_mul, abs_of_nonneg hpow_nonneg]
        norm_num

private theorem printedTailX1_eq_half_mul_X2
    {a : Nat} (ha : 150 ≤ a) :
    printedTailX1 a = (1 / 2 : ℚ) * printedTailX2 a := by
  unfold printedTailX1 printedTailX2
  have haQ : (0 : ℚ) < a := by exact_mod_cast (by omega : 0 < a)
  field_simp [(by nlinarith : (3 : ℚ) * a ≠ 0)]

private theorem printedTailX1_pow_le_scaled_X2_pow
    {a s R : Nat} (ha : 150 ≤ a) (hRs : R + 1 ≤ s) :
    (printedTailX1 a)^s ≤
      (1 / 2 : ℚ)^(R + 1) * (printedTailX2 a)^s := by
  have hx2_nonneg : 0 ≤ printedTailX2 a := by
    unfold printedTailX2
    positivity
  rw [printedTailX1_eq_half_mul_X2 (a := a) ha, mul_pow]
  have hhalf :
      (1 / 2 : ℚ)^s ≤ (1 / 2 : ℚ)^(R + 1) :=
    pow_le_pow_of_le_one (by norm_num : (0 : ℚ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℚ) ≤ 1) hRs
  exact mul_le_mul_of_nonneg_right hhalf (pow_nonneg hx2_nonneg s)

private theorem inv_six_mul_le_printedTailX1_of_half_le
    {a : Nat} (ha : 150 ≤ a) {y : ℝ}
    (hy : (a : ℝ) / 2 ≤ y) :
    1 / (6 * y) ≤ (printedTailX1 a : ℝ) := by
  have ha_pos : (0 : ℝ) < a := by
    exact_mod_cast (by omega : 0 < a)
  have hy_pos : 0 < y := by nlinarith
  have hden_pos : 0 < 3 * (a : ℝ) := by nlinarith
  have hden_le : 3 * (a : ℝ) ≤ 6 * y := by nlinarith
  have hx1_cast : (printedTailX1 a : ℝ) = 1 / (3 * (a : ℝ)) := by
    unfold printedTailX1
    norm_num
  rw [hx1_cast]
  exact one_div_le_one_div_of_le hden_pos hden_le

private theorem printedTailWTruncReal_a_sub_R0_eq_tail
    {a : Nat} (ha : 150 ≤ a) (μ : List Nat) (y : ℝ) :
    printedTailWTruncReal μ a a y -
        printedTailWTruncReal μ a (printedTailR0 a) y =
      ∑ s ∈ (Finset.range (a + 1)).filter
          (fun s : Nat => printedTailR0 a + 1 ≤ s),
        (printedTailOmegaCoeff μ a s : ℝ) * (1 / (6 * y))^s := by
  have hsubset :
      Finset.range (printedTailR0 a + 1) ⊆ Finset.range (a + 1) := by
    intro s hs
    have hslt : s < printedTailR0 a + 1 := Finset.mem_range.mp hs
    unfold printedTailR0 printedTailP at hslt
    exact Finset.mem_range.mpr (by omega)
  unfold printedTailWTruncReal
  rw [← Finset.sum_sdiff hsubset]
  have hsdiff :
      Finset.range (a + 1) \ Finset.range (printedTailR0 a + 1) =
        (Finset.range (a + 1)).filter
          (fun s : Nat => printedTailR0 a + 1 ≤ s) := by
    ext s
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_filter]
    omega
  rw [hsdiff]
  abel

/-- On the upper event `y >= a/2`, the finite Taylor tail between the
degree-`a` polynomial and the retained `r0` prefix is bounded by the `x1`
coefficient tail.  This is the finite-window part of the Taylor--Gamma
event split; the separate analytic issue is whether the full function `W`
can be replaced by its degree-`a` window. -/
theorem abs_printedTailWTruncReal_a_sub_R0_le_x1_tail
    {a : Nat} (ha : 150 ≤ a) (μ : List Nat) {y : ℝ}
    (hy : (a : ℝ) / 2 ≤ y) :
    |printedTailWTruncReal μ a a y -
        printedTailWTruncReal μ a (printedTailR0 a) y| ≤
      ((∑ s ∈ (Finset.range (a + 1)).filter
          (fun s : Nat => printedTailR0 a + 1 ≤ s),
        printedTailWAbsCoeff μ a s * (printedTailX1 a)^s : ℚ) : ℝ) := by
  have ht_nonneg : 0 ≤ 1 / (6 * y) := by
    have ha_pos : (0 : ℝ) < a := by
      exact_mod_cast (by omega : 0 < a)
    have hy_pos : 0 < y := by nlinarith
    positivity
  have ht_le : 1 / (6 * y) ≤ (printedTailX1 a : ℝ) :=
    inv_six_mul_le_printedTailX1_of_half_le (a := a) ha hy
  rw [printedTailWTruncReal_a_sub_R0_eq_tail (a := a) ha μ y]
  calc
    |∑ s ∈ (Finset.range (a + 1)).filter
          (fun s : Nat => printedTailR0 a + 1 ≤ s),
        (printedTailOmegaCoeff μ a s : ℝ) * (1 / (6 * y))^s|
        ≤ ∑ s ∈ (Finset.range (a + 1)).filter
          (fun s : Nat => printedTailR0 a + 1 ≤ s),
            |(printedTailOmegaCoeff μ a s : ℝ) * (1 / (6 * y))^s| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ (Finset.range (a + 1)).filter
          (fun s : Nat => printedTailR0 a + 1 ≤ s),
            (printedTailWAbsCoeff μ a s : ℝ) *
              (printedTailX1 a : ℝ)^s := by
          refine Finset.sum_le_sum fun s _hs => ?_
          have homega :
              |(printedTailOmegaCoeff μ a s : ℝ)| ≤
                (printedTailWAbsCoeff μ a s : ℝ) := by
            exact_mod_cast abs_printedTailOmegaCoeff_le_WAbsCoeff μ a s
          have hpow :
              (1 / (6 * y))^s ≤ (printedTailX1 a : ℝ)^s :=
            pow_le_pow_left₀ ht_nonneg ht_le s
          have hpow_nonneg : 0 ≤ (1 / (6 * y))^s :=
            pow_nonneg ht_nonneg s
          have hW_nonneg :
              0 ≤ (printedTailWAbsCoeff μ a s : ℝ) := by
            exact_mod_cast printedTailWAbsCoeff_nonneg μ a s
          rw [abs_mul, abs_of_nonneg hpow_nonneg]
          exact mul_le_mul homega hpow hpow_nonneg hW_nonneg
    _ =
      ((∑ s ∈ (Finset.range (a + 1)).filter
          (fun s : Nat => printedTailR0 a + 1 ≤ s),
        printedTailWAbsCoeff μ a s * (printedTailX1 a)^s : ℚ) : ℝ) := by
          rw [Rat.cast_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Rat.cast_mul, Rat.cast_pow]

/-- Upper-event coefficient tail used for the first term of
`truncationResidueRhs`: on `X >= a/2`, one has `t_X <= x1 = x2/2`, so the
majorant tail after `r0` is controlled by the `x2` point certificate. -/
theorem printedTailWAbsCoeff_x1_tail_le_residue_term
    (hpoint : PrintedTailWPointBoundX2)
    {a : Nat} (ha : 150 ≤ a) {μ : List Nat}
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    (∑ s ∈ (Finset.range (a + 1)).filter
        (fun s : Nat => printedTailR0 a + 1 ≤ s),
        printedTailWAbsCoeff μ a s * (printedTailX1 a)^s)
      ≤ 920 / (2 : ℚ)^(printedTailR0 a + 1) := by
  let C : ℚ := (1 / 2 : ℚ)^(printedTailR0 a + 1)
  have hterm :
      (∑ s ∈ (Finset.range (a + 1)).filter
          (fun s : Nat => printedTailR0 a + 1 ≤ s),
          printedTailWAbsCoeff μ a s * (printedTailX1 a)^s)
        ≤
      ∑ s ∈ (Finset.range (a + 1)).filter
          (fun s : Nat => printedTailR0 a + 1 ≤ s),
          C * (printedTailWAbsCoeff μ a s * (printedTailX2 a)^s) := by
    refine Finset.sum_le_sum fun s hs => ?_
    have hRs : printedTailR0 a + 1 ≤ s :=
      (Finset.mem_filter.mp hs).2
    have hW : 0 ≤ printedTailWAbsCoeff μ a s :=
      printedTailWAbsCoeff_nonneg μ a s
    have hx1 :=
      printedTailX1_pow_le_scaled_X2_pow
        (a := a) (s := s) (R := printedTailR0 a) ha hRs
    calc
      printedTailWAbsCoeff μ a s * (printedTailX1 a)^s
          ≤ printedTailWAbsCoeff μ a s *
              (C * (printedTailX2 a)^s) :=
            mul_le_mul_of_nonneg_left hx1 hW
      _ = C * (printedTailWAbsCoeff μ a s * (printedTailX2 a)^s) := by
            dsimp [C]
            ring
  have hsubset :
      (Finset.range (a + 1)).filter
          (fun s : Nat => printedTailR0 a + 1 ≤ s) ⊆
        Finset.range (a + 1) := by
    intro s hs
    exact (Finset.mem_filter.mp hs).1
  have hx2_nonneg : 0 ≤ printedTailX2 a := by
    unfold printedTailX2
    positivity
  have hpoint_subset :
      (∑ s ∈ (Finset.range (a + 1)).filter
          (fun s : Nat => printedTailR0 a + 1 ≤ s),
          printedTailWAbsCoeff μ a s * (printedTailX2 a)^s)
        ≤ ∑ s ∈ Finset.range (a + 1),
          printedTailWAbsCoeff μ a s * (printedTailX2 a)^s :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (by
        intro s _hs _hnot
        exact mul_nonneg (printedTailWAbsCoeff_nonneg μ a s)
          (pow_nonneg hx2_nonneg s))
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  calc
    (∑ s ∈ (Finset.range (a + 1)).filter
        (fun s : Nat => printedTailR0 a + 1 ≤ s),
        printedTailWAbsCoeff μ a s * (printedTailX1 a)^s)
        ≤ ∑ s ∈ (Finset.range (a + 1)).filter
          (fun s : Nat => printedTailR0 a + 1 ≤ s),
          C * (printedTailWAbsCoeff μ a s * (printedTailX2 a)^s) := hterm
    _ = C * (∑ s ∈ (Finset.range (a + 1)).filter
          (fun s : Nat => printedTailR0 a + 1 ≤ s),
          printedTailWAbsCoeff μ a s * (printedTailX2 a)^s) := by
          rw [Finset.mul_sum]
    _ ≤ C * 920 :=
          mul_le_mul_of_nonneg_left
            (hpoint_subset.trans (hpoint a ha μ hμ)) hC_nonneg
    _ = 920 / (2 : ℚ)^(printedTailR0 a + 1) := by
          dsimp [C]
          rw [one_div_pow]
          ring

/-- Pointwise upper-event finite-window tail bound in the displayed residue
constant form. -/
theorem abs_printedTailWTruncReal_a_sub_R0_le_residue_term
    (hpoint : PrintedTailWPointBoundX2)
    {a : Nat} (ha : 150 ≤ a) {μ : List Nat}
    (hμ : Prop51.IsPartitionOf μ (M a)) {y : ℝ}
    (hy : (a : ℝ) / 2 ≤ y) :
    |printedTailWTruncReal μ a a y -
        printedTailWTruncReal μ a (printedTailR0 a) y| ≤
      ((920 / (2 : ℚ)^(printedTailR0 a + 1) : ℚ) : ℝ) := by
  have htail := abs_printedTailWTruncReal_a_sub_R0_le_x1_tail
    (a := a) ha μ hy
  have hbudget := printedTailWAbsCoeff_x1_tail_le_residue_term
    hpoint (a := a) ha (μ := μ) hμ
  exact htail.trans (by exact_mod_cast hbudget)

/-- Closed pointwise upper-event finite-window tail bound using the proved
`x₂` point certificate. -/
theorem abs_printedTailWTruncReal_a_sub_R0_le_residue_term_closed
    {a : Nat} (ha : 150 ≤ a) {μ : List Nat}
    (hμ : Prop51.IsPartitionOf μ (M a)) {y : ℝ}
    (hy : (a : ℝ) / 2 ≤ y) :
    |printedTailWTruncReal μ a a y -
        printedTailWTruncReal μ a (printedTailR0 a) y| ≤
      ((920 / (2 : ℚ)^(printedTailR0 a + 1) : ℚ) : ℝ) :=
  abs_printedTailWTruncReal_a_sub_R0_le_residue_term
    printedTailWPointBoundX2_closed (a := a) ha (μ := μ) hμ hy

/-- Low-index part of the lower-tail event, after the Chernoff probability
factor has been pulled out.  This is the finite algebraic companion to
`gammaFullMeasure_shifted_Iio_half_le_nine_tenths_pow`. -/
theorem gammaWeight_absOmega_low_tail_le_residue_term
    (hmom : PrintedTailAbsoluteMomentBounds)
    {a : Nat} (ha : 150 ≤ a) {μ : List Nat}
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    (∑ s ∈ (Finset.range (printedTailR0 a + 1)).filter
        (fun s : Nat => s ≤ a / 8),
        gammaWeight a s * |printedTailOmegaCoeff μ a s|) *
        (9 / 10 : ℚ)^(a - a / 8)
      ≤ 9 * (9 / 10 : ℚ)^(a - a / 8) := by
  have hsubset :
      (Finset.range (printedTailR0 a + 1)).filter
          (fun s : Nat => s ≤ a / 8) ⊆
        Finset.range (printedTailR0 a + 1) := by
    intro s hs
    exact (Finset.mem_filter.mp hs).1
  have hsum_subset :
      (∑ s ∈ (Finset.range (printedTailR0 a + 1)).filter
          (fun s : Nat => s ≤ a / 8),
          gammaWeight a s * |printedTailOmegaCoeff μ a s|)
        ≤ ∑ s ∈ Finset.range (printedTailR0 a + 1),
          gammaWeight a s * |printedTailOmegaCoeff μ a s| :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (by
        intro s hs _hnot
        have hgamma_nonneg : 0 ≤ gammaWeight a s := by
          unfold gammaWeight
          positivity
        exact mul_nonneg hgamma_nonneg (abs_nonneg _))
  have hmom0 := (hmom a ha μ hμ).1
  have hfactor_nonneg : 0 ≤ (9 / 10 : ℚ)^(a - a / 8) := by
    positivity
  exact mul_le_mul_of_nonneg_right
    (hsum_subset.trans hmom0) hfactor_nonneg

/-- Integral lower-event bound for the retained `W_{\le r0}` Taylor
polynomial.  The terms with `s <= a/8` use the shifted Gamma lower-tail
probability, while the terms with `s > a/8` are bounded by their full Gamma
moments. -/
theorem integral_abs_printedTailWTruncReal_R0_lower_event_le_residue_terms
    {a : Nat} (ha : 150 ≤ a) (μ : List Nat) :
    (∫ y in Set.Iio ((a : ℝ) / 2),
        |printedTailWTruncReal μ a (printedTailR0 a) y|
          ∂ gammaFullMeasure a) ≤
      (((∑ s ∈ (Finset.range (printedTailR0 a + 1)).filter
          (fun s : Nat => s ≤ a / 8),
          gammaWeight a s * |printedTailOmegaCoeff μ a s|) *
          (9 / 10 : ℚ)^(a - a / 8) +
        (∑ s ∈ (Finset.range (printedTailR0 a + 1)).filter
          (fun s : Nat => a / 8 + 1 ≤ s),
          gammaWeight a s * |printedTailOmegaCoeff μ a s|) : ℚ) : ℝ) := by
  let S : Set ℝ := Set.Iio ((a : ℝ) / 2)
  let T : Finset Nat := Finset.range (printedTailR0 a + 1)
  let G : Nat → ℚ := fun s =>
    gammaWeight a s * |printedTailOmegaCoeff μ a s|
  let F : ℚ := (9 / 10 : ℚ)^(a - a / 8)
  have hRle : printedTailR0 a ≤ printedTailP a + 1 := by
    unfold printedTailR0 printedTailP
    omega
  have hmono :
      (fun y => |printedTailWTruncReal μ a (printedTailR0 a) y|) ≤ᵐ[gammaFullMeasure a]
        fun y => ∑ s ∈ T,
          ((|printedTailOmegaCoeff μ a s| : ℚ) : ℝ) *
            (1 / (6 * y))^s := by
    filter_upwards [ae_nonneg_gammaFullMeasure a] with y hy_nonneg
    have ht_nonneg : 0 ≤ 1 / (6 * y) := by positivity
    simpa [T] using
      abs_printedTailWTruncReal_le_absOmega_sum
        (μ := μ) (a := a) (R := printedTailR0 a) ht_nonneg
  have hleft_int :
      IntegrableOn
        (fun y => |printedTailWTruncReal μ a (printedTailR0 a) y|)
        S (gammaFullMeasure a) := by
    exact ((integrable_printedTailWTruncReal
      (a := a) (R := printedTailR0 a) (μ := μ) ha hRle).abs).integrableOn
  have hright_int :
      IntegrableOn
        (fun y => ∑ s ∈ T,
          ((|printedTailOmegaCoeff μ a s| : ℚ) : ℝ) *
            (1 / (6 * y))^s)
        S (gammaFullMeasure a) := by
    refine (MeasureTheory.integrable_finset_sum T ?_).integrableOn
    intro s hs
    have hsle : s ≤ printedTailP a + 1 := by
      have hsR : s < printedTailR0 a + 1 := by
        simpa [T] using Finset.mem_range.mp hs
      omega
    exact (integrable_invPow_gammaFullMeasure
      (a := a) (r := s) ha hsle).const_mul _
  have hpoint_integral :
      (∫ y in S, |printedTailWTruncReal μ a (printedTailR0 a) y|
          ∂ gammaFullMeasure a) ≤
        ∫ y in S, (∑ s ∈ T,
          ((|printedTailOmegaCoeff μ a s| : ℚ) : ℝ) *
            (1 / (6 * y))^s) ∂ gammaFullMeasure a :=
    MeasureTheory.setIntegral_mono_ae
      hleft_int hright_int hmono
  have hsum_eval :
      (∫ y in S, (∑ s ∈ T,
          ((|printedTailOmegaCoeff μ a s| : ℚ) : ℝ) *
            (1 / (6 * y))^s) ∂ gammaFullMeasure a)
        =
        ∑ s ∈ T,
          ∫ y in S,
            ((|printedTailOmegaCoeff μ a s| : ℚ) : ℝ) *
              (1 / (6 * y))^s ∂ gammaFullMeasure a := by
    rw [MeasureTheory.integral_finset_sum]
    intro s hs
    have hsle : s ≤ printedTailP a + 1 := by
      have hsR : s < printedTailR0 a + 1 := by
        simpa [T] using Finset.mem_range.mp hs
      omega
    exact ((integrable_invPow_gammaFullMeasure
      (a := a) (r := s) ha hsle).const_mul _).integrableOn.integrable
  have hterm :
      (∑ s ∈ T,
          ∫ y in S,
            ((|printedTailOmegaCoeff μ a s| : ℚ) : ℝ) *
              (1 / (6 * y))^s ∂ gammaFullMeasure a)
        ≤
        ∑ s ∈ T,
          if s ≤ a / 8 then
            (G s : ℝ) * (F : ℝ)
          else
            (G s : ℝ) := by
    refine Finset.sum_le_sum fun s hs => ?_
    have hsleR0 : s ≤ printedTailR0 a := by
      have hslt : s < printedTailR0 a + 1 := by
        simpa [T] using Finset.mem_range.mp hs
      omega
    have hslt : s < a := by
      unfold printedTailR0 printedTailP at hsleR0
      omega
    have hsleP : s ≤ printedTailP a + 1 := by omega
    have hcoeff_nonneg :
        0 ≤ (((|printedTailOmegaCoeff μ a s| : ℚ) : ℝ)) := by
      exact_mod_cast (abs_nonneg (printedTailOmegaCoeff μ a s))
    by_cases hslow : s ≤ a / 8
    · have hprob :=
        gammaFullMeasure_shifted_Iio_half_le_nine_tenths_pow
          (a := a) (s := s) ha hslow
      have hprobR :
          (gammaFullMeasure (a - s) S).toReal ≤ (F : ℝ) := by
        have hF_nonneg : 0 ≤ (F : ℝ) := by
          dsimp [F]
          positivity
        have hprob' :
            gammaFullMeasure (a - s) S ≤ ENNReal.ofReal (F : ℝ) := by
          simpa [S, F, Rat.cast_pow] using hprob
        exact ENNReal.toReal_le_of_le_ofReal hF_nonneg hprob'
      have hweight_nonneg : 0 ≤ (gammaWeight a s : ℝ) := by
        unfold gammaWeight
        positivity
      calc
        (∫ y in S,
            ((|printedTailOmegaCoeff μ a s| : ℚ) : ℝ) *
              (1 / (6 * y))^s ∂ gammaFullMeasure a)
            =
          ((|printedTailOmegaCoeff μ a s| : ℚ) : ℝ) *
            ∫ y in S, (1 / (6 * y))^s ∂ gammaFullMeasure a := by
            rw [MeasureTheory.integral_const_mul]
        _ =
          ((|printedTailOmegaCoeff μ a s| : ℚ) : ℝ) *
            ((gammaWeight a s : ℝ) *
              (gammaFullMeasure (a - s) S).toReal) := by
            rw [setIntegral_invPow_gammaFullMeasure_Iio_eq_gammaWeight_mul_shifted
              (a := a) (s := s) ha hslt ((a : ℝ) / 2)]
        _ ≤
          ((|printedTailOmegaCoeff μ a s| : ℚ) : ℝ) *
            ((gammaWeight a s : ℝ) * (F : ℝ)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hprobR hweight_nonneg)
              hcoeff_nonneg
        _ = (G s : ℝ) * (F : ℝ) := by
            dsimp [G]
            norm_num
            ring
        _ = (if s ≤ a / 8 then (G s : ℝ) * (F : ℝ)
            else (G s : ℝ)) := by simp [hslow]
    · have hintegral_nonneg :
          0 ≤ᵐ[gammaFullMeasure a]
            fun y : ℝ => (1 / (6 * y))^s := by
        filter_upwards [ae_nonneg_gammaFullMeasure a] with y hy_nonneg
        have ht_nonneg : 0 ≤ 1 / (6 * y) := by positivity
        exact pow_nonneg ht_nonneg s
      have hset_le :
          (∫ y in S, (1 / (6 * y))^s ∂ gammaFullMeasure a) ≤
            ∫ y, (1 / (6 * y))^s ∂ gammaFullMeasure a :=
        MeasureTheory.setIntegral_le_integral
          (integrable_invPow_gammaFullMeasure
            (a := a) (r := s) ha hsleP) hintegral_nonneg
      calc
        (∫ y in S,
            ((|printedTailOmegaCoeff μ a s| : ℚ) : ℝ) *
              (1 / (6 * y))^s ∂ gammaFullMeasure a)
            =
          ((|printedTailOmegaCoeff μ a s| : ℚ) : ℝ) *
            ∫ y in S, (1 / (6 * y))^s ∂ gammaFullMeasure a := by
            rw [MeasureTheory.integral_const_mul]
        _ ≤
          ((|printedTailOmegaCoeff μ a s| : ℚ) : ℝ) *
            ∫ y, (1 / (6 * y))^s ∂ gammaFullMeasure a :=
            mul_le_mul_of_nonneg_left hset_le hcoeff_nonneg
        _ =
          ((|printedTailOmegaCoeff μ a s| : ℚ) : ℝ) *
            (gammaWeight a s : ℝ) := by
            rw [integral_invPow_gammaFullMeasure_eq_gammaMonomialMoment
              (a := a) (r := s) ha hsleP]
            rw [gammaMonomialMoment_eq_gammaWeight]
        _ = (G s : ℝ) := by
            dsimp [G]
            norm_num
            ring
        _ = (if s ≤ a / 8 then (G s : ℝ) * (F : ℝ)
            else (G s : ℝ)) := by simp [hslow]
  have hsplit :
      (∑ s ∈ T,
          if s ≤ a / 8 then
            (G s : ℝ) * (F : ℝ)
          else
            (G s : ℝ)) =
        ((∑ s ∈ T.filter (fun s : Nat => s ≤ a / 8), G s) * F +
          ∑ s ∈ T.filter (fun s : Nat => a / 8 + 1 ≤ s), G s : ℚ) := by
    have hsum :=
      Finset.sum_filter_add_sum_filter_not
        (s := T) (p := fun s : Nat => s ≤ a / 8)
        (f := fun s : Nat =>
          if s ≤ a / 8 then
            (G s : ℝ) * (F : ℝ)
          else
            (G s : ℝ))
    rw [← hsum]
    rw [Rat.cast_add, Rat.cast_mul, Rat.cast_sum]
    congr 1
    · rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun s hs => ?_
      simp [T] at hs
      simp [hs.2]
    · have hnot_eq :
        T.filter (fun s : Nat => ¬s ≤ a / 8) =
          T.filter (fun s : Nat => a / 8 + 1 ≤ s) := by
        ext s
        simp only [Finset.mem_filter]
        constructor
        · intro h
          exact ⟨h.1, by omega⟩
        · intro h
          exact ⟨h.1, by omega⟩
      rw [hnot_eq, Rat.cast_sum]
      refine Finset.sum_congr rfl fun s hs => ?_
      simp at hs
      simp [hs.2]
  calc
    (∫ y in Set.Iio ((a : ℝ) / 2),
        |printedTailWTruncReal μ a (printedTailR0 a) y|
          ∂ gammaFullMeasure a)
        =
      ∫ y in S, |printedTailWTruncReal μ a (printedTailR0 a) y|
          ∂ gammaFullMeasure a := rfl
    _ ≤
      ∫ y in S, (∑ s ∈ T,
          ((|printedTailOmegaCoeff μ a s| : ℚ) : ℝ) *
            (1 / (6 * y))^s) ∂ gammaFullMeasure a := hpoint_integral
    _ =
      ∑ s ∈ T,
          ∫ y in S,
            ((|printedTailOmegaCoeff μ a s| : ℚ) : ℝ) *
              (1 / (6 * y))^s ∂ gammaFullMeasure a := hsum_eval
    _ ≤
      ∑ s ∈ T,
          if s ≤ a / 8 then
            (G s : ℝ) * (F : ℝ)
          else
            (G s : ℝ) := hterm
    _ =
      (((∑ s ∈ (Finset.range (printedTailR0 a + 1)).filter
          (fun s : Nat => s ≤ a / 8),
          gammaWeight a s * |printedTailOmegaCoeff μ a s|) *
          (9 / 10 : ℚ)^(a - a / 8) +
        (∑ s ∈ (Finset.range (printedTailR0 a + 1)).filter
          (fun s : Nat => a / 8 + 1 ≤ s),
          gammaWeight a s * |printedTailOmegaCoeff μ a s|) : ℚ) : ℝ) := by
        simpa [T, G, F] using hsplit

/-- The four rational residue pieces which remain after the analytic
Taylor--Gamma event split:

* upper-event coefficient tail beyond `r0`,
* the crude lower-event probability term,
* low-index lower-tail monomial terms, and
* high-index lower-tail monomial terms.

The next analytic step is to prove that the real truncation error is bounded
by this finite expression. -/
def truncationResiduePiecesLhs (μ : List Nat) (a : Nat) : ℚ :=
  (∑ s ∈ (Finset.range (a + 1)).filter
      (fun s : Nat => printedTailR0 a + 1 ≤ s),
      printedTailWAbsCoeff μ a s * (printedTailX1 a)^s) +
    2 * (5 / 6 : ℚ)^a +
    ((∑ s ∈ (Finset.range (printedTailR0 a + 1)).filter
        (fun s : Nat => s ≤ a / 8),
        gammaWeight a s * |printedTailOmegaCoeff μ a s|) *
        (9 / 10 : ℚ)^(a - a / 8)) +
    (∑ s ∈ (Finset.range (printedTailR0 a + 1)).filter
        (fun s : Nat => a / 8 + 1 ≤ s),
        gammaWeight a s * |printedTailOmegaCoeff μ a s|)

/-- The finite residue pieces are bounded by the displayed residue budget in
`Printed.lean`.  This theorem is the rational bookkeeping companion to the
event split; it deliberately uses the exact four terms of
`truncationResidueRhs`. -/
theorem truncationResiduePiecesLhs_le_truncationResidueRhs
    (hpoint : PrintedTailWPointBoundX2)
    (hmom : PrintedTailAbsoluteMomentBounds)
    {a : Nat} (ha : 150 ≤ a) {μ : List Nat}
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    truncationResiduePiecesLhs μ a ≤ truncationResidueRhs a := by
  have hupper := printedTailWAbsCoeff_x1_tail_le_residue_term
    hpoint (a := a) ha (μ := μ) hμ
  have hlow := gammaWeight_absOmega_low_tail_le_residue_term
    hmom (a := a) ha (μ := μ) hμ
  have hhigh := gammaWeight_absOmega_high_tail_le_residue_term
    hpoint (a := a) ha (μ := μ) hμ
  have hpieces :
      truncationResiduePiecesLhs μ a ≤
        920 / (2 : ℚ)^(printedTailR0 a + 1) +
          2 * (5 / 6 : ℚ)^a +
          9 * (9 / 10 : ℚ)^(a - a / 8) +
          920 * (a : ℚ) * (3 / 10 : ℚ)^(a / 8 + 1) := by
    unfold truncationResiduePiecesLhs
    nlinarith [hupper, hlow, hhigh]
  have hbudget :
      920 / (2 : ℚ)^(printedTailR0 a + 1) +
          2 * (5 / 6 : ℚ)^a +
          9 * (9 / 10 : ℚ)^(a - a / 8) +
          920 * (a : ℚ) * (3 / 10 : ℚ)^(a / 8 + 1) =
        truncationResidueRhs a := by
    unfold truncationResidueRhs printedTailR0 printedTailP
    ring
  exact hpieces.trans_eq hbudget

end Prop52
