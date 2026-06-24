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

end Prop52
