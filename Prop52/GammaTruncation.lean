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
