/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Completion bridge for the Proposition 5.2 Gamma tail

This file isolates the remaining Taylor--Gamma truncation theorem.  The
Gamma integration-by-parts lower bound is closed in `GammaIBP.lean`, and the
finite residue arithmetic is closed in `GammaTruncation.lean`.  What remains
is the analytic comparison between the untruncated Gamma expectation and the
finite Taylor-Gamma sum.  We keep that comparison as one explicit interface
so the public theorem surface does not obscure the only open analytic point.
-/

import Prop52.GammaIBP

namespace Prop52

open MeasureTheory

/-- The untruncated Gamma expectation
`E[exp(-L(t_X)) (1 - J(t_X))]` used in the integration-by-parts margin. -/
noncomputable def printedTailWGammaIntegral (μ : List Nat) (a : Nat) : ℝ :=
  ∫ y, Real.exp (-(printedTailLGammaArg μ a y)) *
    (1 - printedTailJReal μ a (1 / (6 * y))) ∂ gammaFullMeasure a

/-- The finite Taylor-Gamma sum, written as the corresponding Gamma
expectation before applying `integral_printedTailWTruncReal_R0_eq_mainSum`. -/
noncomputable def printedTailWTruncGammaIntegral
    (μ : List Nat) (a : Nat) : ℝ :=
  ∫ y, printedTailWTruncReal μ a (printedTailR0 a) y ∂ gammaFullMeasure a

/-- Remaining Taylor--Gamma truncation estimate.

This is the formal version of the absolute-error statement
`|E W(t_X) - sum_{s<=r0} gamma_s omega_s| <= residue pieces`.  The existing
Lean code already proves that these residue pieces fit under the displayed
`truncationResidueRhs`; the missing work is the analytic event split proving
this inequality itself.
-/
def PrintedTailGammaTruncationErrorBound : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      |printedTailWGammaIntegral μ a -
          printedTailWTruncGammaIntegral μ a| ≤
        (truncationResiduePiecesLhs μ a : ℝ)

/-- The closed point/moment certificates imply the rational residue budget
needed after the analytic truncation comparison. -/
theorem truncationResiduePiecesLhs_le_truncationResidueRhs_closed
    {a : Nat} (ha : 150 ≤ a) {μ : List Nat}
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    truncationResiduePiecesLhs μ a ≤ truncationResidueRhs a := by
  exact truncationResiduePiecesLhs_le_truncationResidueRhs
    printedTailWPointBoundX2_closed
    (printedTailAbsoluteMomentBounds_of_majorant
      (printedTailMajorantMomentBounds_of_wPointMomentBounds
        printedTailWPointMomentBounds_closed))
    (a := a) ha (μ := μ) hμ

/-- Once the Taylor--Gamma truncation error is proved, the printed
Gamma/integral lower bound follows from the closed integration-by-parts margin
and the finite residue arithmetic. -/
theorem printedTailGammaIntegralLowerBound_of_truncationError
    (htrunc : PrintedTailGammaTruncationErrorBound) :
    PrintedTailGammaIntegralLowerBound := by
  intro a ha μ hμ
  have hlow :
      9 / (40 * ((a : ℝ) - 2)) ≤ printedTailWGammaIntegral μ a := by
    simpa [printedTailWGammaIntegral] using
      gammaFull_WIntegral_lower (a := a) (μ := μ) ha hμ
  have herr := htrunc a ha μ hμ
  have hresQ := truncationResiduePiecesLhs_le_truncationResidueRhs_closed
    (a := a) ha (μ := μ) hμ
  have hresR :
      (truncationResiduePiecesLhs μ a : ℝ) ≤
        (truncationResidueRhs a : ℝ) := by
    exact_mod_cast hresQ
  have hmain :
      printedTailWTruncGammaIntegral μ a =
        (printedTailMainSum μ a : ℝ) := by
    simpa [printedTailWTruncGammaIntegral] using
      integral_printedTailWTruncReal_R0_eq_mainSum
        (μ := μ) (a := a) ha
  have hupper :
      printedTailWGammaIntegral μ a ≤
        (printedTailMainSum μ a : ℝ) +
          (truncationResidueRhs a : ℝ) := by
    have hdiff :
        printedTailWGammaIntegral μ a -
            printedTailWTruncGammaIntegral μ a ≤
          (truncationResiduePiecesLhs μ a : ℝ) :=
      (le_abs_self _).trans herr
    calc
      printedTailWGammaIntegral μ a
          ≤ printedTailWTruncGammaIntegral μ a +
              (truncationResiduePiecesLhs μ a : ℝ) := by
            linarith
      _ = (printedTailMainSum μ a : ℝ) +
              (truncationResiduePiecesLhs μ a : ℝ) := by
            rw [hmain]
      _ ≤ (printedTailMainSum μ a : ℝ) +
              (truncationResidueRhs a : ℝ) := by
            linarith
  have hreal :
      ((9 / (40 * ((a : ℚ) - 2)) : ℚ) : ℝ) ≤
        ((printedTailMainSum μ a + truncationResidueRhs a : ℚ) : ℝ) := by
    calc
      ((9 / (40 * ((a : ℚ) - 2)) : ℚ) : ℝ)
          = 9 / (40 * ((a : ℝ) - 2)) := by norm_num
      _ ≤ printedTailWGammaIntegral μ a := hlow
      _ ≤ (printedTailMainSum μ a : ℝ) +
            (truncationResidueRhs a : ℝ) := hupper
      _ = ((printedTailMainSum μ a + truncationResidueRhs a : ℚ) : ℝ) := by
            norm_num
  exact (Rat.cast_le (K := ℝ)).mp hreal

end Prop52
