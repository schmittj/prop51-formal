/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Public facade for corrected Chen--Larson Proposition 5.2

This is the intended human-facing file for the corrected Proposition 5.2
formalization.  At this stage it exposes the corrected coefficient, the exact
correction identity, executable sanity checks against the `g = 4` example, and
the large-range reduction to the printed-series sign theorem plus the
Proposition 5.1 rectangle theorem.
-/

import Prop52.Statement
import Prop51.Rectangle
import Prop52.Finite
import Prop52.Printed
import Prop52.MidBridge
import Prop52.GammaCompletion

namespace Prop52

/-- The corrected coefficient differs from the printed coefficient by
`(M-1) * [t^a]F_μ(t)`. -/
theorem correctedCoeff_eq_printedCoeff_add (a : Nat) (μ : List Nat) :
    correctedCoeff a μ =
      printedCoeff μ a + ((M a : ℚ) - 1) * Prop51.bCoeff μ a := by
  simp [correctedCoeff, printedCoeff]
  ring

/-- For positive partitions of `M a`, the exponent `N` equals `M a + length`. -/
theorem N_eq_M_add_length {a : Nat} {μ : List Nat}
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    N μ = M a + μ.length := by
  obtain ⟨hsum, _hpos⟩ := hμ
  unfold N
  rw [Prop51.sum_map_add_one, hsum]

/-- A positive partition of `M a` is nonempty once `2 <= a`. -/
theorem one_le_length_of_partition {a : Nat} {μ : List Nat}
    (ha : 2 ≤ a) (hμ : Prop51.IsPartitionOf μ (M a)) :
    1 ≤ μ.length := by
  obtain ⟨hsum, _hpos⟩ := hμ
  rcases μ with - | ⟨m, μ⟩
  · simp [M] at hsum
    omega
  · simp

/-- The Prop52 partition exponent lies in the Prop51 rectangle. -/
theorem rectangle_bounds_of_partition {a : Nat} {μ : List Nat}
    (ha : 2 ≤ a) (hμ : Prop51.IsPartitionOf μ (M a)) :
    6*a - 7 ≤ N μ ∧ N μ ≤ 12*a - 8 := by
  have hN := N_eq_M_add_length hμ
  have hlen_pos := one_le_length_of_partition ha hμ
  obtain ⟨_hsum, hpos⟩ := hμ
  have hlen_le := Prop51.length_le_sum μ hpos
  have hsumM : μ.sum = M a := _hsum
  simp [M] at hN hsumM
  constructor
  · omega
  · omega

/-- Large-range reduction: once the printed-series coefficient is known
negative, corrected Proposition 5.2 is negative by the correction identity and
the Proposition 5.1 rectangle theorem. -/
theorem correctedCoeff_neg_large_of_printed
    (hprinted : PrintedCoeffNegativityLarge) :
    CorrectedCoeffNegativityLarge := by
  intro a ha μ hμ
  have hpart := hμ
  obtain ⟨_hsum, hpos⟩ := hμ
  have hrect := rectangle_bounds_of_partition (a := a) (μ := μ) (by omega) hpart
  have hb : Prop51.bCoeff μ a < 0 :=
    Prop51.bCoeff_neg_of_rectangle μ a (N μ)
      hpos rfl (by omega) hrect.1 hrect.2
  have hp : printedCoeff μ a < 0 := hprinted a ha μ hpart
  have hMpos : 0 < ((M a : ℚ) - 1) := by
    norm_num [M]
    omega
  rw [correctedCoeff_eq_printedCoeff_add]
  nlinarith

/-- Final assembly interface for corrected Proposition 5.2.

The remaining proof work is now concentrated in two independent inputs:

* `hfinite`: the exact finite nonvanishing check for `2 <= a <= 13`;
* `hprinted`: the printed-series sign theorem for `a >= 14`.

Together with the correction identity and the Proposition 5.1 rectangle
theorem, these imply the full corrected nonvanishing statement. -/
theorem correctedCoeff_nonvanishing_of_finite_and_printed
    (hfinite : CorrectedCoeffFiniteNonvanishing)
    (hprinted : PrintedCoeffNegativityLarge) :
    CorrectedCoeffNonvanishing := by
  intro a ha μ hμ
  by_cases hsmall : a ≤ 13
  · exact hfinite a ha hsmall μ hμ
  · have hlarge : correctedCoeff a μ < 0 :=
      correctedCoeff_neg_large_of_printed hprinted a (by omega) μ hμ
    exact ne_of_lt hlarge

/-! The finite input in the preceding assembly theorem is now fully proved in
`Prop52.Finite`, by exact checks for `2 <= a <= 8` and a modular-certificate
lift for `9 <= a <= 13`.  The remaining analytic input for the complete
corrected Proposition 5.2 statement is the printed-series large-range sign
theorem. -/

theorem correctedCoeff_nonvanishing_of_printed
    (hprinted : PrintedCoeffNegativityLarge) :
    CorrectedCoeffNonvanishing :=
  correctedCoeff_nonvanishing_of_finite_and_printed
    correctedCoeff_finite_nonvanishing hprinted

/-- Final assembly after the remaining printed-sign proof has been split into
the interval-certificate range `14 <= a <= 149` and the large-tail range
`a >= 150`. -/
theorem correctedCoeff_nonvanishing_of_printed_mid_tail
    (hmid : PrintedCoeffNegativityMid)
    (htail : PrintedCoeffNegativityTail) :
    CorrectedCoeffNonvanishing :=
  correctedCoeff_nonvanishing_of_printed
    (printedCoeffNegativityLarge_of_mid_tail hmid htail)

/-- Final assembly when the large-tail printed proof is supplied in the
normalized form used by the Gamma/truncation/error argument. -/
theorem correctedCoeff_nonvanishing_of_printed_mid_normalizedTail
    (hmid : PrintedCoeffNegativityMid)
    (htail : PrintedTailNormalizedLowerBound) :
    CorrectedCoeffNonvanishing :=
  correctedCoeff_nonvanishing_of_printed
    (printedCoeffNegativityLarge_of_mid_normalizedTail hmid htail)

/-- Final assembly when the printed large-tail proof is supplied through the
exact low/high split and the three finite normalized error estimates. -/
theorem correctedCoeff_nonvanishing_of_printed_mid_split_errorBounds
    (hmid : PrintedCoeffNegativityMid)
    (hsplit : PrintedTailExactSplit)
    (hmain : PrintedTailMainLowerBound)
    (hh : PrintedTailHErrorBound)
    (hk : PrintedTailKErrorBound)
    (homega : PrintedTailOmegaErrorBound) :
    CorrectedCoeffNonvanishing :=
  correctedCoeff_nonvanishing_of_printed_mid_tail hmid
    (printedCoeffNegativityTail_of_split_errorBounds
      hsplit hmain hh hk homega)

/-- Final assembly after the exact low/high split has been closed in Lean.
The remaining large-tail inputs are precisely the main Gamma lower bound and
the three normalized error estimates. -/
theorem correctedCoeff_nonvanishing_of_printed_mid_errorBounds
    (hmid : PrintedCoeffNegativityMid)
    (hmain : PrintedTailMainLowerBound)
    (hh : PrintedTailHErrorBound)
    (hk : PrintedTailKErrorBound)
    (homega : PrintedTailOmegaErrorBound) :
    CorrectedCoeffNonvanishing :=
  correctedCoeff_nonvanishing_of_printed_mid_tail hmid
    (printedCoeffNegativityTail_of_errorBounds hmain hh hk homega)

/-- Final assembly after replacing the `h`-error estimate by the two
absolute-moment bounds used in the printed proof. -/
theorem correctedCoeff_nonvanishing_of_printed_mid_moments_errorBounds
    (hmid : PrintedCoeffNegativityMid)
    (hmain : PrintedTailMainLowerBound)
    (hmom : PrintedTailAbsoluteMomentBounds)
    (hk : PrintedTailKErrorBound)
    (homega : PrintedTailOmegaErrorBound) :
    CorrectedCoeffNonvanishing :=
  correctedCoeff_nonvanishing_of_printed_mid_errorBounds hmid hmain
    (printedTailHErrorBound_of_absoluteMoments hmom) hk homega

/-- Final assembly after replacing both the `h`- and `k`-error estimates by
the absolute-moment inputs used in the printed proof. -/
theorem correctedCoeff_nonvanishing_of_printed_mid_moments_eMoment_errorBounds
    (hmid : PrintedCoeffNegativityMid)
    (hmain : PrintedTailMainLowerBound)
    (hmom : PrintedTailAbsoluteMomentBounds)
    (he : PrintedTailEAbsoluteMomentBound)
    (homega : PrintedTailOmegaErrorBound) :
    CorrectedCoeffNonvanishing :=
  correctedCoeff_nonvanishing_of_printed_mid_moments_errorBounds hmid hmain
    hmom (printedTailKErrorBound_of_eAbsoluteMoment he) homega

/-- Final assembly using the coefficientwise-positive majorant moment bounds
for `\widehat W` and `\widehat E`, matching the majorant layer of the printed
tail proof. -/
theorem correctedCoeff_nonvanishing_of_printed_mid_majorantMoments_errorBounds
    (hmid : PrintedCoeffNegativityMid)
    (hmain : PrintedTailMainLowerBound)
    (hmaj : PrintedTailMajorantMomentBounds)
    (homega : PrintedTailOmegaErrorBound) :
    CorrectedCoeffNonvanishing :=
  correctedCoeff_nonvanishing_of_printed_mid_moments_eMoment_errorBounds
    hmid hmain
    (printedTailAbsoluteMomentBounds_of_majorant hmaj)
    (printedTailEAbsoluteMomentBound_of_majorant hmaj)
    homega

/-- Final assembly using the printed-proof majorant moment bounds and the
pointwise top-coefficient estimate `|\omega_a| <= 920 (3a/2)^a`.  The
normalization of that pointwise estimate to the `1/a^2` omega error is proved
in `Prop52.Printed`. -/
theorem correctedCoeff_nonvanishing_of_printed_mid_majorantMoments_omegaCoeff
    (hmid : PrintedCoeffNegativityMid)
    (hmain : PrintedTailMainLowerBound)
    (hmaj : PrintedTailMajorantMomentBounds)
    (homegaCoeff : PrintedTailOmegaCoeffMajorant) :
    CorrectedCoeffNonvanishing :=
  correctedCoeff_nonvanishing_of_printed_mid_majorantMoments_errorBounds
    hmid hmain hmaj
    (printedTailOmegaErrorBound_of_coeffMajorant homegaCoeff)

/-- Final assembly using the majorant moment bounds and the finite
`\widehat W(x_2) <= 920` point-bound certificate.  This is the current closest
public tail interface to the printed proof's majorant layer. -/
theorem correctedCoeff_nonvanishing_of_printed_mid_majorantMoments_wPointX2
    (hmid : PrintedCoeffNegativityMid)
    (hmain : PrintedTailMainLowerBound)
    (hmaj : PrintedTailMajorantMomentBounds)
    (hpoint : PrintedTailWPointBoundX2) :
    CorrectedCoeffNonvanishing :=
  correctedCoeff_nonvanishing_of_printed_mid_majorantMoments_omegaCoeff
    hmid hmain hmaj
    (printedTailOmegaCoeffMajorant_of_wPointBoundX2 hpoint)

/-- Final assembly with the printed proof's finite point/derivative majorant
certificates in place of the abstract majorant-moment assumptions. -/
theorem correctedCoeff_nonvanishing_of_printed_mid_wPointMoments_wPointX2
    (hmid : PrintedCoeffNegativityMid)
    (hmain : PrintedTailMainLowerBound)
    (hmomPoint : PrintedTailWPointMomentBounds)
    (hpoint : PrintedTailWPointBoundX2) :
    CorrectedCoeffNonvanishing :=
  correctedCoeff_nonvanishing_of_printed_mid_majorantMoments_wPointX2
    hmid hmain
    (printedTailMajorantMomentBounds_of_wPointMomentBounds hmomPoint)
    hpoint

/-- Final assembly with the main lower estimate supplied in the Gamma/integral
form of the printed proof; the Taylor--Gamma truncation residue is discharged
inside `Prop52.Printed`. -/
theorem correctedCoeff_nonvanishing_of_printed_mid_gammaIntegral_wPointMoments_wPointX2
    (hmid : PrintedCoeffNegativityMid)
    (hgamma : PrintedTailGammaIntegralLowerBound)
    (hmomPoint : PrintedTailWPointMomentBounds)
    (hpoint : PrintedTailWPointBoundX2) :
    CorrectedCoeffNonvanishing :=
  correctedCoeff_nonvanishing_of_printed_mid_wPointMoments_wPointX2
    hmid
    (printedTailMainLowerBound_of_gammaIntegralLowerBound hgamma)
    hmomPoint
    hpoint

/-- Final assembly after the finite point/derivative bounds for
`\widehat W` have been proved from the endpoint estimates in `Prop52.Printed`.
The remaining analytic tail inputs are the mid-range certificate, the
Gamma/integral lower bound, and the finite `x_2` point bound used for the
coefficientwise `omega_a` estimate. -/
theorem correctedCoeff_nonvanishing_of_printed_mid_gammaIntegral_wPointX2
    (hmid : PrintedCoeffNegativityMid)
    (hgamma : PrintedTailGammaIntegralLowerBound)
    (hpoint : PrintedTailWPointBoundX2) :
    CorrectedCoeffNonvanishing :=
  correctedCoeff_nonvanishing_of_printed_mid_gammaIntegral_wPointMoments_wPointX2
    hmid hgamma printedTailWPointMomentBounds_closed hpoint

/-- Final assembly after both finite `\widehat W` point interfaces have been
proved from the endpoint estimates in `Prop52.Printed`.  The remaining
large-tail analytic input is now the Gamma/integral lower bound, together with
the separate mid-range certificate for `14 <= a <= 149`. -/
theorem correctedCoeff_nonvanishing_of_printed_mid_gammaIntegral
    (hmid : PrintedCoeffNegativityMid)
    (hgamma : PrintedTailGammaIntegralLowerBound) :
    CorrectedCoeffNonvanishing :=
  correctedCoeff_nonvanishing_of_printed_mid_gammaIntegral_wPointX2
    hmid hgamma printedTailWPointBoundX2_closed

/-- Public assembly after the mid-range certificate has been closed in Lean.
The only remaining large-tail input is the Gamma/integral lower bound. -/
theorem correctedCoeff_nonvanishing_of_gammaIntegral
    (hgamma : PrintedTailGammaIntegralLowerBound) :
    CorrectedCoeffNonvanishing :=
  correctedCoeff_nonvanishing_of_printed_mid_gammaIntegral
    printedCoeffNegativityMid_closed hgamma

/-- Printed-series negativity for all `a >= 14`, assembled from the closed
mid-range certificate and the Gamma/integral tail lower bound. -/
theorem printedCoeffNegativityLarge_of_gammaIntegral
    (hgamma : PrintedTailGammaIntegralLowerBound) :
    PrintedCoeffNegativityLarge :=
  printedCoeffNegativityLarge_of_mid_tail printedCoeffNegativityMid_closed
    (printedCoeffNegativityTail_of_errorBounds
      (printedTailMainLowerBound_of_gammaIntegralLowerBound hgamma)
      (printedTailHErrorBound_of_absoluteMoments
        (printedTailAbsoluteMomentBounds_of_majorant
          (printedTailMajorantMomentBounds_of_wPointMomentBounds
            printedTailWPointMomentBounds_closed)))
      (printedTailKErrorBound_of_eAbsoluteMoment
        (printedTailEAbsoluteMomentBound_of_majorant
          (printedTailMajorantMomentBounds_of_wPointMomentBounds
            printedTailWPointMomentBounds_closed)))
      (printedTailOmegaErrorBound_of_coeffMajorant
        (printedTailOmegaCoeffMajorant_of_wPointBoundX2
          printedTailWPointBoundX2_closed)))

/-- Large-range strict negativity for the corrected coefficient once the
Gamma/integral lower bound is available. -/
theorem correctedCoeff_neg_of_gammaIntegral
    (hgamma : PrintedTailGammaIntegralLowerBound)
    {a : Nat} (ha : 14 ≤ a)
    {μ : List Nat} (hμ : Prop51.IsPartitionOf μ (M a)) :
    correctedCoeff a μ < 0 :=
  correctedCoeff_neg_large_of_printed
    (printedCoeffNegativityLarge_of_gammaIntegral hgamma)
    a ha μ hμ

/-- Public assembly with the remaining analytic work isolated as the
Taylor--Gamma truncation-error theorem.  The Gamma integration-by-parts lower
bound, residue budget, finite range, mid-range, and Proposition 5.1 rectangle
inputs are all closed in Lean. -/
theorem correctedCoeff_nonvanishing_of_gammaTruncationError
    (htrunc : PrintedTailGammaTruncationErrorBound) :
    CorrectedCoeffNonvanishing :=
  correctedCoeff_nonvanishing_of_gammaIntegral
    (printedTailGammaIntegralLowerBound_of_truncationError htrunc)

/-- Public large-range strict negativity with the remaining analytic work
isolated as the Taylor--Gamma truncation-error theorem. -/
theorem correctedCoeff_neg_of_gammaTruncationError
    (htrunc : PrintedTailGammaTruncationErrorBound)
    {a : Nat} (ha : 14 ≤ a)
    {μ : List Nat} (hμ : Prop51.IsPartitionOf μ (M a)) :
    correctedCoeff a μ < 0 :=
  correctedCoeff_neg_of_gammaIntegral
    (printedTailGammaIntegralLowerBound_of_truncationError htrunc)
    ha hμ

/-- Public assembly from the paper-shaped Taylor--Gamma truncation lemma.
The truncation error is stated directly with the displayed residue budget
`truncationResidueRhs`, so the finite internal residue decomposition remains
hidden from the human-facing theorem surface. -/
theorem correctedCoeff_nonvanishing_of_gammaTruncationResidue
    (htrunc : PrintedTailGammaTruncationResidueBound) :
    CorrectedCoeffNonvanishing :=
  correctedCoeff_nonvanishing_of_gammaIntegral
    (printedTailGammaIntegralLowerBound_of_truncationResidue htrunc)

/-- Large-range strict negativity from the paper-shaped Taylor--Gamma
truncation lemma. -/
theorem correctedCoeff_neg_of_gammaTruncationResidue
    (htrunc : PrintedTailGammaTruncationResidueBound)
    {a : Nat} (ha : 14 ≤ a)
    {μ : List Nat} (hμ : Prop51.IsPartitionOf μ (M a)) :
    correctedCoeff a μ < 0 :=
  correctedCoeff_neg_of_gammaIntegral
    (printedTailGammaIntegralLowerBound_of_truncationResidue htrunc)
    ha hμ

/-- Public assembly with the remaining analytic work reduced to the
paper-shaped upper-event Taylor bound
`|W(t)-W_{\le r0}(t)| <= 920/2^(r0+1)` on `Y >= a/2`.
The lower event, Gamma moments, residue arithmetic, mid-range, small range,
and Proposition 5.1 rectangle input are all closed in Lean. -/
theorem correctedCoeff_nonvanishing_of_upperEventResidue
    (hupper : PrintedTailUpperEventResidueBound) :
    CorrectedCoeffNonvanishing :=
  correctedCoeff_nonvanishing_of_gammaTruncationResidue
    (printedTailGammaTruncationResidueBound_of_upperEvent hupper)

/-- Large-range strict negativity with only the paper-shaped upper-event
Taylor tail left as an input. -/
theorem correctedCoeff_neg_of_upperEventResidue
    (hupper : PrintedTailUpperEventResidueBound)
    {a : Nat} (ha : 14 ≤ a)
    {μ : List Nat} (hμ : Prop51.IsPartitionOf μ (M a)) :
    correctedCoeff a μ < 0 :=
  correctedCoeff_neg_of_gammaTruncationResidue
    (printedTailGammaTruncationResidueBound_of_upperEvent hupper)
    ha hμ

/-- Public assembly with the remaining analytic work reduced to the pointwise
upper-event Taylor tail.  This is the same paper-shaped residue constant as
`correctedCoeff_nonvanishing_of_upperEventResidue`, but before the elementary
integration step over the upper Gamma event. -/
theorem correctedCoeff_nonvanishing_of_upperEventPointwiseResidue
    (hpoint : PrintedTailUpperEventPointwiseResidueBound) :
    CorrectedCoeffNonvanishing :=
  correctedCoeff_nonvanishing_of_upperEventResidue
    (printedTailUpperEventResidueBound_of_pointwise hpoint)

/-- Large-range strict negativity from the pointwise upper-event Taylor tail. -/
theorem correctedCoeff_neg_of_upperEventPointwiseResidue
    (hpoint : PrintedTailUpperEventPointwiseResidueBound)
    {a : Nat} (ha : 14 ≤ a)
    {μ : List Nat} (hμ : Prop51.IsPartitionOf μ (M a)) :
    correctedCoeff a μ < 0 :=
  correctedCoeff_neg_of_upperEventResidue
    (printedTailUpperEventResidueBound_of_pointwise hpoint)
    ha hμ

/-- Public assembly from the pure real-variable Taylor tail on
`0 <= t <= x1`.  This is the smallest remaining analytic interface: the Gamma
substitution and integration over the upper event are both closed in Lean. -/
theorem correctedCoeff_nonvanishing_of_realTailResidue
    (htail : PrintedTailWRealTailResidueBound) :
    CorrectedCoeffNonvanishing :=
  correctedCoeff_nonvanishing_of_upperEventResidue
    (printedTailUpperEventResidueBound_of_realTail htail)

/-- Large-range strict negativity from the pure real-variable Taylor tail. -/
theorem correctedCoeff_neg_of_realTailResidue
    (htail : PrintedTailWRealTailResidueBound)
    {a : Nat} (ha : 14 ≤ a)
    {μ : List Nat} (hμ : Prop51.IsPartitionOf μ (M a)) :
    correctedCoeff a μ < 0 :=
  correctedCoeff_neg_of_upperEventResidue
    (printedTailUpperEventResidueBound_of_realTail htail)
    ha hμ

/-- Public assembly from the real power-series representation of the full
upper-event function.  Once the `omega` coefficients are shown to sum to
`exp(-L(t)) * (1 - J(t))` on `0 <= t <= x1`, the closed coefficient-majorant
tail proves the printed residue bound. -/
theorem correctedCoeff_nonvanishing_of_realSeriesHasSum
    (hseries : PrintedTailWRealSeriesHasSum) :
    CorrectedCoeffNonvanishing :=
  correctedCoeff_nonvanishing_of_realTailResidue
    (printedTailWRealTailResidueBound_of_hasSum hseries)

/-- Large-range strict negativity from the real power-series representation
of the full upper-event function. -/
theorem correctedCoeff_neg_of_realSeriesHasSum
    (hseries : PrintedTailWRealSeriesHasSum)
    {a : Nat} (ha : 14 ≤ a)
    {μ : List Nat} (hμ : Prop51.IsPartitionOf μ (M a)) :
    correctedCoeff a μ < 0 :=
  correctedCoeff_neg_of_realTailResidue
    (printedTailWRealTailResidueBound_of_hasSum hseries)
    ha hμ

/-- Public assembly with the remaining analytic work reduced to the upper
event Taylor bound for the full `W` integrand.  The lower event, finite
Gamma moments, finite-window upper tail, residue arithmetic, mid-range, and
small range are closed in Lean. -/
theorem correctedCoeff_nonvanishing_of_upperEventTruncation
    (hupper : PrintedTailUpperEventTruncationBound) :
    CorrectedCoeffNonvanishing :=
  correctedCoeff_nonvanishing_of_gammaTruncationError
    (printedTailGammaTruncationErrorBound_of_upperEvent hupper)

/-- Public large-range strict negativity with the remaining analytic work
reduced to the upper-event Taylor bound for the full `W` integrand. -/
theorem correctedCoeff_neg_of_upperEventTruncation
    (hupper : PrintedTailUpperEventTruncationBound)
    {a : Nat} (ha : 14 ≤ a)
    {μ : List Nat} (hμ : Prop51.IsPartitionOf μ (M a)) :
    correctedCoeff a μ < 0 :=
  correctedCoeff_neg_of_gammaTruncationError
    (printedTailGammaTruncationErrorBound_of_upperEvent hupper)
    ha hμ

/-! ## Executable checks for the smallest corrected example

For `g = 4` (`a = 2`) and `μ = (1^6)`, the corrected note records

* `[t^2]F_μ = -195/8`,
* the printed coefficient is `45/8`,
* the corrected coefficient is `-465/4`.
-/

example : Prop51.bCoeff [1, 1, 1, 1, 1, 1] 2 = -195 / 8 := by
  native_decide

example : printedCoeff [1, 1, 1, 1, 1, 1] 2 = 45 / 8 := by
  native_decide

example : correctedCoeff 2 [1, 1, 1, 1, 1, 1] = -465 / 4 := by
  native_decide

end Prop52
