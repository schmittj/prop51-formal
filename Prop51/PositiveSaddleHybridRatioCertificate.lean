/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Lower-tempered hybrid ratio certificate

This file packages the generated lower-prefix quotient and raw-budget
certificates with the analytic large-row sharp top-offset envelope.
-/

import Prop51.PositiveSaddlePrefixExpRatioCertificate
import Prop51.PositiveSaddlePrefixRawBudget

namespace Prop51

/-- Concrete lower-tempered hybrid ratio certificate.

The prefix strip `2000 < a < 3000` is supplied by generated chunks, while
the large strip `3000 ≤ a` is closed by
`positiveTemperedLargeExp_lowerSharpTopOffsetExpQuotientTargetCrossmulLarge`. -/
theorem positiveSaddleLargeTailCandidateTemperedLowerSharpTopOffsetHybridRatioChunkedCertificate :
    PositiveSaddleLargeTailCandidateTemperedLowerSharpTopOffsetHybridRatioChunkedCertificate
      999 10 :=
  positiveSaddleLargeTailCandidateTemperedLowerPrefixTopOffsetRawBudgetChunksCertificate
    |>.toSharpTopOffsetHybridRatioChunkedCertificate
      positiveSaddleLargeTailCandidateTemperedLowerPrefixTopOffsetExpRatioCertificate

/-- Large-tail wrapper with the lower hybrid ratio certificate filled in.

After this packaging step, the large-tail audit route still asks for the
product bounds, the solo bound, and the upper reverse middle-band large-exp
target.  The lower tempered adjacent-step side, including the finite prefix
`2000 < a < 3000`, is supplied by the concrete certificates imported above. -/
theorem positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate_of_upperMiddle
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    (product :
      PositiveSaddleLargeTailProductBoundsCertificate
        smallXBound smallYBound temperedXBound temperedYBound)
    (soloY :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
        positiveYgcompBound N a ≤ positiveLargeTailSoloTenSeventhsBound a N)
    (upperMiddle :
      PositiveSaddleLargeTailCandidateTemperedUpperReverseMiddleExpTargetCrossmulCertificate) :
    PositiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate
      999 10 smallXBound smallYBound temperedXBound temperedYBound where
  productBounds := product
  soloY := soloY
  temperedLowerSharpTopOffsetHybridRatioChunked :=
    positiveSaddleLargeTailCandidateTemperedLowerSharpTopOffsetHybridRatioChunkedCertificate
  temperedUpperReverseMiddleExpTarget := upperMiddle

/-- Same hybrid wrapper, but with the solo side supplied in the
denominator-cleared `QqEplusGcompBound` saddle form.

This records the current Lean-side reduction of the TeX solo saddle estimate:
the final proof still needs the same saddle inequality, but in a form that is
friendlier for rational coefficient estimates than the normalized
`positiveYgcompBound` quotient. -/
theorem positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate_of_upperMiddle_soloGcompSaddleCleared
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    (product :
      PositiveSaddleLargeTailProductBoundsCertificate
        smallXBound smallYBound temperedXBound temperedYBound)
    (soloY :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
        positiveLargeTailSoloGcompSaddleCleared a N)
    (upperMiddle :
      PositiveSaddleLargeTailCandidateTemperedUpperReverseMiddleExpTargetCrossmulCertificate) :
    PositiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate
      999 10 smallXBound smallYBound temperedXBound temperedYBound :=
  positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate_of_upperMiddle
    product
    (fun {a N} ha hrect =>
      positiveYgcompBound_le_positiveLargeTailSoloTenSeventhsBound_of_gcompSaddleCleared
        (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect) ha
        (soloY (a := a) (N := N) ha hrect))
    upperMiddle

/-- Same hybrid wrapper, but with the solo side supplied in the
denominator-cleared `QqEplusGcompBound` saddle form already measured against
the final `(10/7)^a` envelope. -/
theorem positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate_of_upperMiddle_soloGcompSaddleTenSeventhsCleared
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    (product :
      PositiveSaddleLargeTailProductBoundsCertificate
        smallXBound smallYBound temperedXBound temperedYBound)
    (soloY :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
        positiveLargeTailSoloGcompSaddleTenSeventhsCleared a N)
    (upperMiddle :
      PositiveSaddleLargeTailCandidateTemperedUpperReverseMiddleExpTargetCrossmulCertificate) :
    PositiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate
      999 10 smallXBound smallYBound temperedXBound temperedYBound :=
  positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate_of_upperMiddle
    product
    (fun {a N} ha hrect =>
      positiveYgcompBound_le_positiveLargeTailSoloTenSeventhsBound_of_gcompSaddleTenSeventhsCleared
        (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect) ha
        (soloY (a := a) (N := N) ha hrect))
    upperMiddle

/-- Same hybrid wrapper with the solo side supplied as the split-final-term
factorial closed-composition sum, cleared directly against `(10/7)^a`. -/
theorem positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate_of_upperMiddle_soloGcompClosedFactorialSplitBlockSumTenSeventhsCleared
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    (product :
      PositiveSaddleLargeTailProductBoundsCertificate
        smallXBound smallYBound temperedXBound temperedYBound)
    (soloY :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
        positiveLargeTailSoloGcompClosedFactorialSplitBlockSumTenSeventhsCleared
          a N)
    (upperMiddle :
      PositiveSaddleLargeTailCandidateTemperedUpperReverseMiddleExpTargetCrossmulCertificate) :
    PositiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate
      999 10 smallXBound smallYBound temperedXBound temperedYBound :=
  positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate_of_upperMiddle
    product
    (fun {a N} ha hrect =>
      positiveYgcompBound_le_positiveLargeTailSoloTenSeventhsBound_of_gcompClosedFactorialSplitBlockSumTenSeventhsCleared
        (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect) ha
        (soloY (a := a) (N := N) ha hrect))
    upperMiddle

/-- Same hybrid wrapper, but the split-final-term factorial solo target only
has to be supplied at the upper rectangle edge `N = posNhi a`; monotonicity of
the solo block sum fills in the rest of the rectangle. -/
theorem positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate_of_upperMiddle_soloGcompClosedFactorialSplitBlockSumTenSeventhsCleared_upperEdge
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    (product :
      PositiveSaddleLargeTailProductBoundsCertificate
        smallXBound smallYBound temperedXBound temperedYBound)
    (soloY :
      ∀ {a : Nat}, 2000 < a →
        positiveLargeTailSoloGcompClosedFactorialSplitBlockSumTenSeventhsCleared
          a (posNhi a))
    (upperMiddle :
      PositiveSaddleLargeTailCandidateTemperedUpperReverseMiddleExpTargetCrossmulCertificate) :
    PositiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate
      999 10 smallXBound smallYBound temperedXBound temperedYBound :=
  positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate_of_upperMiddle_soloGcompClosedFactorialSplitBlockSumTenSeventhsCleared
    product
    (fun {a N} ha hrect =>
      positiveLargeTailSoloGcompClosedFactorialSplitBlockSumTenSeventhsCleared_of_upperEdge
        (a := a) (N := N) hrect (soloY (a := a) ha))
    upperMiddle

/-- Large-tail wrapper with both adjacent-step sides filled in.

After the upper-middle reverse target is now concrete, this route asks only for
the product bounds and the solo `Y` envelope. -/
theorem positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    (product :
      PositiveSaddleLargeTailProductBoundsCertificate
        smallXBound smallYBound temperedXBound temperedYBound)
    (soloY :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
        positiveYgcompBound N a ≤ positiveLargeTailSoloTenSeventhsBound a N) :
    PositiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate
      999 10 smallXBound smallYBound temperedXBound temperedYBound :=
  positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate_of_upperMiddle
    product soloY
    positiveSaddleLargeTailCandidateTemperedUpperReverseMiddleExpTargetCrossmulCertificate

/-- Large-tail wrapper with both adjacent-step sides filled in and the solo
side supplied as the cleared `Gcomp` saddle target. -/
theorem positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate_of_soloGcompSaddleCleared
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    (product :
      PositiveSaddleLargeTailProductBoundsCertificate
        smallXBound smallYBound temperedXBound temperedYBound)
    (soloY :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
        positiveLargeTailSoloGcompSaddleCleared a N) :
    PositiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate
      999 10 smallXBound smallYBound temperedXBound temperedYBound :=
  positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate_of_upperMiddle_soloGcompSaddleCleared
    product soloY
    positiveSaddleLargeTailCandidateTemperedUpperReverseMiddleExpTargetCrossmulCertificate

/-- Large-tail wrapper with both adjacent-step sides filled in and the solo
side supplied as the ten-sevenths cleared `Gcomp` saddle target. -/
theorem positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate_of_soloGcompSaddleTenSeventhsCleared
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    (product :
      PositiveSaddleLargeTailProductBoundsCertificate
        smallXBound smallYBound temperedXBound temperedYBound)
    (soloY :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
        positiveLargeTailSoloGcompSaddleTenSeventhsCleared a N) :
    PositiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate
      999 10 smallXBound smallYBound temperedXBound temperedYBound :=
  positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate_of_upperMiddle_soloGcompSaddleTenSeventhsCleared
    product soloY
    positiveSaddleLargeTailCandidateTemperedUpperReverseMiddleExpTargetCrossmulCertificate

/-- Large-tail wrapper with both adjacent-step sides filled in and the solo
side supplied as the split-final-term factorial target cleared directly
against `(10/7)^a`. -/
theorem positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate_of_soloGcompClosedFactorialSplitBlockSumTenSeventhsCleared
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    (product :
      PositiveSaddleLargeTailProductBoundsCertificate
        smallXBound smallYBound temperedXBound temperedYBound)
    (soloY :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
        positiveLargeTailSoloGcompClosedFactorialSplitBlockSumTenSeventhsCleared
          a N) :
    PositiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate
      999 10 smallXBound smallYBound temperedXBound temperedYBound :=
  positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate_of_upperMiddle_soloGcompClosedFactorialSplitBlockSumTenSeventhsCleared
    product soloY
    positiveSaddleLargeTailCandidateTemperedUpperReverseMiddleExpTargetCrossmulCertificate

/-- Large-tail wrapper with both adjacent-step sides filled in and the solo
side supplied only at the upper rectangle edge. -/
theorem positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate_of_soloGcompClosedFactorialSplitBlockSumTenSeventhsCleared_upperEdge
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    (product :
      PositiveSaddleLargeTailProductBoundsCertificate
        smallXBound smallYBound temperedXBound temperedYBound)
    (soloY :
      ∀ {a : Nat}, 2000 < a →
        positiveLargeTailSoloGcompClosedFactorialSplitBlockSumTenSeventhsCleared
          a (posNhi a)) :
    PositiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate
      999 10 smallXBound smallYBound temperedXBound temperedYBound :=
  positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate_of_upperMiddle_soloGcompClosedFactorialSplitBlockSumTenSeventhsCleared_upperEdge
    product soloY
    positiveSaddleLargeTailCandidateTemperedUpperReverseMiddleExpTargetCrossmulCertificate

/-- Large-tail audit certificate with the lower hybrid ratio side concrete.

This is the proof-facing large-tail target after the current lower-side work:
closing `upperMiddle` and supplying product/solo bounds suffices to obtain the
canonical `PositiveSaddleLargeTailAuditCertificate`. -/
theorem positiveSaddleLargeTailAuditCertificate_of_upperMiddle
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    (product :
      PositiveSaddleLargeTailProductBoundsCertificate
        smallXBound smallYBound temperedXBound temperedYBound)
    (soloY :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
        positiveYgcompBound N a ≤ positiveLargeTailSoloTenSeventhsBound a N)
    (upperMiddle :
      PositiveSaddleLargeTailCandidateTemperedUpperReverseMiddleExpTargetCrossmulCertificate) :
    PositiveSaddleLargeTailAuditCertificate :=
  (positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate_of_upperMiddle
    product soloY upperMiddle).toLargeTailAuditCertificate

/-- Large-tail audit certificate with the lower hybrid ratio side concrete and
the solo side supplied as the cleared `Gcomp` saddle target. -/
theorem positiveSaddleLargeTailAuditCertificate_of_upperMiddle_soloGcompSaddleCleared
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    (product :
      PositiveSaddleLargeTailProductBoundsCertificate
        smallXBound smallYBound temperedXBound temperedYBound)
    (soloY :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
        positiveLargeTailSoloGcompSaddleCleared a N)
    (upperMiddle :
      PositiveSaddleLargeTailCandidateTemperedUpperReverseMiddleExpTargetCrossmulCertificate) :
    PositiveSaddleLargeTailAuditCertificate :=
  (positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate_of_upperMiddle_soloGcompSaddleCleared
    product soloY upperMiddle).toLargeTailAuditCertificate

/-- Large-tail audit certificate after both adjacent-step sides are filled.

The remaining analytic inputs are exactly the product bounds and the solo
`Y` bound. -/
theorem positiveSaddleLargeTailAuditCertificate_of_product_solo
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    (product :
      PositiveSaddleLargeTailProductBoundsCertificate
        smallXBound smallYBound temperedXBound temperedYBound)
    (soloY :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
        positiveYgcompBound N a ≤ positiveLargeTailSoloTenSeventhsBound a N) :
    PositiveSaddleLargeTailAuditCertificate :=
  (positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate
    product soloY).toLargeTailAuditCertificate

/-- Large-tail audit certificate after both adjacent-step sides are filled and
the solo side is reduced to the cleared `Gcomp` saddle target. -/
theorem positiveSaddleLargeTailAuditCertificate_of_product_soloGcompSaddleCleared
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    (product :
      PositiveSaddleLargeTailProductBoundsCertificate
        smallXBound smallYBound temperedXBound temperedYBound)
    (soloY :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
        positiveLargeTailSoloGcompSaddleCleared a N) :
    PositiveSaddleLargeTailAuditCertificate :=
  (positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate_of_soloGcompSaddleCleared
    product soloY).toLargeTailAuditCertificate

/-- Large-tail audit certificate after both adjacent-step sides are filled
and the solo side is reduced to the ten-sevenths cleared `Gcomp` saddle
target. -/
theorem positiveSaddleLargeTailAuditCertificate_of_product_soloGcompSaddleTenSeventhsCleared
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    (product :
      PositiveSaddleLargeTailProductBoundsCertificate
        smallXBound smallYBound temperedXBound temperedYBound)
    (soloY :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
        positiveLargeTailSoloGcompSaddleTenSeventhsCleared a N) :
    PositiveSaddleLargeTailAuditCertificate :=
  (positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate_of_soloGcompSaddleTenSeventhsCleared
    product soloY).toLargeTailAuditCertificate

/-- Large-tail audit certificate after both adjacent-step sides are filled
and the solo side is reduced to the split-final-term factorial target cleared
directly against `(10/7)^a`. -/
theorem positiveSaddleLargeTailAuditCertificate_of_product_soloGcompClosedFactorialSplitBlockSumTenSeventhsCleared
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    (product :
      PositiveSaddleLargeTailProductBoundsCertificate
        smallXBound smallYBound temperedXBound temperedYBound)
    (soloY :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
        positiveLargeTailSoloGcompClosedFactorialSplitBlockSumTenSeventhsCleared
          a N) :
    PositiveSaddleLargeTailAuditCertificate :=
  (positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate_of_soloGcompClosedFactorialSplitBlockSumTenSeventhsCleared
    product soloY).toLargeTailAuditCertificate

/-- Large-tail audit certificate with a direct split-final-term solo
obligation only at `N = posNhi a`. -/
theorem positiveSaddleLargeTailAuditCertificate_of_product_soloGcompClosedFactorialSplitBlockSumTenSeventhsCleared_upperEdge
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    (product :
      PositiveSaddleLargeTailProductBoundsCertificate
        smallXBound smallYBound temperedXBound temperedYBound)
    (soloY :
      ∀ {a : Nat}, 2000 < a →
        positiveLargeTailSoloGcompClosedFactorialSplitBlockSumTenSeventhsCleared
          a (posNhi a)) :
    PositiveSaddleLargeTailAuditCertificate :=
  (positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate_of_soloGcompClosedFactorialSplitBlockSumTenSeventhsCleared_upperEdge
    product soloY).toLargeTailAuditCertificate

/-- Large-tail audit certificate after both adjacent-step sides are filled and
the solo side is reduced to the explicit `Gcomp` double-sum target. -/
theorem positiveSaddleLargeTailAuditCertificate_of_product_soloGcompBlockSumCleared
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    (product :
      PositiveSaddleLargeTailProductBoundsCertificate
        smallXBound smallYBound temperedXBound temperedYBound)
    (soloY :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
        positiveLargeTailSoloGcompBlockSumCleared a N) :
    PositiveSaddleLargeTailAuditCertificate :=
  positiveSaddleLargeTailAuditCertificate_of_product_soloGcompSaddleCleared
    product
    (fun {a N} ha hrect =>
      positiveLargeTailSoloGcompSaddleCleared_of_blockSumCleared
        (soloY (a := a) (N := N) ha hrect))

/-- Large-tail audit certificate with the product side reduced to the explicit
`Gcomp` block-sum product certificate and the solo side reduced to the
explicit solo block-sum target. -/
theorem positiveSaddleLargeTailAuditCertificate_of_productBlockSum_soloGcompBlockSumCleared
    (product : PositiveSaddleLargeTailProductBlockSumCertificate)
    (soloY :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
        positiveLargeTailSoloGcompBlockSumCleared a N) :
    PositiveSaddleLargeTailAuditCertificate :=
  positiveSaddleLargeTailAuditCertificate_of_product_soloGcompBlockSumCleared
    product.toProductBoundsCertificate soloY

/-- Large-tail audit certificate with the product side supplied through the
named scalar block-sum targets and the solo side supplied through the explicit
solo block-sum target. -/
theorem positiveSaddleLargeTailAuditCertificate_of_productBlockSumScalars_soloGcompBlockSumCleared
    (product : PositiveSaddleLargeTailProductBlockSumScalarCertificate)
    (soloY :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
        positiveLargeTailSoloGcompBlockSumCleared a N) :
    PositiveSaddleLargeTailAuditCertificate :=
  positiveSaddleLargeTailAuditCertificate_of_productBlockSum_soloGcompBlockSumCleared
    product.toBlockSumCertificate soloY

/-- Large-tail audit certificate with the product and solo sides supplied
through closed-composition block-sum targets. -/
theorem positiveSaddleLargeTailAuditCertificate_of_productClosedBlockSumScalars_soloGcompClosedBlockSumCleared
    (product : PositiveSaddleLargeTailProductClosedBlockSumScalarCertificate)
    (soloY :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
        positiveLargeTailSoloGcompClosedBlockSumCleared a N) :
    PositiveSaddleLargeTailAuditCertificate :=
  positiveSaddleLargeTailAuditCertificate_of_productBlockSumScalars_soloGcompBlockSumCleared
    product.toBlockSumScalarCertificate
    (fun {a N} ha hrect =>
      positiveLargeTailSoloGcompBlockSumCleared_of_closedBlockSumCleared
        (soloY (a := a) (N := N) ha hrect))

/-- Large-tail audit certificate with the product and solo sides supplied
through active closed-composition block-sum targets. -/
theorem positiveSaddleLargeTailAuditCertificate_of_productClosedActiveBlockSumScalars_soloGcompClosedActiveBlockSumCleared
    (product : PositiveSaddleLargeTailProductClosedActiveBlockSumScalarCertificate)
    (soloY :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
        positiveLargeTailSoloGcompClosedActiveBlockSumCleared a N) :
    PositiveSaddleLargeTailAuditCertificate :=
  positiveSaddleLargeTailAuditCertificate_of_productClosedBlockSumScalars_soloGcompClosedBlockSumCleared
    product.toClosedBlockSumScalarCertificate
    (fun {a N} ha hrect =>
      positiveLargeTailSoloGcompClosedBlockSumCleared_of_active
        (soloY (a := a) (N := N) ha hrect))

/-- Large-tail audit certificate with the product and solo sides supplied
through factorial-only active closed-composition block-sum targets. -/
theorem positiveSaddleLargeTailAuditCertificate_of_productClosedFactorialBlockSumScalars_soloGcompClosedFactorialBlockSumCleared
    (product : PositiveSaddleLargeTailProductClosedFactorialBlockSumScalarCertificate)
    (soloY :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
        positiveLargeTailSoloGcompClosedFactorialBlockSumCleared a N) :
    PositiveSaddleLargeTailAuditCertificate :=
  positiveSaddleLargeTailAuditCertificate_of_productClosedBlockSumScalars_soloGcompClosedBlockSumCleared
    product.toClosedBlockSumScalarCertificate
    (fun {a N} ha hrect =>
      positiveLargeTailSoloGcompClosedBlockSumCleared_of_factorial
        (soloY (a := a) (N := N) ha hrect))

/-- Preferred hybrid-ratio large-tail certificate with the product and solo
sides supplied through split-final-term factorial-only active
closed-composition block-sum targets.

The resulting product bound functions are the original explicit block-sum
bounds; the split-factorial inputs are used only to prove the scalar product
fields for those bounds. -/
theorem positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedCertificate_of_productClosedFactorialSplitBlockSumScalars_soloGcompClosedFactorialSplitBlockSumCleared
    (product :
      PositiveSaddleLargeTailProductClosedFactorialSplitBlockSumScalarCertificate)
    (soloY :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
        positiveLargeTailSoloGcompClosedFactorialSplitBlockSumCleared a N) :
    PositiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate
      999 10
      positiveLargeTailProductXBlockBound positiveLargeTailProductYBlockBound
      positiveLargeTailProductXBlockBound positiveLargeTailProductYBlockBound := by
  have productBounds :
      PositiveSaddleLargeTailProductBoundsCertificate
        positiveLargeTailProductXBlockBound positiveLargeTailProductYBlockBound
        positiveLargeTailProductXBlockBound positiveLargeTailProductYBlockBound :=
    product.toProductBoundsCertificate
  exact
    positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate_of_soloGcompSaddleCleared
      productBounds
      (fun {a N} ha hrect =>
        positiveLargeTailSoloGcompSaddleCleared_of_closedFactorialSplitBlockSumCleared
          (soloY (a := a) (N := N) ha hrect))

/-- Large-tail audit certificate with the product and solo sides supplied
through split-final-term factorial-only active closed-composition block-sum
targets. -/
theorem positiveSaddleLargeTailAuditCertificate_of_productClosedFactorialSplitBlockSumScalars_soloGcompClosedFactorialSplitBlockSumCleared
    (product :
      PositiveSaddleLargeTailProductClosedFactorialSplitBlockSumScalarCertificate)
    (soloY :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
        positiveLargeTailSoloGcompClosedFactorialSplitBlockSumCleared a N) :
    PositiveSaddleLargeTailAuditCertificate :=
  (positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedCertificate_of_productClosedFactorialSplitBlockSumScalars_soloGcompClosedFactorialSplitBlockSumCleared
    product soloY).toLargeTailAuditCertificate

/-- Preferred hybrid-ratio large-tail certificate with both split-final-term
factorial inputs supplied through fast rational exponential evaluators. -/
theorem positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedCertificate_of_productClosedFactorialSplitBlockSumScalarsFastExp_soloGcompClosedFactorialSplitBlockSumFastCleared
    (product :
      PositiveSaddleLargeTailProductClosedFactorialSplitBlockSumScalarFastExpCertificate)
    (soloY :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
        positiveLargeTailSoloGcompClosedFactorialSplitBlockSumFastCleared
          a N) :
    PositiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate
      999 10
      positiveLargeTailProductXBlockBound positiveLargeTailProductYBlockBound
      positiveLargeTailProductXBlockBound positiveLargeTailProductYBlockBound :=
  positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedCertificate_of_productClosedFactorialSplitBlockSumScalars_soloGcompClosedFactorialSplitBlockSumCleared
    product.toClosedFactorialSplitBlockSumScalarCertificate
    (fun {a N} ha hrect =>
      positiveLargeTailSoloGcompClosedFactorialSplitBlockSumCleared_of_fast
        (soloY (a := a) (N := N) ha hrect))

/-- Large-tail audit certificate whose remaining product and solo fields use
the fast split-final-term factorial targets. -/
theorem positiveSaddleLargeTailAuditCertificate_of_productClosedFactorialSplitBlockSumScalarsFastExp_soloGcompClosedFactorialSplitBlockSumFastCleared
    (product :
      PositiveSaddleLargeTailProductClosedFactorialSplitBlockSumScalarFastExpCertificate)
    (soloY :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
        positiveLargeTailSoloGcompClosedFactorialSplitBlockSumFastCleared
          a N) :
    PositiveSaddleLargeTailAuditCertificate :=
  (positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedCertificate_of_productClosedFactorialSplitBlockSumScalarsFastExp_soloGcompClosedFactorialSplitBlockSumFastCleared
    product soloY).toLargeTailAuditCertificate

/-- Preferred hybrid-ratio large-tail certificate with the product side
supplied through fast split-final-term factorial targets and the solo side
supplied directly as the `(10/7)^a` envelope.

This is a weaker solo obligation than the cleared `partialExpUpperFast`
target above; the underlying hybrid-ratio audit certificate only needs the
`positiveYgcompBound` envelope. -/
theorem positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedCertificate_of_productClosedFactorialSplitBlockSumScalarsFastExp_soloTenSeventhsBound
    (product :
      PositiveSaddleLargeTailProductClosedFactorialSplitBlockSumScalarFastExpCertificate)
    (soloY :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
        positiveYgcompBound N a ≤
          positiveLargeTailSoloTenSeventhsBound a N) :
    PositiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate
      999 10
      positiveLargeTailProductXBlockBound positiveLargeTailProductYBlockBound
      positiveLargeTailProductXBlockBound positiveLargeTailProductYBlockBound :=
  positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate
    product.toProductBoundsCertificate soloY

/-- Large-tail audit certificate with fast split-final-term product targets
and the direct `(10/7)^a` solo envelope as the remaining inputs. -/
theorem positiveSaddleLargeTailAuditCertificate_of_productClosedFactorialSplitBlockSumScalarsFastExp_soloTenSeventhsBound
    (product :
      PositiveSaddleLargeTailProductClosedFactorialSplitBlockSumScalarFastExpCertificate)
    (soloY :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
        positiveYgcompBound N a ≤
          positiveLargeTailSoloTenSeventhsBound a N) :
    PositiveSaddleLargeTailAuditCertificate :=
  (positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedCertificate_of_productClosedFactorialSplitBlockSumScalarsFastExp_soloTenSeventhsBound
    product soloY).toLargeTailAuditCertificate

/-- Preferred hybrid-ratio large-tail certificate with fast split-final-term
product targets and a split-final-term factorial solo target estimated
directly against the final `(10/7)^a` envelope.

This route avoids the stronger `partialExpUpperFast` solo obligation while
still records the factorial split used by generated solo witnesses. -/
theorem positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedCertificate_of_productClosedFactorialSplitBlockSumScalarsFastExp_soloGcompClosedFactorialSplitBlockSumTenSeventhsCleared
    (product :
      PositiveSaddleLargeTailProductClosedFactorialSplitBlockSumScalarFastExpCertificate)
    (soloY :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
        positiveLargeTailSoloGcompClosedFactorialSplitBlockSumTenSeventhsCleared
          a N) :
    PositiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate
      999 10
      positiveLargeTailProductXBlockBound positiveLargeTailProductYBlockBound
      positiveLargeTailProductXBlockBound positiveLargeTailProductYBlockBound :=
  positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedCertificate_of_productClosedFactorialSplitBlockSumScalarsFastExp_soloTenSeventhsBound
    product
    (fun {a N} ha hrect =>
      positiveYgcompBound_le_positiveLargeTailSoloTenSeventhsBound_of_gcompClosedFactorialSplitBlockSumTenSeventhsCleared
        (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect) ha
        (soloY (a := a) (N := N) ha hrect))

/-- Preferred hybrid-ratio large-tail certificate with fast split-final-term
product targets and the direct solo target checked only at the upper
rectangle edge. -/
theorem positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedCertificate_of_productClosedFactorialSplitBlockSumScalarsFastExp_soloGcompClosedFactorialSplitBlockSumTenSeventhsCleared_upperEdge
    (product :
      PositiveSaddleLargeTailProductClosedFactorialSplitBlockSumScalarFastExpCertificate)
    (soloY :
      ∀ {a : Nat}, 2000 < a →
        positiveLargeTailSoloGcompClosedFactorialSplitBlockSumTenSeventhsCleared
          a (posNhi a)) :
    PositiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate
      999 10
      positiveLargeTailProductXBlockBound positiveLargeTailProductYBlockBound
      positiveLargeTailProductXBlockBound positiveLargeTailProductYBlockBound :=
  positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedCertificate_of_productClosedFactorialSplitBlockSumScalarsFastExp_soloGcompClosedFactorialSplitBlockSumTenSeventhsCleared
    product
    (fun {a N} ha hrect =>
      positiveLargeTailSoloGcompClosedFactorialSplitBlockSumTenSeventhsCleared_of_upperEdge
        (a := a) (N := N) hrect (soloY (a := a) ha))

/-- Preferred hybrid-ratio large-tail certificate with the strengthened
upper-edge/lower-`N` product target and the direct solo target checked only
at the upper rectangle edge.  The product target is intentionally stronger
than the TeX scalar comparison; its conversion is recorded in
`PositiveSaddleLargeTailProductClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerNCertificate.toClosedFactorialSplitBlockSumScalarFastExpCertificate`.
-/
theorem positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedCertificate_of_productClosedFactorialSplitBlockSumScalarsFastExpUpperEdgeLowerN_soloGcompClosedFactorialSplitBlockSumTenSeventhsCleared_upperEdge
    (product :
      PositiveSaddleLargeTailProductClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerNCertificate)
    (soloY :
      ∀ {a : Nat}, 2000 < a →
        positiveLargeTailSoloGcompClosedFactorialSplitBlockSumTenSeventhsCleared
          a (posNhi a)) :
    PositiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate
      999 10
      positiveLargeTailProductXBlockBound positiveLargeTailProductYBlockBound
      positiveLargeTailProductXBlockBound positiveLargeTailProductYBlockBound :=
  positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedCertificate_of_productClosedFactorialSplitBlockSumScalarsFastExp_soloGcompClosedFactorialSplitBlockSumTenSeventhsCleared_upperEdge
    product.toClosedFactorialSplitBlockSumScalarFastExpCertificate soloY

/-- Large-tail audit certificate with fast split-final-term product targets
and the split-final-term factorial solo target estimated directly against
the final `(10/7)^a` envelope. -/
theorem positiveSaddleLargeTailAuditCertificate_of_productClosedFactorialSplitBlockSumScalarsFastExp_soloGcompClosedFactorialSplitBlockSumTenSeventhsCleared
    (product :
      PositiveSaddleLargeTailProductClosedFactorialSplitBlockSumScalarFastExpCertificate)
    (soloY :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
        positiveLargeTailSoloGcompClosedFactorialSplitBlockSumTenSeventhsCleared
          a N) :
    PositiveSaddleLargeTailAuditCertificate :=
  (positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedCertificate_of_productClosedFactorialSplitBlockSumScalarsFastExp_soloGcompClosedFactorialSplitBlockSumTenSeventhsCleared
    product soloY).toLargeTailAuditCertificate

/-- Large-tail audit certificate with fast split-final-term product targets
and the direct split-final-term solo target checked only at `N = posNhi a`. -/
theorem positiveSaddleLargeTailAuditCertificate_of_productClosedFactorialSplitBlockSumScalarsFastExp_soloGcompClosedFactorialSplitBlockSumTenSeventhsCleared_upperEdge
    (product :
      PositiveSaddleLargeTailProductClosedFactorialSplitBlockSumScalarFastExpCertificate)
    (soloY :
      ∀ {a : Nat}, 2000 < a →
        positiveLargeTailSoloGcompClosedFactorialSplitBlockSumTenSeventhsCleared
          a (posNhi a)) :
    PositiveSaddleLargeTailAuditCertificate :=
  (positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedCertificate_of_productClosedFactorialSplitBlockSumScalarsFastExp_soloGcompClosedFactorialSplitBlockSumTenSeventhsCleared_upperEdge
    product soloY).toLargeTailAuditCertificate

/-- Large-tail audit certificate with the strengthened upper-edge/lower-`N`
product target and the direct split-final-term solo target checked only at
`N = posNhi a`. -/
theorem positiveSaddleLargeTailAuditCertificate_of_productClosedFactorialSplitBlockSumScalarsFastExpUpperEdgeLowerN_soloGcompClosedFactorialSplitBlockSumTenSeventhsCleared_upperEdge
    (product :
      PositiveSaddleLargeTailProductClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerNCertificate)
    (soloY :
      ∀ {a : Nat}, 2000 < a →
        positiveLargeTailSoloGcompClosedFactorialSplitBlockSumTenSeventhsCleared
          a (posNhi a)) :
    PositiveSaddleLargeTailAuditCertificate :=
  (positiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedCertificate_of_productClosedFactorialSplitBlockSumScalarsFastExpUpperEdgeLowerN_soloGcompClosedFactorialSplitBlockSumTenSeventhsCleared_upperEdge
    product soloY).toLargeTailAuditCertificate

end Prop51
