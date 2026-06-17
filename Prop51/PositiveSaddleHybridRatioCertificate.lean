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

end Prop51
