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

end Prop51
