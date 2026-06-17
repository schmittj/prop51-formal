/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Lower-prefix large-exp quotient chunks

This generated-style file records reduced-checker chunks for the remaining
large-exp quotient half of the lower hybrid prefix strip `2000 < a < 3000`,
`t < 10`.  Each chunk checks the cutoff-`700` numerator majorant against the
row-dependent target `(5a-213)/(5a)` times an `800`-term denominator prefix;
`PositiveSaddleChunks` proves that these reduced checks imply the actual
large-exp quotient bound.
-/

import Prop51.PositiveSaddleChunks

namespace Prop51

/-- First generated 50-row chunk for the reduced lower-prefix large-exp
quotient checker. -/
theorem checkPositiveTemperedLowerPrefixTopOffsetExpRatioReducedChunk_2001_50_0_10 :
    checkPositiveTemperedLowerPrefixTopOffsetExpRatioReducedChunk 2001 50 0 10 =
      true := by
  native_decide

/-- Second generated 50-row chunk for the reduced lower-prefix large-exp
quotient checker. -/
theorem checkPositiveTemperedLowerPrefixTopOffsetExpRatioReducedChunk_2051_50_0_10 :
    checkPositiveTemperedLowerPrefixTopOffsetExpRatioReducedChunk 2051 50 0 10 =
      true := by
  native_decide

/-- Third generated 50-row chunk for the reduced lower-prefix large-exp
quotient checker. -/
theorem checkPositiveTemperedLowerPrefixTopOffsetExpRatioReducedChunk_2101_50_0_10 :
    checkPositiveTemperedLowerPrefixTopOffsetExpRatioReducedChunk 2101 50 0 10 =
      true := by
  native_decide

/-- Fourth generated 50-row chunk for the reduced lower-prefix large-exp
quotient checker. -/
theorem checkPositiveTemperedLowerPrefixTopOffsetExpRatioReducedChunk_2151_50_0_10 :
    checkPositiveTemperedLowerPrefixTopOffsetExpRatioReducedChunk 2151 50 0 10 =
      true := by
  native_decide

end Prop51
