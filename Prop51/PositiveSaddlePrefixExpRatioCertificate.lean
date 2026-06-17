/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Lower-prefix large-exp quotient certificate

This file packages the generated reduced-checker chunks from
`PositiveSaddlePrefixExpRatio*.lean` into the large-exp quotient certificate
used by the split lower-prefix route.
-/

import Prop51.PositiveSaddlePrefixExpRatio
import Prop51.PositiveSaddlePrefixExpRatio2
import Prop51.PositiveSaddlePrefixExpRatio3
import Prop51.PositiveSaddlePrefixExpRatio4
import Prop51.PositiveSaddlePrefixExpRatio5

namespace Prop51

/-- Packaged reduced-checker chunks for the lower-prefix large-exp quotient. -/
theorem positiveSaddleLargeTailCandidateTemperedLowerPrefixTopOffsetExpRatioChunksCertificate :
    PositiveSaddleLargeTailCandidateTemperedLowerPrefixTopOffsetExpRatioChunksCertificate
      50 10 where
  aLenPos := by norm_num
  tLenPos := by norm_num
  lowerPrefixTopOffsetExpRatioChunk := by
    intro aChunk tChunk haChunk htChunk
    rcases (mem_positiveLargeTailLowerPrefixAChunks_iff
        (by norm_num : 0 < 50)).mp haChunk with
      ⟨i, hi, rfl⟩
    rcases (mem_positiveLargeTailLowerTopOffsetTChunks_iff
        (by norm_num : 0 < 10)).mp htChunk with
      ⟨j, hj, rfl⟩
    norm_num at hi hj
    have hj0 : j = 0 := by omega
    subst j
    interval_cases i
    · exact checkPositiveTemperedLowerPrefixTopOffsetExpRatioReducedChunk_2001_50_0_10
    · exact checkPositiveTemperedLowerPrefixTopOffsetExpRatioReducedChunk_2051_50_0_10
    · exact checkPositiveTemperedLowerPrefixTopOffsetExpRatioReducedChunk_2101_50_0_10
    · exact checkPositiveTemperedLowerPrefixTopOffsetExpRatioReducedChunk_2151_50_0_10
    · exact checkPositiveTemperedLowerPrefixTopOffsetExpRatioReducedChunk_2201_50_0_10
    · exact checkPositiveTemperedLowerPrefixTopOffsetExpRatioReducedChunk_2251_50_0_10
    · exact checkPositiveTemperedLowerPrefixTopOffsetExpRatioReducedChunk_2301_50_0_10
    · exact checkPositiveTemperedLowerPrefixTopOffsetExpRatioReducedChunk_2351_50_0_10
    · exact checkPositiveTemperedLowerPrefixTopOffsetExpRatioReducedChunk_2401_50_0_10
    · exact checkPositiveTemperedLowerPrefixTopOffsetExpRatioReducedChunk_2451_50_0_10
    · exact checkPositiveTemperedLowerPrefixTopOffsetExpRatioReducedChunk_2501_50_0_10
    · exact checkPositiveTemperedLowerPrefixTopOffsetExpRatioReducedChunk_2551_50_0_10
    · exact checkPositiveTemperedLowerPrefixTopOffsetExpRatioReducedChunk_2601_50_0_10
    · exact checkPositiveTemperedLowerPrefixTopOffsetExpRatioReducedChunk_2651_50_0_10
    · exact checkPositiveTemperedLowerPrefixTopOffsetExpRatioReducedChunk_2701_50_0_10
    · exact checkPositiveTemperedLowerPrefixTopOffsetExpRatioReducedChunk_2751_50_0_10
    · exact checkPositiveTemperedLowerPrefixTopOffsetExpRatioReducedChunk_2801_50_0_10
    · exact checkPositiveTemperedLowerPrefixTopOffsetExpRatioReducedChunk_2851_50_0_10
    · exact checkPositiveTemperedLowerPrefixTopOffsetExpRatioReducedChunk_2901_50_0_10
    · exact checkPositiveTemperedLowerPrefixTopOffsetExpRatioReducedChunk_2951_50_0_10

/-- Packaged lower-prefix large-exp quotient certificate. -/
theorem positiveSaddleLargeTailCandidateTemperedLowerPrefixTopOffsetExpRatioCertificate :
    PositiveSaddleLargeTailCandidateTemperedLowerPrefixTopOffsetExpRatioCertificate :=
  positiveSaddleLargeTailCandidateTemperedLowerPrefixTopOffsetExpRatioChunksCertificate
    |>.toExpRatioCertificate

end Prop51
