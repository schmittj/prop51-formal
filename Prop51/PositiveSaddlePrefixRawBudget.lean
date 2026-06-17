/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Lower-prefix raw budget certificate

This generated-style certificate closes the raw-only half of the lower
hybrid prefix strip `2000 < a < 3000`, `t < 10`, after extracting the
row-dependent large-exp quotient target `(5a-213)/(5a)`.
-/

import Prop51.PositiveSaddleChunks

namespace Prop51

/-- Single native chunk for the complete raw-only lower-prefix budget. -/
theorem checkPositiveTemperedLowerPrefixTopOffsetRawBudgetChunk_2001_999_0_10 :
    checkPositiveTemperedLowerPrefixTopOffsetRawBudgetChunk 2001 999 0 10 =
      true := by
  native_decide

/-- Packaged raw-only lower-prefix budget certificate. -/
theorem positiveSaddleLargeTailCandidateTemperedLowerPrefixTopOffsetRawBudgetChunksCertificate :
    PositiveSaddleLargeTailCandidateTemperedLowerPrefixTopOffsetRawBudgetChunksCertificate
      999 10 where
  aLenPos := by norm_num
  tLenPos := by norm_num
  lowerPrefixTopOffsetRawBudgetChunk := by
    intro aChunk tChunk haChunk htChunk
    rcases (mem_positiveLargeTailLowerPrefixAChunks_iff
        (by norm_num : 0 < 999)).mp haChunk with
      ⟨i, hi, rfl⟩
    rcases (mem_positiveLargeTailLowerTopOffsetTChunks_iff
        (by norm_num : 0 < 10)).mp htChunk with
      ⟨j, hj, rfl⟩
    norm_num at hi hj
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst i
    subst j
    exact checkPositiveTemperedLowerPrefixTopOffsetRawBudgetChunk_2001_999_0_10

end Prop51
