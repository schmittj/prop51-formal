import Prop51.PositiveSaddleChunks

namespace Prop51

set_option maxHeartbeats 0

/-!
Generated scaled fixed-point finite tangent-edge shard.

This checks the second retained-`k` chunk for the first active `N` chunk over
`401 ≤ a < 501`.  It extends `positiveSaddleFiniteTangentShard0` along the
same fixed-`N`/`k` bounded checker route.
-/

theorem positiveSaddleFiniteTangentShard0K21 :
    checkPositiveSmallTangentExpEdgeFixedNIndexRowRangeKChunk
      20 401 100
      0 21 20 = true := by
  exact
    checkPositiveSmallTangentExpEdgeFixedNIndexRowRangeKChunk_of_scaledExpFallback
      (S := 10^20)
      (by norm_num) (by norm_num) (by norm_num)
      (by native_decide)

end Prop51
