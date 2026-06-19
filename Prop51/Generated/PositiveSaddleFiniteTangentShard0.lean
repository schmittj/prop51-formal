import Prop51.PositiveSaddleChunks

namespace Prop51

/- Generated scaled fixed-point finite tangent-edge shard.

This shard proves one bounded-window `smallTangentExpEdge` atom through the
verified upward-rounded fixed-point exponential fallback checker.  It is the
first checked artifact for the bounded tangent field; it is not yet assembled
into the public bounded certificate. -/

theorem positiveSaddleFiniteTangentShard0 :
    checkPositiveSmallTangentExpEdgeFixedNIndexRowRangeKChunk
      20 401 100
      0 1 20 = true := by
  exact
    checkPositiveSmallTangentExpEdgeFixedNIndexRowRangeKChunk_of_scaledExpFallback
      (S := 10^20)
      (by norm_num) (by norm_num) (by norm_num)
      (by native_decide)

end Prop51
