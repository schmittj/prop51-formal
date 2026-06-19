import Prop51.PositiveSaddleChunks

namespace Prop51

set_option maxHeartbeats 0

/-!
Generated scaled fixed-point finite tangent-edge shard near `a = 1000`.

This checks the first active `N` chunk and first retained-`k` chunk for
`901 ≤ a < 1001`, giving a representative benchmark/proof artifact away from
the lowest row block.
-/

theorem positiveSaddleFiniteTangentShard1000 :
    checkPositiveSmallTangentExpEdgeFixedNIndexRowRangeKChunk
      20 901 100
      0 1 20 = true := by
  exact
    checkPositiveSmallTangentExpEdgeFixedNIndexRowRangeKChunk_of_scaledExpFallback
      (S := 10^20)
      (by norm_num) (by norm_num) (by norm_num)
      (by native_decide)

end Prop51
