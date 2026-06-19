import Prop51.PositiveSaddleChunks

namespace Prop51

set_option maxHeartbeats 0

/-!
Generated scaled fixed-point finite tangent-edge shard near `a = 2000`.

This checks the first active `N` chunk and first retained-`k` chunk for
`1901 ≤ a < 2001`, giving a representative benchmark/proof artifact near the
top of the finite window.
-/

theorem positiveSaddleFiniteTangentShard2000 :
    checkPositiveSmallTangentExpEdgeFixedNIndexRowRangeKChunk
      20 1901 100
      0 1 20 = true := by
  exact
    checkPositiveSmallTangentExpEdgeFixedNIndexRowRangeKChunk_of_scaledExpFallback
      (S := 10^20)
      (by norm_num) (by norm_num) (by norm_num)
      (by native_decide)

end Prop51
