import Prop51.PositiveSaddleChunks

namespace Prop51

set_option maxHeartbeats 0

/-!
Generated finite displayed-solo saddle shard.

This checks the first fixed `N` chunk for `401 ≤ a < 406`.  Benchmarking
showed that this exact rational solo saddle checker is much heavier than the
tangent fixed-point checker: five rows are close to the practical shard limit
for the current route.  The proof now uses the verified hybrid fixed-point
exponential checker, falling back to the exact rational cell checker only when
the rounded lower bound is too conservative.
-/

theorem positiveSaddleFiniteSoloSaddleShard0Rows5 :
    checkPositiveSoloDisplayedYSaddleClearedFixedNIndexRowRange
      20 401 5
      0 = true := by
  exact
    checkPositiveSoloDisplayedYSaddleClearedFixedNIndexRowRange_of_scaledExpFallback
      (S := 10^4) (nLen := 20) (lo := 401) (len := 5) (nIndex := 0)
      (by norm_num) (by norm_num) (by norm_num)
      (by native_decide)

end Prop51
