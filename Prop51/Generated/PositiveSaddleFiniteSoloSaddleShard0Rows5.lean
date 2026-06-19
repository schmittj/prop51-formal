import Prop51.PositiveSaddleChunks

namespace Prop51

set_option maxHeartbeats 0

/-!
Generated finite displayed-solo saddle shard.

This checks the first fixed `N` chunk for `401 ≤ a < 406`.  Benchmarking
showed that this exact rational solo saddle checker is much heavier than the
tangent fixed-point checker: five rows are close to the practical shard limit
for the current route.
-/

theorem positiveSaddleFiniteSoloSaddleShard0Rows5 :
    checkPositiveSoloDisplayedYSaddleClearedFixedNIndexRowRange
      20 401 5
      0 = true := by
  native_decide

end Prop51
