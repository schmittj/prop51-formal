import Prop51.PositiveSaddleChunks

namespace Prop51

set_option maxHeartbeats 0

/-!
Generated finite displayed-solo saddle shard.

This checks the first fixed `N` chunk for `401 ≤ a < 411` using the row-cached
hybrid fixed-point solo saddle checker.  The cached checker shares `cList a`
and the rounded solo exponential across each row; this makes a 10-row shard
compile where the previous uncached/hybrid 10-row check timed out.
-/

theorem positiveSaddleFiniteSoloSaddleShard0Rows10 :
    checkPositiveSoloDisplayedYSaddleClearedFixedNIndexRowRange
      20 401 10
      0 = true := by
  exact
    checkPositiveSoloDisplayedYSaddleClearedFixedNIndexRowRange_of_scaledExpCached
      (S := 10^4) (nLen := 20) (lo := 401) (len := 10) (nIndex := 0)
      (by norm_num) (by norm_num) (by norm_num)
      (by native_decide)

end Prop51
