import Prop51.Main

namespace Prop51

/-!
First direct raw-product finite shard.

This targets the bounded product field directly through
`checkPositiveXYProductRawClearedTableFixedNIndexRowRangeKChunk`, avoiding the
independent `Xplus`/`Gcomp` product surrogate that is known to be too strong.
It covers the first row `a = 401`, the first 20 active `N` values, and
retained `k = 1,...,5`.
-/

theorem positiveSaddleFiniteProductCombinedShard0_a401_n0_k1to5 :
    checkPositiveXYProductRawClearedTableFixedNIndexRowRangeKChunk
      20 401 1 0 1 5 = true := by
  native_decide

end Prop51
