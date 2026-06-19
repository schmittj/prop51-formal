import Prop51.PositiveSaddleChunks

namespace Prop51

set_option maxHeartbeats 0

/-!
Generated finite displayed-solo unit-budget shard.

This checks the same first fixed `N` chunk and first ten bounded rows as
`positiveSaddleFiniteSoloSaddleShard0Rows10`, but for the normalized
unit-budget solo condition.
-/

theorem positiveSaddleFiniteSoloBudgetShard0Rows10 :
    checkPositiveSoloDisplayedYBoundUnitFixedNIndexRowRange
      20 401 10
      0 = true := by
  native_decide

end Prop51
