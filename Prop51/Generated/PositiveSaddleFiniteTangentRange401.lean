import Prop51.PositiveSaddleChunks

namespace Prop51

/-!
Generated scaled fixed-point finite tangent row-range shard.

This compact shard checks the full tangent-edge row `a = 401` with the
verified upward-rounded fixed-point checker.  The bridge
`checkPositiveSmallTangentExpEdgeFixedNIndexRowRangeKChunk_of_checkRangeScaledExp`
can project this row-range result to any active fixed-`N`/`k` chunk required by
the bounded active analytic constructor.
-/

theorem positiveSaddleFiniteTangentRange401 :
    checkPositiveSmallTangentExpEdgeRangeScaledExp (10^20) 401 1 = true := by
  native_decide

end Prop51
