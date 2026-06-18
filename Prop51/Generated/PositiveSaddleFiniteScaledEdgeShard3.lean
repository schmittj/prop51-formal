import Prop51.PositiveSaddle

namespace Prop51

set_option maxHeartbeats 600000

/- Generated scaled fixed-point finite edge-budget shard.

This shard intentionally proves the existing canonical
`checkPositiveEdgeBudgetUnitRange` predicate through
`checkPositiveEdgeBudgetUnitRangeScaledExp`.  The Lean-side deviation from the
TeX/exact-rational scan is only computational: `partialExpUpper` is replaced
by a verified upward-rounded fixed-point upper bound. -/

theorem positiveSaddleFiniteScaledEdgeShard3 :
    checkPositiveEdgeBudgetUnitRange 701 100 = true := by
  exact
    checkPositiveEdgeBudgetUnitRange_of_checkPositiveEdgeBudgetUnitRangeScaledExp
      (S := 10^20) (lo := 701) (len := 100)
      (by norm_num) (by norm_num) (by norm_num)
      (by native_decide)

end Prop51
