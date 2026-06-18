import Prop51.PositiveSaddleChunks

namespace Prop51

/- Generated finite-window positive-saddle atom shard. -/

/-
Individual finite-window atom shard.
Shard 1 of 8752; balanced by atoms; atoms 0 <= i < 1 out of 8752.
Fields: ['edge-fixed'].
-/

theorem positiveSaddleFiniteEdgeShard_edge_fixed_r0_k0 :
    checkPositiveEdgeMajorantKChunkUnitRowRange
      401 10 1 20
      (fun _ => positiveEdgeFixedKScaleUpTo 20 (posKmax 411)) = true := by
  exact
    checkPositiveEdgeMajorantKChunkUnitRowRange_of_checkPositiveEdgeMajorantKChunkUnitRowRangeFast
      (by native_decide)

end Prop51
