import Prop51.PositiveSaddleChunks
import Prop51.Generated.PositiveSaddleFiniteScaledEdgeShard0
import Prop51.Generated.PositiveSaddleFiniteScaledEdgeShard1
import Prop51.Generated.PositiveSaddleFiniteScaledEdgeShard2
import Prop51.Generated.PositiveSaddleFiniteScaledEdgeShard3
import Prop51.Generated.PositiveSaddleFiniteScaledEdgeShard4
import Prop51.Generated.PositiveSaddleFiniteScaledEdgeShard5
import Prop51.Generated.PositiveSaddleFiniteScaledEdgeShard6
import Prop51.Generated.PositiveSaddleFiniteScaledEdgeShard7
import Prop51.Generated.PositiveSaddleFiniteScaledEdgeShard8
import Prop51.Generated.PositiveSaddleFiniteScaledEdgeShard9
import Prop51.Generated.PositiveSaddleFiniteScaledEdgeShard10
import Prop51.Generated.PositiveSaddleFiniteScaledEdgeShard11
import Prop51.Generated.PositiveSaddleFiniteScaledEdgeShard12
import Prop51.Generated.PositiveSaddleFiniteScaledEdgeShard13
import Prop51.Generated.PositiveSaddleFiniteScaledEdgeShard14
import Prop51.Generated.PositiveSaddleFiniteScaledEdgeShard15

namespace Prop51

/- Generated assembly for the scaled fixed-point finite edge-budget shards.

The Lean-side deviation from the TeX exact-rational scan is confined to the
imported shard proofs: each shard proves the canonical
`checkPositiveEdgeBudgetUnitRange` predicate through a verified upward-rounded
fixed-point exponential upper bound.  This file only combines those canonical
range predicates over the standard 100-row finite-window cover. -/

theorem positiveSaddleFiniteScaledEdgeRanges :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleFixedRowChunks 100 →
      checkPositiveEdgeBudgetUnitRange chunk.1 chunk.2 = true := by
  intro chunk hchunk
  rcases (mem_positiveSaddleFixedRowChunks_iff (by norm_num : 0 < 100)).1
      hchunk with
    ⟨i, hi, rfl⟩
  norm_num at hi
  interval_cases i
  · simpa using positiveSaddleFiniteScaledEdgeShard0
  · simpa using positiveSaddleFiniteScaledEdgeShard1
  · simpa using positiveSaddleFiniteScaledEdgeShard2
  · simpa using positiveSaddleFiniteScaledEdgeShard3
  · simpa using positiveSaddleFiniteScaledEdgeShard4
  · simpa using positiveSaddleFiniteScaledEdgeShard5
  · simpa using positiveSaddleFiniteScaledEdgeShard6
  · simpa using positiveSaddleFiniteScaledEdgeShard7
  · simpa using positiveSaddleFiniteScaledEdgeShard8
  · simpa using positiveSaddleFiniteScaledEdgeShard9
  · simpa using positiveSaddleFiniteScaledEdgeShard10
  · simpa using positiveSaddleFiniteScaledEdgeShard11
  · simpa using positiveSaddleFiniteScaledEdgeShard12
  · simpa using positiveSaddleFiniteScaledEdgeShard13
  · simpa using positiveSaddleFiniteScaledEdgeShard14
  · simpa using positiveSaddleFiniteScaledEdgeShard15

theorem positiveSaddleFiniteScaledEdgeBudget :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeMajorantSum a ≤ positiveEdgeBudget := by
  intro a ha h2000
  exact positiveEdgeBudget_of_checkPositiveEdgeBudgetUnitRow
    (checkPositiveEdgeBudgetUnitRow_of_checkPositiveEdgeBudgetUnitRangeChunks
      (chunks := positiveSaddleFixedRowChunks 100)
      (by
        intro chunk hchunk
        exact positiveSaddleFiniteScaledEdgeRanges hchunk)
      ((positiveSaddleFixedRowChunks_cover (by norm_num : 0 < 100)) ha h2000))

end Prop51
