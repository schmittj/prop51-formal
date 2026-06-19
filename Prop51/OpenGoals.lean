import Prop51.Main
import Prop51.PositiveSaddle
import Prop51.Generated.PositiveSaddleFiniteScaledEdge

namespace Prop51

/-!
`OpenGoals` is the machine-readable dashboard for the remaining route to the
final theorem.

The intended split is `401 ≤ a < 3000` for bounded checking and `3000 ≤ a` for
the analytic tail.  The currently available Lean assembly still has separate
generated interfaces for the old `401 ≤ a ≤ 2000` finite window and the
`2001 ≤ a < 3000` prefix strip; this dashboard packages both on the bounded
side through theorem-facing product/solo pointwise obligations, so the product
and solo inputs are the genuine large-`a` analytic fields.
-/

/-- The actual theorem-facing product prefix obligation on `2000 < a < 3000`.

This is the bounded-strip counterpart of `LargeTailProductCertificate`.  It is
deliberately stated as the normalized combined-product target used downstream,
not as the older exact upper-edge split-factorial product chunks.  Those chunks
are still available below as a compatibility proof producer, but the bounded
checker route should target this pointwise statement directly. -/
structure PositiveSaddleLargeTailProductPrefixPointwise : Prop where
  small :
    ∀ {a N k : Nat}, 2000 < a → a < 3000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        Xnorm N k * Ynorm N (posJ a k)
          ≤ positiveSmallLargeGcompProductTarget a N k
  tempered :
    ∀ {a N k : Nat}, 2000 < a → a < 3000 → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k →
        Xnorm N k * Ynorm N (posJ a k)
          ≤ positiveTemperedLargeGcompProductTarget a N k

/-- The actual theorem-facing solo prefix obligation on `2000 < a < 3000`.

This replaces the earlier exact upper-edge split-sum scalar chunks as the
canonical bounded field.  Those exact chunks are still available below as a
compatibility proof producer, but benchmarking showed that they are too heavy
to be the main completion route. -/
def PositiveSaddleLargeTailSoloPrefixNormUnit : Prop :=
  ∀ {a N : Nat}, 2000 < a → a < 3000 → positiveRectangle a N →
    (200000000 : ℚ) * normalizedSoloTerm a N ≤ 1

/-- Compatibility bridge from the older exact fast-upper-edge solo prefix
chunks to the actual solo norm prefix target.

The canonical bounded certificate now asks for
`PositiveSaddleLargeTailSoloPrefixNormUnit` directly; this theorem records the
Lean-side deviation from the older generated exact-split route without
discarding that route. -/
theorem positiveSaddleLargeTailSoloPrefixNormUnit_of_fastUpperEdgeBoundPrefixChunks
    {aLen : Nat}
    (hprefix :
      PositiveSaddleLargeTailSoloFastUpperEdgeBoundPrefixChunksCertificate
        positiveLargeTailSoloUpperEdgeExactBound aLen) :
    PositiveSaddleLargeTailSoloPrefixNormUnit := by
  intro a N ha haPrefix hrect
  have hscalar :
      positiveLargeTailSoloFastUpperEdgeBoundScalar
        positiveLargeTailSoloUpperEdgeExactBound a :=
    hprefix.toPrefixCertificate.soloScalar ha haPrefix
  have hfast :
      positiveLargeTailSoloGcompClosedFactorialSplitBlockSumFastCleared
        a (posNhi a) := by
    unfold positiveLargeTailSoloFastUpperEdgeBoundScalar at hscalar
    unfold positiveLargeTailSoloGcompClosedFactorialSplitBlockSumFastCleared
    simpa [positiveLargeTailSoloUpperEdgeExactBound] using hscalar
  have hY :
      positiveYgcompBound N a ≤ positiveLargeTailSoloTenSeventhsBound a N :=
    positiveYgcompBound_le_positiveLargeTailSoloTenSeventhsBound_of_gcompSaddleCleared
      (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect) ha
      (positiveLargeTailSoloGcompSaddleCleared_of_closedFactorialSplitBlockSumFastCleared
        (positiveLargeTailSoloGcompClosedFactorialSplitBlockSumFastCleared_of_upperEdge
          (a := a) (N := N) hrect hfast))
  have hYUnit :
      (200000000 : ℚ) *
          (positiveDyadicDecay a / 2 * positiveYgcompBound N a)
        ≤ 1 :=
    positiveLargeTailSoloYUnit_of_Y_bound hY
      (positiveLargeTailSoloTenSeventhsScalarBudget ha hrect)
  exact positiveLargeTailSoloNormUnit_of_Y_unit
    (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect)
    (by omega : 1 ≤ a) hYUnit

/-- Direct sharp proof of the bounded solo prefix norm-unit field.

This intentionally bypasses the older generated exact-split prefix chunks.
The proof uses the sharp `Qq` saddle target and the constant-budget split
estimate in `PositiveSaddle`, so the `2001 ≤ a < 3000` strip is handled by the
same analytic solo machinery as the tail rather than by a finite grid. -/
theorem positiveSaddleLargeTailSoloPrefixNormUnit_of_sharpConst :
    PositiveSaddleLargeTailSoloPrefixNormUnit := by
  intro a N ha _haPrefix hrect
  have hdelta :
      (4 : ℚ) * (2 : ℚ)^a *
          positiveLargeTailSoloSharpDeltaBudgetBlockSum a (posNhi a)
        ≤ 29 * (a : ℚ) * c a * (10 / 7 : ℚ)^a := by
    have hdelta_le :
        positiveLargeTailSoloSharpDeltaBudgetBlockSum a (posNhi a)
          ≤ positiveLargeTailSoloSharpLargeDegreeSplitBudgetBlockSum a :=
      positiveLargeTailSoloSharpDeltaBudgetBlockSum_upperEdge_le_largeDegreeSplit
        (a := a) (by omega : 361 ≤ a)
    have hscale : 0 ≤ (4 : ℚ) * (2 : ℚ)^a := by
      positivity
    exact (mul_le_mul_of_nonneg_left hdelta_le hscale).trans
      (positiveLargeTailSoloSharpLargeDegreeSplitBudgetBlockSum_scaled_le_target_of_const
        (a := a) (by omega : 802 ≤ a))
  have hEdge :
      positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSumTenSeventhsCleared
        a (posNhi a) :=
    positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSumTenSeventhsCleared_of_deltaBudgetBlockSum
      hdelta
  exact
    positiveLargeTailSoloNormUnit_of_sharpGcompSaddleTenSeventhsCleared
      ha hrect
      (positiveLargeTailSoloSharpGcompSaddleTenSeventhsCleared_of_closedFactorialSplitBlockSumTenSeventhsCleared
        (positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSumTenSeventhsCleared_of_upperEdge
          hrect hEdge))

/-- Compatibility bridge from the older exact fast-upper-edge product prefix
chunks to the actual product prefix pointwise target.

The bounded certificate now asks for
`PositiveSaddleLargeTailProductPrefixPointwise` directly.  This theorem keeps
the legacy exact-split route usable for comparison and small exceptions, while
allowing the main bounded checker to avoid compiling those heavy chunks. -/
theorem positiveSaddleLargeTailProductPrefixPointwise_of_fastUpperEdgeLowerNProductBoundPrefixChunks
    {aLen kLen : Nat}
    (hprefix :
      PositiveSaddleLargeTailProductFastUpperEdgeLowerNProductBoundPrefixChunksCertificate
        (fun a k =>
          positiveLargeTailProductXUpperEdgeExactBound a k *
            positiveLargeTailProductYUpperEdgeExactBound a k)
        aLen kLen) :
    PositiveSaddleLargeTailProductPrefixPointwise where
  small := by
    intro a N k ha haPrefix hrect hk hsmall
    have hsmallEdge : k ≤ ceilSqrt (posNhi a) :=
      hsmall.trans (ceilSqrt_mono hrect.2)
    have hprod :
        positiveXplusYProductGcompBound a N k
          ≤ positiveSmallLargeGcompProductTarget a N k :=
      positiveXplusYProductGcompBound_le_smallLargeGcompProductTarget_of_fastUpperEdgeLowerN
        ha hrect hk
        (hprefix.toPrefixCertificate.smallScalar
          ha haPrefix hk hsmallEdge)
    exact
      (Xnorm_mul_Ynorm_le_of_Xplus_mul_Ynorm
        (XplusYnorm_le_positiveXplusYProductGcompBound a N k)).trans hprod
  tempered := by
    intro a N k ha haPrefix hrect hk htempered
    have htemperedEdge : ceilSqrt (posNlo a) < k :=
      lt_of_le_of_lt (ceilSqrt_mono hrect.1) htempered
    have hprod :
        positiveXplusYProductGcompBound a N k
          ≤ positiveTemperedLargeGcompProductTarget a N k :=
      positiveXplusYProductGcompBound_le_temperedLargeGcompProductTarget_of_fastUpperEdgeLowerN
        ha hrect hk
        (hprefix.toPrefixCertificate.temperedScalar
          ha haPrefix hk htemperedEdge)
    exact
      (Xnorm_mul_Ynorm_le_of_Xplus_mul_Ynorm
        (XplusYnorm_le_positiveXplusYProductGcompBound a N k)).trans hprod

/-- Constructor from denominator-cleared actual-product bounds on the bounded
prefix strip.

This is the proof surface intended for the endpoint-reduced bounded checker:
it proves the same theorem-facing product target as the legacy exact prefix
chunks, but its inputs are the actual `Bq * Qq` raw inequalities. -/
theorem PositiveSaddleLargeTailProductPrefixPointwise.ofRawCleared
    (hsmall :
      ∀ {a N k : Nat}, 2000 < a → a < 3000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          positiveSmallLargeXYProductRawCleared a N k)
    (htempered :
      ∀ {a N k : Nat}, 2000 < a → a < 3000 → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k →
          positiveTemperedLargeXYProductRawCleared a N k) :
    PositiveSaddleLargeTailProductPrefixPointwise where
  small := by
    intro a N k ha haPrefix hrect hk hsmallN
    exact
      positiveSmallLargeXYProductTarget_of_rawCleared
        (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect)
        (by omega : 1 ≤ a) hk
        (hsmall ha haPrefix hrect hk hsmallN)
  tempered := by
    intro a N k ha haPrefix hrect hk htemperedN
    exact
      positiveTemperedLargeXYProductTarget_of_rawCleared
        (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect)
        (by omega : 2 ≤ a) hk
        (htempered ha haPrefix hrect hk htemperedN)

/-- Constructor from raw actual-product bounds away from the sign-lock zone
on the bounded prefix strip.

The sign-lock cells contribute a nonpositive actual product, so the bounded
checker only needs to prove raw-cleared inequalities on the complement. -/
theorem PositiveSaddleLargeTailProductPrefixPointwise.ofRawClearedAwayFromSignLock
    (hsmall :
      ∀ {a N k : Nat}, 2000 < a → a < 3000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          ¬ (361 ≤ k ∧ (N : ℚ) ≤ (40 / 3 : ℚ) * (k : ℚ)) →
          positiveSmallLargeXYProductRawCleared a N k)
    (htempered :
      ∀ {a N k : Nat}, 2000 < a → a < 3000 → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k →
          ¬ (361 ≤ k ∧ (N : ℚ) ≤ (40 / 3 : ℚ) * (k : ℚ)) →
          positiveTemperedLargeXYProductRawCleared a N k) :
    PositiveSaddleLargeTailProductPrefixPointwise where
  small := by
    intro a N k ha haPrefix hrect hk hsmallN
    have hN : 1 ≤ N :=
      positiveRectangle_N_pos (by omega : 2 ≤ a) hrect
    by_cases hlock :
        361 ≤ k ∧ (N : ℚ) ≤ (40 / 3 : ℚ) * (k : ℚ)
    · exact
        positiveSmallLargeXYProductTarget_of_signLock
          ha hN hk hlock.1 hlock.2
    · exact
        positiveSmallLargeXYProductTarget_of_rawCleared hN
          (by omega : 1 ≤ a) hk
          (hsmall ha haPrefix hrect hk hsmallN hlock)
  tempered := by
    intro a N k ha haPrefix hrect hk htemperedN
    have hN : 1 ≤ N :=
      positiveRectangle_N_pos (by omega : 2 ≤ a) hrect
    by_cases hlock :
        361 ≤ k ∧ (N : ℚ) ≤ (40 / 3 : ℚ) * (k : ℚ)
    · exact
        positiveTemperedLargeXYProductTarget_of_signLock
          ha hN hk hlock.1 hlock.2
    · exact
        positiveTemperedLargeXYProductTarget_of_rawCleared hN
          (by omega : 2 ≤ a) hk
          (htempered ha haPrefix hrect hk htemperedN hlock)

/-- Prefix-strip constructor with the sign-lock complement stated as the
integer inequality used by executable checkers. -/
theorem PositiveSaddleLargeTailProductPrefixPointwise.ofRawClearedNatSignLockComplement
    (hsmall :
      ∀ {a N k : Nat}, 2000 < a → a < 3000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          positiveSmallLargeXYProductRawCleared a N k)
    (htempered :
      ∀ {a N k : Nat}, 2000 < a → a < 3000 → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k →
          (k < 361 ∨ 40 * k < 3 * N) →
          positiveTemperedLargeXYProductRawCleared a N k) :
    PositiveSaddleLargeTailProductPrefixPointwise :=
  PositiveSaddleLargeTailProductPrefixPointwise.ofRawClearedAwayFromSignLock
    (by
      intro a N k ha haPrefix hrect hk hsmallN _hnotLock
      exact hsmall ha haPrefix hrect hk hsmallN)
    (by
      intro a N k ha haPrefix hrect hk htemperedN hnotLock
      exact htempered ha haPrefix hrect hk htemperedN
        (signLock_natAlternative_of_not hnotLock))

/-- Prefix-strip constructor from raw actual-product bounds only on cells
where the coefficient `Bq N k` is positive. -/
theorem PositiveSaddleLargeTailProductPrefixPointwise.ofRawClearedBqPositive
    (hsmall :
      ∀ {a N k : Nat}, 2000 < a → a < 3000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N → 0 < Bq N k →
          positiveSmallLargeXYProductRawCleared a N k)
    (htempered :
      ∀ {a N k : Nat}, 2000 < a → a < 3000 → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k → 0 < Bq N k →
          positiveTemperedLargeXYProductRawCleared a N k) :
    PositiveSaddleLargeTailProductPrefixPointwise :=
  PositiveSaddleLargeTailProductPrefixPointwise.ofRawCleared
    (by
      intro a N k ha haPrefix hrect hk hsmallN
      by_cases hB : 0 < Bq N k
      · exact hsmall ha haPrefix hrect hk hsmallN hB
      · exact
          positiveSmallLargeXYProductRawCleared_of_Bq_nonpos
            ha hk (le_of_not_gt hB))
    (by
      intro a N k ha haPrefix hrect hk htemperedN
      by_cases hB : 0 < Bq N k
      · exact htempered ha haPrefix hrect hk htemperedN hB
      · exact
          positiveTemperedLargeXYProductRawCleared_of_Bq_nonpos
            ha hk (le_of_not_gt hB))

/-- Prefix-strip constructor combining the nonpositive-`Bq` shortcut with the
integer sign-lock complement for the tempered branch. -/
theorem PositiveSaddleLargeTailProductPrefixPointwise.ofRawClearedBqPositiveNatSignLockComplement
    (hsmall :
      ∀ {a N k : Nat}, 2000 < a → a < 3000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N → 0 < Bq N k →
          positiveSmallLargeXYProductRawCleared a N k)
    (htempered :
      ∀ {a N k : Nat}, 2000 < a → a < 3000 → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k →
          (k < 361 ∨ 40 * k < 3 * N) → 0 < Bq N k →
          positiveTemperedLargeXYProductRawCleared a N k) :
    PositiveSaddleLargeTailProductPrefixPointwise :=
  PositiveSaddleLargeTailProductPrefixPointwise.ofRawClearedNatSignLockComplement
    (by
      intro a N k ha haPrefix hrect hk hsmallN
      by_cases hB : 0 < Bq N k
      · exact hsmall ha haPrefix hrect hk hsmallN hB
      · exact
          positiveSmallLargeXYProductRawCleared_of_Bq_nonpos
            ha hk (le_of_not_gt hB))
    (by
      intro a N k ha haPrefix hrect hk htemperedN hnotLock
      by_cases hB : 0 < Bq N k
      · exact htempered ha haPrefix hrect hk htemperedN hnotLock hB
      · exact
          positiveTemperedLargeXYProductRawCleared_of_Bq_nonpos
            ha hk (le_of_not_gt hB))

/-- Prefix-strip constructor after the first-coefficient sign reduction.

Since `Bq N 1 ≤ 0`, the checker-facing positive-`Bq` domain starts at
`k = 2`; this version records that reduction explicitly. -/
theorem PositiveSaddleLargeTailProductPrefixPointwise.ofRawClearedBqPositiveGeTwoNatSignLockComplement
    (hsmall :
      ∀ {a N k : Nat}, 2000 < a → a < 3000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N → 2 ≤ k → 0 < Bq N k →
          positiveSmallLargeXYProductRawCleared a N k)
    (htempered :
      ∀ {a N k : Nat}, 2000 < a → a < 3000 → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k →
          (k < 361 ∨ 40 * k < 3 * N) → 2 ≤ k → 0 < Bq N k →
          positiveTemperedLargeXYProductRawCleared a N k) :
    PositiveSaddleLargeTailProductPrefixPointwise :=
  PositiveSaddleLargeTailProductPrefixPointwise.ofRawClearedBqPositiveNatSignLockComplement
    (by
      intro a N k ha haPrefix hrect hk hsmallN hB
      exact hsmall ha haPrefix hrect hk hsmallN
        (two_le_of_Bq_pos (mem_positiveKRange.mp hk).1 hB) hB)
    (by
      intro a N k ha haPrefix hrect hk htemperedN hnotLock hB
      exact htempered ha haPrefix hrect hk htemperedN hnotLock
        (two_le_of_Bq_pos (mem_positiveKRange.mp hk).1 hB) hB)

/-- In the post-`2000` positive rectangle, the first retained `Bq`
coefficient is already strictly positive. -/
theorem Bq_two_pos_of_gt_2000_positiveRectangle {a N : Nat} (ha : 2000 < a)
    (hrect : positiveRectangle a N) :
    0 < Bq N 2 :=
  Bq_two_pos_of_le (by
    have hNlo : posNlo a ≤ N := hrect.1
    unfold posNlo at hNlo
    omega)

/-- Prefix-strip constructor that splits off the first retained product cell.

After the `Bq N 1 ≤ 0` reduction, the bounded checker can treat `k = 2`
separately and send the genuine tail to a `k ≥ 3` checker, matching the
large-tail product split. -/
theorem PositiveSaddleLargeTailProductPrefixPointwise.ofRawClearedBqPositiveTwoAndGeThreeNatSignLockComplement
    (hsmallTwo :
      ∀ {a N : Nat}, 2000 < a → a < 3000 → positiveRectangle a N →
        positiveSmallLargeXYProductRawCleared a N 2)
    (hsmallGeThree :
      ∀ {a N k : Nat}, 2000 < a → a < 3000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N → 3 ≤ k → 0 < Bq N k →
          positiveSmallLargeXYProductRawCleared a N k)
    (htemperedGeThree :
      ∀ {a N k : Nat}, 2000 < a → a < 3000 → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k →
          (k < 361 ∨ 40 * k < 3 * N) → 3 ≤ k → 0 < Bq N k →
          positiveTemperedLargeXYProductRawCleared a N k) :
    PositiveSaddleLargeTailProductPrefixPointwise :=
  PositiveSaddleLargeTailProductPrefixPointwise.ofRawClearedBqPositiveGeTwoNatSignLockComplement
    (by
      intro a N k ha haPrefix hrect hk hsmallN hk2 hB
      by_cases hk_eq : k = 2
      · subst k
        exact hsmallTwo ha haPrefix hrect
      · exact hsmallGeThree ha haPrefix hrect hk hsmallN (by omega) hB)
    (by
      intro a N k ha haPrefix hrect hk htemperedN hnotLock hk2 hB
      by_cases hk_eq : k = 2
      · subst k
        have hNgt : 4 < N := by
          have hNlo : posNlo a ≤ N := hrect.1
          unfold posNlo at hNlo
          omega
        have hceil : 2 < ceilSqrt N :=
          lt_ceilSqrt_of_sq_lt (n := N) (k := 2) (by
            norm_num
            exact hNgt)
        omega
      · exact htemperedGeThree ha haPrefix hrect hk htemperedN hnotLock
          (by omega) hB)

/-- Fast-exp variant of
`PositiveSaddleLargeTailProductPrefixPointwise.ofRawClearedBqPositiveTwoAndGeThreeNatSignLockComplement`.

The assumptions are the same reduced actual-product domain, but the
denominator-cleared inequalities use the executable large-exp evaluator.
This is the intended bounded-prefix proof surface once endpoint or compact row
checking supplies the remaining cells. -/
theorem PositiveSaddleLargeTailProductPrefixPointwise.ofRawClearedFastExpBqPositiveTwoAndGeThreeNatSignLockComplement
    (hsmallTwo :
      ∀ {a N : Nat}, 2000 < a → a < 3000 → positiveRectangle a N →
        positiveSmallLargeXYProductRawClearedFastExp a N 2)
    (hsmallGeThree :
      ∀ {a N k : Nat}, 2000 < a → a < 3000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N → 3 ≤ k → 0 < Bq N k →
          positiveSmallLargeXYProductRawClearedFastExp a N k)
    (htemperedGeThree :
      ∀ {a N k : Nat}, 2000 < a → a < 3000 → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k →
          (k < 361 ∨ 40 * k < 3 * N) → 3 ≤ k → 0 < Bq N k →
          positiveTemperedLargeXYProductRawClearedFastExp a N k) :
    PositiveSaddleLargeTailProductPrefixPointwise :=
  PositiveSaddleLargeTailProductPrefixPointwise.ofRawClearedBqPositiveTwoAndGeThreeNatSignLockComplement
    (by
      intro a N ha haPrefix hrect
      exact positiveSmallLargeXYProductRawCleared_of_fastExp
        (hsmallTwo ha haPrefix hrect))
    (by
      intro a N k ha haPrefix hrect hk hsmallN hk3 hB
      exact positiveSmallLargeXYProductRawCleared_of_fastExp
        (hsmallGeThree ha haPrefix hrect hk hsmallN hk3 hB))
    (by
      intro a N k ha haPrefix hrect hk htemperedN hnotLock hk3 hB
      exact positiveTemperedLargeXYProductRawCleared_of_fastExp
        (htemperedGeThree ha haPrefix hrect hk htemperedN hnotLock hk3 hB))

/-- Direct saddle proof of the entire bounded product-prefix pointwise field.

This is the bounded-strip counterpart of the direct large-tail route: it
targets the actual raw `Bq * Qq` predicates and does not use the legacy exact
upper-edge split-product grid. -/
theorem PositiveSaddleLargeTailProductPrefixPointwise.ofDirectSaddle :
    PositiveSaddleLargeTailProductPrefixPointwise :=
  PositiveSaddleLargeTailProductPrefixPointwise.ofRawClearedBqPositiveTwoAndGeThreeNatSignLockComplement
    (by
      intro a N ha _haPrefix hrect
      have hk : 2 ∈ positiveKRange a := by
        refine mem_positiveKRange.mpr ⟨by omega, ?_⟩
        unfold posKmax
        rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 10)]
        omega
      have hsmall : 2 ≤ ceilSqrt N := by
        have hNgt : 1 * 1 < N := by
          have hlo : posNlo a ≤ N := hrect.1
          unfold posNlo at hlo
          omega
        have hceil : 1 < ceilSqrt N :=
          lt_ceilSqrt_of_sq_lt (n := N) (k := 1) hNgt
        omega
      exact positiveSmallLargeXYProductRawCleared_of_directSaddle_geTwo
        ha hrect hk hsmall (by omega))
    (by
      intro a N k ha _haPrefix hrect hk hsmallN hk3 _hB
      exact positiveSmallLargeXYProductRawCleared_of_directSaddle_geTwo
        ha hrect hk hsmallN (by omega))
    (by
      intro a N k ha _haPrefix hrect hk htemperedN _hnotLock _hk3 _hB
      exact positiveTemperedLargeXYProductRawCleared_of_directSaddle
        ha hrect hk htemperedN)

/-- The bounded positive-saddle obligation for the current canonical route.

This is intentionally route-facing: the finite `401 ≤ a ≤ 2000` input is any
proof producer that can build the existing positive-saddle certificate from the
live large-tail pointwise and candidate/reserve inputs.  This lets the bounded
route consume either the older tangent-product chunks or the newer direct
edge-majorant checker without changing `Completion.lean`.

The `2001 ≤ a < 3000` strip is carried by the direct product prefix pointwise
and solo prefix norm targets above.  This is a Lean-side divergence from the
older generated exact upper-edge chunks: those chunks are kept as compatibility
proof producers, not as theorem-facing fields. -/
structure BoundedPositiveCertificate where
  toPositiveSaddleCertificate :
    PositiveSaddleEntropyShadowLargeExpPointwiseCertificate →
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate →
        PositiveSaddleCertificate (fun _ => positiveSoloBudget)
  productPrefixPointwise : PositiveSaddleLargeTailProductPrefixPointwise
  soloPrefixNormUnit : PositiveSaddleLargeTailSoloPrefixNormUnit

/-- Endpoint-reduced bounded-window target for the current completion route.

This is the bounded checker surface recommended by the completion plan: prove
the retained positive terms directly below the executable small/tempered edge
majorants on `401 ≤ a ≤ 2000`, plus the finite solo and edge budgets.  The
large-`a` entropy tail is intentionally not a field here; `BoundedPositiveCertificate`
gets it from the current product/solo/candidate route. -/
structure BoundedMajorantBudgetCertificate : Prop where
  small :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        normalizedPositiveIfTerm a N k ≤ positiveSmallMajorantTerm a k
  tempered :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k →
        normalizedPositiveIfTerm a N k ≤ positiveTemperedMajorantTerm a k
  soloY :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget
  edgeBudget :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeMajorantSum a ≤ positiveEdgeBudget

theorem BoundedMajorantBudgetCertificate.toPositiveSaddleCertificate
    (cert : BoundedMajorantBudgetCertificate)
    (pointwise : PositiveSaddleEntropyShadowLargeExpPointwiseCertificate)
    (candidate :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  (show PositiveSaddleMajorantBudgetCertificate from
    { small := cert.small
      tempered := cert.tempered
      soloY := cert.soloY
      edgeBudget := cert.edgeBudget
      entropyTail :=
        (pointwise.toLargeExpCandidateSplitTemperedRawClearedReserveCertificate
          candidate.toRawClearedBoundsCertificate).entropyTail }).toCertificate

/-- Direct bounded-majorant constructor with the generated finite edge budget
inserted.  The remaining bounded checker fields are exactly the finite
small/tempered majorant bounds and finite solo budget. -/
def BoundedMajorantBudgetCertificate.ofScaledEdge
    (small :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          normalizedPositiveIfTerm a N k ≤ positiveSmallMajorantTerm a k)
    (tempered :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k →
          normalizedPositiveIfTerm a N k ≤ positiveTemperedMajorantTerm a k)
    (soloY :
      ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget) :
    BoundedMajorantBudgetCertificate where
  small := small
  tempered := tempered
  soloY := soloY
  edgeBudget := positiveSaddleFiniteScaledEdgeBudget

/-- Completion-facing bounded constructor for the direct edge-majorant route.

This removes the tangent-product interface from the bounded checker target:
future generated bounded rows can certify the actual majorants consumed by the
finite-window assembly, while the prefix strip remains the same theorem-facing
product/solo obligation used by `Completion.lean`. -/
def BoundedPositiveCertificate.ofMajorantBudgetDirectPrefix
    (cert : BoundedMajorantBudgetCertificate)
    (productPrefix : PositiveSaddleLargeTailProductPrefixPointwise)
    (soloPrefix : PositiveSaddleLargeTailSoloPrefixNormUnit) :
    BoundedPositiveCertificate where
  toPositiveSaddleCertificate := cert.toPositiveSaddleCertificate
  productPrefixPointwise := productPrefix
  soloPrefixNormUnit := soloPrefix

/-- Completion-facing direct-majorant bounded constructor with the generated
finite edge budget inserted. -/
def BoundedPositiveCertificate.ofScaledEdgeMajorantDirectPrefix
    (small :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          normalizedPositiveIfTerm a N k ≤ positiveSmallMajorantTerm a k)
    (tempered :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k →
          normalizedPositiveIfTerm a N k ≤ positiveTemperedMajorantTerm a k)
    (soloY :
      ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget)
    (productPrefix : PositiveSaddleLargeTailProductPrefixPointwise)
    (soloPrefix : PositiveSaddleLargeTailSoloPrefixNormUnit) :
    BoundedPositiveCertificate :=
  BoundedPositiveCertificate.ofMajorantBudgetDirectPrefix
    (BoundedMajorantBudgetCertificate.ofScaledEdge small tempered soloY)
    productPrefix soloPrefix

/-- Direct combined-product bounded-majorant constructor with the generated
scaled edge budget inserted.

This is the proof surface for the bounded checker once the retained positive
cells are reduced to combined `X_k(N) * Y_{a-k}(N)` estimates.  Lean handles the
`Bq N k ≤ 0` shortcut and the normalized-summand bookkeeping here; the checker
only has to supply the positive-`Bq` product inequalities and the finite solo
budget. -/
def BoundedMajorantBudgetCertificate.ofCombinedProductScaledEdge
    (smallXY :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N → 0 < Bq N k →
          Xnorm N k * Ynorm N (posJ a k) ≤
            positiveSmallXYProductBound a N k)
    (temperedXY :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k → 0 < Bq N k →
          Xnorm N k * Ynorm N (posJ a k) ≤
            positiveTemperedXYProductBound a N k)
    (soloY :
      ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget) :
    BoundedMajorantBudgetCertificate where
  small := by
    intro a N k ha ha2000 hrect hk hsmall
    exact normalizedPositiveIfTerm_le_smallMajorant_of_XYProduct
      ha ha2000 hrect hk
      (fun hB => smallXY ha ha2000 hrect hk hsmall hB)
  tempered := by
    intro a N k ha ha2000 hrect hk htempered
    exact normalizedPositiveIfTerm_le_temperedMajorant_of_XYProduct
      ha ha2000 hrect hk htempered
      (fun hB => temperedXY ha ha2000 hrect hk htempered hB)
  soloY := soloY
  edgeBudget := positiveSaddleFiniteScaledEdgeBudget

/-- Completion-facing combined-product bounded constructor with direct prefix
fields and the generated scaled edge budget inserted. -/
def BoundedPositiveCertificate.ofCombinedProductScaledEdgeMajorantDirectPrefix
    (smallXY :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N → 0 < Bq N k →
          Xnorm N k * Ynorm N (posJ a k) ≤
            positiveSmallXYProductBound a N k)
    (temperedXY :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k → 0 < Bq N k →
          Xnorm N k * Ynorm N (posJ a k) ≤
            positiveTemperedXYProductBound a N k)
    (soloY :
      ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget)
    (productPrefix : PositiveSaddleLargeTailProductPrefixPointwise)
    (soloPrefix : PositiveSaddleLargeTailSoloPrefixNormUnit) :
    BoundedPositiveCertificate :=
  BoundedPositiveCertificate.ofMajorantBudgetDirectPrefix
    (BoundedMajorantBudgetCertificate.ofCombinedProductScaledEdge
      smallXY temperedXY soloY)
    productPrefix soloPrefix

/-- Bounded certificate with all product fields supplied by the direct saddle
route.

The only bounded inputs left here are the finite solo budget and the solo
prefix norm-unit field.  The product prefix is the corrected direct `Bq * Qq`
route, avoiding the legacy exact upper-edge split-product grid. -/
def BoundedPositiveCertificate.ofDirectSaddle
    (soloY :
      ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget)
    (soloPrefix : PositiveSaddleLargeTailSoloPrefixNormUnit) :
    BoundedPositiveCertificate :=
  BoundedPositiveCertificate.ofCombinedProductScaledEdgeMajorantDirectPrefix
    (by
      intro a N k ha ha2000 hrect hk hsmall hB
      exact positiveSmallXYProductBound_of_directSaddle_geTwo
        ha ha2000 hrect hk hsmall
        (two_le_of_Bq_pos (mem_positiveKRange.mp hk).1 hB))
    (by
      intro a N k ha ha2000 hrect hk htempered _hB
      exact positiveTemperedXYProductBound_of_directSaddle
        ha ha2000 hrect hk htempered)
    soloY
    PositiveSaddleLargeTailProductPrefixPointwise.ofDirectSaddle
    soloPrefix

/-- Compatibility constructor for the previous bounded route, which supplies
the edge budget through fixed row/`k` chunks. -/
def BoundedPositiveCertificate.ofActiveAnalyticFixedEdge
    {tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      tangentNLen soloSaddleNLen soloBudgetNLen tangentKLen edgeKLen
      productPrefixALen productPrefixKLen soloPrefixALen : Nat}
    (cert :
      PositiveSaddleFixedFiniteWindowActiveAnalyticProductTangentSoloNFixedEdgeKChunkedAuditCertificate
        tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
        tangentNLen soloSaddleNLen soloBudgetNLen tangentKLen edgeKLen)
    (productPrefix :
      PositiveSaddleLargeTailProductFastUpperEdgeLowerNProductBoundPrefixChunksCertificate
        (fun a k =>
          positiveLargeTailProductXUpperEdgeExactBound a k *
            positiveLargeTailProductYUpperEdgeExactBound a k)
        productPrefixALen productPrefixKLen)
    (soloPrefix :
      PositiveSaddleLargeTailSoloFastUpperEdgeBoundPrefixChunksCertificate
        positiveLargeTailSoloUpperEdgeExactBound
        soloPrefixALen) :
    BoundedPositiveCertificate where
  toPositiveSaddleCertificate := fun pointwise candidate =>
    (cert.toTangentProductBudgetCertificate_of_pointwise pointwise candidate).toCertificate
  productPrefixPointwise :=
    positiveSaddleLargeTailProductPrefixPointwise_of_fastUpperEdgeLowerNProductBoundPrefixChunks
      productPrefix
  soloPrefixNormUnit :=
    positiveSaddleLargeTailSoloPrefixNormUnit_of_fastUpperEdgeBoundPrefixChunks
      soloPrefix

/-- Constructor for the bounded route that uses the compact semantic edge
budget.  This is the Lean-side implementation note for the finite-edge
divergence from the TeX scan: the edge computation may be certified by a
verified row checker for `positiveEdgeMajorantSum`, while the tangent and solo
finite obligations stay in the established active chunk interfaces. -/
def BoundedPositiveCertificate.ofActiveAnalyticSemanticEdge
    {tangentRowLen soloSaddleRowLen soloBudgetRowLen
      tangentNLen soloSaddleNLen soloBudgetNLen tangentKLen
      productPrefixALen productPrefixKLen soloPrefixALen : Nat}
    (tangentRowLenPos : 0 < tangentRowLen)
    (soloSaddleRowLenPos : 0 < soloSaddleRowLen)
    (soloBudgetRowLenPos : 0 < soloBudgetRowLen)
    (tangentNLenPos : 0 < tangentNLen)
    (soloSaddleNLenPos : 0 < soloSaddleNLen)
    (soloBudgetNLenPos : 0 < soloBudgetNLen)
    (tangentKLenPos : 0 < tangentKLen)
    (smallXYTangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N → 0 < Bq N k →
          Xnorm N k * Ynorm N (posJ a k) ≤
            positiveSmallXYProductTangentBound a N k)
    (temperedXY :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k → 0 < Bq N k →
          Xnorm N k * Ynorm N (posJ a k) ≤
            positiveTemperedXYProductBound a N k)
    (smallTangentExpEdgeRowRangeNIndexKChunks :
      ∀ {rowChunk : Nat × Nat},
        rowChunk ∈ positiveSaddleFixedRowChunks tangentRowLen →
        ∀ {nIndex : Nat},
          nIndex ∈
            positiveProductFixedNChunkIndicesForRowRange
              tangentNLen rowChunk.1 rowChunk.2 →
        ∀ {kChunk : Nat × Nat}, kChunk ∈ positiveTangentFixedKChunks tangentKLen →
          checkPositiveSmallTangentExpEdgeFixedNIndexRowRangeKChunk
            tangentNLen rowChunk.1 rowChunk.2 nIndex kChunk.1 kChunk.2 = true)
    (soloYSaddleClearedRowRangeNIndexChunks :
      ∀ {rowChunk : Nat × Nat},
        rowChunk ∈ positiveSaddleFixedRowChunks soloSaddleRowLen →
        ∀ {nIndex : Nat},
          nIndex ∈
            positiveProductFixedNChunkIndicesForRowRange
              soloSaddleNLen rowChunk.1 rowChunk.2 →
          checkPositiveSoloDisplayedYSaddleClearedFixedNIndexRowRange
            soloSaddleNLen rowChunk.1 rowChunk.2 nIndex = true)
    (soloYBudgetRowRangeNIndexChunks :
      ∀ {rowChunk : Nat × Nat},
        rowChunk ∈ positiveSaddleFixedRowChunks soloBudgetRowLen →
        ∀ {nIndex : Nat},
          nIndex ∈
            positiveProductFixedNChunkIndicesForRowRange
              soloBudgetNLen rowChunk.1 rowChunk.2 →
          checkPositiveSoloDisplayedYBoundUnitFixedNIndexRowRange
            soloBudgetNLen rowChunk.1 rowChunk.2 nIndex = true)
    (edgeBudget :
      ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
        positiveEdgeMajorantSum a ≤ positiveEdgeBudget)
    (productPrefix :
      PositiveSaddleLargeTailProductFastUpperEdgeLowerNProductBoundPrefixChunksCertificate
        (fun a k =>
          positiveLargeTailProductXUpperEdgeExactBound a k *
            positiveLargeTailProductYUpperEdgeExactBound a k)
        productPrefixALen productPrefixKLen)
    (soloPrefix :
      PositiveSaddleLargeTailSoloFastUpperEdgeBoundPrefixChunksCertificate
        positiveLargeTailSoloUpperEdgeExactBound
        soloPrefixALen) :
    BoundedPositiveCertificate where
  toPositiveSaddleCertificate := fun pointwise candidate =>
    (positiveSaddleActiveAnalyticProductTangentSoloNSemanticEdge_toTangentProductBudgetCertificate
      tangentRowLenPos soloSaddleRowLenPos soloBudgetRowLenPos
      tangentNLenPos soloSaddleNLenPos soloBudgetNLenPos tangentKLenPos
      smallXYTangent temperedXY smallTangentExpEdgeRowRangeNIndexKChunks
      soloYSaddleClearedRowRangeNIndexChunks soloYBudgetRowRangeNIndexChunks
      edgeBudget pointwise candidate).toCertificate
  productPrefixPointwise :=
    positiveSaddleLargeTailProductPrefixPointwise_of_fastUpperEdgeLowerNProductBoundPrefixChunks
      productPrefix
  soloPrefixNormUnit :=
    positiveSaddleLargeTailSoloPrefixNormUnit_of_fastUpperEdgeBoundPrefixChunks
      soloPrefix

/-- Constructor for the bounded route with the already-generated scaled
finite edge-budget shards inserted.

This is a proof-production specialization of
`BoundedPositiveCertificate.ofActiveAnalyticSemanticEdge`: the edge budget is
no longer a future bounded-certificate field, since it is supplied by
`positiveSaddleFiniteScaledEdgeBudget`.  The remaining finite inputs are the
actual tangent product, finite solo, and `2001 ≤ a < 3000` prefix obligations. -/
def BoundedPositiveCertificate.ofActiveAnalyticScaledEdge
    {tangentRowLen soloSaddleRowLen soloBudgetRowLen
      tangentNLen soloSaddleNLen soloBudgetNLen tangentKLen
      productPrefixALen productPrefixKLen soloPrefixALen : Nat}
    (tangentRowLenPos : 0 < tangentRowLen)
    (soloSaddleRowLenPos : 0 < soloSaddleRowLen)
    (soloBudgetRowLenPos : 0 < soloBudgetRowLen)
    (tangentNLenPos : 0 < tangentNLen)
    (soloSaddleNLenPos : 0 < soloSaddleNLen)
    (soloBudgetNLenPos : 0 < soloBudgetNLen)
    (tangentKLenPos : 0 < tangentKLen)
    (smallXYTangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N → 0 < Bq N k →
          Xnorm N k * Ynorm N (posJ a k) ≤
            positiveSmallXYProductTangentBound a N k)
    (temperedXY :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k → 0 < Bq N k →
          Xnorm N k * Ynorm N (posJ a k) ≤
            positiveTemperedXYProductBound a N k)
    (smallTangentExpEdgeRowRangeNIndexKChunks :
      ∀ {rowChunk : Nat × Nat},
        rowChunk ∈ positiveSaddleFixedRowChunks tangentRowLen →
        ∀ {nIndex : Nat},
          nIndex ∈
            positiveProductFixedNChunkIndicesForRowRange
              tangentNLen rowChunk.1 rowChunk.2 →
        ∀ {kChunk : Nat × Nat}, kChunk ∈ positiveTangentFixedKChunks tangentKLen →
          checkPositiveSmallTangentExpEdgeFixedNIndexRowRangeKChunk
            tangentNLen rowChunk.1 rowChunk.2 nIndex kChunk.1 kChunk.2 = true)
    (soloYSaddleClearedRowRangeNIndexChunks :
      ∀ {rowChunk : Nat × Nat},
        rowChunk ∈ positiveSaddleFixedRowChunks soloSaddleRowLen →
        ∀ {nIndex : Nat},
          nIndex ∈
            positiveProductFixedNChunkIndicesForRowRange
              soloSaddleNLen rowChunk.1 rowChunk.2 →
          checkPositiveSoloDisplayedYSaddleClearedFixedNIndexRowRange
            soloSaddleNLen rowChunk.1 rowChunk.2 nIndex = true)
    (soloYBudgetRowRangeNIndexChunks :
      ∀ {rowChunk : Nat × Nat},
        rowChunk ∈ positiveSaddleFixedRowChunks soloBudgetRowLen →
        ∀ {nIndex : Nat},
          nIndex ∈
            positiveProductFixedNChunkIndicesForRowRange
              soloBudgetNLen rowChunk.1 rowChunk.2 →
          checkPositiveSoloDisplayedYBoundUnitFixedNIndexRowRange
            soloBudgetNLen rowChunk.1 rowChunk.2 nIndex = true)
    (productPrefix :
      PositiveSaddleLargeTailProductFastUpperEdgeLowerNProductBoundPrefixChunksCertificate
        (fun a k =>
          positiveLargeTailProductXUpperEdgeExactBound a k *
            positiveLargeTailProductYUpperEdgeExactBound a k)
        productPrefixALen productPrefixKLen)
    (soloPrefix :
      PositiveSaddleLargeTailSoloFastUpperEdgeBoundPrefixChunksCertificate
        positiveLargeTailSoloUpperEdgeExactBound
        soloPrefixALen) :
    BoundedPositiveCertificate :=
  BoundedPositiveCertificate.ofActiveAnalyticSemanticEdge
    tangentRowLenPos soloSaddleRowLenPos soloBudgetRowLenPos
    tangentNLenPos soloSaddleNLenPos soloBudgetNLenPos tangentKLenPos
    smallXYTangent temperedXY smallTangentExpEdgeRowRangeNIndexKChunks
    soloYSaddleClearedRowRangeNIndexChunks soloYBudgetRowRangeNIndexChunks
    positiveSaddleFiniteScaledEdgeBudget productPrefix soloPrefix

/-- Constructor for the bounded route with theorem-facing prefix fields.

This is the completion-facing version of
`BoundedPositiveCertificate.ofActiveAnalyticSemanticEdge`: the `2001 <= a <
3000` strip is supplied by the direct product and solo prefix obligations
from this file, rather than by the older exact upper-edge prefix chunk
certificates.  This records the Lean proof-production deviation from the TeX
scan: the bounded assembly should target the same combined product and
normalized solo estimates used by `Completion.lean`, with exact prefix chunks
reserved only as a compatibility proof producer. -/
def BoundedPositiveCertificate.ofActiveAnalyticSemanticEdgeDirectPrefix
    {tangentRowLen soloSaddleRowLen soloBudgetRowLen
      tangentNLen soloSaddleNLen soloBudgetNLen tangentKLen : Nat}
    (tangentRowLenPos : 0 < tangentRowLen)
    (soloSaddleRowLenPos : 0 < soloSaddleRowLen)
    (soloBudgetRowLenPos : 0 < soloBudgetRowLen)
    (tangentNLenPos : 0 < tangentNLen)
    (soloSaddleNLenPos : 0 < soloSaddleNLen)
    (soloBudgetNLenPos : 0 < soloBudgetNLen)
    (tangentKLenPos : 0 < tangentKLen)
    (smallXYTangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N → 0 < Bq N k →
          Xnorm N k * Ynorm N (posJ a k) ≤
            positiveSmallXYProductTangentBound a N k)
    (temperedXY :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k → 0 < Bq N k →
          Xnorm N k * Ynorm N (posJ a k) ≤
            positiveTemperedXYProductBound a N k)
    (smallTangentExpEdgeRowRangeNIndexKChunks :
      ∀ {rowChunk : Nat × Nat},
        rowChunk ∈ positiveSaddleFixedRowChunks tangentRowLen →
        ∀ {nIndex : Nat},
          nIndex ∈
            positiveProductFixedNChunkIndicesForRowRange
              tangentNLen rowChunk.1 rowChunk.2 →
        ∀ {kChunk : Nat × Nat}, kChunk ∈ positiveTangentFixedKChunks tangentKLen →
          checkPositiveSmallTangentExpEdgeFixedNIndexRowRangeKChunk
            tangentNLen rowChunk.1 rowChunk.2 nIndex kChunk.1 kChunk.2 = true)
    (soloYSaddleClearedRowRangeNIndexChunks :
      ∀ {rowChunk : Nat × Nat},
        rowChunk ∈ positiveSaddleFixedRowChunks soloSaddleRowLen →
        ∀ {nIndex : Nat},
          nIndex ∈
            positiveProductFixedNChunkIndicesForRowRange
              soloSaddleNLen rowChunk.1 rowChunk.2 →
          checkPositiveSoloDisplayedYSaddleClearedFixedNIndexRowRange
            soloSaddleNLen rowChunk.1 rowChunk.2 nIndex = true)
    (soloYBudgetRowRangeNIndexChunks :
      ∀ {rowChunk : Nat × Nat},
        rowChunk ∈ positiveSaddleFixedRowChunks soloBudgetRowLen →
        ∀ {nIndex : Nat},
          nIndex ∈
            positiveProductFixedNChunkIndicesForRowRange
              soloBudgetNLen rowChunk.1 rowChunk.2 →
          checkPositiveSoloDisplayedYBoundUnitFixedNIndexRowRange
            soloBudgetNLen rowChunk.1 rowChunk.2 nIndex = true)
    (edgeBudget :
      ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
        positiveEdgeMajorantSum a ≤ positiveEdgeBudget)
    (productPrefix : PositiveSaddleLargeTailProductPrefixPointwise)
    (soloPrefix : PositiveSaddleLargeTailSoloPrefixNormUnit) :
    BoundedPositiveCertificate where
  toPositiveSaddleCertificate := fun pointwise candidate =>
    (positiveSaddleActiveAnalyticProductTangentSoloNSemanticEdge_toTangentProductBudgetCertificate
      tangentRowLenPos soloSaddleRowLenPos soloBudgetRowLenPos
      tangentNLenPos soloSaddleNLenPos soloBudgetNLenPos tangentKLenPos
      smallXYTangent temperedXY smallTangentExpEdgeRowRangeNIndexKChunks
      soloYSaddleClearedRowRangeNIndexChunks soloYBudgetRowRangeNIndexChunks
      edgeBudget pointwise candidate).toCertificate
  productPrefixPointwise := productPrefix
  soloPrefixNormUnit := soloPrefix

/-- Completion-facing bounded constructor with the generated scaled edge
budget inserted and direct theorem-facing prefix fields exposed. -/
def BoundedPositiveCertificate.ofActiveAnalyticScaledEdgeDirectPrefix
    {tangentRowLen soloSaddleRowLen soloBudgetRowLen
      tangentNLen soloSaddleNLen soloBudgetNLen tangentKLen : Nat}
    (tangentRowLenPos : 0 < tangentRowLen)
    (soloSaddleRowLenPos : 0 < soloSaddleRowLen)
    (soloBudgetRowLenPos : 0 < soloBudgetRowLen)
    (tangentNLenPos : 0 < tangentNLen)
    (soloSaddleNLenPos : 0 < soloSaddleNLen)
    (soloBudgetNLenPos : 0 < soloBudgetNLen)
    (tangentKLenPos : 0 < tangentKLen)
    (smallXYTangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N → 0 < Bq N k →
          Xnorm N k * Ynorm N (posJ a k) ≤
            positiveSmallXYProductTangentBound a N k)
    (temperedXY :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k → 0 < Bq N k →
          Xnorm N k * Ynorm N (posJ a k) ≤
            positiveTemperedXYProductBound a N k)
    (smallTangentExpEdgeRowRangeNIndexKChunks :
      ∀ {rowChunk : Nat × Nat},
        rowChunk ∈ positiveSaddleFixedRowChunks tangentRowLen →
        ∀ {nIndex : Nat},
          nIndex ∈
            positiveProductFixedNChunkIndicesForRowRange
              tangentNLen rowChunk.1 rowChunk.2 →
        ∀ {kChunk : Nat × Nat}, kChunk ∈ positiveTangentFixedKChunks tangentKLen →
          checkPositiveSmallTangentExpEdgeFixedNIndexRowRangeKChunk
            tangentNLen rowChunk.1 rowChunk.2 nIndex kChunk.1 kChunk.2 = true)
    (soloYSaddleClearedRowRangeNIndexChunks :
      ∀ {rowChunk : Nat × Nat},
        rowChunk ∈ positiveSaddleFixedRowChunks soloSaddleRowLen →
        ∀ {nIndex : Nat},
          nIndex ∈
            positiveProductFixedNChunkIndicesForRowRange
              soloSaddleNLen rowChunk.1 rowChunk.2 →
          checkPositiveSoloDisplayedYSaddleClearedFixedNIndexRowRange
            soloSaddleNLen rowChunk.1 rowChunk.2 nIndex = true)
    (soloYBudgetRowRangeNIndexChunks :
      ∀ {rowChunk : Nat × Nat},
        rowChunk ∈ positiveSaddleFixedRowChunks soloBudgetRowLen →
        ∀ {nIndex : Nat},
          nIndex ∈
            positiveProductFixedNChunkIndicesForRowRange
              soloBudgetNLen rowChunk.1 rowChunk.2 →
          checkPositiveSoloDisplayedYBoundUnitFixedNIndexRowRange
            soloBudgetNLen rowChunk.1 rowChunk.2 nIndex = true)
    (productPrefix : PositiveSaddleLargeTailProductPrefixPointwise)
    (soloPrefix : PositiveSaddleLargeTailSoloPrefixNormUnit) :
    BoundedPositiveCertificate :=
  BoundedPositiveCertificate.ofActiveAnalyticSemanticEdgeDirectPrefix
    tangentRowLenPos soloSaddleRowLenPos soloBudgetRowLenPos
    tangentNLenPos soloSaddleNLenPos soloBudgetNLenPos tangentKLenPos
    smallXYTangent temperedXY smallTangentExpEdgeRowRangeNIndexKChunks
    soloYSaddleClearedRowRangeNIndexChunks soloYBudgetRowRangeNIndexChunks
    positiveSaddleFiniteScaledEdgeBudget productPrefix soloPrefix

/-- The large-tail product obligation for the current canonical route.

This is intentionally stated as the normalized combined actual product target,
not as the older independent `Gcomp` majorant product.  This matches the TeX
combined-product route: the raw `Bq * Qq` form can be supplied via
`LargeTailProductCertificate.ofRawCleared`.  The legacy upper-edge/lower-`N`
`Gcomp` scalar constructors below are kept for comparison with older generated
artifacts, but they are no longer a viable completion route for the exact
split-factorial product: the small `k ≥ 4` exact-upper-edge obligation is
false already at `(a,k) = (3000,4)`. -/
structure LargeTailProductCertificate where
  largeSmall :
    ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        Xnorm N k * Ynorm N (posJ a k)
          ≤ positiveSmallLargeGcompProductTarget a N k
  largeTempered :
    ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k →
        Xnorm N k * Ynorm N (posJ a k)
          ≤ positiveTemperedLargeGcompProductTarget a N k

/-- Constructor from denominator-cleared actual-product large-tail bounds.

This is the preferred proof-production shape for the remaining analytic
product work: it keeps rational denominator clearing local and uses
`Xnorm_mul_Ynorm_eq_raw_div` through the bridge in `PositiveSaddle`. -/
theorem LargeTailProductCertificate.ofRawCleared
    (hsmall :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          positiveSmallLargeXYProductRawCleared a N k)
    (htempered :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k →
          positiveTemperedLargeXYProductRawCleared a N k) :
    LargeTailProductCertificate where
  largeSmall := by
    intro a N k ha hrect hk hsmallN
    exact
      positiveSmallLargeXYProductTarget_of_rawCleared
        (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect)
        (by omega : 1 ≤ a) hk
        (hsmall ha hrect hk hsmallN)
  largeTempered := by
    intro a N k ha hrect hk htemperedN
    exact
      positiveTemperedLargeXYProductTarget_of_rawCleared
        (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect)
        (by omega : 2 ≤ a) hk
        (htempered ha hrect hk htemperedN)

/-- Constructor from the existing large-tail product-bounds certificate,
routed through the actual combined raw product.

This intentionally avoids using the older normalized independent-`Gcomp`
product as the route-facing conclusion.  The split `B`/`Q` product-bound
certificate is only a way to prove the denominator-cleared actual
`Bq * Qq` inequality, after which `LargeTailProductCertificate.ofRawCleared`
performs the final normalization. -/
theorem LargeTailProductCertificate.ofProductBounds
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    (cert : PositiveSaddleLargeTailProductBoundsCertificate
      smallXBound smallYBound temperedXBound temperedYBound) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofRawCleared
    (by
      intro a N k ha hrect hk hsmallN
      exact cert.smallXYProductRawCleared
        (by omega : 2000 < a) hrect hk hsmallN)
    (by
      intro a N k ha hrect hk htemperedN
      exact cert.temperedXYProductRawCleared
        (by omega : 2000 < a) hrect hk htemperedN)

/-- Constructor from raw actual-product bounds away from the sign-lock zone.

Cells satisfying `361 ≤ k` and `N ≤ (40/3) k` need no product estimate:
`Xnorm N k` is nonpositive by §5, while `Ynorm` and the large-tail targets are
nonnegative.  The remaining raw obligations are the only cells where the
combined-product estimate still has to do work. -/
theorem LargeTailProductCertificate.ofRawClearedAwayFromSignLock
    (hsmall :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          ¬ (361 ≤ k ∧ (N : ℚ) ≤ (40 / 3 : ℚ) * (k : ℚ)) →
          positiveSmallLargeXYProductRawCleared a N k)
    (htempered :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k →
          ¬ (361 ≤ k ∧ (N : ℚ) ≤ (40 / 3 : ℚ) * (k : ℚ)) →
          positiveTemperedLargeXYProductRawCleared a N k) :
    LargeTailProductCertificate where
  largeSmall := by
    intro a N k ha hrect hk hsmallN
    have hN : 1 ≤ N :=
      positiveRectangle_N_pos (by omega : 2 ≤ a) hrect
    by_cases hlock :
        361 ≤ k ∧ (N : ℚ) ≤ (40 / 3 : ℚ) * (k : ℚ)
    · exact
        positiveSmallLargeXYProductTarget_of_signLock
          (by omega : 2000 < a) hN hk hlock.1 hlock.2
    · exact
        positiveSmallLargeXYProductTarget_of_rawCleared hN
          (by omega : 1 ≤ a) hk
          (hsmall ha hrect hk hsmallN hlock)
  largeTempered := by
    intro a N k ha hrect hk htemperedN
    have hN : 1 ≤ N :=
      positiveRectangle_N_pos (by omega : 2 ≤ a) hrect
    by_cases hlock :
        361 ≤ k ∧ (N : ℚ) ≤ (40 / 3 : ℚ) * (k : ℚ)
    · exact
        positiveTemperedLargeXYProductTarget_of_signLock
          (by omega : 2000 < a) hN hk hlock.1 hlock.2
    · exact
        positiveTemperedLargeXYProductTarget_of_rawCleared hN
          (by omega : 2 ≤ a) hk
          (htempered ha hrect hk htemperedN hlock)

/-- Constructor from raw actual-product bounds on the denominator-cleared
complement of the sign-lock zone.

This is the preferred remaining proof surface for the product tail.  It keeps
the TeX sign-lock split, but states the non-sign-lock branch as
`k < 361 ∨ 40*k < 3*N`, avoiding rational negated conjunctions in the
eventual checker/analytic proof.  In the small branch the sign-lock case is
impossible from `k ≤ ceilSqrt N`, so no extra complement hypothesis is asked
there. -/
theorem LargeTailProductCertificate.ofRawClearedNatSignLockComplement
    (hsmall :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          positiveSmallLargeXYProductRawCleared a N k)
    (htempered :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k →
          (k < 361 ∨ 40 * k < 3 * N) →
          positiveTemperedLargeXYProductRawCleared a N k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofRawClearedAwayFromSignLock
    (by
      intro a N k ha hrect hk hsmallN hnotLock
      exact hsmall ha hrect hk hsmallN)
    (by
      intro a N k ha hrect hk htemperedN hnotLock
      exact htempered ha hrect hk htemperedN
        (signLock_natAlternative_of_not hnotLock))

/-- Constructor from actual-product raw bounds only on cells where the
coefficient `B_k(N)` is positive.

This follows the combined-product route in the TeX argument: cells with
`Bq N k ≤ 0` contribute a nonpositive actual product because `Qq` is
nonnegative, so they should not be sent to any independent `Gcomp` product
majorant. -/
theorem LargeTailProductCertificate.ofRawClearedBqPositive
    (hsmall :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N → 0 < Bq N k →
          positiveSmallLargeXYProductRawCleared a N k)
    (htempered :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k → 0 < Bq N k →
          positiveTemperedLargeXYProductRawCleared a N k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofRawCleared
    (by
      intro a N k ha hrect hk hsmallN
      by_cases hB : 0 < Bq N k
      · exact hsmall ha hrect hk hsmallN hB
      · exact
          positiveSmallLargeXYProductRawCleared_of_Bq_nonpos
            (by omega : 2000 < a) hk (le_of_not_gt hB))
    (by
      intro a N k ha hrect hk htemperedN
      by_cases hB : 0 < Bq N k
      · exact htempered ha hrect hk htemperedN hB
      · exact
          positiveTemperedLargeXYProductRawCleared_of_Bq_nonpos
            (by omega : 2000 < a) hk (le_of_not_gt hB))

/-- Product-tail constructor combining the two free reductions now available
for the actual raw product: nonpositive `Bq` cells are automatic, and the
§5 sign-lock zone is automatic in the tempered branch.  The remaining
tempered work is exactly the denominator-cleared complement
`k < 361 ∨ 40*k < 3*N` with `0 < Bq N k`. -/
theorem LargeTailProductCertificate.ofRawClearedBqPositiveNatSignLockComplement
    (hsmall :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N → 0 < Bq N k →
          positiveSmallLargeXYProductRawCleared a N k)
    (htempered :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k →
          (k < 361 ∨ 40 * k < 3 * N) → 0 < Bq N k →
          positiveTemperedLargeXYProductRawCleared a N k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofRawClearedNatSignLockComplement
    (by
      intro a N k ha hrect hk hsmallN
      by_cases hB : 0 < Bq N k
      · exact hsmall ha hrect hk hsmallN hB
      · exact
          positiveSmallLargeXYProductRawCleared_of_Bq_nonpos
            (by omega : 2000 < a) hk (le_of_not_gt hB))
    (by
      intro a N k ha hrect hk htemperedN hnotLock
      by_cases hB : 0 < Bq N k
      · exact htempered ha hrect hk htemperedN hnotLock hB
      · exact
          positiveTemperedLargeXYProductRawCleared_of_Bq_nonpos
            (by omega : 2000 < a) hk (le_of_not_gt hB))

/-- Product-tail constructor after the first-coefficient sign reduction.

Since `Bq N 1 ≤ 0`, the live actual-product obligations with `0 < Bq N k`
start at `k = 2`.  This is the version future tail-product checkers should
target: it keeps both free reductions from
`ofRawClearedBqPositiveNatSignLockComplement` and removes the uniformly
nonpositive first coefficient from the remaining domain. -/
theorem LargeTailProductCertificate.ofRawClearedBqPositiveGeTwoNatSignLockComplement
    (hsmall :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N → 2 ≤ k → 0 < Bq N k →
          positiveSmallLargeXYProductRawCleared a N k)
    (htempered :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k →
          (k < 361 ∨ 40 * k < 3 * N) → 2 ≤ k → 0 < Bq N k →
          positiveTemperedLargeXYProductRawCleared a N k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofRawClearedBqPositiveNatSignLockComplement
    (by
      intro a N k ha hrect hk hsmallN hB
      exact hsmall ha hrect hk hsmallN
        (two_le_of_Bq_pos (mem_positiveKRange.mp hk).1 hB) hB)
    (by
      intro a N k ha hrect hk htemperedN hnotLock hB
      exact htempered ha hrect hk htemperedN hnotLock
        (two_le_of_Bq_pos (mem_positiveKRange.mp hk).1 hB) hB)

/-- In the large positive rectangle, the first retained `Bq` coefficient is
strictly positive. -/
theorem Bq_two_pos_of_large_positiveRectangle {a N : Nat} (ha : 3000 ≤ a)
    (hrect : positiveRectangle a N) :
    0 < Bq N 2 :=
  Bq_two_pos_of_le (by
    have hNlo : posNlo a ≤ N := hrect.1
    unfold posNlo at hNlo
    omega)

/-! ### First retained product cell (`k = 2`) -/

/-- Direct scalar budget for the first retained small-branch product cell
after substituting the closed form
`Bq N 2 = 5*N*(5*N-72)/72`.

This is the preferred Lean surface for the `k = 2` product cell: prove a
tight bound on the actual `Qq N (a-2)` coefficient and then discharge this
single scalar inequality.  It intentionally avoids the coarse
`(10/7)^(a-2)` solo envelope recorded below, which is useful only as a
diagnostic route for this shifted index. -/
def positiveSmallFirstCellQBudget (a N : Nat) (qBound : ℚ) : Prop :=
  (2 : ℚ)^(posJ a 2) * (posNhi a : ℚ) *
      (5 * (N : ℚ) - 72) * qBound
    ≤ 9360 * (posJ a 2 : ℚ) *
      positiveSmallLargeExp a 2 * c (posJ a 2)

/-- Row-only endpoint form of the first retained product-cell budget used by
the canonical large-tail product route. -/
def positiveSmallFirstCellYUpperEdgeBudget (a : Nat) : Prop :=
  positiveSmallFirstCellQBudget a (posNhi a)
    (positiveLargeTailProductYUpperEdgeExactBound a 2)

/-- The product-side `Y` upper-edge bound in the first retained cell is the
same split-factorial solo `Y` block sum at the shifted index `j = a - 2`.
This is the bridge that lets first-cell work reuse solo-style estimates
without unfolding the double sum. -/
theorem positiveLargeTailProductYUpperEdgeExactBound_eq_shiftedSolo
    (a k : Nat) :
    positiveLargeTailProductYUpperEdgeExactBound a k =
      positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
        (posJ a k) (posNhi a) := by
  rfl

theorem positiveLargeTailProductYUpperEdgeExactBound_two_eq_shiftedSolo
    (a : Nat) :
    positiveLargeTailProductYUpperEdgeExactBound a 2 =
      positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
        (posJ a 2) (posNhi a) := by
  exact positiveLargeTailProductYUpperEdgeExactBound_eq_shiftedSolo a 2

/-- The product-side `Y` upper-edge bound in the next retained cell is again
the shifted solo split-factorial block sum, now at `j = a - 3`. -/
theorem positiveLargeTailProductYUpperEdgeExactBound_three_eq_shiftedSolo
    (a : Nat) :
    positiveLargeTailProductYUpperEdgeExactBound a 3 =
      positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
        (posJ a 3) (posNhi a) := by
  exact positiveLargeTailProductYUpperEdgeExactBound_eq_shiftedSolo a 3

/-- Compare the product-side `Y` upper-edge factor with the solo upper-edge
factor at the shifted index, paying only the explicit polynomial-degree
scaling from `posNhi (a-k)` to `posNhi a`.

This is a direct helper for the frozen large-tail product route: future
`hsmallGeFour`/`htemperedGeFour` proofs can reuse solo-style upper-edge
estimates for the `Y_{a-k}` factor without re-expanding the split block. -/
theorem positiveLargeTailProductYUpperEdgeExactBound_le_scaled_shiftedSoloUpperEdge
    {a k : Nat} {R : ℚ} (hR1 : 1 ≤ R)
    (hNhi :
      (posNhi a : ℚ) ≤ R * (posNhi (posJ a k) : ℚ)) :
    positiveLargeTailProductYUpperEdgeExactBound a k
      ≤ R^(posJ a k) *
        positiveLargeTailSoloUpperEdgeExactBound (posJ a k) := by
  rw [positiveLargeTailProductYUpperEdgeExactBound_eq_shiftedSolo]
  unfold positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
    positiveLargeTailSoloUpperEdgeExactBound
  exact
    positiveLargeTailYGcompClosedFactorialSplitBlockSum_le_scaled_of_natCast_le
      hR1 hNhi

/-- Scalar comparison left after proving the shifted first-cell `Y` block by
the fast solo-style exponential envelope.

The large extra term in `positiveSmallExponentUpper a 2` is intended to pay
for the polynomial prefactor
`posNhi a * (5 * posNhi a - 72)`. -/
def positiveSmallFirstCellShiftedSoloFastExpBudget (a : Nat) : Prop :=
  (29 / 4 : ℚ) * (posNhi a : ℚ) *
      ((5 : ℚ) * (posNhi a : ℚ) - 72) *
        partialExpUpperFast (positiveSoloYExponent (posJ a 2))
          (8 * posJ a 2)
    ≤ 9360 * positiveSmallLargeExp a 2

/-- First-cell budget from a shifted solo fast bound plus the remaining
one-dimensional scalar comparison.

This is the current analytic target for the `k = 2` product cell: prove the
solo-shaped split sum for `j = a - 2` at the product upper edge, then prove
that the small-branch exponential has enough slack for the polynomial factor.
-/
theorem positiveSmallFirstCellYUpperEdgeBudget_of_shiftedSoloFastCleared
    {a : Nat} (ha : 2000 < a)
    (hsolo :
      positiveLargeTailSoloGcompClosedFactorialSplitBlockSumFastCleared
        (posJ a 2) (posNhi a))
    (hbudget : positiveSmallFirstCellShiftedSoloFastExpBudget a) :
    positiveSmallFirstCellYUpperEdgeBudget a := by
  unfold positiveSmallFirstCellYUpperEdgeBudget positiveSmallFirstCellQBudget
  rw [positiveLargeTailProductYUpperEdgeExactBound_two_eq_shiftedSolo]
  unfold positiveLargeTailSoloGcompClosedFactorialSplitBlockSumFastCleared
    at hsolo
  have hhi15 : 15 ≤ posNhi a := by
    unfold posNhi
    omega
  have hhi15Q : (15 : ℚ) ≤ (posNhi a : ℚ) := by
    exact_mod_cast hhi15
  have hlinear_nonneg :
      0 ≤ (5 : ℚ) * (posNhi a : ℚ) - 72 := by
    nlinarith
  have hscale_nonneg :
      0 ≤ ((posNhi a : ℚ) *
        ((5 : ℚ) * (posNhi a : ℚ) - 72) / 4) := by
    positivity
  have hscaledSolo :
      ((posNhi a : ℚ) *
          ((5 : ℚ) * (posNhi a : ℚ) - 72) / 4) *
        ((4 : ℚ) * (2 : ℚ)^(posJ a 2) *
          positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
            (posJ a 2) (posNhi a))
        ≤
      ((posNhi a : ℚ) *
          ((5 : ℚ) * (posNhi a : ℚ) - 72) / 4) *
        (29 * (posJ a 2 : ℚ) * c (posJ a 2) *
          partialExpUpperFast (positiveSoloYExponent (posJ a 2))
            (8 * posJ a 2)) :=
    mul_le_mul_of_nonneg_left hsolo hscale_nonneg
  have hjc_nonneg : 0 ≤ (posJ a 2 : ℚ) * c (posJ a 2) :=
    mul_nonneg (Nat.cast_nonneg _) (c_nonneg (posJ a 2))
  have hbudgetScaled :
      ((posJ a 2 : ℚ) * c (posJ a 2)) *
        ((29 / 4 : ℚ) * (posNhi a : ℚ) *
          ((5 : ℚ) * (posNhi a : ℚ) - 72) *
            partialExpUpperFast (positiveSoloYExponent (posJ a 2))
              (8 * posJ a 2))
        ≤
      ((posJ a 2 : ℚ) * c (posJ a 2)) *
        (9360 * positiveSmallLargeExp a 2) :=
    mul_le_mul_of_nonneg_left hbudget hjc_nonneg
  calc
    (2 : ℚ)^(posJ a 2) * (posNhi a : ℚ) *
          (5 * (posNhi a : ℚ) - 72) *
          positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
            (posJ a 2) (posNhi a)
        =
      ((posNhi a : ℚ) *
          ((5 : ℚ) * (posNhi a : ℚ) - 72) / 4) *
        ((4 : ℚ) * (2 : ℚ)^(posJ a 2) *
          positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
            (posJ a 2) (posNhi a)) := by
        ring
    _ ≤
      ((posNhi a : ℚ) *
          ((5 : ℚ) * (posNhi a : ℚ) - 72) / 4) *
        (29 * (posJ a 2 : ℚ) * c (posJ a 2) *
          partialExpUpperFast (positiveSoloYExponent (posJ a 2))
            (8 * posJ a 2)) := hscaledSolo
    _ =
      ((posJ a 2 : ℚ) * c (posJ a 2)) *
        ((29 / 4 : ℚ) * (posNhi a : ℚ) *
          ((5 : ℚ) * (posNhi a : ℚ) - 72) *
            partialExpUpperFast (positiveSoloYExponent (posJ a 2))
              (8 * posJ a 2)) := by
        ring
    _ ≤
      ((posJ a 2 : ℚ) * c (posJ a 2)) *
        (9360 * positiveSmallLargeExp a 2) := hbudgetScaled
    _ =
      9360 * (posJ a 2 : ℚ) *
        positiveSmallLargeExp a 2 * c (posJ a 2) := by
        ring

/-- The small-branch exponential at `k = 2` has enough endpoint slack to pay
for the polynomial factor left by the shifted solo first-cell estimate.

This is intentionally a coarse inequality.  The proof uses only
`posNhi a ≤ posSmallCutoff a ^ 2` and a four-step `partialExpUpper` shift;
it does not expand the variable-cutoff exponential. -/
theorem positiveSmallFirstCellShiftedSoloFastExpBudget_of_large
    {a : Nat} (ha : 3000 ≤ a) :
    positiveSmallFirstCellShiftedSoloFastExpBudget a := by
  unfold positiveSmallFirstCellShiftedSoloFastExpBudget positiveSmallLargeExp
  rw [partialExpUpperFast_eq]
  let y : ℚ := positiveSoloYExponent (posJ a 2)
  let z : ℚ := positiveSmallExponentUpper a 2
  let d : ℚ := (1139 / 1000 : ℚ) * (posSmallCutoff a : ℚ)
  let C : ℚ :=
    (29 / 4 : ℚ) * (posNhi a : ℚ) *
      ((5 : ℚ) * (posNhi a : ℚ) - 72)
  let target : ℚ := 9360 / C
  have hNge15 : 15 ≤ posNhi a := by
    unfold posNhi
    omega
  have hNge15Q : (15 : ℚ) ≤ (posNhi a : ℚ) := by
    exact_mod_cast hNge15
  have hlinear_pos :
      0 < (5 : ℚ) * (posNhi a : ℚ) - 72 := by
    nlinarith
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  have hCnonneg : 0 ≤ C := hCpos.le
  have hy0 : 0 ≤ y := by
    dsimp [y]
    unfold positiveSoloYExponent
    positivity
  have hy_lt_a : y < (a : ℚ) := by
    have haQ : (3000 : ℚ) ≤ (a : ℚ) := by
      exact_mod_cast ha
    have hj_le : (posJ a 2 : ℚ) ≤ (a : ℚ) := by
      exact_mod_cast Nat.sub_le a 2
    dsimp [y]
    unfold positiveSoloYExponent
    nlinarith
  have hcutoff_a_le : a ≤ 8 * posJ a 2 := by
    unfold posJ
    omega
  have hcutoff :
      partialExpUpper y (8 * posJ a 2) ≤ partialExpUpper y a :=
    partialExpUpper_cutoff_le_of_le hcutoff_a_le hy0 hy_lt_a
  have hk : 2 ∈ positiveKRange a := by
    refine mem_positiveKRange.mpr ⟨by omega, ?_⟩
    unfold posKmax
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 10)]
    omega
  have hz_lt_a : z < (a : ℚ) := by
    dsimp [z]
    exact positiveSmallExponentUpper_lt_largeExpCutoff
      (by omega : 2000 < a) hk
  have hd0 : 0 ≤ d := by
    dsimp [d]
    positivity
  have hdrop : y + d ≤ z := by
    have hjposNat : 0 < posJ a 2 := by
      unfold posJ
      omega
    have hjposQ : (0 : ℚ) < (posJ a 2 : ℚ) := by
      exact_mod_cast hjposNat
    have hj_le : (posJ a 2 : ℚ) ≤ (a : ℚ) := by
      exact_mod_cast Nat.sub_le a 2
    have hratio : 1 ≤ (a : ℚ) / (posJ a 2 : ℚ) := by
      rw [le_div_iff₀ hjposQ]
      simpa using hj_le
    dsimp [y, z, d]
    unfold positiveSoloYExponent positiveSmallExponentUpper
    nlinarith
  have hN_le_s_sq :
      (posNhi a : ℚ) ≤ (posSmallCutoff a : ℚ)^2 := by
    have hnat : posNhi a ≤ posSmallCutoff a * posSmallCutoff a := by
      unfold posSmallCutoff
      exact le_ceilSqrt_sq (posNhi a)
    simpa [pow_two] using (show (posNhi a : ℚ) ≤
      (posSmallCutoff a : ℚ) * (posSmallCutoff a : ℚ) by
        exact_mod_cast hnat)
  have hN_sq_le_s_four :
      (posNhi a : ℚ)^2 ≤ (posSmallCutoff a : ℚ)^4 := by
    have hNnonneg : 0 ≤ (posNhi a : ℚ) := by positivity
    have hsSqNonneg : 0 ≤ (posSmallCutoff a : ℚ)^2 := sq_nonneg _
    calc
      (posNhi a : ℚ)^2
          ≤ (posSmallCutoff a : ℚ)^2 * (posNhi a : ℚ) :=
            by
              simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using
                mul_le_mul_of_nonneg_right hN_le_s_sq hNnonneg
      _ ≤ (posSmallCutoff a : ℚ)^2 * (posSmallCutoff a : ℚ)^2 :=
            mul_le_mul_of_nonneg_left hN_le_s_sq hsSqNonneg
      _ = (posSmallCutoff a : ℚ)^4 := by ring
  have hC_le_quad :
      C ≤ (145 / 4 : ℚ) * (posNhi a : ℚ)^2 := by
    have hlinear :
        (5 : ℚ) * (posNhi a : ℚ) - 72
          ≤ (5 : ℚ) * (posNhi a : ℚ) := by
      linarith
    have hscale : 0 ≤ (29 / 4 : ℚ) * (posNhi a : ℚ) := by
      positivity
    dsimp [C]
    calc
      (29 / 4 : ℚ) * (posNhi a : ℚ) *
          ((5 : ℚ) * (posNhi a : ℚ) - 72)
          ≤ (29 / 4 : ℚ) * (posNhi a : ℚ) *
              ((5 : ℚ) * (posNhi a : ℚ)) :=
            mul_le_mul_of_nonneg_left hlinear hscale
      _ = (145 / 4 : ℚ) * (posNhi a : ℚ)^2 := by ring
  have hquad_le_gap :
      (145 / 4 : ℚ) * (posNhi a : ℚ)^2
        ≤ 9360 * (d / 4)^4 := by
    have hcoeff :
        (145 / 4 : ℚ) ≤ 9360 * (1139 / 4000 : ℚ)^4 := by
      norm_num
    have hN2nonneg : 0 ≤ (posNhi a : ℚ)^2 := sq_nonneg _
    have hcoeffStep :
        (145 / 4 : ℚ) * (posNhi a : ℚ)^2
          ≤ (9360 * (1139 / 4000 : ℚ)^4) *
              (posNhi a : ℚ)^2 :=
      mul_le_mul_of_nonneg_right hcoeff hN2nonneg
    have hscale : 0 ≤ 9360 * (1139 / 4000 : ℚ)^4 := by
      norm_num
    calc
      (145 / 4 : ℚ) * (posNhi a : ℚ)^2
          ≤ (9360 * (1139 / 4000 : ℚ)^4) *
              (posNhi a : ℚ)^2 := hcoeffStep
      _ ≤ (9360 * (1139 / 4000 : ℚ)^4) *
              (posSmallCutoff a : ℚ)^4 :=
            mul_le_mul_of_nonneg_left hN_sq_le_s_four hscale
      _ = 9360 * (d / 4)^4 := by
            dsimp [d]
            ring
  have hgap_le_shift :
      9360 * (d / 4)^4 ≤ 9360 * (1 + d / 4)^4 := by
    have hbase0 : 0 ≤ d / 4 := by positivity
    have hbase : d / 4 ≤ 1 + d / 4 := by linarith
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hbase0 hbase 4) (by norm_num)
  have hpoly : C ≤ 9360 * (1 + d / 4)^4 :=
    hC_le_quad.trans (hquad_le_gap.trans hgap_le_shift)
  have hbudget :
      1 ≤ target * (1 + d / 4)^4 := by
    have hrewrite :
        target * (1 + d / 4)^4 =
          (9360 * (1 + d / 4)^4) / C := by
      dsimp [target]
      ring
    rw [hrewrite]
    rw [le_div_iff₀ hCpos]
    nlinarith
  have hshift :
      partialExpUpper y a ≤ target * partialExpUpper z a :=
    partialExpUpper_le_mul_of_four_step_shift
      (y := y) (z := z) (d₀ := d) (target := target) (T := a)
      hy0 hd0 (by omega : 1 ≤ a) hz_lt_a hdrop hbudget
  have hexp :
      partialExpUpper y (8 * posJ a 2)
        ≤ target * partialExpUpper z a :=
    hcutoff.trans hshift
  calc
    (29 / 4 : ℚ) * (posNhi a : ℚ) *
        ((5 : ℚ) * (posNhi a : ℚ) - 72) *
        partialExpUpper y (8 * posJ a 2)
        = C * partialExpUpper y (8 * posJ a 2) := by
          dsimp [C]
    _ ≤ C * (target * partialExpUpper z a) :=
          mul_le_mul_of_nonneg_left hexp hCnonneg
    _ = 9360 * partialExpUpper z a := by
          dsimp [target]
          field_simp [hCpos.ne']

/-- Sharp recurrence-level `Qq` target for the first retained product cell.

This is deliberately a bound on the actual coefficient majorant
`QqSharpGcompBound`, not on the older product-side non-sharp `Y` block.  The
closed solo theorem currently available in Lean is sharp and normalized; the
first product cell can therefore reuse future sharp fast `Qq` estimates
directly through `positiveSmallFirstCellQBudget` instead of detouring through
the non-sharp split-factorial product bound. -/
def positiveSmallFirstCellSharpQFastCleared (a N : Nat) : Prop :=
  (4 : ℚ) * (2 : ℚ)^(posJ a 2) *
      QqSharpGcompBound N (posJ a 2)
    ≤ 29 * (posJ a 2 : ℚ) * c (posJ a 2) *
      partialExpUpperFast (positiveSoloYExponent (posJ a 2))
        (8 * posJ a 2)

/-- Explicit sharp closed-factorial target for the first retained product
cell.

This is the concrete analytic target behind
`positiveSmallFirstCellSharpQFastCleared`: it replaces the recurrence-level
`QqSharpGcompBound` by the sharp closed-composition split block already used
in the solo proof.  This is a Lean-side refinement of the TeX route, whose
first product cell is naturally sharp; the older non-sharp `Y` product block is
kept only as a compatibility route below. -/
def positiveSmallFirstCellSharpClosedFactorialSplitBlockSumFastCleared
    (a N : Nat) : Prop :=
  (4 : ℚ) * (2 : ℚ)^(posJ a 2) *
      positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum
        (posJ a 2) N
    ≤ 29 * (posJ a 2 : ℚ) * c (posJ a 2) *
      partialExpUpperFast (positiveSoloYExponent (posJ a 2))
        (8 * posJ a 2)

/-- Constant-budget version of the explicit sharp first-cell target.

For `3000 ≤ a`, the fast solo exponential factor at degree `a-2` is at
least `500`, so this constant-cleared inequality implies the fast target.
It removes the exponential evaluator from the first-cell proof obligation. -/
def positiveSmallFirstCellSharpClosedFactorialSplitBlockSumConstCleared
    (a N : Nat) : Prop :=
  (4 : ℚ) * (2 : ℚ)^(posJ a 2) *
      positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum
        (posJ a 2) N
    ≤ 14500 * (posJ a 2 : ℚ) * c (posJ a 2)

/-- Own-edge constant-budget target for the sharp first product cell.

The product-edge target has a `14500` constant because it includes the fixed
factor `50` needed to move from `posNhi (a-2)` to `posNhi a`.  At the natural
own edge of `j = a - 2`, the remaining target is the cleaner constant
`290`. -/
def positiveSmallFirstCellSharpOwnEdgeConstCleared (a : Nat) : Prop :=
  (4 : ℚ) * (2 : ℚ)^(posJ a 2) *
      positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum
        (posJ a 2) (posNhi (posJ a 2))
    ≤ 290 * (posJ a 2 : ℚ) * c (posJ a 2)

/-- The own-edge first-cell target follows from a constant budget on the
large-degree remainder of the sharp solo block at `j = a - 2`.

This is the current direct first-cell proof surface: the dominant
large-degree simple block is already bounded by `140 * j * c j`, so the
remaining non-large-degree block only has to fit into `150 * j * c j`.  The
argument intentionally uses the sharp split-factorial solo decomposition,
not the much coarser ten-sevenths solo envelope. -/
theorem positiveSmallFirstCellSharpOwnEdgeConstCleared_of_largeDegreeRemainder
    {a : Nat} (ha : 3000 ≤ a)
    (hremainder :
      (4 : ℚ) * (2 : ℚ)^(posJ a 2) *
          positiveLargeTailSoloSharpLargeDegreeRemainderBlockSum (posJ a 2)
        ≤ 150 * (posJ a 2 : ℚ) * c (posJ a 2)) :
    positiveSmallFirstCellSharpOwnEdgeConstCleared a := by
  unfold positiveSmallFirstCellSharpOwnEdgeConstCleared
  let j : Nat := posJ a 2
  have hj_pos : 1 ≤ j := by
    dsimp [j]
    unfold posJ
    omega
  have hj_delta : 361 ≤ j := by
    dsimp [j]
    unfold posJ
    omega
  have hsplit :
      (4 : ℚ) * (2 : ℚ)^j *
          positiveLargeTailSoloSharpLargeDegreeSplitBudgetBlockSum j
        ≤ 290 * (j : ℚ) * c j :=
    positiveLargeTailSoloSharpLargeDegreeSplitBudgetBlockSum_scaled_le_twoNinety_of_remainder
      (a := j) hj_pos (by simpa [j] using hremainder)
  have hclosed :
      positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum
          j (posNhi j)
        ≤ positiveLargeTailSoloSharpDeltaBudgetBlockSum j (posNhi j) :=
    positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum_le_deltaBudgetBlockSum
      j (posNhi j)
  have hdelta :
      positiveLargeTailSoloSharpDeltaBudgetBlockSum j (posNhi j)
        ≤ positiveLargeTailSoloSharpLargeDegreeSplitBudgetBlockSum j :=
    positiveLargeTailSoloSharpDeltaBudgetBlockSum_upperEdge_le_largeDegreeSplit
      (a := j) hj_delta
  have hsum :
      positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum
          j (posNhi j)
        ≤ positiveLargeTailSoloSharpLargeDegreeSplitBudgetBlockSum j :=
    hclosed.trans hdelta
  have hscale : 0 ≤ (4 : ℚ) * (2 : ℚ)^j := by
    positivity
  have hscaled :
      (4 : ℚ) * (2 : ℚ)^j *
          positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum
            j (posNhi j)
        ≤
      (4 : ℚ) * (2 : ℚ)^j *
          positiveLargeTailSoloSharpLargeDegreeSplitBudgetBlockSum j :=
    mul_le_mul_of_nonneg_left hsum hscale
  exact (hscaled.trans hsplit)

/-- First-cell own-edge target from the sharp remainder parts.

This is the route intended for the live product certificate.  It records the
Lean-side split not present in the paper text: after the already-closed
large-degree simple block, the remaining constant `150` is distributed across
the proportional, low-middle, and very-low residual bands. -/
theorem positiveSmallFirstCellSharpOwnEdgeConstCleared_of_remainderParts
    {a : Nat} (ha : 3000 ≤ a)
    {Cprop Cmiddle CveryLow : ℚ}
    (hprop :
      (4 : ℚ) * (2 : ℚ)^(posJ a 2) *
          positiveLargeTailSoloSharpProportionalRemainderSimpleBlockSum
            (posJ a 2)
        ≤ Cprop * (posJ a 2 : ℚ) * c (posJ a 2))
    (hmiddle :
      (4 : ℚ) * (2 : ℚ)^(posJ a 2) *
          positiveLargeTailSoloSharpLowMiddleRemainderSimpleBlockSum
            (posJ a 2)
        ≤ Cmiddle * (posJ a 2 : ℚ) * c (posJ a 2))
    (hveryLow :
      (4 : ℚ) * (2 : ℚ)^(posJ a 2) *
          positiveLargeTailSoloSharpVeryLowDegreeRemainderBlockSum
            (posJ a 2)
        ≤ CveryLow * (posJ a 2 : ℚ) * c (posJ a 2))
    (hbudget : Cprop + Cmiddle + CveryLow ≤ 150) :
    positiveSmallFirstCellSharpOwnEdgeConstCleared a :=
  positiveSmallFirstCellSharpOwnEdgeConstCleared_of_largeDegreeRemainder ha
    (positiveLargeTailSoloSharpLargeDegreeRemainderBlockSum_scaled_le_const_of_prop_lowMiddle_veryLow
      (a := posJ a 2) (show 802 ≤ posJ a 2 by
        unfold posJ
        omega)
      hprop hmiddle hveryLow hbudget)

/-- First-cell own-edge target after closing the proportional and low-middle
active Poisson tails.

The only remaining first-cell remainder input is the very-low residual with
constant `52278/625`; the two active exponential tails each cost
`20736/625`. -/
theorem positiveSmallFirstCellSharpOwnEdgeConstCleared_of_veryLowRemainder
    {a : Nat} (ha : 3000 ≤ a)
    (hveryLow :
      (4 : ℚ) * (2 : ℚ)^(posJ a 2) *
          positiveLargeTailSoloSharpVeryLowDegreeRemainderBlockSum
            (posJ a 2)
        ≤ (52278 / 625 : ℚ) * (posJ a 2 : ℚ) * c (posJ a 2)) :
    positiveSmallFirstCellSharpOwnEdgeConstCleared a :=
  positiveSmallFirstCellSharpOwnEdgeConstCleared_of_remainderParts
    (a := a) ha
    (Cprop := 20736 / 625)
    (Cmiddle := 20736 / 625)
    (CveryLow := 52278 / 625)
    (positiveLargeTailSoloSharpProportionalRemainderSimpleBlockSum_scaled_le_const
      (a := posJ a 2) (show 401 ≤ posJ a 2 by
        unfold posJ
        omega))
    (positiveLargeTailSoloSharpLowMiddleRemainderSimpleBlockSum_scaled_le_const
      (a := posJ a 2) (show 401 ≤ posJ a 2 by
        unfold posJ
        omega))
    hveryLow
    (by norm_num)

/-- The sharp own-edge first-cell target is closed analytically.

The final very-low residual costs only `3 * j * c j`, well below the
remaining `52278/625` allowance after the proportional and low-middle active
Poisson tails. -/
theorem positiveSmallFirstCellSharpOwnEdgeConstCleared_large
    {a : Nat} (ha : 3000 ≤ a) :
    positiveSmallFirstCellSharpOwnEdgeConstCleared a := by
  refine positiveSmallFirstCellSharpOwnEdgeConstCleared_of_veryLowRemainder
    (a := a) ha ?_
  have hvery :=
    positiveLargeTailSoloSharpVeryLowDegreeRemainderBlockSum_scaled_le_three
      (a := posJ a 2) (show 401 ≤ posJ a 2 by
        unfold posJ
        omega)
  have hjc_nonneg : 0 ≤ (posJ a 2 : ℚ) * c (posJ a 2) :=
    mul_nonneg (Nat.cast_nonneg _) (c_nonneg _)
  exact hvery.trans
    (by
      calc
        3 * (posJ a 2 : ℚ) * c (posJ a 2)
            =
          3 * ((posJ a 2 : ℚ) * c (posJ a 2)) := by
            ring
        _ ≤ (52278 / 625 : ℚ) *
            ((posJ a 2 : ℚ) * c (posJ a 2)) := by
            exact mul_le_mul_of_nonneg_right
              (by norm_num : (3 : ℚ) ≤ 52278 / 625)
              hjc_nonneg
        _ = (52278 / 625 : ℚ) * (posJ a 2 : ℚ) *
            c (posJ a 2) := by
            ring)

/-- The sharp recurrence-level `Qq` majorant is monotone in the rectangle
parameter. -/
theorem QqSharpGcompBound_mono_N {N M m : Nat} (hNM : N ≤ M) :
    QqSharpGcompBound N m ≤ QqSharpGcompBound M m := by
  unfold QqSharpGcompBound
  refine expCoeff_mono ?_ ?_ m
  · intro j
    by_cases h0 : j = 0
    · simp [h0]
    · by_cases h1 : j = 1
      · subst j
        norm_num [c_one]
        positivity
      · simp [h0, h1]
        positivity
  · intro j
    have hNMq : (N : ℚ) ≤ (M : ℚ) := by
      exact_mod_cast hNM
    by_cases h0 : j = 0
    · simp [h0]
    · by_cases h1 : j = 1
      · subst j
        norm_num [c_one]
        nlinarith
      · simp [h0, h1]
        have hcoef :
            (2 * (N : ℚ)) / 25 ≤ (2 * (M : ℚ)) / 25 := by
          nlinarith
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef (by positivity))
          (by positivity)

/-- It is enough to check the sharp fast first-cell target at the upper
rectangle edge. -/
theorem positiveSmallFirstCellSharpQFastCleared_of_upperEdge
    {a N : Nat} (hrect : positiveRectangle a N)
    (hEdge : positiveSmallFirstCellSharpQFastCleared a (posNhi a)) :
    positiveSmallFirstCellSharpQFastCleared a N := by
  unfold positiveSmallFirstCellSharpQFastCleared at hEdge ⊢
  have hQ :
      QqSharpGcompBound N (posJ a 2)
        ≤ QqSharpGcompBound (posNhi a) (posJ a 2) :=
    QqSharpGcompBound_mono_N (m := posJ a 2) hrect.2
  have hscale : 0 ≤ (4 : ℚ) * (2 : ℚ)^(posJ a 2) := by
    positivity
  exact (mul_le_mul_of_nonneg_left hQ hscale).trans hEdge

/-- It is enough to check the explicit sharp closed-factorial first-cell
target at the upper rectangle edge. -/
theorem
    positiveSmallFirstCellSharpClosedFactorialSplitBlockSumFastCleared_of_upperEdge
    {a N : Nat} (hrect : positiveRectangle a N)
    (hEdge :
      positiveSmallFirstCellSharpClosedFactorialSplitBlockSumFastCleared
        a (posNhi a)) :
    positiveSmallFirstCellSharpClosedFactorialSplitBlockSumFastCleared
      a N := by
  unfold positiveSmallFirstCellSharpClosedFactorialSplitBlockSumFastCleared
    at hEdge ⊢
  have hsum :
      positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum
          (posJ a 2) N
        ≤ positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum
          (posJ a 2) (posNhi a) :=
    positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum_mono_N
      hrect.2
  have hscale : 0 ≤ (4 : ℚ) * (2 : ℚ)^(posJ a 2) := by
    positivity
  exact (mul_le_mul_of_nonneg_left hsum hscale).trans hEdge

/-- It is enough to check the constant-budget sharp closed-factorial
first-cell target at the upper rectangle edge. -/
theorem
    positiveSmallFirstCellSharpClosedFactorialSplitBlockSumConstCleared_of_upperEdge
    {a N : Nat} (hrect : positiveRectangle a N)
    (hEdge :
      positiveSmallFirstCellSharpClosedFactorialSplitBlockSumConstCleared
        a (posNhi a)) :
    positiveSmallFirstCellSharpClosedFactorialSplitBlockSumConstCleared
      a N := by
  unfold positiveSmallFirstCellSharpClosedFactorialSplitBlockSumConstCleared
    at hEdge ⊢
  have hsum :
      positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum
          (posJ a 2) N
        ≤ positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum
          (posJ a 2) (posNhi a) :=
    positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum_mono_N
      hrect.2
  have hscale : 0 ≤ (4 : ℚ) * (2 : ℚ)^(posJ a 2) := by
    positivity
  exact (mul_le_mul_of_nonneg_left hsum hscale).trans hEdge

/-- The constant-budget first-cell target implies the fast explicit sharp
closed-factorial target in the large-tail range. -/
theorem
    positiveSmallFirstCellSharpClosedFactorialSplitBlockSumFastCleared_of_const
    {a N : Nat} (ha : 3000 ≤ a)
    (h :
      positiveSmallFirstCellSharpClosedFactorialSplitBlockSumConstCleared
        a N) :
    positiveSmallFirstCellSharpClosedFactorialSplitBlockSumFastCleared
      a N := by
  unfold positiveSmallFirstCellSharpClosedFactorialSplitBlockSumConstCleared
    at h
  unfold positiveSmallFirstCellSharpClosedFactorialSplitBlockSumFastCleared
  have hj2500 : 2500 ≤ posJ a 2 := by
    unfold posJ
    omega
  have hexp :
      (500 : ℚ) ≤
        partialExpUpperFast (positiveSoloYExponent (posJ a 2))
          (8 * posJ a 2) :=
    by
      have hy_ge :
          (500 : ℚ) ≤ positiveSoloYExponent (posJ a 2) := by
        have hjQ : (2500 : ℚ) ≤ (posJ a 2 : ℚ) := by
          exact_mod_cast hj2500
        unfold positiveSoloYExponent
        nlinarith
      have hy0 : 0 ≤ positiveSoloYExponent (posJ a 2) := by
        unfold positiveSoloYExponent
        positivity
      have hyT :
          positiveSoloYExponent (posJ a 2) <
            ((8 * posJ a 2 : Nat) : ℚ) := by
        have hjQ : (1 : ℚ) ≤ (posJ a 2 : ℚ) := by
          exact_mod_cast (by omega : 1 ≤ posJ a 2)
        unfold positiveSoloYExponent
        norm_num [Nat.cast_mul]
        nlinarith
      have hterm :
          positiveSoloYExponent (posJ a 2) ^ (1 : Nat) /
              (((1 : Nat).factorial : Nat) : ℚ)
            ≤ partialExpUpper (positiveSoloYExponent (posJ a 2))
              (8 * posJ a 2) :=
        expTerm_le_partialExpUpper
          (z := positiveSoloYExponent (posJ a 2)) (m := 1)
          (T := 8 * posJ a 2) (by omega : 1 < 8 * posJ a 2)
          hy0 hyT
      have hterm_eq :
          positiveSoloYExponent (posJ a 2) ^ (1 : Nat) /
              (((1 : Nat).factorial : Nat) : ℚ)
            = positiveSoloYExponent (posJ a 2) := by
        norm_num
      rw [partialExpUpperFast_eq]
      rw [hterm_eq] at hterm
      exact hy_ge.trans hterm
  have hcoef_nonneg :
      0 ≤ (29 : ℚ) * (posJ a 2 : ℚ) * c (posJ a 2) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (c_nonneg _)
  have hbudget :
      14500 * (posJ a 2 : ℚ) * c (posJ a 2)
        ≤ 29 * (posJ a 2 : ℚ) * c (posJ a 2) *
          partialExpUpperFast (positiveSoloYExponent (posJ a 2))
            (8 * posJ a 2) := by
    calc
      14500 * (posJ a 2 : ℚ) * c (posJ a 2)
          =
        (29 * (posJ a 2 : ℚ) * c (posJ a 2)) * (500 : ℚ) := by
          ring
      _ ≤ (29 * (posJ a 2 : ℚ) * c (posJ a 2)) *
          partialExpUpperFast (positiveSoloYExponent (posJ a 2))
            (8 * posJ a 2) :=
          mul_le_mul_of_nonneg_left hexp hcoef_nonneg
      _ =
        29 * (posJ a 2 : ℚ) * c (posJ a 2) *
          partialExpUpperFast (positiveSoloYExponent (posJ a 2))
            (8 * posJ a 2) := by
          ring
  exact h.trans hbudget

/-- The explicit sharp closed-factorial first-cell target implies the
recurrence-level sharp `Qq` first-cell target. -/
theorem positiveSmallFirstCellSharpQFastCleared_of_closedFactorialSplit
    {a N : Nat}
    (h :
      positiveSmallFirstCellSharpClosedFactorialSplitBlockSumFastCleared
        a N) :
    positiveSmallFirstCellSharpQFastCleared a N := by
  unfold positiveSmallFirstCellSharpClosedFactorialSplitBlockSumFastCleared
    at h
  unfold positiveSmallFirstCellSharpQFastCleared
  have hQ_le_split :
      QqSharpGcompBound N (posJ a 2)
        ≤ positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum
          (posJ a 2) N := by
    calc
      QqSharpGcompBound N (posJ a 2)
          =
        positiveLargeTailSoloSharpGcompSaddleSum (posJ a 2) N :=
          (positiveLargeTailSoloSharpGcompSaddleSum_eq_QqSharpGcompBound
            (posJ a 2) N).symm
      _ ≤ positiveLargeTailSoloSharpGcompBlockSum (posJ a 2) N :=
          positiveLargeTailSoloSharpGcompSaddleSum_le_blockSum
            (posJ a 2) N
      _ ≤ positiveLargeTailSoloSharpGcompClosedBlockSum (posJ a 2) N :=
          positiveLargeTailSoloSharpGcompBlockSum_le_closedBlockSum
            (posJ a 2) N
      _ = positiveLargeTailSoloSharpGcompClosedFactorialBlockSum
          (posJ a 2) N :=
          (positiveLargeTailSoloSharpGcompClosedFactorialBlockSum_eq_closedBlockSum
            (posJ a 2) N).symm
      _ = positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum
          (posJ a 2) N :=
          (positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum_eq_factorialBlockSum
            (posJ a 2) N).symm
  have hscale : 0 ≤ (4 : ℚ) * (2 : ℚ)^(posJ a 2) := by
    positivity
  exact (mul_le_mul_of_nonneg_left hQ_le_split hscale).trans h

/-- A sharp fast `Qq` first-cell estimate supplies the direct first-cell
`Qq` budget.

This records the intended completion route for the `k = 2` product cell:
prove the sharp fast `Qq` estimate, then use the already-closed scalar
comparison `positiveSmallFirstCellShiftedSoloFastExpBudget_of_large`.  The
older non-sharp upper-edge `Y` route remains below as a compatibility path,
but it is not forced on the canonical product-tail proof. -/
theorem positiveSmallFirstCellQBudget_of_sharpQFastCleared
    {a N : Nat} (ha : 3000 ≤ a) (hrect : positiveRectangle a N)
    (hsharp : positiveSmallFirstCellSharpQFastCleared a N) :
    positiveSmallFirstCellQBudget a N
      (QqSharpGcompBound N (posJ a 2)) := by
  unfold positiveSmallFirstCellSharpQFastCleared at hsharp
  unfold positiveSmallFirstCellQBudget
  have hNge15 : 15 ≤ N := by
    have hNlo : posNlo a ≤ N := hrect.1
    unfold posNlo at hNlo
    omega
  have hlinear_nonneg :
      0 ≤ (5 : ℚ) * (N : ℚ) - 72 := by
    have hNge15Q : (15 : ℚ) ≤ (N : ℚ) := by
      exact_mod_cast hNge15
    nlinarith
  have hlinear_le :
      (5 : ℚ) * (N : ℚ) - 72
        ≤ (5 : ℚ) * (posNhi a : ℚ) - 72 := by
    have hNle : (N : ℚ) ≤ (posNhi a : ℚ) := by
      exact_mod_cast hrect.2
    nlinarith
  have hy0 : 0 ≤ positiveSoloYExponent (posJ a 2) := by
    unfold positiveSoloYExponent
    positivity
  have hy_lt_T :
      positiveSoloYExponent (posJ a 2)
        < ((8 * posJ a 2 : Nat) : ℚ) := by
    have hjQ : (1 : ℚ) ≤ (posJ a 2 : ℚ) := by
      exact_mod_cast (by unfold posJ; omega : 1 ≤ posJ a 2)
    unfold positiveSoloYExponent
    rw [Nat.cast_mul]
    norm_num
    nlinarith
  have hpartial_nonneg :
      0 ≤
        partialExpUpperFast (positiveSoloYExponent (posJ a 2))
          (8 * posJ a 2) := by
    rw [partialExpUpperFast_eq]
    exact partialExpUpper_nonneg_of_nonneg_lt hy0 hy_lt_T
  have hcoef_nonneg :
      0 ≤
        (29 / 4 : ℚ) * (posNhi a : ℚ) *
          partialExpUpperFast (positiveSoloYExponent (posJ a 2))
            (8 * posJ a 2) := by
    positivity
  have hbudget := positiveSmallFirstCellShiftedSoloFastExpBudget_of_large ha
  unfold positiveSmallFirstCellShiftedSoloFastExpBudget at hbudget
  have hbudgetN :
      (29 / 4 : ℚ) * (posNhi a : ℚ) *
          ((5 : ℚ) * (N : ℚ) - 72) *
          partialExpUpperFast (positiveSoloYExponent (posJ a 2))
            (8 * posJ a 2)
        ≤ 9360 * positiveSmallLargeExp a 2 := by
    calc
      (29 / 4 : ℚ) * (posNhi a : ℚ) *
          ((5 : ℚ) * (N : ℚ) - 72) *
          partialExpUpperFast (positiveSoloYExponent (posJ a 2))
            (8 * posJ a 2)
          =
        ((29 / 4 : ℚ) * (posNhi a : ℚ) *
          partialExpUpperFast (positiveSoloYExponent (posJ a 2))
            (8 * posJ a 2)) *
          ((5 : ℚ) * (N : ℚ) - 72) := by
            ring
      _ ≤
        ((29 / 4 : ℚ) * (posNhi a : ℚ) *
          partialExpUpperFast (positiveSoloYExponent (posJ a 2))
            (8 * posJ a 2)) *
          ((5 : ℚ) * (posNhi a : ℚ) - 72) :=
            mul_le_mul_of_nonneg_left hlinear_le hcoef_nonneg
      _ =
        (29 / 4 : ℚ) * (posNhi a : ℚ) *
          ((5 : ℚ) * (posNhi a : ℚ) - 72) *
          partialExpUpperFast (positiveSoloYExponent (posJ a 2))
            (8 * posJ a 2) := by
            ring
      _ ≤ 9360 * positiveSmallLargeExp a 2 := hbudget
  have hscale_nonneg :
      0 ≤ (posNhi a : ℚ) *
          ((5 : ℚ) * (N : ℚ) - 72) / 4 := by
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg (posNhi a)) hlinear_nonneg)
      (by norm_num)
  have hsharpScaled :=
    mul_le_mul_of_nonneg_left hsharp hscale_nonneg
  have hjc_nonneg :
      0 ≤ (posJ a 2 : ℚ) * c (posJ a 2) :=
    mul_nonneg (Nat.cast_nonneg _) (c_nonneg (posJ a 2))
  have hbudgetScaled :
      ((posJ a 2 : ℚ) * c (posJ a 2)) *
        ((29 / 4 : ℚ) * (posNhi a : ℚ) *
          ((5 : ℚ) * (N : ℚ) - 72) *
          partialExpUpperFast (positiveSoloYExponent (posJ a 2))
            (8 * posJ a 2))
        ≤
      ((posJ a 2 : ℚ) * c (posJ a 2)) *
        (9360 * positiveSmallLargeExp a 2) :=
    mul_le_mul_of_nonneg_left hbudgetN hjc_nonneg
  calc
    (2 : ℚ)^(posJ a 2) * (posNhi a : ℚ) *
        (5 * (N : ℚ) - 72) *
        QqSharpGcompBound N (posJ a 2)
        =
      ((posNhi a : ℚ) * ((5 : ℚ) * (N : ℚ) - 72) / 4) *
        ((4 : ℚ) * (2 : ℚ)^(posJ a 2) *
          QqSharpGcompBound N (posJ a 2)) := by
          ring
    _ ≤
      ((posNhi a : ℚ) * ((5 : ℚ) * (N : ℚ) - 72) / 4) *
        (29 * (posJ a 2 : ℚ) * c (posJ a 2) *
          partialExpUpperFast (positiveSoloYExponent (posJ a 2))
            (8 * posJ a 2)) := hsharpScaled
    _ =
      ((posJ a 2 : ℚ) * c (posJ a 2)) *
        ((29 / 4 : ℚ) * (posNhi a : ℚ) *
          ((5 : ℚ) * (N : ℚ) - 72) *
          partialExpUpperFast (positiveSoloYExponent (posJ a 2))
            (8 * posJ a 2)) := by
          ring
    _ ≤
      ((posJ a 2 : ℚ) * c (posJ a 2)) *
        (9360 * positiveSmallLargeExp a 2) := hbudgetScaled
    _ =
      9360 * (posJ a 2 : ℚ) *
        positiveSmallLargeExp a 2 * c (posJ a 2) := by
          ring

/-- Low-threshold version of the reusable `(1+3/a)^a` bound.

The proof is the same rational estimate as
`one_add_three_div_pow_le_fifty`; the lower threshold is useful for the
shifted first product cell, where the solo index is `a - 2` and hence is
only `2998` at the canonical large-tail threshold `a = 3000`. -/
theorem one_add_three_div_pow_le_fifty_of_twelve
    {a s : Nat} (ha : 12 ≤ a) (hs : s ≤ a) :
    (1 + (3 : ℚ) / (a : ℚ))^s ≤ 50 := by
  let n : Nat := a / 3
  have ha_pos_nat : 0 < a := by omega
  have ha_pos : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha_pos_nat
  have hn_pos_nat : 0 < n := by
    dsimp [n]
    omega
  have hn_pos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn_pos_nat
  have hbase_ge_one : (1 : ℚ) ≤ 1 + (3 : ℚ) / (a : ℚ) := by
    have hnonneg : (0 : ℚ) ≤ (3 : ℚ) / (a : ℚ) := by positivity
    linarith
  have hpow_s_a :
      (1 + (3 : ℚ) / (a : ℚ))^s
        ≤ (1 + (3 : ℚ) / (a : ℚ))^a :=
    pow_le_pow_right₀ hbase_ge_one hs
  have hmul : (3 : ℚ) * (n : ℚ) ≤ (a : ℚ) := by
    have hnat : a / 3 * 3 ≤ a := Nat.div_mul_le_self a 3
    have hq : ((a / 3 * 3 : Nat) : ℚ) ≤ (a : ℚ) := by
      exact_mod_cast hnat
    dsimp [n]
    simpa [Nat.cast_mul, mul_comm] using hq
  have hbase_le :
      1 + (3 : ℚ) / (a : ℚ) ≤ 1 + 1 / (n : ℚ) := by
    field_simp [ha_pos.ne', hn_pos.ne']
    nlinarith
  have hpow_base :
      (1 + (3 : ℚ) / (a : ℚ))^a
        ≤ (1 + 1 / (n : ℚ))^a :=
    pow_le_pow_left₀ (by positivity) hbase_le a
  have hexp : a ≤ 3 * (n + 1) := by
    dsimp [n]
    omega
  have hbase2_ge_one : (1 : ℚ) ≤ 1 + 1 / (n : ℚ) := by
    have hnonneg : (0 : ℚ) ≤ 1 / (n : ℚ) := by positivity
    linarith
  have hpow_exp :
      (1 + 1 / (n : ℚ))^a
        ≤ (1 + 1 / (n : ℚ))^(3 * (n + 1)) :=
    pow_le_pow_right₀ hbase2_ge_one hexp
  have hsplit :
      (1 + 1 / (n : ℚ))^(3 * (n + 1))
        =
      ((1 + 1 / (n : ℚ))^n)^3 *
        (1 + 1 / (n : ℚ))^3 := by
    have hnat : 3 * (n + 1) = n * 3 + 3 := by ring
    rw [hnat, pow_add, pow_mul]
  have hmain :
      (1 + 1 / (n : ℚ))^(3 * (n + 1)) ≤ 50 := by
    have he := one_add_inv_pow_le n (by omega : 1 ≤ n)
    have hn_ge4 : (4 : ℚ) ≤ (n : ℚ) := by
      have hn4 : 4 ≤ n := by
        dsimp [n]
        omega
      exact_mod_cast hn4
    have hb2 : 1 + 1 / (n : ℚ) ≤ 5 / 4 := by
      field_simp [hn_pos.ne']
      nlinarith
    have hfirst :
        ((1 + 1 / (n : ℚ))^n)^3 ≤ (68 / 25 : ℚ)^3 :=
      pow_le_pow_left₀ (by positivity) he 3
    have hsecond :
        (1 + 1 / (n : ℚ))^3 ≤ (5 / 4 : ℚ)^3 :=
      pow_le_pow_left₀ (by positivity) hb2 3
    rw [hsplit]
    calc
      ((1 + 1 / (n : ℚ))^n)^3 *
          (1 + 1 / (n : ℚ))^3
          ≤ (68 / 25 : ℚ)^3 * (5 / 4 : ℚ)^3 := by
            exact mul_le_mul hfirst hsecond (by positivity) (by positivity)
      _ ≤ 50 := by norm_num
  exact hpow_s_a.trans (hpow_base.trans (hpow_exp.trans hmain))

/-- Low-threshold successor-exponent variant of
`one_add_three_div_pow_le_fifty_of_twelve`.

This is used for the `j = a - 3` product edge: the rectangle ratio is bounded
by `1 + 3/(j-1)`, and the power is `j = (j-1)+1`. -/
theorem one_add_three_div_pow_succ_le_fifty_of_twelve
    {a : Nat} (ha : 12 ≤ a) :
    (1 + (3 : ℚ) / (a : ℚ))^(a + 1) ≤ 50 := by
  let n : Nat := a / 3
  have ha_pos_nat : 0 < a := by omega
  have ha_pos : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha_pos_nat
  have hn_pos_nat : 0 < n := by
    dsimp [n]
    omega
  have hn_pos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn_pos_nat
  have hbase_ge_one : (1 : ℚ) ≤ 1 + (3 : ℚ) / (a : ℚ) := by
    have hnonneg : (0 : ℚ) ≤ (3 : ℚ) / (a : ℚ) := by positivity
    linarith
  have hmul : (3 : ℚ) * (n : ℚ) ≤ (a : ℚ) := by
    have hnat : a / 3 * 3 ≤ a := Nat.div_mul_le_self a 3
    have hq : ((a / 3 * 3 : Nat) : ℚ) ≤ (a : ℚ) := by
      exact_mod_cast hnat
    dsimp [n]
    simpa [Nat.cast_mul, mul_comm] using hq
  have hbase_le :
      1 + (3 : ℚ) / (a : ℚ) ≤ 1 + 1 / (n : ℚ) := by
    field_simp [ha_pos.ne', hn_pos.ne']
    nlinarith
  have hpow_base :
      (1 + (3 : ℚ) / (a : ℚ))^(a + 1)
        ≤ (1 + 1 / (n : ℚ))^(a + 1) :=
    pow_le_pow_left₀ (by positivity) hbase_le (a + 1)
  have hexp : a + 1 ≤ 3 * (n + 1) + 1 := by
    dsimp [n]
    omega
  have hbase2_ge_one : (1 : ℚ) ≤ 1 + 1 / (n : ℚ) := by
    have hnonneg : (0 : ℚ) ≤ 1 / (n : ℚ) := by positivity
    linarith
  have hpow_exp :
      (1 + 1 / (n : ℚ))^(a + 1)
        ≤ (1 + 1 / (n : ℚ))^(3 * (n + 1) + 1) :=
    pow_le_pow_right₀ hbase2_ge_one hexp
  have hsplit :
      (1 + 1 / (n : ℚ))^(3 * (n + 1) + 1)
        =
      ((1 + 1 / (n : ℚ))^n)^3 *
        (1 + 1 / (n : ℚ))^4 := by
    have hnat : 3 * (n + 1) + 1 = n * 3 + 4 := by ring
    rw [hnat, pow_add, pow_mul]
  have hmain :
      (1 + 1 / (n : ℚ))^(3 * (n + 1) + 1) ≤ 50 := by
    have he := one_add_inv_pow_le n (by omega : 1 ≤ n)
    have hn_ge4 : (4 : ℚ) ≤ (n : ℚ) := by
      have hn4 : 4 ≤ n := by
        dsimp [n]
        omega
      exact_mod_cast hn4
    have hb2 : 1 + 1 / (n : ℚ) ≤ 5 / 4 := by
      field_simp [hn_pos.ne']
      nlinarith
    have hfirst :
        ((1 + 1 / (n : ℚ))^n)^3 ≤ (68 / 25 : ℚ)^3 :=
      pow_le_pow_left₀ (by positivity) he 3
    have hsecond :
        (1 + 1 / (n : ℚ))^4 ≤ (5 / 4 : ℚ)^4 :=
      pow_le_pow_left₀ (by positivity) hb2 4
    rw [hsplit]
    calc
      ((1 + 1 / (n : ℚ))^n)^3 *
          (1 + 1 / (n : ℚ))^4
          ≤ (68 / 25 : ℚ)^3 * (5 / 4 : ℚ)^4 := by
            exact mul_le_mul hfirst hsecond (by positivity) (by positivity)
      _ ≤ 50 := by norm_num
  exact hpow_base.trans (hpow_exp.trans hmain)

/-- The shifted first-cell `Y` block at the product upper edge is controlled
by the same shifted block at its own solo upper edge, at cost `50`.

This is a Lean proof-production divergence from the TeX presentation: the
paper treats the shifted edge estimate directly, while the formal route now
records that the rectangle mismatch `posNhi a > posNhi (a - 2)` costs only a
fixed multiplicative factor.  The remaining first-cell scalar budget can
therefore absorb this factor instead of strengthening the solo theorem to the
larger product edge. -/
theorem positiveLargeTailSoloGcompClosedFactorialSplitBlockSum_productEdge_le_fifty_shiftedUpperEdge
    {a : Nat} (ha : 3000 ≤ a) :
    positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
        (posJ a 2) (posNhi a)
      ≤ (50 : ℚ) *
        positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
          (posJ a 2) (posNhi (posJ a 2)) := by
  let j : Nat := posJ a 2
  let R : ℚ := 1 + (3 : ℚ) / (j : ℚ)
  have hj_large : 12 ≤ j := by
    dsimp [j]
    unfold posJ
    omega
  have hj_le_self : j ≤ j := le_rfl
  have hR1 : (1 : ℚ) ≤ R := by
    dsimp [R]
    have hj_pos : (0 : ℚ) < (j : ℚ) := by
      exact_mod_cast (by omega : 0 < j)
    have hnonneg : (0 : ℚ) ≤ 3 / (j : ℚ) := by positivity
    linarith
  have hM :
      (posNhi a : ℚ) ≤ R * (posNhi j : ℚ) := by
    have hj_pos : (0 : ℚ) < (j : ℚ) := by
      exact_mod_cast (by omega : 0 < j)
    have hposJ_cast : (j : ℚ) = (a : ℚ) - 2 := by
      dsimp [j]
      unfold posJ
      rw [Nat.cast_sub (by omega : 2 ≤ a)]
      norm_num
    have hNhi_a : (posNhi a : ℚ) = 12 * (a : ℚ) - 8 := by
      unfold posNhi
      rw [Nat.cast_sub (by omega : 8 ≤ 12 * a)]
      norm_num
    have hNhi_j : (posNhi j : ℚ) = 12 * (j : ℚ) - 8 := by
      unfold posNhi
      rw [Nat.cast_sub (by omega : 8 ≤ 12 * j)]
      norm_num
    have haQ : (3000 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
    have hden_pos : (0 : ℚ) < (a : ℚ) - 2 := by nlinarith
    dsimp [R]
    rw [hNhi_a, hNhi_j, hposJ_cast]
    rw [← sub_nonneg]
    field_simp [hden_pos.ne']
    ring_nf
    nlinarith
  have hscaled :
      positiveLargeTailSoloGcompClosedFactorialSplitBlockSum j (posNhi a)
        ≤ R^j *
          positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
            j (posNhi j) := by
    unfold positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
    exact
      positiveLargeTailYGcompClosedFactorialSplitBlockSum_le_scaled_of_natCast_le
        (N := posNhi j) (M := posNhi a) (j := j) hR1 hM
  have hpow : R^j ≤ (50 : ℚ) := by
    dsimp [R]
    exact one_add_three_div_pow_le_fifty_of_twelve
      (a := j) (s := j) hj_large hj_le_self
  have hsum_nonneg :
      0 ≤ positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
          j (posNhi j) :=
    positiveLargeTailSoloGcompClosedFactorialSplitBlockSum_nonneg
      j (posNhi j)
  have hscaled50 :
      R^j *
          positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
            j (posNhi j)
        ≤ (50 : ℚ) *
          positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
            j (posNhi j) :=
    mul_le_mul_of_nonneg_right hpow hsum_nonneg
  simpa [j] using hscaled.trans hscaled50

/-- The `k = 3` shifted `Y` block at the product upper edge is controlled by
the same shifted block at its own solo upper edge, again at fixed cost `50`.

This is another Lean proof-production divergence from the TeX presentation:
we isolate the rectangle mismatch `posNhi a > posNhi (a - 3)` and pay it in
the third-cell scalar budget, leaving the solo-shaped input at its natural
upper edge. -/
theorem positiveLargeTailSoloGcompClosedFactorialSplitBlockSum_thirdProductEdge_le_fifty_shiftedUpperEdge
    {a : Nat} (ha : 3000 ≤ a) :
    positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
        (posJ a 3) (posNhi a)
      ≤ (50 : ℚ) *
        positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
          (posJ a 3) (posNhi (posJ a 3)) := by
  let j : Nat := posJ a 3
  let R : ℚ := 1 + (3 : ℚ) / ((j - 1 : Nat) : ℚ)
  have hj_large : 12 ≤ j - 1 := by
    dsimp [j]
    unfold posJ
    omega
  have hR1 : (1 : ℚ) ≤ R := by
    dsimp [R]
    have hden_pos : (0 : ℚ) < ((j - 1 : Nat) : ℚ) := by
      exact_mod_cast (by omega : 0 < j - 1)
    have hnonneg : (0 : ℚ) ≤ 3 / ((j - 1 : Nat) : ℚ) := by
      positivity
    linarith
  have hM :
      (posNhi a : ℚ) ≤ R * (posNhi j : ℚ) := by
    have hden_pos : (0 : ℚ) < ((j - 1 : Nat) : ℚ) := by
      exact_mod_cast (by omega : 0 < j - 1)
    have hden_a_pos : (0 : ℚ) < (a : ℚ) - 4 := by
      have haQ : (3000 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
      nlinarith
    have hposJ_cast : (j : ℚ) = (a : ℚ) - 3 := by
      dsimp [j]
      unfold posJ
      rw [Nat.cast_sub (by omega : 3 ≤ a)]
      norm_num
    have hjm1_cast : ((j - 1 : Nat) : ℚ) = (a : ℚ) - 4 := by
      dsimp [j]
      unfold posJ
      rw [show a - 3 - 1 = a - 4 by omega]
      rw [Nat.cast_sub (by omega : 4 ≤ a)]
      norm_num
    have hNhi_a : (posNhi a : ℚ) = 12 * (a : ℚ) - 8 := by
      unfold posNhi
      rw [Nat.cast_sub (by omega : 8 ≤ 12 * a)]
      norm_num
    have hNhi_j : (posNhi j : ℚ) = 12 * (j : ℚ) - 8 := by
      unfold posNhi
      rw [Nat.cast_sub (by omega : 8 ≤ 12 * j)]
      norm_num
    dsimp [R]
    rw [hNhi_a, hNhi_j, hposJ_cast, hjm1_cast]
    rw [← sub_nonneg]
    have hdiff :
        (1 + 3 / ((a : ℚ) - 4)) *
            (12 * ((a : ℚ) - 3) - 8) - (12 * (a : ℚ) - 8)
          = 12 / ((a : ℚ) - 4) := by
      field_simp [hden_a_pos.ne']
      ring
    rw [hdiff]
    positivity
  have hscaled :
      positiveLargeTailSoloGcompClosedFactorialSplitBlockSum j (posNhi a)
        ≤ R^j *
          positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
            j (posNhi j) := by
    unfold positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
    exact
      positiveLargeTailYGcompClosedFactorialSplitBlockSum_le_scaled_of_natCast_le
        (N := posNhi j) (M := posNhi a) (j := j) hR1 hM
  have hpow : R^j ≤ (50 : ℚ) := by
    have hj_eq : (j - 1) + 1 = j := by omega
    dsimp [R]
    rw [← hj_eq]
    exact one_add_three_div_pow_succ_le_fifty_of_twelve
      (a := j - 1) hj_large
  have hsum_nonneg :
      0 ≤ positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
          j (posNhi j) :=
    positiveLargeTailSoloGcompClosedFactorialSplitBlockSum_nonneg
      j (posNhi j)
  have hscaled50 :
      R^j *
          positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
            j (posNhi j)
        ≤ (50 : ℚ) *
          positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
            j (posNhi j) :=
    mul_le_mul_of_nonneg_right hpow hsum_nonneg
  simpa [j] using hscaled.trans hscaled50

/-- Sharp analogue of
`positiveLargeTailSoloGcompClosedFactorialSplitBlockSum_productEdge_le_fifty_shiftedUpperEdge`.

The same rectangle mismatch `posNhi a > posNhi (a - 2)` costs a factor `50`
for the sharp closed-factorial block.  This is the edge-scaling input needed
to turn the constant first-cell target into a shifted solo-style target at
the natural upper edge of `j = a - 2`. -/
theorem positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum_productEdge_le_fifty_shiftedUpperEdge
    {a : Nat} (ha : 3000 ≤ a) :
    positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum
        (posJ a 2) (posNhi a)
      ≤ (50 : ℚ) *
        positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum
          (posJ a 2) (posNhi (posJ a 2)) := by
  let j : Nat := posJ a 2
  let R : ℚ := 1 + (3 : ℚ) / (j : ℚ)
  have hj_large : 12 ≤ j := by
    dsimp [j]
    unfold posJ
    omega
  have hj_le_self : j ≤ j := le_rfl
  have hR1 : (1 : ℚ) ≤ R := by
    dsimp [R]
    have hj_pos : (0 : ℚ) < (j : ℚ) := by
      exact_mod_cast (by omega : 0 < j)
    have hnonneg : (0 : ℚ) ≤ 3 / (j : ℚ) := by positivity
    linarith
  have hM :
      (posNhi a : ℚ) ≤ R * (posNhi j : ℚ) := by
    have hj_pos : (0 : ℚ) < (j : ℚ) := by
      exact_mod_cast (by omega : 0 < j)
    have hposJ_cast : (j : ℚ) = (a : ℚ) - 2 := by
      dsimp [j]
      unfold posJ
      rw [Nat.cast_sub (by omega : 2 ≤ a)]
      norm_num
    have hNhi_a : (posNhi a : ℚ) = 12 * (a : ℚ) - 8 := by
      unfold posNhi
      rw [Nat.cast_sub (by omega : 8 ≤ 12 * a)]
      norm_num
    have hNhi_j : (posNhi j : ℚ) = 12 * (j : ℚ) - 8 := by
      unfold posNhi
      rw [Nat.cast_sub (by omega : 8 ≤ 12 * j)]
      norm_num
    have haQ : (3000 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
    have hden_pos : (0 : ℚ) < (a : ℚ) - 2 := by nlinarith
    dsimp [R]
    rw [hNhi_a, hNhi_j, hposJ_cast]
    rw [← sub_nonneg]
    field_simp [hden_pos.ne']
    ring_nf
    nlinarith
  have hscaled :
      positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum
          j (posNhi a)
        ≤ R^j *
          positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum
            j (posNhi j) :=
    positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum_le_scaled_of_natCast_le
      (N := posNhi j) (M := posNhi a) (a := j) hR1 hM
  have hpow : R^j ≤ (50 : ℚ) := by
    dsimp [R]
    exact one_add_three_div_pow_le_fifty_of_twelve
      (a := j) (s := j) hj_large hj_le_self
  have hsum_nonneg :
      0 ≤ positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum
          j (posNhi j) :=
    positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum_nonneg
      j (posNhi j)
  have hscaled50 :
      R^j *
          positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum
            j (posNhi j)
        ≤ (50 : ℚ) *
          positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum
            j (posNhi j) :=
    mul_le_mul_of_nonneg_right hpow hsum_nonneg
  simpa [j] using hscaled.trans hscaled50

/-- The own-edge sharp first-cell constant target implies the product-edge
constant target after paying the fixed edge-scaling factor `50`. -/
theorem
    positiveSmallFirstCellSharpClosedFactorialSplitBlockSumConstCleared_of_ownEdge
    {a : Nat} (ha : 3000 ≤ a)
    (hown : positiveSmallFirstCellSharpOwnEdgeConstCleared a) :
    positiveSmallFirstCellSharpClosedFactorialSplitBlockSumConstCleared
      a (posNhi a) := by
  unfold positiveSmallFirstCellSharpOwnEdgeConstCleared at hown
  unfold positiveSmallFirstCellSharpClosedFactorialSplitBlockSumConstCleared
  have hedge :=
    positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum_productEdge_le_fifty_shiftedUpperEdge
      (a := a) ha
  have hscale_nonneg : 0 ≤ (4 : ℚ) * (2 : ℚ)^(posJ a 2) := by
    positivity
  have hscaled :
      (4 : ℚ) * (2 : ℚ)^(posJ a 2) *
          positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum
            (posJ a 2) (posNhi a)
        ≤
      (50 : ℚ) *
        ((4 : ℚ) * (2 : ℚ)^(posJ a 2) *
          positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum
            (posJ a 2) (posNhi (posJ a 2))) := by
    calc
      (4 : ℚ) * (2 : ℚ)^(posJ a 2) *
          positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum
            (posJ a 2) (posNhi a)
          ≤
        (4 : ℚ) * (2 : ℚ)^(posJ a 2) *
          ((50 : ℚ) *
            positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum
              (posJ a 2) (posNhi (posJ a 2))) := by
          simpa [mul_assoc] using
            mul_le_mul_of_nonneg_left hedge hscale_nonneg
      _ =
        (50 : ℚ) *
          ((4 : ℚ) * (2 : ℚ)^(posJ a 2) *
            positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum
              (posJ a 2) (posNhi (posJ a 2))) := by
          ring
  have hownScaled :
      (50 : ℚ) *
        ((4 : ℚ) * (2 : ℚ)^(posJ a 2) *
          positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum
            (posJ a 2) (posNhi (posJ a 2)))
        ≤
      (50 : ℚ) * (290 * (posJ a 2 : ℚ) * c (posJ a 2)) :=
    mul_le_mul_of_nonneg_left hown (by norm_num)
  calc
    (4 : ℚ) * (2 : ℚ)^(posJ a 2) *
        positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum
          (posJ a 2) (posNhi a)
        ≤
      (50 : ℚ) *
        ((4 : ℚ) * (2 : ℚ)^(posJ a 2) *
          positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSum
            (posJ a 2) (posNhi (posJ a 2))) := hscaled
    _ ≤ (50 : ℚ) * (290 * (posJ a 2 : ℚ) * c (posJ a 2)) :=
      hownScaled
    _ = 14500 * (posJ a 2 : ℚ) * c (posJ a 2) := by
      ring

/-- First-cell scalar budget after paying the fixed `50` factor needed to
move the shifted solo block from `posNhi (a - 2)` to the product edge
`posNhi a`. -/
def positiveSmallFirstCellShiftedSoloFiftyFastExpBudget (a : Nat) : Prop :=
  (29 / 4 : ℚ) * (posNhi a : ℚ) *
      ((5 : ℚ) * (posNhi a : ℚ) - 72) * 50 *
        partialExpUpperFast (positiveSoloYExponent (posJ a 2))
          (8 * posJ a 2)
    ≤ 9360 * positiveSmallLargeExp a 2

/-- The small-branch exponential still has enough slack after paying the
fixed `50` factor from the shifted-edge scaling lemma.

This is the scalar side of the completion-facing first-cell route.  The proof
is the same exponent-gap argument as
`positiveSmallFirstCellShiftedSoloFastExpBudget_of_large`, but uses a
six-step `partialExpUpper` shift so that the square-root gap also pays the
constant edge-scaling factor. -/
theorem positiveSmallFirstCellShiftedSoloFiftyFastExpBudget_of_large
    {a : Nat} (ha : 3000 ≤ a) :
    positiveSmallFirstCellShiftedSoloFiftyFastExpBudget a := by
  unfold positiveSmallFirstCellShiftedSoloFiftyFastExpBudget
    positiveSmallLargeExp
  rw [partialExpUpperFast_eq]
  let y : ℚ := positiveSoloYExponent (posJ a 2)
  let z : ℚ := positiveSmallExponentUpper a 2
  let d : ℚ := (1139 / 1000 : ℚ) * (posSmallCutoff a : ℚ)
  let C : ℚ :=
    (29 / 4 : ℚ) * (posNhi a : ℚ) *
      ((5 : ℚ) * (posNhi a : ℚ) - 72) * 50
  let target : ℚ := 9360 / C
  have hNge15 : 15 ≤ posNhi a := by
    unfold posNhi
    omega
  have hNge15Q : (15 : ℚ) ≤ (posNhi a : ℚ) := by
    exact_mod_cast hNge15
  have hlinear_pos :
      0 < (5 : ℚ) * (posNhi a : ℚ) - 72 := by
    nlinarith
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  have hCnonneg : 0 ≤ C := hCpos.le
  have hy0 : 0 ≤ y := by
    dsimp [y]
    unfold positiveSoloYExponent
    positivity
  have hy_lt_a : y < (a : ℚ) := by
    have haQ : (3000 : ℚ) ≤ (a : ℚ) := by
      exact_mod_cast ha
    have hj_le : (posJ a 2 : ℚ) ≤ (a : ℚ) := by
      exact_mod_cast Nat.sub_le a 2
    dsimp [y]
    unfold positiveSoloYExponent
    nlinarith
  have hcutoff_a_le : a ≤ 8 * posJ a 2 := by
    unfold posJ
    omega
  have hcutoff :
      partialExpUpper y (8 * posJ a 2) ≤ partialExpUpper y a :=
    partialExpUpper_cutoff_le_of_le hcutoff_a_le hy0 hy_lt_a
  have hk : 2 ∈ positiveKRange a := by
    refine mem_positiveKRange.mpr ⟨by omega, ?_⟩
    unfold posKmax
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 10)]
    omega
  have hz_lt_a : z < (a : ℚ) := by
    dsimp [z]
    exact positiveSmallExponentUpper_lt_largeExpCutoff
      (by omega : 2000 < a) hk
  have hd0 : 0 ≤ d := by
    dsimp [d]
    positivity
  have hdrop : y + d ≤ z := by
    have hjposNat : 0 < posJ a 2 := by
      unfold posJ
      omega
    have hjposQ : (0 : ℚ) < (posJ a 2 : ℚ) := by
      exact_mod_cast hjposNat
    have hj_le : (posJ a 2 : ℚ) ≤ (a : ℚ) := by
      exact_mod_cast Nat.sub_le a 2
    have hratio : 1 ≤ (a : ℚ) / (posJ a 2 : ℚ) := by
      rw [le_div_iff₀ hjposQ]
      simpa using hj_le
    dsimp [y, z, d]
    unfold positiveSoloYExponent positiveSmallExponentUpper
    nlinarith
  have hN_le_s_sq :
      (posNhi a : ℚ) ≤ (posSmallCutoff a : ℚ)^2 := by
    have hnat : posNhi a ≤ posSmallCutoff a * posSmallCutoff a := by
      unfold posSmallCutoff
      exact le_ceilSqrt_sq (posNhi a)
    simpa [pow_two] using (show (posNhi a : ℚ) ≤
      (posSmallCutoff a : ℚ) * (posSmallCutoff a : ℚ) by
        exact_mod_cast hnat)
  have hN_sq_le_s_four :
      (posNhi a : ℚ)^2 ≤ (posSmallCutoff a : ℚ)^4 := by
    have hNnonneg : 0 ≤ (posNhi a : ℚ) := by positivity
    have hsSqNonneg : 0 ≤ (posSmallCutoff a : ℚ)^2 := sq_nonneg _
    calc
      (posNhi a : ℚ)^2
          ≤ (posSmallCutoff a : ℚ)^2 * (posNhi a : ℚ) :=
            by
              simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using
                mul_le_mul_of_nonneg_right hN_le_s_sq hNnonneg
      _ ≤ (posSmallCutoff a : ℚ)^2 * (posSmallCutoff a : ℚ)^2 :=
            mul_le_mul_of_nonneg_left hN_le_s_sq hsSqNonneg
      _ = (posSmallCutoff a : ℚ)^4 := by ring
  have hC_le_quad :
      C ≤ (3625 / 2 : ℚ) * (posNhi a : ℚ)^2 := by
    have hlinear :
        (5 : ℚ) * (posNhi a : ℚ) - 72
          ≤ (5 : ℚ) * (posNhi a : ℚ) := by
      linarith
    have hscale : 0 ≤ (29 / 4 : ℚ) * (posNhi a : ℚ) * 50 := by
      positivity
    dsimp [C]
    calc
      (29 / 4 : ℚ) * (posNhi a : ℚ) *
          ((5 : ℚ) * (posNhi a : ℚ) - 72) * 50
          ≤ (29 / 4 : ℚ) * (posNhi a : ℚ) *
              ((5 : ℚ) * (posNhi a : ℚ)) * 50 :=
            by
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                mul_le_mul_of_nonneg_left hlinear hscale
      _ = (3625 / 2 : ℚ) * (posNhi a : ℚ)^2 := by ring
  have hcutoff_ge100 : (100 : Nat) ≤ posSmallCutoff a := by
    unfold posSmallCutoff
    have hlt : 99 < ceilSqrt (posNhi a) :=
      lt_ceilSqrt_of_sq_lt (by
        unfold posNhi
        omega)
    omega
  have hhundred_sq_le_s_sq :
      (100 : ℚ)^2 ≤ (posSmallCutoff a : ℚ)^2 := by
    have h100 : (0 : ℚ) ≤ 100 := by norm_num
    have hle : (100 : ℚ) ≤ (posSmallCutoff a : ℚ) := by
      exact_mod_cast hcutoff_ge100
    exact pow_le_pow_left₀ h100 hle 2
  have hquad_le_gap :
      (3625 / 2 : ℚ) * (posNhi a : ℚ)^2
        ≤ 9360 * (d / 6)^6 := by
    let s : ℚ := (posSmallCutoff a : ℚ)
    let A : ℚ := 9360 * (1139 / 6000 : ℚ)^6
    have hcoeff :
        (3625 / 2 : ℚ) ≤ A * (100 : ℚ)^2 := by
      dsimp [A]
      norm_num
    have hN2nonneg : 0 ≤ (posNhi a : ℚ)^2 := sq_nonneg _
    have hs4nonneg : 0 ≤ s^4 := by
      dsimp [s]
      positivity
    have hstep1 :
        (3625 / 2 : ℚ) * (posNhi a : ℚ)^2
          ≤ (3625 / 2 : ℚ) * s^4 := by
      dsimp [s]
      exact mul_le_mul_of_nonneg_left hN_sq_le_s_four (by norm_num)
    have hstep2 :
        (3625 / 2 : ℚ) * s^4 ≤ (A * (100 : ℚ)^2) * s^4 :=
      mul_le_mul_of_nonneg_right hcoeff hs4nonneg
    have hstep3 :
        (A * (100 : ℚ)^2) * s^4 ≤ A * s^6 := by
      have hA_nonneg : 0 ≤ A := by
        dsimp [A]
        positivity
      have hs2 :
          (100 : ℚ)^2 ≤ s^2 := by
        dsimp [s]
        exact hhundred_sq_le_s_sq
      have hs4_nonneg : 0 ≤ s^4 := by positivity
      have hmul :
          (100 : ℚ)^2 * s^4 ≤ s^2 * s^4 :=
        mul_le_mul_of_nonneg_right hs2 hs4_nonneg
      calc
        (A * (100 : ℚ)^2) * s^4
            = A * ((100 : ℚ)^2 * s^4) := by ring
        _ ≤ A * (s^2 * s^4) :=
            mul_le_mul_of_nonneg_left hmul hA_nonneg
        _ = A * s^6 := by ring
    calc
      (3625 / 2 : ℚ) * (posNhi a : ℚ)^2
          ≤ (3625 / 2 : ℚ) * s^4 := hstep1
      _ ≤ (A * (100 : ℚ)^2) * s^4 := hstep2
      _ ≤ A * s^6 := hstep3
      _ = 9360 * (d / 6)^6 := by
            dsimp [A, s, d]
            ring
  have hgap_le_shift :
      9360 * (d / 6)^6 ≤ 9360 * (1 + d / 6)^6 := by
    have hbase0 : 0 ≤ d / 6 := by positivity
    have hbase : d / 6 ≤ 1 + d / 6 := by linarith
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hbase0 hbase 6) (by norm_num)
  have hpoly : C ≤ 9360 * (1 + d / 6)^6 :=
    hC_le_quad.trans (hquad_le_gap.trans hgap_le_shift)
  have hbudget :
      1 ≤ target * (1 + d / 6)^6 := by
    have hrewrite :
        target * (1 + d / 6)^6 =
          (9360 * (1 + d / 6)^6) / C := by
      dsimp [target]
      ring
    rw [hrewrite]
    rw [le_div_iff₀ hCpos]
    nlinarith
  have hshift :
      partialExpUpper y a ≤ target * partialExpUpper z a :=
    partialExpUpper_le_mul_of_six_step_shift
      (y := y) (z := z) (d₀ := d) (target := target) (T := a)
      hy0 hd0 (by omega : 1 ≤ a) hz_lt_a hdrop hbudget
  have hexp :
      partialExpUpper y (8 * posJ a 2)
        ≤ target * partialExpUpper z a :=
    hcutoff.trans hshift
  calc
    (29 / 4 : ℚ) * (posNhi a : ℚ) *
        ((5 : ℚ) * (posNhi a : ℚ) - 72) * 50 *
        partialExpUpper y (8 * posJ a 2)
        = C * partialExpUpper y (8 * posJ a 2) := by
          dsimp [C]
    _ ≤ C * (target * partialExpUpper z a) :=
          mul_le_mul_of_nonneg_left hexp hCnonneg
    _ = 9360 * partialExpUpper z a := by
          dsimp [target]
          field_simp [hCpos.ne']

/-- First-cell budget from a shifted solo fast bound checked only at the
shifted index's own upper edge.

The extra factor `50` is supplied by
`positiveLargeTailSoloGcompClosedFactorialSplitBlockSum_productEdge_le_fifty_shiftedUpperEdge`.
This is the narrower completion target for the product first cell: prove the
ordinary solo-style upper-edge theorem at `j = a - 2`, then discharge the
separate scalar comparison with the fixed factor included. -/
theorem positiveSmallFirstCellYUpperEdgeBudget_of_shiftedSoloOwnEdgeFastCleared
    {a : Nat} (ha : 3000 ≤ a)
    (hsolo :
      positiveLargeTailSoloGcompClosedFactorialSplitBlockSumFastCleared
        (posJ a 2) (posNhi (posJ a 2)))
    (hbudget : positiveSmallFirstCellShiftedSoloFiftyFastExpBudget a) :
    positiveSmallFirstCellYUpperEdgeBudget a := by
  unfold positiveSmallFirstCellYUpperEdgeBudget positiveSmallFirstCellQBudget
  rw [positiveLargeTailProductYUpperEdgeExactBound_two_eq_shiftedSolo]
  have hscaleEdge :=
    positiveLargeTailSoloGcompClosedFactorialSplitBlockSum_productEdge_le_fifty_shiftedUpperEdge
      (a := a) ha
  unfold positiveLargeTailSoloGcompClosedFactorialSplitBlockSumFastCleared
    at hsolo
  have hhi15 : 15 ≤ posNhi a := by
    unfold posNhi
    omega
  have hhi15Q : (15 : ℚ) ≤ (posNhi a : ℚ) := by
    exact_mod_cast hhi15
  have hlinear_nonneg :
      0 ≤ (5 : ℚ) * (posNhi a : ℚ) - 72 := by
    nlinarith
  have hscale_nonneg :
      0 ≤ ((posNhi a : ℚ) *
        ((5 : ℚ) * (posNhi a : ℚ) - 72) / 4) := by
    positivity
  have hpow_nonneg : 0 ≤ (4 : ℚ) * (2 : ℚ)^(posJ a 2) := by
    positivity
  have hscaledBlock :
      (4 : ℚ) * (2 : ℚ)^(posJ a 2) *
          positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
            (posJ a 2) (posNhi a)
        ≤
      (50 : ℚ) *
        ((4 : ℚ) * (2 : ℚ)^(posJ a 2) *
          positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
            (posJ a 2) (posNhi (posJ a 2))) := by
    calc
      (4 : ℚ) * (2 : ℚ)^(posJ a 2) *
          positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
            (posJ a 2) (posNhi a)
          ≤
        (4 : ℚ) * (2 : ℚ)^(posJ a 2) *
          ((50 : ℚ) *
            positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
              (posJ a 2) (posNhi (posJ a 2))) := by
          simpa [mul_assoc] using
            mul_le_mul_of_nonneg_left hscaleEdge hpow_nonneg
      _ =
        (50 : ℚ) *
          ((4 : ℚ) * (2 : ℚ)^(posJ a 2) *
            positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
              (posJ a 2) (posNhi (posJ a 2))) := by
          ring
  have hsoloScaled :
      (50 : ℚ) *
        ((4 : ℚ) * (2 : ℚ)^(posJ a 2) *
          positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
            (posJ a 2) (posNhi (posJ a 2)))
        ≤
      (50 : ℚ) *
        (29 * (posJ a 2 : ℚ) * c (posJ a 2) *
          partialExpUpperFast (positiveSoloYExponent (posJ a 2))
            (8 * posJ a 2)) :=
    mul_le_mul_of_nonneg_left hsolo (by norm_num)
  have hscaledSolo :
      ((posNhi a : ℚ) *
          ((5 : ℚ) * (posNhi a : ℚ) - 72) / 4) *
        ((4 : ℚ) * (2 : ℚ)^(posJ a 2) *
          positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
            (posJ a 2) (posNhi a))
        ≤
      ((posNhi a : ℚ) *
          ((5 : ℚ) * (posNhi a : ℚ) - 72) / 4) *
        ((50 : ℚ) *
          (29 * (posJ a 2 : ℚ) * c (posJ a 2) *
            partialExpUpperFast (positiveSoloYExponent (posJ a 2))
              (8 * posJ a 2))) :=
    mul_le_mul_of_nonneg_left (hscaledBlock.trans hsoloScaled)
      hscale_nonneg
  have hjc_nonneg : 0 ≤ (posJ a 2 : ℚ) * c (posJ a 2) :=
    mul_nonneg (Nat.cast_nonneg _) (c_nonneg (posJ a 2))
  have hbudgetScaled :
      ((posJ a 2 : ℚ) * c (posJ a 2)) *
        ((29 / 4 : ℚ) * (posNhi a : ℚ) *
          ((5 : ℚ) * (posNhi a : ℚ) - 72) * 50 *
            partialExpUpperFast (positiveSoloYExponent (posJ a 2))
              (8 * posJ a 2))
        ≤
      ((posJ a 2 : ℚ) * c (posJ a 2)) *
        (9360 * positiveSmallLargeExp a 2) :=
    mul_le_mul_of_nonneg_left hbudget hjc_nonneg
  calc
    (2 : ℚ)^(posJ a 2) * (posNhi a : ℚ) *
          (5 * (posNhi a : ℚ) - 72) *
          positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
            (posJ a 2) (posNhi a)
        =
      ((posNhi a : ℚ) *
          ((5 : ℚ) * (posNhi a : ℚ) - 72) / 4) *
        ((4 : ℚ) * (2 : ℚ)^(posJ a 2) *
          positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
            (posJ a 2) (posNhi a)) := by
        ring
    _ ≤
      ((posNhi a : ℚ) *
          ((5 : ℚ) * (posNhi a : ℚ) - 72) / 4) *
        ((50 : ℚ) *
          (29 * (posJ a 2 : ℚ) * c (posJ a 2) *
            partialExpUpperFast (positiveSoloYExponent (posJ a 2))
              (8 * posJ a 2))) := hscaledSolo
    _ =
      ((posJ a 2 : ℚ) * c (posJ a 2)) *
        ((29 / 4 : ℚ) * (posNhi a : ℚ) *
          ((5 : ℚ) * (posNhi a : ℚ) - 72) * 50 *
            partialExpUpperFast (positiveSoloYExponent (posJ a 2))
              (8 * posJ a 2)) := by
        ring
    _ ≤
      ((posJ a 2 : ℚ) * c (posJ a 2)) *
        (9360 * positiveSmallLargeExp a 2) := hbudgetScaled
    _ =
      9360 * (posJ a 2 : ℚ) *
        positiveSmallLargeExp a 2 * c (posJ a 2) := by
        ring

/-- Large-`a` first-cell budget after the scalar comparison has been closed.

The only remaining first-cell analytic input is now the shifted solo-style
split-sum bound at `j = a - 2`, `N = posNhi a`. -/
theorem positiveSmallFirstCellYUpperEdgeBudget_of_shiftedSoloFastCleared_large
    {a : Nat} (ha : 3000 ≤ a)
    (hsolo :
      positiveLargeTailSoloGcompClosedFactorialSplitBlockSumFastCleared
        (posJ a 2) (posNhi a)) :
    positiveSmallFirstCellYUpperEdgeBudget a :=
  positiveSmallFirstCellYUpperEdgeBudget_of_shiftedSoloFastCleared
    (by omega : 2000 < a) hsolo
    (positiveSmallFirstCellShiftedSoloFastExpBudget_of_large ha)

/-- The direct first-cell budget using the actual `Qq` coefficient. -/
def positiveSmallFirstCellRawQBudget (a N : Nat) : Prop :=
  positiveSmallFirstCellQBudget a N (Qq N (posJ a 2))

/-- Degree-two closed form for the product-side `X` upper-edge split sum.

This is deliberately an upper majorant, not the actual signed `Bq N 2`
coefficient.  The Lean product route uses it only to recover the direct
first-cell `Qq` budget from the stronger exact upper-edge product scalar
when a legacy product scalar package is supplied. -/
theorem positiveLargeTailProductXClosedFactorialSplitBlockBound_two
    (a N : Nat) :
    positiveLargeTailProductXClosedFactorialSplitBlockBound a N 2 =
      (N : ℚ) * (144 / 25) + (N : ℚ)^2 * (25 / 72) := by
  unfold positiveLargeTailProductXClosedFactorialSplitBlockBound
  rw [positiveLargeTailXGcompClosedFactorialSplitBlockSum_eq_Icc]
  norm_num [positiveLargeTailXGcompClosedFactorialSplitBlockSum,
    Finset.sum_range_succ, c_one, c_two]
  ring_nf

/-- Degree-three closed form for the product-side `X` upper-edge split sum.

This is the first genuine tail cell after the closed `k = 2` first-cell
envelope.  The planned `k = 3` product peel uses this polynomial factor with
the same shifted solo-style estimate for the `Y` side; keeping the closed form
named prevents the proof from repeatedly unfolding the double split sum. -/
theorem positiveLargeTailProductXClosedFactorialSplitBlockBound_three
    (a N : Nat) :
    positiveLargeTailProductXClosedFactorialSplitBlockBound a N 3 =
      (N : ℚ) * (1728 / 25) + (N : ℚ)^2 * (24 / 5) +
        (N : ℚ)^3 * (125 / 1296) := by
  unfold positiveLargeTailProductXClosedFactorialSplitBlockBound
  rw [positiveLargeTailXGcompClosedFactorialSplitBlockSum_eq_Icc]
  norm_num [positiveLargeTailXGcompClosedFactorialSplitBlockSum,
    Finset.sum_range_succ, c_one]
  norm_num [Nat.factorial]
  ring_nf

/-- Scalar comparison left after proving the `k = 3` shifted `Y` block by
the fast solo-style exponential envelope.

This is the exact analogue of
`positiveSmallFirstCellShiftedSoloFastExpBudget`, with the degree-three `X`
factor left explicit.  The closed form
`positiveLargeTailProductXClosedFactorialSplitBlockBound_three` is intended
for the subsequent one-dimensional proof of this budget. -/
def positiveSmallThirdCellShiftedSoloFastExpBudget (a : Nat) : Prop :=
  (29 / 2 : ℚ) * (posNhi a : ℚ) *
      positiveLargeTailProductXUpperEdgeExactBound a 3 *
        partialExpUpperFast (positiveSoloYExponent (posJ a 3))
          (8 * posJ a 3)
    ≤ 390 * positiveSmallLargeExpFast a 3 *
      ((posNlo a : ℚ) * c 3)

/-- Strengthened third-cell scalar comparison with the fixed `50` paid for
the product-edge to own-edge shift of the shifted solo `Y` block. -/
def positiveSmallThirdCellShiftedSoloFiftyFastExpBudget (a : Nat) : Prop :=
  (29 / 2 : ℚ) * (posNhi a : ℚ) *
      positiveLargeTailProductXUpperEdgeExactBound a 3 * 50 *
        partialExpUpperFast (positiveSoloYExponent (posJ a 3))
          (8 * posJ a 3)
    ≤ 390 * positiveSmallLargeExpFast a 3 *
      ((posNlo a : ℚ) * c 3)

/-- The degree-three `X` upper-edge factor is bounded by a deliberately
coarse cubic once `a ≥ 3000`.

This is the numerical core behind the `k = 3` scalar peel: the exact closed
form has leading coefficient `125/1296 < 1/10`, and the lower-degree terms are
negligible at the large-tail threshold. -/
theorem positiveLargeTailProductXUpperEdgeExactBound_three_le_cubic
    {a : Nat} (ha : 3000 ≤ a) :
    positiveLargeTailProductXUpperEdgeExactBound a 3
      ≤ (1 / 10 : ℚ) * (posNhi a : ℚ)^3 := by
  unfold positiveLargeTailProductXUpperEdgeExactBound
  rw [positiveLargeTailProductXClosedFactorialSplitBlockBound_three]
  have hNge : (2000 : ℚ) ≤ (posNhi a : ℚ) := by
    have hNgeNat : 2000 ≤ posNhi a := by
      unfold posNhi
      omega
    exact_mod_cast hNgeNat
  have hNnonneg : (0 : ℚ) ≤ (posNhi a : ℚ) := by positivity
  nlinarith [sq_nonneg ((posNhi a : ℚ) - 2000)]

/-- Sharper cubic bound for the degree-three `X` upper-edge factor.

The previous `N^3/10` bound is intentionally roomy.  The own-edge third-cell
route needs the exact leading coefficient and the real `a = 3000` rectangle
size to pay the additional fixed edge-scaling factor. -/
theorem positiveLargeTailProductXUpperEdgeExactBound_three_le_sharp_cubic
    {a : Nat} (ha : 3000 ≤ a) :
    positiveLargeTailProductXUpperEdgeExactBound a 3
      ≤ (49 / 500 : ℚ) * (posNhi a : ℚ)^3 := by
  unfold positiveLargeTailProductXUpperEdgeExactBound
  rw [positiveLargeTailProductXClosedFactorialSplitBlockBound_three]
  let N : ℚ := (posNhi a : ℚ)
  have hNge : (30000 : ℚ) ≤ N := by
    have hNgeNat : 30000 ≤ posNhi a := by
      unfold posNhi
      omega
    have hNgeQ : (30000 : ℚ) ≤ (posNhi a : ℚ) := by
      exact_mod_cast hNgeNat
    simpa [N] using hNgeQ
  have hNnonneg : 0 ≤ N := by positivity
  have hquad :
      (1728 / 25 : ℚ) + (24 / 5 : ℚ) * N +
          (125 / 1296 : ℚ) * N^2
        ≤ (49 / 500 : ℚ) * N^2 := by
    nlinarith [sq_nonneg (N - 30000)]
  calc
    (posNhi a : ℚ) * (1728 / 25) +
        (posNhi a : ℚ)^2 * (24 / 5) +
          (posNhi a : ℚ)^3 * (125 / 1296)
        =
      N * ((1728 / 25 : ℚ) + (24 / 5 : ℚ) * N +
        (125 / 1296 : ℚ) * N^2) := by
          dsimp [N]
          ring
    _ ≤ N * ((49 / 500 : ℚ) * N^2) :=
          mul_le_mul_of_nonneg_left hquad hNnonneg
    _ = (49 / 500 : ℚ) * (posNhi a : ℚ)^3 := by
          dsimp [N]
          ring

/-- The small-branch exponential at `k = 3` has enough endpoint slack to pay
for the exact cubic `X_3` factor and the shifted solo-style `Y` estimate.

This is the one-dimensional scalar comparison exposed by
`positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar_three_of_shiftedSoloFastCleared`.
The proof is intentionally coarse: after bounding `X_3` by `N^3/10`, the
square-root exponent gap pays the resulting quartic factor through the octic
`partialExpUpper` shift. -/
theorem positiveSmallThirdCellShiftedSoloFastExpBudget_of_large
    {a : Nat} (ha : 3000 ≤ a) :
    positiveSmallThirdCellShiftedSoloFastExpBudget a := by
  unfold positiveSmallThirdCellShiftedSoloFastExpBudget
  rw [positiveSmallLargeExpFast_eq]
  unfold positiveSmallLargeExp
  rw [partialExpUpperFast_eq]
  let y : ℚ := positiveSoloYExponent (posJ a 3)
  let z : ℚ := positiveSmallExponentUpper a 3
  let d : ℚ := (1139 / 1000 : ℚ) * (posSmallCutoff a : ℚ)
  let C : ℚ :=
    (29 / 2 : ℚ) * (posNhi a : ℚ) *
      positiveLargeTailProductXUpperEdgeExactBound a 3
  let R : ℚ := 390 * (posNlo a : ℚ) * c 3
  let target : ℚ := R / C
  have hNhi_pos : (0 : ℚ) < (posNhi a : ℚ) := by
    exact_mod_cast posNhi_pos (by omega : 1 ≤ a)
  have hNlo_pos : (0 : ℚ) < (posNlo a : ℚ) := by
    exact_mod_cast posNlo_pos (by omega : 2 ≤ a)
  have hXpos :
      0 < positiveLargeTailProductXUpperEdgeExactBound a 3 := by
    unfold positiveLargeTailProductXUpperEdgeExactBound
    rw [positiveLargeTailProductXClosedFactorialSplitBlockBound_three]
    positivity
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  have hCnonneg : 0 ≤ C := hCpos.le
  have hc3_lb : (60 : ℚ) ≤ c 3 := by
    have h := c_lb 3 (by norm_num : 1 ≤ 3)
    norm_num at h
    exact h
  have hc3_nonneg : 0 ≤ c 3 :=
    (by norm_num : (0 : ℚ) ≤ 60).trans hc3_lb
  have hRnonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have hy0 : 0 ≤ y := by
    dsimp [y]
    unfold positiveSoloYExponent
    positivity
  have hy_lt_a : y < (a : ℚ) := by
    have haQ : (3000 : ℚ) ≤ (a : ℚ) := by
      exact_mod_cast ha
    have hj_le : (posJ a 3 : ℚ) ≤ (a : ℚ) := by
      exact_mod_cast Nat.sub_le a 3
    dsimp [y]
    unfold positiveSoloYExponent
    nlinarith
  have hcutoff_a_le : a ≤ 8 * posJ a 3 := by
    unfold posJ
    omega
  have hcutoff :
      partialExpUpper y (8 * posJ a 3) ≤ partialExpUpper y a :=
    partialExpUpper_cutoff_le_of_le hcutoff_a_le hy0 hy_lt_a
  have hk : 3 ∈ positiveKRange a := by
    refine mem_positiveKRange.mpr ⟨by omega, ?_⟩
    unfold posKmax
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 10)]
    omega
  have hz_lt_a : z < (a : ℚ) := by
    dsimp [z]
    exact positiveSmallExponentUpper_lt_largeExpCutoff
      (by omega : 2000 < a) hk
  have hd0 : 0 ≤ d := by
    dsimp [d]
    positivity
  have hdrop : y + d ≤ z := by
    have hjposNat : 0 < posJ a 3 := by
      unfold posJ
      omega
    have hjposQ : (0 : ℚ) < (posJ a 3 : ℚ) := by
      exact_mod_cast hjposNat
    have hj_le : (posJ a 3 : ℚ) ≤ (a : ℚ) := by
      exact_mod_cast Nat.sub_le a 3
    have hratio : 1 ≤ (a : ℚ) / (posJ a 3 : ℚ) := by
      rw [le_div_iff₀ hjposQ]
      simpa using hj_le
    dsimp [y, z, d]
    unfold positiveSoloYExponent positiveSmallExponentUpper
    nlinarith
  have hN_le_s_sq :
      (posNhi a : ℚ) ≤ (posSmallCutoff a : ℚ)^2 := by
    have hnat : posNhi a ≤ posSmallCutoff a * posSmallCutoff a := by
      unfold posSmallCutoff
      exact le_ceilSqrt_sq (posNhi a)
    simpa [pow_two] using (show (posNhi a : ℚ) ≤
      (posSmallCutoff a : ℚ) * (posSmallCutoff a : ℚ) by
        exact_mod_cast hnat)
  have hN_four_le_s_eight :
      (posNhi a : ℚ)^4 ≤ (posSmallCutoff a : ℚ)^8 := by
    have hNnonneg : 0 ≤ (posNhi a : ℚ) := hNhi_pos.le
    calc
      (posNhi a : ℚ)^4
          ≤ ((posSmallCutoff a : ℚ)^2)^4 :=
            pow_le_pow_left₀ hNnonneg hN_le_s_sq 4
      _ = (posSmallCutoff a : ℚ)^8 := by ring
  have hC_le_quartic :
      C ≤ (29 / 20 : ℚ) * (posNhi a : ℚ)^4 := by
    have hX :=
      positiveLargeTailProductXUpperEdgeExactBound_three_le_cubic
        (a := a) ha
    have hscale : 0 ≤ (29 / 2 : ℚ) * (posNhi a : ℚ) := by
      positivity
    dsimp [C]
    calc
      (29 / 2 : ℚ) * (posNhi a : ℚ) *
          positiveLargeTailProductXUpperEdgeExactBound a 3
          ≤ (29 / 2 : ℚ) * (posNhi a : ℚ) *
              ((1 / 10 : ℚ) * (posNhi a : ℚ)^3) :=
            mul_le_mul_of_nonneg_left hX hscale
      _ = (29 / 20 : ℚ) * (posNhi a : ℚ)^4 := by ring
  have hNlo_ge : (10000 : ℚ) ≤ (posNlo a : ℚ) := by
    have hNlo_geNat : 10000 ≤ posNlo a := by
      unfold posNlo
      omega
    exact_mod_cast hNlo_geNat
  have hcoeff :
      (29 / 20 : ℚ)
        ≤ 390 * 10000 * 60 * (1139 / 8000 : ℚ)^8 := by
    norm_num
  have hcoeff_to_R :
      390 * 10000 * 60 * (1139 / 8000 : ℚ)^8
        ≤ R * (1139 / 8000 : ℚ)^8 := by
    dsimp [R]
    nlinarith
  have hcoeff_R :
      (29 / 20 : ℚ) ≤ R * (1139 / 8000 : ℚ)^8 :=
    hcoeff.trans hcoeff_to_R
  have hs8_nonneg : 0 ≤ (posSmallCutoff a : ℚ)^8 := by positivity
  have hquartic_le_gap :
      (29 / 20 : ℚ) * (posNhi a : ℚ)^4
        ≤ R * (d / 8)^8 := by
    calc
      (29 / 20 : ℚ) * (posNhi a : ℚ)^4
          ≤ (29 / 20 : ℚ) * (posSmallCutoff a : ℚ)^8 :=
            mul_le_mul_of_nonneg_left hN_four_le_s_eight
              (by norm_num : (0 : ℚ) ≤ 29 / 20)
      _ ≤ (R * (1139 / 8000 : ℚ)^8) *
            (posSmallCutoff a : ℚ)^8 :=
            mul_le_mul_of_nonneg_right hcoeff_R hs8_nonneg
      _ = R * (d / 8)^8 := by
            dsimp [d]
            ring
  have hgap_le_shift :
      R * (d / 8)^8 ≤ R * (1 + d / 8)^8 := by
    have hbase0 : 0 ≤ d / 8 := by positivity
    have hbase : d / 8 ≤ 1 + d / 8 := by linarith
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hbase0 hbase 8) hRnonneg
  have hpoly : C ≤ R * (1 + d / 8)^8 :=
    hC_le_quartic.trans (hquartic_le_gap.trans hgap_le_shift)
  have hbudget :
      1 ≤ target * (1 + d / 8)^8 := by
    have hrewrite :
        target * (1 + d / 8)^8 =
          (R * (1 + d / 8)^8) / C := by
      dsimp [target]
      ring
    rw [hrewrite]
    rw [le_div_iff₀ hCpos]
    nlinarith
  have hshift :
      partialExpUpper y a ≤ target * partialExpUpper z a :=
    partialExpUpper_le_mul_of_eight_step_shift
      (y := y) (z := z) (d₀ := d) (target := target) (T := a)
      hy0 hd0 (by omega : 1 ≤ a) hz_lt_a hdrop hbudget
  have hexp :
      partialExpUpper y (8 * posJ a 3)
        ≤ target * partialExpUpper z a :=
    hcutoff.trans hshift
  calc
    (29 / 2 : ℚ) * (posNhi a : ℚ) *
        positiveLargeTailProductXUpperEdgeExactBound a 3 *
        partialExpUpper y (8 * posJ a 3)
        = C * partialExpUpper y (8 * posJ a 3) := by
          dsimp [C]
    _ ≤ C * (target * partialExpUpper z a) :=
          mul_le_mul_of_nonneg_left hexp hCnonneg
    _ = 390 * partialExpUpper z a *
          ((posNlo a : ℚ) * c 3) := by
          dsimp [target, R]
          field_simp [hCpos.ne']

/-- The third-cell scalar budget has enough slack to pay the fixed `50`
edge-shift factor once the exact degree-three `X` coefficient and the true
large-tail lower rectangle edge are used.

This is deliberately still a one-dimensional estimate; the only change from
`positiveSmallThirdCellShiftedSoloFastExpBudget_of_large` is that the edge
shift is paid in the scalar budget instead of being exposed as a separate
product-edge solo assumption. -/
theorem positiveSmallThirdCellShiftedSoloFiftyFastExpBudget_of_large
    {a : Nat} (ha : 3000 ≤ a) :
    positiveSmallThirdCellShiftedSoloFiftyFastExpBudget a := by
  unfold positiveSmallThirdCellShiftedSoloFiftyFastExpBudget
  rw [positiveSmallLargeExpFast_eq]
  unfold positiveSmallLargeExp
  rw [partialExpUpperFast_eq]
  let y : ℚ := positiveSoloYExponent (posJ a 3)
  let z : ℚ := positiveSmallExponentUpper a 3
  let d : ℚ := (1139 / 1000 : ℚ) * (posSmallCutoff a : ℚ)
  let C : ℚ :=
    (29 / 2 : ℚ) * (posNhi a : ℚ) *
      positiveLargeTailProductXUpperEdgeExactBound a 3 * 50
  let R : ℚ := 390 * (posNlo a : ℚ) * c 3
  let target : ℚ := R / C
  have hNhi_pos : (0 : ℚ) < (posNhi a : ℚ) := by
    exact_mod_cast posNhi_pos (by omega : 1 ≤ a)
  have hNlo_pos : (0 : ℚ) < (posNlo a : ℚ) := by
    exact_mod_cast posNlo_pos (by omega : 2 ≤ a)
  have hXpos :
      0 < positiveLargeTailProductXUpperEdgeExactBound a 3 := by
    unfold positiveLargeTailProductXUpperEdgeExactBound
    rw [positiveLargeTailProductXClosedFactorialSplitBlockBound_three]
    positivity
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  have hCnonneg : 0 ≤ C := hCpos.le
  have hc3_lb : (60 : ℚ) ≤ c 3 := by
    have h := c_lb 3 (by norm_num : 1 ≤ 3)
    norm_num at h
    exact h
  have hc3_nonneg : 0 ≤ c 3 :=
    (by norm_num : (0 : ℚ) ≤ 60).trans hc3_lb
  have hRnonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have hy0 : 0 ≤ y := by
    dsimp [y]
    unfold positiveSoloYExponent
    positivity
  have hy_lt_a : y < (a : ℚ) := by
    have haQ : (3000 : ℚ) ≤ (a : ℚ) := by
      exact_mod_cast ha
    have hj_le : (posJ a 3 : ℚ) ≤ (a : ℚ) := by
      exact_mod_cast Nat.sub_le a 3
    dsimp [y]
    unfold positiveSoloYExponent
    nlinarith
  have hcutoff_a_le : a ≤ 8 * posJ a 3 := by
    unfold posJ
    omega
  have hcutoff :
      partialExpUpper y (8 * posJ a 3) ≤ partialExpUpper y a :=
    partialExpUpper_cutoff_le_of_le hcutoff_a_le hy0 hy_lt_a
  have hk : 3 ∈ positiveKRange a := by
    refine mem_positiveKRange.mpr ⟨by omega, ?_⟩
    unfold posKmax
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 10)]
    omega
  have hz_lt_a : z < (a : ℚ) := by
    dsimp [z]
    exact positiveSmallExponentUpper_lt_largeExpCutoff
      (by omega : 2000 < a) hk
  have hd0 : 0 ≤ d := by
    dsimp [d]
    positivity
  have hdrop : y + d ≤ z := by
    have hjposNat : 0 < posJ a 3 := by
      unfold posJ
      omega
    have hjposQ : (0 : ℚ) < (posJ a 3 : ℚ) := by
      exact_mod_cast hjposNat
    have hj_le : (posJ a 3 : ℚ) ≤ (a : ℚ) := by
      exact_mod_cast Nat.sub_le a 3
    have hratio : 1 ≤ (a : ℚ) / (posJ a 3 : ℚ) := by
      rw [le_div_iff₀ hjposQ]
      simpa using hj_le
    dsimp [y, z, d]
    unfold positiveSoloYExponent positiveSmallExponentUpper
    nlinarith
  have hN_le_s_sq :
      (posNhi a : ℚ) ≤ (posSmallCutoff a : ℚ)^2 := by
    have hnat : posNhi a ≤ posSmallCutoff a * posSmallCutoff a := by
      unfold posSmallCutoff
      exact le_ceilSqrt_sq (posNhi a)
    simpa [pow_two] using (show (posNhi a : ℚ) ≤
      (posSmallCutoff a : ℚ) * (posSmallCutoff a : ℚ) by
        exact_mod_cast hnat)
  have hN_four_le_s_eight :
      (posNhi a : ℚ)^4 ≤ (posSmallCutoff a : ℚ)^8 := by
    have hNnonneg : 0 ≤ (posNhi a : ℚ) := hNhi_pos.le
    calc
      (posNhi a : ℚ)^4
          ≤ ((posSmallCutoff a : ℚ)^2)^4 :=
            pow_le_pow_left₀ hNnonneg hN_le_s_sq 4
      _ = (posSmallCutoff a : ℚ)^8 := by ring
  have hC_le_quartic :
      C ≤ (1421 / 20 : ℚ) * (posNhi a : ℚ)^4 := by
    have hX :=
      positiveLargeTailProductXUpperEdgeExactBound_three_le_sharp_cubic
        (a := a) ha
    have hscale : 0 ≤ (29 / 2 : ℚ) * (posNhi a : ℚ) * 50 := by
      positivity
    dsimp [C]
    calc
      (29 / 2 : ℚ) * (posNhi a : ℚ) *
          positiveLargeTailProductXUpperEdgeExactBound a 3 * 50
          =
        ((29 / 2 : ℚ) * (posNhi a : ℚ) * 50) *
          positiveLargeTailProductXUpperEdgeExactBound a 3 := by
            ring
      _ ≤ ((29 / 2 : ℚ) * (posNhi a : ℚ) * 50) *
              ((49 / 500 : ℚ) * (posNhi a : ℚ)^3) :=
            mul_le_mul_of_nonneg_left hX hscale
      _ = (1421 / 20 : ℚ) * (posNhi a : ℚ)^4 := by ring
  have hNlo_ge : (17992 : ℚ) ≤ (posNlo a : ℚ) := by
    have hNlo_geNat : 17992 ≤ posNlo a := by
      unfold posNlo
      omega
    exact_mod_cast hNlo_geNat
  have hcoeff :
      (1421 / 20 : ℚ)
        ≤ 390 * 17992 * 60 * (1139 / 8000 : ℚ)^8 := by
    norm_num
  have hcoeff_to_R :
      390 * 17992 * 60 * (1139 / 8000 : ℚ)^8
        ≤ R * (1139 / 8000 : ℚ)^8 := by
    dsimp [R]
    nlinarith
  have hcoeff_R :
      (1421 / 20 : ℚ) ≤ R * (1139 / 8000 : ℚ)^8 :=
    hcoeff.trans hcoeff_to_R
  have hs8_nonneg : 0 ≤ (posSmallCutoff a : ℚ)^8 := by positivity
  have hquartic_le_gap :
      (1421 / 20 : ℚ) * (posNhi a : ℚ)^4
        ≤ R * (d / 8)^8 := by
    calc
      (1421 / 20 : ℚ) * (posNhi a : ℚ)^4
          ≤ (1421 / 20 : ℚ) * (posSmallCutoff a : ℚ)^8 :=
            mul_le_mul_of_nonneg_left hN_four_le_s_eight
              (by norm_num : (0 : ℚ) ≤ 1421 / 20)
      _ ≤ (R * (1139 / 8000 : ℚ)^8) *
            (posSmallCutoff a : ℚ)^8 :=
            mul_le_mul_of_nonneg_right hcoeff_R hs8_nonneg
      _ = R * (d / 8)^8 := by
            dsimp [d]
            ring
  have hgap_le_shift :
      R * (d / 8)^8 ≤ R * (1 + d / 8)^8 := by
    have hbase0 : 0 ≤ d / 8 := by positivity
    have hbase : d / 8 ≤ 1 + d / 8 := by linarith
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hbase0 hbase 8) hRnonneg
  have hpoly : C ≤ R * (1 + d / 8)^8 :=
    hC_le_quartic.trans (hquartic_le_gap.trans hgap_le_shift)
  have hbudget :
      1 ≤ target * (1 + d / 8)^8 := by
    have hrewrite :
        target * (1 + d / 8)^8 =
          (R * (1 + d / 8)^8) / C := by
      dsimp [target]
      ring
    rw [hrewrite]
    rw [le_div_iff₀ hCpos]
    nlinarith
  have hshift :
      partialExpUpper y a ≤ target * partialExpUpper z a :=
    partialExpUpper_le_mul_of_eight_step_shift
      (y := y) (z := z) (d₀ := d) (target := target) (T := a)
      hy0 hd0 (by omega : 1 ≤ a) hz_lt_a hdrop hbudget
  have hexp :
      partialExpUpper y (8 * posJ a 3)
        ≤ target * partialExpUpper z a :=
    hcutoff.trans hshift
  calc
    (29 / 2 : ℚ) * (posNhi a : ℚ) *
        positiveLargeTailProductXUpperEdgeExactBound a 3 * 50 *
        partialExpUpper y (8 * posJ a 3)
        = C * partialExpUpper y (8 * posJ a 3) := by
          dsimp [C]
    _ ≤ C * (target * partialExpUpper z a) :=
          mul_le_mul_of_nonneg_left hexp hCnonneg
    _ = 390 * partialExpUpper z a *
          ((posNlo a : ℚ) * c 3) := by
          dsimp [target, R]
          field_simp [hCpos.ne']

/-- The `k = 3` small-branch product scalar follows from a shifted solo-style
fast bound for the `Y` factor and the remaining scalar budget above.

This peels the first genuine tail cell into the same two ingredients as the
closed `k = 2` first-cell proof: a shifted solo `Y` estimate and a
one-dimensional scalar comparison. -/
theorem positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar_three_of_shiftedSoloFastCleared
    {a : Nat}
    (hsolo :
      positiveLargeTailSoloGcompClosedFactorialSplitBlockSumFastCleared
        (posJ a 3) (posNhi a))
    (hbudget : positiveSmallThirdCellShiftedSoloFastExpBudget a) :
    positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
      (fun a k =>
        positiveLargeTailProductXUpperEdgeExactBound a k *
          positiveLargeTailProductYUpperEdgeExactBound a k) a 3 := by
  unfold positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
  change
    2 * (2 : ℚ)^(posJ a 3) * (posNhi a : ℚ) *
        (positiveLargeTailProductXUpperEdgeExactBound a 3 *
          positiveLargeTailProductYUpperEdgeExactBound a 3)
      ≤ 130 * ((3 : ℚ) * (posJ a 3 : ℚ)) *
        positiveSmallLargeExpFast a 3 *
          ((posNlo a : ℚ) * c 3 * c (posJ a 3))
  rw [positiveLargeTailProductYUpperEdgeExactBound_three_eq_shiftedSolo]
  unfold positiveLargeTailSoloGcompClosedFactorialSplitBlockSumFastCleared
    at hsolo
  unfold positiveSmallThirdCellShiftedSoloFastExpBudget at hbudget
  have hXnonneg :
      0 ≤ positiveLargeTailProductXUpperEdgeExactBound a 3 := by
    unfold positiveLargeTailProductXUpperEdgeExactBound
    exact positiveLargeTailProductXClosedFactorialSplitBlockBound_nonneg
      a (posNhi a) 3
  have hscale_nonneg :
      0 ≤
        ((posNhi a : ℚ) *
          positiveLargeTailProductXUpperEdgeExactBound a 3 / 2) := by
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) hXnonneg)
      (by norm_num : (0 : ℚ) ≤ 2)
  have hscaledSolo :
      ((posNhi a : ℚ) *
          positiveLargeTailProductXUpperEdgeExactBound a 3 / 2) *
        ((4 : ℚ) * (2 : ℚ)^(posJ a 3) *
          positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
            (posJ a 3) (posNhi a))
        ≤
      ((posNhi a : ℚ) *
          positiveLargeTailProductXUpperEdgeExactBound a 3 / 2) *
        (29 * (posJ a 3 : ℚ) * c (posJ a 3) *
          partialExpUpperFast (positiveSoloYExponent (posJ a 3))
            (8 * posJ a 3)) :=
    mul_le_mul_of_nonneg_left hsolo hscale_nonneg
  have hjc_nonneg : 0 ≤ (posJ a 3 : ℚ) * c (posJ a 3) :=
    mul_nonneg (Nat.cast_nonneg _) (c_nonneg (posJ a 3))
  have hbudgetScaled :
      ((posJ a 3 : ℚ) * c (posJ a 3)) *
        ((29 / 2 : ℚ) * (posNhi a : ℚ) *
          positiveLargeTailProductXUpperEdgeExactBound a 3 *
            partialExpUpperFast (positiveSoloYExponent (posJ a 3))
              (8 * posJ a 3))
        ≤
      ((posJ a 3 : ℚ) * c (posJ a 3)) *
        (390 * positiveSmallLargeExpFast a 3 *
          ((posNlo a : ℚ) * c 3)) :=
    mul_le_mul_of_nonneg_left hbudget hjc_nonneg
  calc
    2 * (2 : ℚ)^(posJ a 3) * (posNhi a : ℚ) *
        (positiveLargeTailProductXUpperEdgeExactBound a 3 *
          positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
            (posJ a 3) (posNhi a))
        =
      ((posNhi a : ℚ) *
          positiveLargeTailProductXUpperEdgeExactBound a 3 / 2) *
        ((4 : ℚ) * (2 : ℚ)^(posJ a 3) *
          positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
            (posJ a 3) (posNhi a)) := by
        ring
    _ ≤
      ((posNhi a : ℚ) *
          positiveLargeTailProductXUpperEdgeExactBound a 3 / 2) *
        (29 * (posJ a 3 : ℚ) * c (posJ a 3) *
          partialExpUpperFast (positiveSoloYExponent (posJ a 3))
            (8 * posJ a 3)) := hscaledSolo
    _ =
      ((posJ a 3 : ℚ) * c (posJ a 3)) *
        ((29 / 2 : ℚ) * (posNhi a : ℚ) *
          positiveLargeTailProductXUpperEdgeExactBound a 3 *
            partialExpUpperFast (positiveSoloYExponent (posJ a 3))
              (8 * posJ a 3)) := by
        ring
    _ ≤
      ((posJ a 3 : ℚ) * c (posJ a 3)) *
        (390 * positiveSmallLargeExpFast a 3 *
          ((posNlo a : ℚ) * c 3)) := hbudgetScaled
    _ =
      130 * ((3 : ℚ) * (posJ a 3 : ℚ)) *
        positiveSmallLargeExpFast a 3 *
          ((posNlo a : ℚ) * c 3 * c (posJ a 3)) := by
        ring

/-- Large-`a` `k = 3` small-product scalar after the shifted solo-style `Y`
bound has been supplied. -/
theorem positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar_three_of_shiftedSoloFastCleared_large
    {a : Nat} (ha : 3000 ≤ a)
    (hsolo :
      positiveLargeTailSoloGcompClosedFactorialSplitBlockSumFastCleared
        (posJ a 3) (posNhi a)) :
    positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
      (fun a k =>
        positiveLargeTailProductXUpperEdgeExactBound a k *
          positiveLargeTailProductYUpperEdgeExactBound a k) a 3 :=
  positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar_three_of_shiftedSoloFastCleared
    hsolo (positiveSmallThirdCellShiftedSoloFastExpBudget_of_large ha)

/-- Large-`a` `k = 3` small-product scalar from the shifted solo bound at
the shifted index's own upper edge.

The product rectangle mismatch is paid by
`positiveLargeTailSoloGcompClosedFactorialSplitBlockSum_thirdProductEdge_le_fifty_shiftedUpperEdge`;
the strengthened scalar budget above absorbs the resulting fixed factor. -/
theorem positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar_three_of_shiftedSoloOwnEdgeFastCleared_large
    {a : Nat} (ha : 3000 ≤ a)
    (hsolo :
      positiveLargeTailSoloGcompClosedFactorialSplitBlockSumFastCleared
        (posJ a 3) (posNhi (posJ a 3))) :
    positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
      (fun a k =>
        positiveLargeTailProductXUpperEdgeExactBound a k *
          positiveLargeTailProductYUpperEdgeExactBound a k) a 3 := by
  unfold positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
  change
    2 * (2 : ℚ)^(posJ a 3) * (posNhi a : ℚ) *
        (positiveLargeTailProductXUpperEdgeExactBound a 3 *
          positiveLargeTailProductYUpperEdgeExactBound a 3)
      ≤ 130 * ((3 : ℚ) * (posJ a 3 : ℚ)) *
        positiveSmallLargeExpFast a 3 *
          ((posNlo a : ℚ) * c 3 * c (posJ a 3))
  rw [positiveLargeTailProductYUpperEdgeExactBound_three_eq_shiftedSolo]
  have hscaleEdge :=
    positiveLargeTailSoloGcompClosedFactorialSplitBlockSum_thirdProductEdge_le_fifty_shiftedUpperEdge
      (a := a) ha
  unfold positiveLargeTailSoloGcompClosedFactorialSplitBlockSumFastCleared
    at hsolo
  have hbudget :=
    positiveSmallThirdCellShiftedSoloFiftyFastExpBudget_of_large ha
  unfold positiveSmallThirdCellShiftedSoloFiftyFastExpBudget at hbudget
  have hXnonneg :
      0 ≤ positiveLargeTailProductXUpperEdgeExactBound a 3 := by
    unfold positiveLargeTailProductXUpperEdgeExactBound
    exact positiveLargeTailProductXClosedFactorialSplitBlockBound_nonneg
      a (posNhi a) 3
  have hscale_nonneg :
      0 ≤
        ((posNhi a : ℚ) *
          positiveLargeTailProductXUpperEdgeExactBound a 3 / 2) := by
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) hXnonneg)
      (by norm_num : (0 : ℚ) ≤ 2)
  have hpow_nonneg : 0 ≤ (4 : ℚ) * (2 : ℚ)^(posJ a 3) := by
    positivity
  have hscaledBlock :
      (4 : ℚ) * (2 : ℚ)^(posJ a 3) *
          positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
            (posJ a 3) (posNhi a)
        ≤
      (4 : ℚ) * (2 : ℚ)^(posJ a 3) *
        ((50 : ℚ) *
          positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
            (posJ a 3) (posNhi (posJ a 3))) :=
    mul_le_mul_of_nonneg_left hscaleEdge hpow_nonneg
  have hscaledSoloOwn :
      (4 : ℚ) * (2 : ℚ)^(posJ a 3) *
          positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
            (posJ a 3) (posNhi (posJ a 3))
        ≤
      29 * (posJ a 3 : ℚ) * c (posJ a 3) *
        partialExpUpperFast (positiveSoloYExponent (posJ a 3))
          (8 * posJ a 3) := hsolo
  have hscaledSoloOwn50 :
      (4 : ℚ) * (2 : ℚ)^(posJ a 3) *
        ((50 : ℚ) *
          positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
            (posJ a 3) (posNhi (posJ a 3)))
        ≤
      50 *
        (29 * (posJ a 3 : ℚ) * c (posJ a 3) *
          partialExpUpperFast (positiveSoloYExponent (posJ a 3))
            (8 * posJ a 3)) := by
    have h50 : (0 : ℚ) ≤ 50 := by norm_num
    calc
      (4 : ℚ) * (2 : ℚ)^(posJ a 3) *
        ((50 : ℚ) *
          positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
            (posJ a 3) (posNhi (posJ a 3)))
          =
        50 *
          ((4 : ℚ) * (2 : ℚ)^(posJ a 3) *
            positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
              (posJ a 3) (posNhi (posJ a 3))) := by
            ring
      _ ≤ 50 *
          (29 * (posJ a 3 : ℚ) * c (posJ a 3) *
            partialExpUpperFast (positiveSoloYExponent (posJ a 3))
              (8 * posJ a 3)) :=
            mul_le_mul_of_nonneg_left hscaledSoloOwn h50
  have hscaledSolo :
      ((posNhi a : ℚ) *
          positiveLargeTailProductXUpperEdgeExactBound a 3 / 2) *
        ((4 : ℚ) * (2 : ℚ)^(posJ a 3) *
          positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
            (posJ a 3) (posNhi a))
        ≤
      ((posNhi a : ℚ) *
          positiveLargeTailProductXUpperEdgeExactBound a 3 / 2) *
        (50 *
          (29 * (posJ a 3 : ℚ) * c (posJ a 3) *
            partialExpUpperFast (positiveSoloYExponent (posJ a 3))
              (8 * posJ a 3))) :=
    mul_le_mul_of_nonneg_left
      (hscaledBlock.trans hscaledSoloOwn50) hscale_nonneg
  have hjc_nonneg : 0 ≤ (posJ a 3 : ℚ) * c (posJ a 3) :=
    mul_nonneg (Nat.cast_nonneg _) (c_nonneg (posJ a 3))
  have hbudgetScaled :
      ((posJ a 3 : ℚ) * c (posJ a 3)) *
        ((29 / 2 : ℚ) * (posNhi a : ℚ) *
          positiveLargeTailProductXUpperEdgeExactBound a 3 * 50 *
            partialExpUpperFast (positiveSoloYExponent (posJ a 3))
              (8 * posJ a 3))
        ≤
      ((posJ a 3 : ℚ) * c (posJ a 3)) *
        (390 * positiveSmallLargeExpFast a 3 *
          ((posNlo a : ℚ) * c 3)) :=
    mul_le_mul_of_nonneg_left hbudget hjc_nonneg
  calc
    2 * (2 : ℚ)^(posJ a 3) * (posNhi a : ℚ) *
        (positiveLargeTailProductXUpperEdgeExactBound a 3 *
          positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
            (posJ a 3) (posNhi a))
        =
      ((posNhi a : ℚ) *
          positiveLargeTailProductXUpperEdgeExactBound a 3 / 2) *
        ((4 : ℚ) * (2 : ℚ)^(posJ a 3) *
          positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
            (posJ a 3) (posNhi a)) := by
        ring
    _ ≤
      ((posNhi a : ℚ) *
          positiveLargeTailProductXUpperEdgeExactBound a 3 / 2) *
        (50 *
          (29 * (posJ a 3 : ℚ) * c (posJ a 3) *
            partialExpUpperFast (positiveSoloYExponent (posJ a 3))
              (8 * posJ a 3))) := hscaledSolo
    _ =
      ((posJ a 3 : ℚ) * c (posJ a 3)) *
        ((29 / 2 : ℚ) * (posNhi a : ℚ) *
          positiveLargeTailProductXUpperEdgeExactBound a 3 * 50 *
            partialExpUpperFast (positiveSoloYExponent (posJ a 3))
              (8 * posJ a 3)) := by
        ring
    _ ≤
      ((posJ a 3 : ℚ) * c (posJ a 3)) *
        (390 * positiveSmallLargeExpFast a 3 *
          ((posNlo a : ℚ) * c 3)) := hbudgetScaled
    _ =
      130 * ((3 : ℚ) * (posJ a 3 : ℚ)) *
        positiveSmallLargeExpFast a 3 *
          ((posNlo a : ℚ) * c 3 * c (posJ a 3)) := by
        ring

/-- The degree-two upper-edge `X` split sum is large enough to pay for the
actual first-cell linear `Bq` factor after the old product scalar inequality
is rescaled by the lower rectangle edge. -/
theorem positiveSmallFirstCell_linearFactor_le_scaledXUpperEdge
    (a : Nat) (ha : 2000 < a) :
    (5 : ℚ) * (posNhi a : ℚ) - 72 ≤
      (72 / (5 * (posNlo a : ℚ))) *
        positiveLargeTailProductXUpperEdgeExactBound a 2 := by
  have hlo_pos : (0 : ℚ) < (posNlo a : ℚ) := by
    exact_mod_cast posNlo_pos (by omega : 2 ≤ a)
  have hX_nonneg :
      0 ≤ (posNhi a : ℚ) * (144 / 25) := by
    positivity
  have hX_sq :
      (posNhi a : ℚ)^2 * (25 / 72)
        ≤ positiveLargeTailProductXUpperEdgeExactBound a 2 := by
    unfold positiveLargeTailProductXUpperEdgeExactBound
    rw [positiveLargeTailProductXClosedFactorialSplitBlockBound_two]
    linarith
  have hscale_nonneg :
      0 ≤ (72 / (5 * (posNlo a : ℚ)) : ℚ) := by
    positivity
  have hscaled :
      (72 / (5 * (posNlo a : ℚ)) : ℚ) *
          ((posNhi a : ℚ)^2 * (25 / 72))
        ≤
      (72 / (5 * (posNlo a : ℚ)) : ℚ) *
        positiveLargeTailProductXUpperEdgeExactBound a 2 :=
    mul_le_mul_of_nonneg_left hX_sq hscale_nonneg
  have hcore :
      (5 : ℚ) * (posNhi a : ℚ) - 72
        ≤ (72 / (5 * (posNlo a : ℚ)) : ℚ) *
            ((posNhi a : ℚ)^2 * (25 / 72)) := by
    have hhi_cast : (posNhi a : ℚ) = 12 * (a : ℚ) - 8 := by
      have hsub : 8 ≤ 12 * a := by omega
      unfold posNhi
      rw [Nat.cast_sub hsub]
      norm_num
    have hlo_cast : (posNlo a : ℚ) = 6 * (a : ℚ) - 7 := by
      have hsub : 7 ≤ 6 * a := by omega
      unfold posNlo
      rw [Nat.cast_sub hsub]
      norm_num
    rw [div_mul_eq_mul_div]
    field_simp [show (5 : ℚ) * (posNlo a : ℚ) ≠ 0 by positivity]
    rw [hhi_cast, hlo_cast]
    ring_nf
    nlinarith [show (0 : ℚ) ≤ (a : ℚ) by positivity]
  exact hcore.trans hscaled

/-- The endpoint first-cell budget follows from the stronger exact
upper-edge product scalar at `k = 2`.

This is a Lean-side bridge from the older exact split-product scalar package
to the current completion-facing first-cell route.  It does not revive the
independent `Gcomp` product estimate as the final target; it only reuses a
stronger scalar inequality when it is available. -/
theorem positiveSmallFirstCellYUpperEdgeBudget_of_exactSmallProductScalar
    {a : Nat} (ha : 2000 < a)
    (hscalar :
      positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
        (fun a k =>
          positiveLargeTailProductXUpperEdgeExactBound a k *
            positiveLargeTailProductYUpperEdgeExactBound a k) a 2) :
    positiveSmallFirstCellYUpperEdgeBudget a := by
  unfold positiveSmallFirstCellYUpperEdgeBudget positiveSmallFirstCellQBudget
  have hscalar' := hscalar
  unfold positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
    at hscalar'
  have hscale_nonneg :
      0 ≤ (36 / (5 * (posNlo a : ℚ)) : ℚ) := by
    have hlo_pos : (0 : ℚ) < (posNlo a : ℚ) := by
      exact_mod_cast posNlo_pos (by omega : 2 ≤ a)
    positivity
  have hscaled :=
    mul_le_mul_of_nonneg_left hscalar' hscale_nonneg
  have hY_nonneg :
      0 ≤ positiveLargeTailProductYUpperEdgeExactBound a 2 := by
    unfold positiveLargeTailProductYUpperEdgeExactBound
    exact positiveLargeTailProductYClosedFactorialSplitBlockBound_nonneg
      a (posNhi a) 2
  have hpow_hi_nonneg :
      0 ≤ (2 : ℚ)^(posJ a 2) * (posNhi a : ℚ) := by
    positivity
  have hcoeff := positiveSmallFirstCell_linearFactor_le_scaledXUpperEdge a ha
  have hcoeffY :
      ((5 : ℚ) * (posNhi a : ℚ) - 72) *
          positiveLargeTailProductYUpperEdgeExactBound a 2
        ≤
      ((72 / (5 * (posNlo a : ℚ)) : ℚ) *
          positiveLargeTailProductXUpperEdgeExactBound a 2) *
        positiveLargeTailProductYUpperEdgeExactBound a 2 :=
    mul_le_mul_of_nonneg_right hcoeff hY_nonneg
  have hleft :
      (2 : ℚ)^(posJ a 2) * (posNhi a : ℚ) *
          ((5 : ℚ) * (posNhi a : ℚ) - 72) *
          positiveLargeTailProductYUpperEdgeExactBound a 2
        ≤
      (36 / (5 * (posNlo a : ℚ)) : ℚ) *
        (2 * (2 : ℚ)^(posJ a 2) * (posNhi a : ℚ) *
          (positiveLargeTailProductXUpperEdgeExactBound a 2 *
            positiveLargeTailProductYUpperEdgeExactBound a 2)) := by
    calc
      (2 : ℚ)^(posJ a 2) * (posNhi a : ℚ) *
          ((5 : ℚ) * (posNhi a : ℚ) - 72) *
          positiveLargeTailProductYUpperEdgeExactBound a 2
          =
        ((2 : ℚ)^(posJ a 2) * (posNhi a : ℚ)) *
          (((5 : ℚ) * (posNhi a : ℚ) - 72) *
            positiveLargeTailProductYUpperEdgeExactBound a 2) := by
          ring
      _ ≤
        ((2 : ℚ)^(posJ a 2) * (posNhi a : ℚ)) *
          (((72 / (5 * (posNlo a : ℚ)) : ℚ) *
              positiveLargeTailProductXUpperEdgeExactBound a 2) *
            positiveLargeTailProductYUpperEdgeExactBound a 2) :=
          mul_le_mul_of_nonneg_left hcoeffY hpow_hi_nonneg
      _ =
        (36 / (5 * (posNlo a : ℚ)) : ℚ) *
          (2 * (2 : ℚ)^(posJ a 2) * (posNhi a : ℚ) *
            (positiveLargeTailProductXUpperEdgeExactBound a 2 *
              positiveLargeTailProductYUpperEdgeExactBound a 2)) := by
          ring
  exact hleft.trans (by
    calc
      (36 / (5 * (posNlo a : ℚ)) : ℚ) *
        (2 * (2 : ℚ)^(posJ a 2) * (posNhi a : ℚ) *
          (positiveLargeTailProductXUpperEdgeExactBound a 2 *
            positiveLargeTailProductYUpperEdgeExactBound a 2))
          ≤
        (36 / (5 * (posNlo a : ℚ)) : ℚ) *
          (130 * ((2 : ℚ) * (posJ a 2 : ℚ)) *
            positiveSmallLargeExpFast a 2 *
              ((posNlo a : ℚ) * c 2 * c (posJ a 2))) := hscaled
      _ =
        9360 * (posJ a 2 : ℚ) *
          positiveSmallLargeExp a 2 * c (posJ a 2) := by
        have hlo_ne : (posNlo a : ℚ) ≠ 0 := by
          exact_mod_cast (posNlo_pos (by omega : 2 ≤ a)).ne'
        rw [positiveSmallLargeExpFast_eq, c_two]
        field_simp [hlo_ne]
        ring)

/-- A bound on the shifted `Qq` coefficient reduces the first-cell budget to
the scalar `positiveSmallFirstCellQBudget` inequality. -/
theorem positiveSmallFirstCellRawQBudget_of_QBound
    {a N : Nat} (ha : 2000 < a) (hrect : positiveRectangle a N)
    {qBound : ℚ}
    (hQ : Qq N (posJ a 2) ≤ qBound)
    (hbudget : positiveSmallFirstCellQBudget a N qBound) :
    positiveSmallFirstCellRawQBudget a N := by
  have hfactor_nonneg :
      0 ≤ (2 : ℚ)^(posJ a 2) * (posNhi a : ℚ) *
          (5 * (N : ℚ) - 72) := by
    have hNlo : posNlo a ≤ N := hrect.1
    have hN15 : 15 ≤ N := by
      unfold posNlo at hNlo
      omega
    have hNfactor : 0 ≤ (5 : ℚ) * (N : ℚ) - 72 := by
      have h75 : (75 : ℚ) ≤ 5 * (N : ℚ) := by
        exact_mod_cast (by nlinarith : 75 ≤ 5 * N)
      linarith
    positivity
  have hscaled :=
    mul_le_mul_of_nonneg_left hQ hfactor_nonneg
  unfold positiveSmallFirstCellRawQBudget positiveSmallFirstCellQBudget
  exact hscaled.trans hbudget

/-- The actual shifted `Qq` coefficient is bounded by the split-factorial
`Y` block majorant at the same rectangle point. -/
theorem Qq_le_positiveLargeTailProductYClosedFactorialSplitBlockBound
    {a N k : Nat} :
    Qq N (posJ a k) ≤
      positiveLargeTailProductYClosedFactorialSplitBlockBound a N k := by
  have hclosed :
      positiveLargeTailYGcompClosedBlockSum N (posJ a k) =
        positiveLargeTailYGcompClosedFactorialSplitBlockSum N (posJ a k) := by
    rw [← positiveLargeTailYGcompClosedFactorialBlockSum_eq_closedBlockSum
        N (posJ a k),
      positiveLargeTailYGcompClosedFactorialBlockSum_eq_splitBlockSum
        N (posJ a k)]
  unfold positiveLargeTailProductYClosedFactorialSplitBlockBound
  calc
    Qq N (posJ a k)
        ≤ QqEplusGcompBound N (posJ a k) :=
          Qq_le_EplusGcompBound N (posJ a k)
    _ ≤ positiveLargeTailYGcompBlockSum N (posJ a k) :=
          QqEplusGcompBound_le_positiveLargeTailYGcompBlockSum
            N (posJ a k)
    _ ≤ positiveLargeTailYGcompClosedBlockSum N (posJ a k) :=
          positiveLargeTailYGcompBlockSum_le_closedBlockSum N (posJ a k)
    _ = positiveLargeTailYGcompClosedFactorialSplitBlockSum N (posJ a k) :=
          hclosed

/-- Upper-edge version of the shifted `Qq` bound used by the completion
route.  This keeps the first-cell proof on the actual combined
`Bq * Qq` product rather than the older independent product majorant. -/
theorem Qq_le_positiveLargeTailProductYUpperEdgeExactBound
    {a N k : Nat} (hrect : positiveRectangle a N) :
    Qq N (posJ a k) ≤ positiveLargeTailProductYUpperEdgeExactBound a k := by
  have hsameN :
      Qq N (posJ a k) ≤
        positiveLargeTailProductYClosedFactorialSplitBlockBound a N k :=
    Qq_le_positiveLargeTailProductYClosedFactorialSplitBlockBound
  have hmono :
      positiveLargeTailProductYClosedFactorialSplitBlockBound a N k
        ≤ positiveLargeTailProductYClosedFactorialSplitBlockBound
            a (posNhi a) k :=
    positiveLargeTailProductYClosedFactorialSplitBlockBound_mono_N
      (a := a) (k := k) hrect.2
  unfold positiveLargeTailProductYUpperEdgeExactBound
  exact hsameN.trans hmono

/-- If the first-cell `Qq` majorant is independent of `N`, it is enough to
check the scalar first-cell budget at the upper rectangle edge.

This is the endpoint reduction used by the completion route.  It is purely
algebraic: the only `N`-dependent factor in
`positiveSmallFirstCellQBudget` is `5*N - 72`, which is monotone on the
rectangle once the supplied `qBound` is nonnegative. -/
theorem positiveSmallFirstCellQBudget_of_upperEdgeQBound
    {a N : Nat} (hrect : positiveRectangle a N) {qBound : ℚ}
    (hqBound : 0 ≤ qBound)
    (hbudget :
      positiveSmallFirstCellQBudget a (posNhi a) qBound) :
    positiveSmallFirstCellQBudget a N qBound := by
  unfold positiveSmallFirstCellQBudget at hbudget ⊢
  let scale : ℚ :=
    (2 : ℚ)^(posJ a 2) * (posNhi a : ℚ) * qBound
  have hNle : (N : ℚ) ≤ (posNhi a : ℚ) := by
    exact_mod_cast hrect.2
  have hlinear :
      (5 : ℚ) * (N : ℚ) - 72 ≤
        5 * (posNhi a : ℚ) - 72 := by
    linarith
  have hscale_nonneg : 0 ≤ scale := by
    dsimp [scale]
    positivity
  have hscaled :
      scale * ((5 : ℚ) * (N : ℚ) - 72) ≤
        scale * (5 * (posNhi a : ℚ) - 72) :=
    mul_le_mul_of_nonneg_left hlinear hscale_nonneg
  calc
    (2 : ℚ)^(posJ a 2) * (posNhi a : ℚ) *
          (5 * (N : ℚ) - 72) * qBound
        =
      scale * ((5 : ℚ) * (N : ℚ) - 72) := by
        dsimp [scale]
        ring
    _ ≤ scale * (5 * (posNhi a : ℚ) - 72) := hscaled
    _ =
      (2 : ℚ)^(posJ a 2) * (posNhi a : ℚ) *
          (5 * (posNhi a : ℚ) - 72) * qBound := by
        dsimp [scale]
        ring
    _ ≤
      9360 * (posJ a 2 : ℚ) *
        positiveSmallLargeExp a 2 * c (posJ a 2) := hbudget

/-- Upper-edge specialization of
`positiveSmallFirstCellQBudget_of_upperEdgeQBound` for the exact split-factorial
`Y` block majorant used in the canonical product route. -/
theorem positiveSmallFirstCellQBudget_of_YUpperEdgeBudgetAtUpperEdge
    {a N : Nat} (hrect : positiveRectangle a N)
    (hbudget : positiveSmallFirstCellYUpperEdgeBudget a) :
    positiveSmallFirstCellQBudget a N
        (positiveLargeTailProductYUpperEdgeExactBound a 2) := by
  unfold positiveSmallFirstCellYUpperEdgeBudget at hbudget
  refine positiveSmallFirstCellQBudget_of_upperEdgeQBound hrect ?_ hbudget
  unfold positiveLargeTailProductYUpperEdgeExactBound
  exact positiveLargeTailProductYClosedFactorialSplitBlockBound_nonneg
    a (posNhi a) 2

/-- The direct `Qq` first-cell budget implies the live raw-cleared product
target for `k = 2`.

The proof is just algebra plus the closed form for `Bq N 2`; it is kept as a
small named bridge so later analytic work can focus on bounding
`Qq N (a-2)` rather than expanding the full product target. -/
theorem positiveSmallLargeXYProductRawCleared_two_of_rawQBudget
    {a N : Nat} (ha : 2000 < a) (hrect : positiveRectangle a N)
    (hbudget : positiveSmallFirstCellRawQBudget a N) :
    positiveSmallLargeXYProductRawCleared a N 2 := by
  have hNpos : (0 : ℚ) < (N : ℚ) := by
    exact_mod_cast positiveRectangle_N_pos (by omega : 2 ≤ a) hrect
  have hscale_nonneg : 0 ≤ (5 * (N : ℚ) / 36 : ℚ) := by
    positivity
  have hbudget' := hbudget
  unfold positiveSmallFirstCellRawQBudget positiveSmallFirstCellQBudget
    at hbudget'
  have hscaled :
      (5 * (N : ℚ) / 36) *
          ((2 : ℚ)^(posJ a 2) * (posNhi a : ℚ) *
            (5 * (N : ℚ) - 72) * Qq N (posJ a 2))
        ≤
      (5 * (N : ℚ) / 36) *
          (9360 * (posJ a 2 : ℚ) *
            positiveSmallLargeExp a 2 * c (posJ a 2)) :=
    mul_le_mul_of_nonneg_left hbudget' hscale_nonneg
  have hc2 : c 2 = 5 := by
    rw [c_succ_succ]
    norm_num [c_one]
  unfold positiveSmallLargeXYProductRawCleared
  calc
    2 * (2 : ℚ)^(posJ a 2) * (posNhi a : ℚ) *
        Bq N 2 * Qq N (posJ a 2)
        =
      (5 * (N : ℚ) / 36) *
        ((2 : ℚ)^(posJ a 2) * (posNhi a : ℚ) *
          (5 * (N : ℚ) - 72) * Qq N (posJ a 2)) := by
          rw [Bq_two]
          ring
    _ ≤
      (5 * (N : ℚ) / 36) *
        (9360 * (posJ a 2 : ℚ) *
          positiveSmallLargeExp a 2 * c (posJ a 2)) := hscaled
    _ =
      130 * ((2 : ℚ) * (posJ a 2 : ℚ)) *
        positiveSmallLargeExp a 2 *
          ((N : ℚ) * c 2 * c (posJ a 2)) := by
          rw [hc2]
          ring

/-- Combined first-cell bridge from a direct `Qq` upper bound and its scalar
budget. -/
theorem positiveSmallLargeXYProductRawCleared_two_of_QBound
    {a N : Nat} (ha : 2000 < a) (hrect : positiveRectangle a N)
    {qBound : ℚ}
    (hQ : Qq N (posJ a 2) ≤ qBound)
    (hbudget : positiveSmallFirstCellQBudget a N qBound) :
    positiveSmallLargeXYProductRawCleared a N 2 :=
  positiveSmallLargeXYProductRawCleared_two_of_rawQBudget ha hrect
    (positiveSmallFirstCellRawQBudget_of_QBound ha hrect hQ hbudget)

/-- First-cell bridge using the upper-edge split-factorial `Y` majorant as
the direct `Qq` budget. -/
theorem positiveSmallLargeXYProductRawCleared_two_of_YUpperEdgeBudget
    {a N : Nat} (ha : 2000 < a) (hrect : positiveRectangle a N)
    (hbudget :
      positiveSmallFirstCellQBudget a N
        (positiveLargeTailProductYUpperEdgeExactBound a 2)) :
    positiveSmallLargeXYProductRawCleared a N 2 :=
  positiveSmallLargeXYProductRawCleared_two_of_QBound ha hrect
    (Qq_le_positiveLargeTailProductYUpperEdgeExactBound
      (a := a) (N := N) (k := 2) hrect)
    hbudget

/-- Prefix-strip constructor with the same first-cell split used by the
large-tail product route.

The bounded prefix `2000 < a < 3000` can now use the direct upper-edge
`Qq N (a-2)` budget for `k = 2`, and reserve the split-factorial product
scalar checks for the genuine tail `k ≥ 3`.  This is a Lean-side
proof-production refinement of the older prefix chunks; it does not change
the mathematical product estimate, which is still the combined raw
`Bq * Qq` target. -/
theorem PositiveSaddleLargeTailProductPrefixPointwise.ofYUpperEdgeTwoEndpointAndClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerNGeThree
    (hbudgetTwoUpper :
      ∀ {a : Nat}, 2000 < a → a < 3000 →
        positiveSmallFirstCellYUpperEdgeBudget a)
    (hsmallGeThree :
      ∀ {a k : Nat}, 2000 < a → a < 3000 →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) → 3 ≤ k →
          positiveLargeTailSmallProductClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerN
            a k)
    (htemperedGeThree :
      ∀ {a k : Nat}, 2000 < a → a < 3000 →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) → 3 ≤ k →
          positiveLargeTailTemperedProductClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerN
            a k) :
    PositiveSaddleLargeTailProductPrefixPointwise :=
  PositiveSaddleLargeTailProductPrefixPointwise.ofRawClearedBqPositiveTwoAndGeThreeNatSignLockComplement
    (by
      intro a N ha haPrefix hrect
      exact positiveSmallLargeXYProductRawCleared_two_of_YUpperEdgeBudget
        ha hrect
        (positiveSmallFirstCellQBudget_of_YUpperEdgeBudgetAtUpperEdge
          hrect (hbudgetTwoUpper ha haPrefix)))
    (by
      intro a N k ha haPrefix hrect hk hsmallN hk3 _hB
      have hsmallEdge : k ≤ ceilSqrt (posNhi a) :=
        hsmallN.trans (ceilSqrt_mono hrect.2)
      exact positiveSmallLargeXYProductRawCleared_of_upperEdgeLowerN
        ha hrect hk (hsmallGeThree ha haPrefix hk hsmallEdge hk3))
    (by
      intro a N k ha haPrefix hrect hk htemperedN hnotLock hk3 _hB
      have htemperedEdge : ceilSqrt (posNlo a) < k :=
        lt_of_le_of_lt (ceilSqrt_mono hrect.1) htemperedN
      have hrowAlt : k < 361 ∨ 40 * k < 3 * posNhi a := by
        rcases hnotLock with hsmallK | hN
        · exact Or.inl hsmallK
        · exact Or.inr (by
            have h3N_hi : 3 * N ≤ 3 * posNhi a :=
              Nat.mul_le_mul_left 3 hrect.2
            omega)
      exact positiveTemperedLargeXYProductRawCleared_of_upperEdgeLowerN
        ha hrect hk
        (htemperedGeThree ha haPrefix hk htemperedEdge hrowAlt hk3))

/-- Combined-product variant of the bounded prefix first-cell split.

This mirrors the large-tail product surface: the first retained cell is handled
by the row-only `Y` upper-edge budget, while all `k ≥ 3` cells use one rational
majorant `xyBound` for the upper-edge split-block product. -/
theorem PositiveSaddleLargeTailProductPrefixPointwise.ofYUpperEdgeTwoEndpointAndFastUpperEdgeLowerNProductBoundGeThreeNatSignLockComplement
    {xyBound : Nat → Nat → ℚ}
    (hproductBound :
      ∀ {a k : Nat}, 2000 < a → a < 3000 → k ∈ positiveKRange a →
        3 ≤ k →
        positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct a k
          ≤ xyBound a k)
    (hbudgetTwoUpper :
      ∀ {a : Nat}, 2000 < a → a < 3000 →
        positiveSmallFirstCellYUpperEdgeBudget a)
    (hsmallGeThree :
      ∀ {a k : Nat}, 2000 < a → a < 3000 →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) → 3 ≤ k →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k)
    (htemperedGeThree :
      ∀ {a k : Nat}, 2000 < a → a < 3000 →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) → 3 ≤ k →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k) :
    PositiveSaddleLargeTailProductPrefixPointwise :=
  PositiveSaddleLargeTailProductPrefixPointwise.ofRawClearedBqPositiveTwoAndGeThreeNatSignLockComplement
    (by
      intro a N ha haPrefix hrect
      exact positiveSmallLargeXYProductRawCleared_two_of_YUpperEdgeBudget
        ha hrect
        (positiveSmallFirstCellQBudget_of_YUpperEdgeBudgetAtUpperEdge
          hrect (hbudgetTwoUpper ha haPrefix)))
    (by
      intro a N k ha haPrefix hrect hk hsmallN hk3 _hB
      have hsmallEdge : k ≤ ceilSqrt (posNhi a) :=
        hsmallN.trans (ceilSqrt_mono hrect.2)
      exact positiveSmallLargeXYProductRawCleared_of_fastUpperEdgeLowerNProductBound
        ha hrect hk (hproductBound ha haPrefix hk hk3)
        (hsmallGeThree ha haPrefix hk hsmallEdge hk3))
    (by
      intro a N k ha haPrefix hrect hk htemperedN hnotLock hk3 _hB
      have htemperedEdge : ceilSqrt (posNlo a) < k :=
        lt_of_le_of_lt (ceilSqrt_mono hrect.1) htemperedN
      have hrowAlt : k < 361 ∨ 40 * k < 3 * posNhi a := by
        rcases hnotLock with hsmallK | hN
        · exact Or.inl hsmallK
        · exact Or.inr (by
            have h3N_hi : 3 * N ≤ 3 * posNhi a :=
              Nat.mul_le_mul_left 3 hrect.2
            omega)
      exact positiveTemperedLargeXYProductRawCleared_of_fastUpperEdgeLowerNProductBound
        ha hrect hk (hproductBound ha haPrefix hk hk3)
        (htemperedGeThree ha haPrefix hk htemperedEdge hrowAlt hk3))

/-- Explicit first retained product-cell budget after replacing
`Y_{a-2}(N)` by the ten-sevenths solo envelope.

This is intentionally stated before cancelling common positive factors, so it
matches the denominator-cleared raw product target exactly.  The nontrivial
remaining analytic point is that the needed `Y` envelope is at index
`posJ a 2 = a-2`, while `N` remains in the larger `a`-rectangle.

This coarse route is retained for audit/diagnostic comparison only; the direct
`Qq` first-cell bridge above is the intended completion-facing surface. -/
def positiveSmallFirstCellTenSeventhsRawBudget (a N : Nat) : Prop :=
  2 * (2 : ℚ)^(posJ a 2) * (posNhi a : ℚ) * Bq N 2 *
      (((N : ℚ) / 2) * c (posJ a 2) / (2 : ℚ)^(posJ a 2) *
        positiveLargeTailSoloTenSeventhsBound (posJ a 2) N)
    ≤ 130 * ((2 : ℚ) * (posJ a 2 : ℚ)) *
      positiveSmallLargeExp a 2 *
        ((N : ℚ) * c 2 * c (posJ a 2))

/-- Cancelled first-cell budget after the `Y_{a-2}` ten-sevenths
replacement.  This is equivalent to
`positiveSmallFirstCellTenSeventhsRawBudget` under the large positive
rectangle hypotheses, but is the scalar form future estimates should target.
-/
def positiveSmallFirstCellTenSeventhsReducedBudget (a N : Nat) : Prop :=
  (posNhi a : ℚ) * Bq N 2 *
      positiveLargeTailSoloTenSeventhsBound (posJ a 2) N
    ≤ 130 * ((2 : ℚ) * (posJ a 2 : ℚ)) *
      positiveSmallLargeExp a 2 * c 2

/-- The reduced first-cell scalar budget implies the raw denominator-cleared
budget used by `positiveSmallLargeXYProductRawCleared_two_of_tenSeventhsY`.
-/
theorem positiveSmallFirstCellTenSeventhsRawBudget_of_reduced
    {a N : Nat} (ha : 3000 ≤ a) (hrect : positiveRectangle a N)
    (hred : positiveSmallFirstCellTenSeventhsReducedBudget a N) :
    positiveSmallFirstCellTenSeventhsRawBudget a N := by
  have hNpos : (0 : ℚ) < (N : ℚ) := by
    exact_mod_cast positiveRectangle_N_pos (by omega : 2 ≤ a) hrect
  have hj : 1 ≤ posJ a 2 := by
    unfold posJ
    omega
  have hcjpos : 0 < c (posJ a 2) :=
    c_pos (posJ a 2) hj
  have hfactor_nonneg :
      0 ≤ (N : ℚ) * c (posJ a 2) := by
    positivity
  have hscaled :=
    mul_le_mul_of_nonneg_right hred hfactor_nonneg
  unfold positiveSmallFirstCellTenSeventhsReducedBudget at hscaled
  unfold positiveSmallFirstCellTenSeventhsRawBudget
  calc
    2 * (2 : ℚ)^(posJ a 2) * (posNhi a : ℚ) * Bq N 2 *
        (((N : ℚ) / 2) * c (posJ a 2) /
          (2 : ℚ)^(posJ a 2) *
          positiveLargeTailSoloTenSeventhsBound (posJ a 2) N)
        =
      ((posNhi a : ℚ) * Bq N 2 *
          positiveLargeTailSoloTenSeventhsBound (posJ a 2) N) *
        ((N : ℚ) * c (posJ a 2)) := by
          have hpow : (2 : ℚ)^(posJ a 2) ≠ 0 := by positivity
          field_simp [hpow]
    _ ≤
      (130 * ((2 : ℚ) * (posJ a 2 : ℚ)) *
          positiveSmallLargeExp a 2 * c 2) *
        ((N : ℚ) * c (posJ a 2)) := hscaled
    _ =
      130 * ((2 : ℚ) * (posJ a 2 : ℚ)) *
        positiveSmallLargeExp a 2 *
          ((N : ℚ) * c 2 * c (posJ a 2)) := by
          ring

/-- Close the first retained small-branch product cell from a ten-sevenths
`Y_{a-2}` envelope and the corresponding raw scalar budget.

This records a genuine Lean-side subproblem rather than silently reusing the
closed solo theorem outside its rectangle: the caller must provide the
`positiveYgcompBound N (a-2)` envelope in the product rectangle. -/
theorem positiveSmallLargeXYProductRawCleared_two_of_tenSeventhsY
    {a N : Nat} (ha : 3000 ≤ a) (hrect : positiveRectangle a N)
    (hY :
      positiveYgcompBound N (posJ a 2) ≤
        positiveLargeTailSoloTenSeventhsBound (posJ a 2) N)
    (hbudget : positiveSmallFirstCellTenSeventhsRawBudget a N) :
    positiveSmallLargeXYProductRawCleared a N 2 := by
  have hN : 1 ≤ N :=
    Nat.succ_le_of_lt (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect)
  have hj : 1 ≤ posJ a 2 := by
    unfold posJ
    omega
  have hYnorm :
      Ynorm N (posJ a 2) ≤
        positiveLargeTailSoloTenSeventhsBound (posJ a 2) N :=
    (Ynorm_le_positiveYgcompBound N (posJ a 2)).trans hY
  have hyfactor_nonneg :
      0 ≤ ((N : ℚ) / 2) * c (posJ a 2) /
          (2 : ℚ)^(posJ a 2) := by
    exact div_nonneg
      (mul_nonneg (div_nonneg (Nat.cast_nonneg N) (by norm_num))
        (c_nonneg (posJ a 2)))
      (by positivity)
  have hQ :
      Qq N (posJ a 2) ≤
        ((N : ℚ) / 2) * c (posJ a 2) /
          (2 : ℚ)^(posJ a 2) *
            positiveLargeTailSoloTenSeventhsBound (posJ a 2) N := by
    rw [Qq_eq_yfactor_mul_Ynorm (N := N) (j := posJ a 2) hN hj]
    exact mul_le_mul_of_nonneg_left hYnorm hyfactor_nonneg
  have hBnonneg : 0 ≤ Bq N 2 :=
    (Bq_two_pos_of_large_positiveRectangle ha hrect).le
  have hBQ :
      Bq N 2 * Qq N (posJ a 2)
        ≤ Bq N 2 *
          (((N : ℚ) / 2) * c (posJ a 2) /
            (2 : ℚ)^(posJ a 2) *
              positiveLargeTailSoloTenSeventhsBound (posJ a 2) N) :=
    mul_le_mul_of_nonneg_left hQ hBnonneg
  have hscale :
      0 ≤ 2 * (2 : ℚ)^(posJ a 2) * (posNhi a : ℚ) := by
    positivity
  have hleft :
      2 * (2 : ℚ)^(posJ a 2) * (posNhi a : ℚ) *
          Bq N 2 * Qq N (posJ a 2)
        ≤
      2 * (2 : ℚ)^(posJ a 2) * (posNhi a : ℚ) * Bq N 2 *
        (((N : ℚ) / 2) * c (posJ a 2) /
          (2 : ℚ)^(posJ a 2) *
            positiveLargeTailSoloTenSeventhsBound (posJ a 2) N) := by
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hBQ hscale
  exact hleft.trans (by
    simpa [positiveSmallFirstCellTenSeventhsRawBudget,
      positiveSmallLargeXYProductRawCleared] using hbudget)

/-- Product-tail constructor that splits off the first retained product cell.

After the uniform `Bq N 1 ≤ 0` reduction, the first live cell is `k = 2`.
This Lean-side split is a proof-production surface reduction for the product
tail: a later proof may handle the `k = 2` term directly and send the true
tail to a `k ≥ 3` first-term/remainder argument.  The underlying estimate is
still the combined raw product `Bq * Qq`, not the older independent `Gcomp`
product route. -/
theorem LargeTailProductCertificate.ofRawClearedBqPositiveTwoAndGeThreeNatSignLockComplement
    (hsmallTwo :
      ∀ {a N : Nat}, 3000 ≤ a → positiveRectangle a N →
        positiveSmallLargeXYProductRawCleared a N 2)
    (hsmallGeThree :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N → 3 ≤ k → 0 < Bq N k →
          positiveSmallLargeXYProductRawCleared a N k)
    (htemperedGeThree :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k →
          (k < 361 ∨ 40 * k < 3 * N) → 3 ≤ k → 0 < Bq N k →
          positiveTemperedLargeXYProductRawCleared a N k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofRawClearedBqPositiveGeTwoNatSignLockComplement
    (by
      intro a N k ha hrect hk hsmallN hk2 hB
      by_cases hk_eq : k = 2
      · subst k
        exact hsmallTwo ha hrect
      · exact hsmallGeThree ha hrect hk hsmallN (by omega) hB)
    (by
      intro a N k ha hrect hk htemperedN hnotLock hk2 hB
      by_cases hk_eq : k = 2
      · subst k
        have hNgt : 4 < N := by
          have hNlo : posNlo a ≤ N := hrect.1
          unfold posNlo at hNlo
          omega
        have hceil : 2 < ceilSqrt N :=
          lt_ceilSqrt_of_sq_lt (n := N) (k := 2) (by
            norm_num
            exact hNgt)
        omega
      · exact htemperedGeThree ha hrect hk htemperedN hnotLock (by omega) hB)

/-- Product-tail constructor after the actual third `B`-coefficient sign
reduction.

For the combined raw product, `Bq N 3 ≤ 0` identically, so the `k = 3` cell is
automatic by `positiveSmallLargeXYProductRawCleared_of_Bq_nonpos` (and its
tempered analogue).  This is a deliberate Lean-side correction to the older
exact upper-edge product route: no shifted solo `Y_{a-3}` estimate is needed
for the actual product target. -/
theorem LargeTailProductCertificate.ofRawClearedBqPositiveTwoAndGeFourNatSignLockComplement
    (hsmallTwo :
      ∀ {a N : Nat}, 3000 ≤ a → positiveRectangle a N →
        positiveSmallLargeXYProductRawCleared a N 2)
    (hsmallGeFour :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N → 4 ≤ k → 0 < Bq N k →
          positiveSmallLargeXYProductRawCleared a N k)
    (htemperedGeFour :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k →
          (k < 361 ∨ 40 * k < 3 * N) → 4 ≤ k → 0 < Bq N k →
          positiveTemperedLargeXYProductRawCleared a N k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofRawClearedBqPositiveTwoAndGeThreeNatSignLockComplement
    hsmallTwo
    (by
      intro a N k ha hrect hk hsmallN hk3 hB
      by_cases hk_eq : k = 3
      · subst k
        exact False.elim ((not_le_of_gt hB) (Bq_three_nonpos N))
      · exact hsmallGeFour ha hrect hk hsmallN (by omega) hB)
    (by
      intro a N k ha hrect hk htemperedN hnotLock hk3 hB
      by_cases hk_eq : k = 3
      · subst k
        exact False.elim ((not_le_of_gt hB) (Bq_three_nonpos N))
      · exact htemperedGeFour ha hrect hk htemperedN hnotLock (by omega) hB)

/-- Fast-exp variant of
`LargeTailProductCertificate.ofRawClearedBqPositiveTwoAndGeThreeNatSignLockComplement`.

The theorem-facing large-tail product certificate remains stated with the
canonical raw inequalities.  This wrapper lets the remaining product proof
use the executable `positive*LargeExpFast` forms on exactly the reduced
first-cell/`k ≥ 3`/sign-lock-complement domain. -/
theorem LargeTailProductCertificate.ofRawClearedFastExpBqPositiveTwoAndGeThreeNatSignLockComplement
    (hsmallTwo :
      ∀ {a N : Nat}, 3000 ≤ a → positiveRectangle a N →
        positiveSmallLargeXYProductRawClearedFastExp a N 2)
    (hsmallGeThree :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N → 3 ≤ k → 0 < Bq N k →
          positiveSmallLargeXYProductRawClearedFastExp a N k)
    (htemperedGeThree :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k →
          (k < 361 ∨ 40 * k < 3 * N) → 3 ≤ k → 0 < Bq N k →
          positiveTemperedLargeXYProductRawClearedFastExp a N k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofRawClearedBqPositiveTwoAndGeThreeNatSignLockComplement
    (by
      intro a N ha hrect
      exact positiveSmallLargeXYProductRawCleared_of_fastExp
        (hsmallTwo ha hrect))
    (by
      intro a N k ha hrect hk hsmallN hk3 hB
      exact positiveSmallLargeXYProductRawCleared_of_fastExp
        (hsmallGeThree ha hrect hk hsmallN hk3 hB))
    (by
      intro a N k ha hrect hk htemperedN hnotLock hk3 hB
      exact positiveTemperedLargeXYProductRawCleared_of_fastExp
        (htemperedGeThree ha hrect hk htemperedN hnotLock hk3 hB))

/-- Direct saddle proof of the large-tail product certificate.

This is the corrected completion-facing product route: it supplies the actual
raw `Bq * Qq` fields directly and bypasses the false exact upper-edge
split-product constructor. -/
theorem LargeTailProductCertificate.ofDirectSaddle :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofRawClearedBqPositiveTwoAndGeThreeNatSignLockComplement
    (by
      intro a N ha hrect
      have hk : 2 ∈ positiveKRange a := by
        refine mem_positiveKRange.mpr ⟨by omega, ?_⟩
        unfold posKmax
        rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 10)]
        omega
      have hsmall : 2 ≤ ceilSqrt N := by
        have hNgt : 1 * 1 < N := by
          have hlo : posNlo a ≤ N := hrect.1
          unfold posNlo at hlo
          omega
        have hceil : 1 < ceilSqrt N :=
          lt_ceilSqrt_of_sq_lt (n := N) (k := 1) hNgt
        omega
      exact positiveSmallLargeXYProductRawCleared_of_directSaddle_geTwo
        (by omega : 2000 < a) hrect hk hsmall (by omega))
    (by
      intro a N k ha hrect hk hsmallN hk3 _hB
      exact positiveSmallLargeXYProductRawCleared_of_directSaddle_geTwo
        (by omega : 2000 < a) hrect hk hsmallN (by omega))
    (by
      intro a N k ha hrect hk htemperedN _hnotLock _hk3 _hB
      exact positiveTemperedLargeXYProductRawCleared_of_directSaddle
        (by omega : 2000 < a) hrect hk htemperedN)

/-- Product-tail constructor where the first retained cell is supplied by a
direct bound for `Qq N (a-2)`.

This is the completion-facing refinement of
`ofRawClearedBqPositiveTwoAndGeThreeNatSignLockComplement`: the `k = 2`
small-branch field is reduced to the tight first-cell `Qq` budget above,
while the true tail still starts at `k ≥ 3` and keeps the same sign-lock and
positive-`Bq` reductions. -/
theorem LargeTailProductCertificate.ofQBoundTwoAndGeThreeNatSignLockComplement
    {qBound : Nat → Nat → ℚ}
    (hQTwo :
      ∀ {a N : Nat}, 3000 ≤ a → positiveRectangle a N →
        Qq N (posJ a 2) ≤ qBound a N)
    (hbudgetTwo :
      ∀ {a N : Nat}, 3000 ≤ a → positiveRectangle a N →
        positiveSmallFirstCellQBudget a N (qBound a N))
    (hsmallGeThree :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N → 3 ≤ k → 0 < Bq N k →
          positiveSmallLargeXYProductRawCleared a N k)
    (htemperedGeThree :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k →
          (k < 361 ∨ 40 * k < 3 * N) → 3 ≤ k → 0 < Bq N k →
          positiveTemperedLargeXYProductRawCleared a N k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofRawClearedBqPositiveTwoAndGeThreeNatSignLockComplement
    (by
      intro a N ha hrect
      exact positiveSmallLargeXYProductRawCleared_two_of_QBound
        (by omega : 2000 < a) hrect (hQTwo ha hrect)
        (hbudgetTwo ha hrect))
    hsmallGeThree htemperedGeThree

/-- Sharp-`Qq` first-cell specialization of the product-tail constructor.

This is the preferred first-cell surface for the current canonical route.  It
uses `Qq_le_SharpGcompBound` and
`positiveSmallFirstCellQBudget_of_sharpQFastCleared`, so the remaining
`k = 2` analytic input is the sharp fast recurrence-level `Qq` estimate
`positiveSmallFirstCellSharpQFastCleared`.  The `k ≥ 3` tail remains the
combined raw product/sign-lock-complement obligation. -/
theorem LargeTailProductCertificate.ofSharpQFastTwoAndGeThreeNatSignLockComplement
    (hsharpTwo :
      ∀ {a N : Nat}, 3000 ≤ a → positiveRectangle a N →
        positiveSmallFirstCellSharpQFastCleared a N)
    (hsmallGeThree :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N → 3 ≤ k → 0 < Bq N k →
          positiveSmallLargeXYProductRawCleared a N k)
    (htemperedGeThree :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k →
          (k < 361 ∨ 40 * k < 3 * N) → 3 ≤ k → 0 < Bq N k →
          positiveTemperedLargeXYProductRawCleared a N k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofQBoundTwoAndGeThreeNatSignLockComplement
    (qBound := fun a N => QqSharpGcompBound N (posJ a 2))
    (by
      intro a N _ha _hrect
      exact Qq_le_SharpGcompBound N (posJ a 2))
    (by
      intro a N ha hrect
      exact positiveSmallFirstCellQBudget_of_sharpQFastCleared
        ha hrect (hsharpTwo ha hrect))
    hsmallGeThree htemperedGeThree

/-- Canonical first-cell specialization of the product-tail constructor:
`Qq N (a-2)` is bounded by the exact upper-edge split-factorial `Y` block
sum, and the remaining first-cell work is the single scalar budget
`positiveSmallFirstCellQBudget`.

This is the route-facing replacement for the failed coarse
ten-sevenths-envelope attempt below. -/
theorem LargeTailProductCertificate.ofYUpperEdgeTwoAndGeThreeNatSignLockComplement
    (hbudgetTwo :
      ∀ {a N : Nat}, 3000 ≤ a → positiveRectangle a N →
        positiveSmallFirstCellQBudget a N
          (positiveLargeTailProductYUpperEdgeExactBound a 2))
    (hsmallGeThree :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N → 3 ≤ k → 0 < Bq N k →
          positiveSmallLargeXYProductRawCleared a N k)
    (htemperedGeThree :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k →
          (k < 361 ∨ 40 * k < 3 * N) → 3 ≤ k → 0 < Bq N k →
          positiveTemperedLargeXYProductRawCleared a N k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofQBoundTwoAndGeThreeNatSignLockComplement
    (qBound := fun a _ => positiveLargeTailProductYUpperEdgeExactBound a 2)
    (by
      intro a N ha hrect
      exact Qq_le_positiveLargeTailProductYUpperEdgeExactBound
        (a := a) (N := N) (k := 2) hrect)
    hbudgetTwo hsmallGeThree htemperedGeThree

/-- Compatibility constructor from the older upper-edge/lower-`N` split-sum
`Gcomp` scalar route.

This is stronger than the live combined-product target and should not be the
main route to completion.  It is retained because the bounded prefix strip and
some legacy generated artifacts still use the independent `Gcomp` product
majorant. -/
theorem LargeTailProductCertificate.ofFastUpperEdgeLowerNScalars
    (hsmall :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k =>
              positiveLargeTailProductXUpperEdgeExactBound a k *
                positiveLargeTailProductYUpperEdgeExactBound a k) a k)
    (htempered :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k =>
              positiveLargeTailProductXUpperEdgeExactBound a k *
                positiveLargeTailProductYUpperEdgeExactBound a k) a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofRawCleared
    (by
      intro a N k ha hrect hk hsmallN
      have hsmallEdge : k ≤ ceilSqrt (posNhi a) :=
        hsmallN.trans (ceilSqrt_mono hrect.2)
      exact
        positiveSmallLargeXYProductRawCleared_of_fastUpperEdgeLowerN
          (by omega : 2000 < a) hrect hk
          (hsmall ha hk hsmallEdge))
    (by
      intro a N k ha hrect hk htemperedN
      have htemperedEdge : ceilSqrt (posNlo a) < k :=
        lt_of_le_of_lt (ceilSqrt_mono hrect.1) htemperedN
      exact
        positiveTemperedLargeXYProductRawCleared_of_fastUpperEdgeLowerN
          (by omega : 2000 < a) hrect hk
          (htempered ha hk htemperedEdge))

/-- One-dimensional fast-scalar constructor after applying the sign-lock
split to the tempered branch.

The TeX sign-lock branch is `N ≤ (40/3)k`.  On the raw-estimate branch Lean
receives the denominator-cleared complement `k < 361 ∨ 40*k < 3*N`; since
`N ≤ posNhi a` in the rectangle, the second alternative can be weakened to
the row-only condition `40*k < 3*posNhi a`.  This is the scalar surface a
large-tail checker should target if the full tempered upper-edge/lower-`N`
inequality is too strong in sign-lock-covered cells. -/
theorem LargeTailProductCertificate.ofFastUpperEdgeLowerNScalarsNatSignLockComplement
    (hsmall :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k =>
              positiveLargeTailProductXUpperEdgeExactBound a k *
                positiveLargeTailProductYUpperEdgeExactBound a k) a k)
    (htempered :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k =>
              positiveLargeTailProductXUpperEdgeExactBound a k *
                positiveLargeTailProductYUpperEdgeExactBound a k) a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofRawClearedNatSignLockComplement
    (by
      intro a N k ha hrect hk hsmallN
      have hsmallEdge : k ≤ ceilSqrt (posNhi a) :=
        hsmallN.trans (ceilSqrt_mono hrect.2)
      exact
        positiveSmallLargeXYProductRawCleared_of_fastUpperEdgeLowerN
          (by omega : 2000 < a) hrect hk
          (hsmall ha hk hsmallEdge))
    (by
      intro a N k ha hrect hk htemperedN hnotLock
      have htemperedEdge : ceilSqrt (posNlo a) < k :=
        lt_of_le_of_lt (ceilSqrt_mono hrect.1) htemperedN
      have hrowAlt : k < 361 ∨ 40 * k < 3 * posNhi a := by
        rcases hnotLock with hsmallK | hN
        · exact Or.inl hsmallK
        · exact Or.inr (by
            have h3N_hi : 3 * N ≤ 3 * posNhi a :=
              Nat.mul_le_mul_left 3 hrect.2
            omega)
      exact
        positiveTemperedLargeXYProductRawCleared_of_fastUpperEdgeLowerN
          (by omega : 2000 < a) hrect hk
          (htempered ha hk htemperedEdge hrowAlt))

/-- Large-tail product constructor for a rational upper-edge product
surrogate, after applying the sign-lock split to the tempered branch.

This is the intended completion-facing surface.  It follows the TeX
combined-product route, but records the Lean proof-production deviation:
instead of expanding the exact upper-edge split product inside the scalar
comparison, a separate `xyBound` may dominate that product.  The tempered
scalar is only required on the denominator-cleared complement of the §5
sign-lock zone. -/
theorem LargeTailProductCertificate.ofFastUpperEdgeLowerNProductBoundScalarsNatSignLockComplement
    {xyBound : Nat → Nat → ℚ}
    (hproductBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct a k
          ≤ xyBound a k)
    (hsmall :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k)
    (htempered :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofRawClearedNatSignLockComplement
    (by
      intro a N k ha hrect hk hsmallN
      have hsmallEdge : k ≤ ceilSqrt (posNhi a) :=
        hsmallN.trans (ceilSqrt_mono hrect.2)
      exact
        positiveSmallLargeXYProductRawCleared_of_fastUpperEdgeLowerNProductBound
          (by omega : 2000 < a) hrect hk
          (hproductBound ha hk)
          (hsmall ha hk hsmallEdge))
    (by
      intro a N k ha hrect hk htemperedN hnotLock
      have htemperedEdge : ceilSqrt (posNlo a) < k :=
        lt_of_le_of_lt (ceilSqrt_mono hrect.1) htemperedN
      have hrowAlt : k < 361 ∨ 40 * k < 3 * posNhi a := by
        rcases hnotLock with hsmallK | hN
        · exact Or.inl hsmallK
        · exact Or.inr (by
            have h3N_hi : 3 * N ≤ 3 * posNhi a :=
              Nat.mul_le_mul_left 3 hrect.2
            omega)
      exact
        positiveTemperedLargeXYProductRawCleared_of_fastUpperEdgeLowerNProductBound
          (by omega : 2000 < a) hrect hk
          (hproductBound ha hk)
          (htempered ha hk htemperedEdge hrowAlt))

/-- Large-tail product constructor for separate rational upper-edge `X` and
`Y` factor surrogates, after applying the sign-lock split to the tempered
branch.

This is the product-tail proof surface to target next.  It is weaker than the
full-hybrid `PositiveSaddle` surface because the tempered scalar is only
required on the row-level complement of the §5 sign-lock zone, and it avoids
the expensive exact split-product expression in the final scalar comparison.
-/
theorem LargeTailProductCertificate.ofFastUpperEdgeLowerNXYBoundScalarsNatSignLockComplement
    {xBound yBound : Nat → Nat → ℚ}
    (hxBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        positiveLargeTailProductXClosedFactorialSplitBlockBound
            a (posNhi a) k ≤ xBound a k)
    (hyBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        positiveLargeTailProductYClosedFactorialSplitBlockBound
            a (posNhi a) k ≤ yBound a k)
    (hsmall :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k => xBound a k * yBound a k) a k)
    (htempered :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k => xBound a k * yBound a k) a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofFastUpperEdgeLowerNProductBoundScalarsNatSignLockComplement
    (xyBound := fun a k => xBound a k * yBound a k)
    (by
      intro a k ha hk
      unfold positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct
      have hx := hxBound ha hk
      have hy := hyBound ha hk
      have hYnonneg :
          0 ≤ positiveLargeTailProductYClosedFactorialSplitBlockBound
            a (posNhi a) k :=
        positiveLargeTailProductYClosedFactorialSplitBlockBound_nonneg
          a (posNhi a) k
      have hxBoundNonneg : 0 ≤ xBound a k :=
        (positiveLargeTailProductXClosedFactorialSplitBlockBound_nonneg
          a (posNhi a) k).trans hx
      exact mul_le_mul hx hy hYnonneg hxBoundNonneg)
    hsmall
    htempered

/-- Large-tail product constructor for separate rational upper-edge `X` and
`Y` factor surrogates after both cheap raw-product reductions.

This is the same completion-facing route as
`ofFastUpperEdgeLowerNXYBoundScalarsNatSignLockComplement`, with the additional
Lean-side reduction from `Bq N 1 ≤ 0`: future scalar witnesses only need to
cover retained positive-`Bq` cells, hence `2 ≤ k`.  The statement is a proof
surface reduction, not a new mathematical estimate; the raw product is still
the actual combined `Bq * Qq` term. -/
theorem LargeTailProductCertificate.ofFastUpperEdgeLowerNXYBoundScalarsGeTwoNatSignLockComplement
    {xBound yBound : Nat → Nat → ℚ}
    (hxBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        positiveLargeTailProductXClosedFactorialSplitBlockBound
            a (posNhi a) k ≤ xBound a k)
    (hyBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        positiveLargeTailProductYClosedFactorialSplitBlockBound
            a (posNhi a) k ≤ yBound a k)
    (hsmall :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) → 2 ≤ k →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k => xBound a k * yBound a k) a k)
    (htempered :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) → 2 ≤ k →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k => xBound a k * yBound a k) a k) :
    LargeTailProductCertificate := by
  have hproductBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct a k
          ≤ xBound a k * yBound a k := by
    intro a k ha hk
    unfold positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct
    have hx := hxBound ha hk
    have hy := hyBound ha hk
    have hYnonneg :
        0 ≤ positiveLargeTailProductYClosedFactorialSplitBlockBound
          a (posNhi a) k :=
      positiveLargeTailProductYClosedFactorialSplitBlockBound_nonneg
        a (posNhi a) k
    have hxBoundNonneg : 0 ≤ xBound a k :=
      (positiveLargeTailProductXClosedFactorialSplitBlockBound_nonneg
        a (posNhi a) k).trans hx
    exact mul_le_mul hx hy hYnonneg hxBoundNonneg
  exact
    LargeTailProductCertificate.ofRawClearedBqPositiveGeTwoNatSignLockComplement
      (by
        intro a N k ha hrect hk hsmallN hk2 _hB
        have hsmallEdge : k ≤ ceilSqrt (posNhi a) :=
          hsmallN.trans (ceilSqrt_mono hrect.2)
        exact
          positiveSmallLargeXYProductRawCleared_of_fastUpperEdgeLowerNProductBound
            (by omega : 2000 < a) hrect hk
            (hproductBound ha hk)
            (hsmall ha hk hsmallEdge hk2))
      (by
        intro a N k ha hrect hk htemperedN hnotLock hk2 _hB
        have htemperedEdge : ceilSqrt (posNlo a) < k :=
          lt_of_le_of_lt (ceilSqrt_mono hrect.1) htemperedN
        have hrowAlt : k < 361 ∨ 40 * k < 3 * posNhi a := by
          rcases hnotLock with hsmallK | hN
          · exact Or.inl hsmallK
          · exact Or.inr (by
              have h3N_hi : 3 * N ≤ 3 * posNhi a :=
                Nat.mul_le_mul_left 3 hrect.2
              omega)
        exact
          positiveTemperedLargeXYProductRawCleared_of_fastUpperEdgeLowerNProductBound
            (by omega : 2000 < a) hrect hk
            (hproductBound ha hk)
            (htempered ha hk htemperedEdge hrowAlt hk2))

/-- Product-bound scalar constructor with the `k = 2` cell split off.

This is the completion-facing first-term/remainder surface for a combined
rational majorant `xyBound`: prove the first retained cell directly, then
prove the row-level scalar inequalities only for the genuine tail `k ≥ 3`.
It is a proof-production split of the same combined raw product route. -/
theorem LargeTailProductCertificate.ofFastUpperEdgeLowerNProductBoundScalarsTwoAndGeThreeNatSignLockComplement
    {xyBound : Nat → Nat → ℚ}
    (hproductBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        3 ≤ k →
        positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct a k
          ≤ xyBound a k)
    (hsmallTwo :
      ∀ {a N : Nat}, 3000 ≤ a → positiveRectangle a N →
        positiveSmallLargeXYProductRawCleared a N 2)
    (hsmallGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) → 3 ≤ k →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k)
    (htemperedGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) → 3 ≤ k →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofRawClearedBqPositiveTwoAndGeThreeNatSignLockComplement
    hsmallTwo
    (by
      intro a N k ha hrect hk hsmallN hk3 _hB
      have hsmallEdge : k ≤ ceilSqrt (posNhi a) :=
        hsmallN.trans (ceilSqrt_mono hrect.2)
      exact
        positiveSmallLargeXYProductRawCleared_of_fastUpperEdgeLowerNProductBound
          (by omega : 2000 < a) hrect hk
          (hproductBound ha hk hk3)
          (hsmallGeThree ha hk hsmallEdge hk3))
    (by
      intro a N k ha hrect hk htemperedN hnotLock hk3 _hB
      have htemperedEdge : ceilSqrt (posNlo a) < k :=
        lt_of_le_of_lt (ceilSqrt_mono hrect.1) htemperedN
      have hrowAlt : k < 361 ∨ 40 * k < 3 * posNhi a := by
        rcases hnotLock with hsmallK | hN
        · exact Or.inl hsmallK
        · exact Or.inr (by
            have h3N_hi : 3 * N ≤ 3 * posNhi a :=
              Nat.mul_le_mul_left 3 hrect.2
            omega)
      exact
        positiveTemperedLargeXYProductRawCleared_of_fastUpperEdgeLowerNProductBound
          (by omega : 2000 < a) hrect hk
          (hproductBound ha hk hk3)
          (htemperedGeThree ha hk htemperedEdge hrowAlt hk3))

/-- Product-bound scalar constructor with `k = 2` split off and the actual
`k = 3` cell removed by the `Bq` sign computation.

This is the live combined-product scalar surface after the third-cell audit:
callers prove the retained first cell directly and then start the scalar
majorant work at the genuine tail `k ≥ 4`.  This intentionally follows the
actual raw product rather than the older exact split-surrogate route. -/
theorem LargeTailProductCertificate.ofFastUpperEdgeLowerNProductBoundScalarsTwoAndGeFourNatSignLockComplement
    {xyBound : Nat → Nat → ℚ}
    (hproductBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        4 ≤ k →
        positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct a k
          ≤ xyBound a k)
    (hsmallTwo :
      ∀ {a N : Nat}, 3000 ≤ a → positiveRectangle a N →
        positiveSmallLargeXYProductRawCleared a N 2)
    (hsmallGeFour :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) → 4 ≤ k →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k)
    (htemperedGeFour :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) → 4 ≤ k →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofRawClearedBqPositiveTwoAndGeFourNatSignLockComplement
    hsmallTwo
    (by
      intro a N k ha hrect hk hsmallN hk4 _hB
      have hsmallEdge : k ≤ ceilSqrt (posNhi a) :=
        hsmallN.trans (ceilSqrt_mono hrect.2)
      exact
        positiveSmallLargeXYProductRawCleared_of_fastUpperEdgeLowerNProductBound
          (by omega : 2000 < a) hrect hk
          (hproductBound ha hk hk4)
          (hsmallGeFour ha hk hsmallEdge hk4))
    (by
      intro a N k ha hrect hk htemperedN hnotLock hk4 _hB
      have htemperedEdge : ceilSqrt (posNlo a) < k :=
        lt_of_le_of_lt (ceilSqrt_mono hrect.1) htemperedN
      have hrowAlt : k < 361 ∨ 40 * k < 3 * posNhi a := by
        rcases hnotLock with hsmallK | hN
        · exact Or.inl hsmallK
        · exact Or.inr (by
            have h3N_hi : 3 * N ≤ 3 * posNhi a :=
              Nat.mul_le_mul_left 3 hrect.2
            omega)
      exact
        positiveTemperedLargeXYProductRawCleared_of_fastUpperEdgeLowerNProductBound
          (by omega : 2000 < a) hrect hk
          (hproductBound ha hk hk4)
          (htemperedGeFour ha hk htemperedEdge hrowAlt hk4))

/-- Sharp-first-cell variant of the combined product-bound scalar constructor.

The first retained cell is handled by a sharp fast recurrence-level bound on
`Qq N (a-2)`.  The `k ≥ 3` tail is the same endpoint product-bound scalar
route as in
`LargeTailProductCertificate.ofFastUpperEdgeLowerNProductBoundScalarsTwoAndGeThreeNatSignLockComplement`.
This avoids both the coarse ten-sevenths first-cell envelope and the older
non-sharp `Y` upper-edge detour. -/
theorem LargeTailProductCertificate.ofSharpQFastTwoAndFastUpperEdgeLowerNProductBoundGeThreeNatSignLockComplement
    {xyBound : Nat → Nat → ℚ}
    (hproductBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        3 ≤ k →
        positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct a k
          ≤ xyBound a k)
    (hsharpTwo :
      ∀ {a N : Nat}, 3000 ≤ a → positiveRectangle a N →
        positiveSmallFirstCellSharpQFastCleared a N)
    (hsmallGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) → 3 ≤ k →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k)
    (htemperedGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) → 3 ≤ k →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofSharpQFastTwoAndGeThreeNatSignLockComplement
    hsharpTwo
    (by
      intro a N k ha hrect hk hsmallN hk3 _hB
      have hsmallEdge : k ≤ ceilSqrt (posNhi a) :=
        hsmallN.trans (ceilSqrt_mono hrect.2)
      exact
        positiveSmallLargeXYProductRawCleared_of_fastUpperEdgeLowerNProductBound
          (by omega : 2000 < a) hrect hk
          (hproductBound ha hk hk3)
          (hsmallGeThree ha hk hsmallEdge hk3))
    (by
      intro a N k ha hrect hk htemperedN hnotLock hk3 _hB
      have htemperedEdge : ceilSqrt (posNlo a) < k :=
        lt_of_le_of_lt (ceilSqrt_mono hrect.1) htemperedN
      have hrowAlt : k < 361 ∨ 40 * k < 3 * posNhi a := by
        rcases hnotLock with hsmallK | hN
        · exact Or.inl hsmallK
        · exact Or.inr (by
            have h3N_hi : 3 * N ≤ 3 * posNhi a :=
              Nat.mul_le_mul_left 3 hrect.2
            omega)
      exact
        positiveTemperedLargeXYProductRawCleared_of_fastUpperEdgeLowerNProductBound
          (by omega : 2000 < a) hrect hk
          (hproductBound ha hk hk3)
          (htemperedGeThree ha hk htemperedEdge hrowAlt hk3))

/-- Endpoint form of the sharp-first-cell combined product-bound constructor.

By `positiveSmallFirstCellSharpQFastCleared_of_upperEdge`, the sharp `Qq`
first-cell estimate only has to be proved at `N = posNhi a`. -/
theorem LargeTailProductCertificate.ofSharpQFastTwoEndpointAndFastUpperEdgeLowerNProductBoundGeThreeNatSignLockComplement
    {xyBound : Nat → Nat → ℚ}
    (hproductBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        3 ≤ k →
        positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct a k
          ≤ xyBound a k)
    (hsharpTwoUpper :
      ∀ {a : Nat}, 3000 ≤ a →
        positiveSmallFirstCellSharpQFastCleared a (posNhi a))
    (hsmallGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) → 3 ≤ k →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k)
    (htemperedGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) → 3 ≤ k →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofSharpQFastTwoAndFastUpperEdgeLowerNProductBoundGeThreeNatSignLockComplement
    hproductBound
    (by
      intro a N ha hrect
      exact positiveSmallFirstCellSharpQFastCleared_of_upperEdge
        hrect (hsharpTwoUpper ha))
    hsmallGeThree htemperedGeThree

/-- Endpoint constructor whose first-cell input is the explicit sharp
closed-factorial split block.

This is the preferred proof surface for the remaining `k = 2` large-tail
product cell: future work should prove the displayed closed-factorial fast
inequality, and this constructor turns it into the completion-facing product
certificate without reintroducing the older non-sharp `Y` route. -/
theorem LargeTailProductCertificate.ofSharpClosedFactorialSplitFastTwoEndpointAndFastUpperEdgeLowerNProductBoundGeThreeNatSignLockComplement
    {xyBound : Nat → Nat → ℚ}
    (hproductBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        3 ≤ k →
        positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct a k
          ≤ xyBound a k)
    (hsharpTwoUpper :
      ∀ {a : Nat}, 3000 ≤ a →
        positiveSmallFirstCellSharpClosedFactorialSplitBlockSumFastCleared
          a (posNhi a))
    (hsmallGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) → 3 ≤ k →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k)
    (htemperedGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) → 3 ≤ k →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofSharpQFastTwoEndpointAndFastUpperEdgeLowerNProductBoundGeThreeNatSignLockComplement
    hproductBound
    (by
      intro a ha
      exact
        positiveSmallFirstCellSharpQFastCleared_of_closedFactorialSplit
          (hsharpTwoUpper ha))
    hsmallGeThree htemperedGeThree

/-- Endpoint constructor whose first-cell input is the constant-budget sharp
closed-factorial split block.

This is the most compact current first-cell surface: the exponential factor
has been absorbed by
`partialExpUpperFast_positiveSoloYExponent_eight_ge_fiveHundred`, so the
remaining `k = 2` proof only has to establish a pure constant multiple of
`(a-2) * c (a-2)`. -/
theorem LargeTailProductCertificate.ofSharpClosedFactorialSplitConstTwoEndpointAndFastUpperEdgeLowerNProductBoundGeThreeNatSignLockComplement
    {xyBound : Nat → Nat → ℚ}
    (hproductBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        3 ≤ k →
        positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct a k
          ≤ xyBound a k)
    (hsharpTwoUpper :
      ∀ {a : Nat}, 3000 ≤ a →
        positiveSmallFirstCellSharpClosedFactorialSplitBlockSumConstCleared
          a (posNhi a))
    (hsmallGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) → 3 ≤ k →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k)
    (htemperedGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) → 3 ≤ k →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofSharpClosedFactorialSplitFastTwoEndpointAndFastUpperEdgeLowerNProductBoundGeThreeNatSignLockComplement
    hproductBound
    (by
      intro a ha
      exact
        positiveSmallFirstCellSharpClosedFactorialSplitBlockSumFastCleared_of_const
          ha (hsharpTwoUpper ha))
    hsmallGeThree htemperedGeThree

/-- Endpoint constructor whose first-cell input is the sharp own-edge
constant-budget target.

This is the current narrowest live `k = 2` product surface.  It records the
Lean-side edge shift explicitly: callers prove the natural solo-style
upper-edge bound at `j = a - 2`, and the product-edge mismatch is paid by
`positiveSmallFirstCellSharpClosedFactorialSplitBlockSumConstCleared_of_ownEdge`.
-/
theorem LargeTailProductCertificate.ofSharpOwnEdgeConstTwoEndpointAndFastUpperEdgeLowerNProductBoundGeThreeNatSignLockComplement
    {xyBound : Nat → Nat → ℚ}
    (hproductBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        3 ≤ k →
        positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct a k
          ≤ xyBound a k)
    (hsharpOwnTwo :
      ∀ {a : Nat}, 3000 ≤ a →
        positiveSmallFirstCellSharpOwnEdgeConstCleared a)
    (hsmallGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) → 3 ≤ k →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k)
    (htemperedGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) → 3 ≤ k →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofSharpClosedFactorialSplitConstTwoEndpointAndFastUpperEdgeLowerNProductBoundGeThreeNatSignLockComplement
    hproductBound
    (by
      intro a ha
      exact
        positiveSmallFirstCellSharpClosedFactorialSplitBlockSumConstCleared_of_ownEdge
          ha (hsharpOwnTwo ha))
    hsmallGeThree htemperedGeThree

/-- Closed first-cell version of the sharp own-edge product constructor.

The retained `k = 2` cell is now discharged by
`positiveSmallFirstCellSharpOwnEdgeConstCleared_large`; callers only supply
the combined upper-edge product majorant and the `k ≥ 3` scalar fields. -/
theorem LargeTailProductCertificate.ofClosedSharpOwnEdgeConstTwoEndpointAndFastUpperEdgeLowerNProductBoundGeThreeNatSignLockComplement
    {xyBound : Nat → Nat → ℚ}
    (hproductBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        3 ≤ k →
        positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct a k
          ≤ xyBound a k)
    (hsmallGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) → 3 ≤ k →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k)
    (htemperedGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) → 3 ≤ k →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofSharpOwnEdgeConstTwoEndpointAndFastUpperEdgeLowerNProductBoundGeThreeNatSignLockComplement
    hproductBound
    (by
      intro a ha
      exact positiveSmallFirstCellSharpOwnEdgeConstCleared_large ha)
    hsmallGeThree htemperedGeThree

/-- Closed first-cell combined-product constructor with the actual third cell
removed by `Bq_three_nonpos`.

This is the narrowed live product surface: `k = 2` is closed by the sharp
own-edge envelope, `k = 3` is nonpositive for the actual `Bq * Qq` term, and
only `k ≥ 4` remains for the combined scalar majorant. -/
theorem LargeTailProductCertificate.ofClosedSharpOwnEdgeConstTwoEndpointAndFastUpperEdgeLowerNProductBoundGeFourNatSignLockComplement
    {xyBound : Nat → Nat → ℚ}
    (hproductBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        4 ≤ k →
        positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct a k
          ≤ xyBound a k)
    (hsmallGeFour :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) → 4 ≤ k →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k)
    (htemperedGeFour :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) → 4 ≤ k →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofFastUpperEdgeLowerNProductBoundScalarsTwoAndGeFourNatSignLockComplement
    hproductBound
    (by
      intro a N ha hrect
      exact
        positiveSmallLargeXYProductRawCleared_two_of_QBound
          (by omega : 2000 < a) hrect
          (Qq_le_SharpGcompBound N (posJ a 2))
          (positiveSmallFirstCellQBudget_of_sharpQFastCleared ha hrect
            (positiveSmallFirstCellSharpQFastCleared_of_upperEdge hrect
              (positiveSmallFirstCellSharpQFastCleared_of_closedFactorialSplit
                (positiveSmallFirstCellSharpClosedFactorialSplitBlockSumFastCleared_of_const
                  ha
                  (positiveSmallFirstCellSharpClosedFactorialSplitBlockSumConstCleared_of_ownEdge
                    ha
                    (positiveSmallFirstCellSharpOwnEdgeConstCleared_large
                      ha)))))))
    hsmallGeFour htemperedGeFour

/-- Canonical combined-product constructor for the remaining large-tail
product route.

The first retained cell is discharged by the direct upper-edge `Y` budget for
`Qq N (a-2)`.  The genuine tail starts at `k ≥ 3` and uses the endpoint
product-bound scalar route on a combined `xyBound`; this avoids returning to
the older independent `Gcomp` product route. -/
theorem LargeTailProductCertificate.ofYUpperEdgeTwoAndFastUpperEdgeLowerNProductBoundGeThreeNatSignLockComplement
    {xyBound : Nat → Nat → ℚ}
    (hproductBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        3 ≤ k →
        positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct a k
          ≤ xyBound a k)
    (hbudgetTwo :
      ∀ {a N : Nat}, 3000 ≤ a → positiveRectangle a N →
        positiveSmallFirstCellQBudget a N
          (positiveLargeTailProductYUpperEdgeExactBound a 2))
    (hsmallGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) → 3 ≤ k →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k)
    (htemperedGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) → 3 ≤ k →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofFastUpperEdgeLowerNProductBoundScalarsTwoAndGeThreeNatSignLockComplement
    hproductBound
    (by
      intro a N ha hrect
      exact positiveSmallLargeXYProductRawCleared_two_of_YUpperEdgeBudget
        (by omega : 2000 < a) hrect (hbudgetTwo ha hrect))
    hsmallGeThree htemperedGeThree

/-- Endpoint first-cell variant of the canonical combined-product constructor.

The `k = 2` budget now has to be checked only at the upper rectangle edge
`N = posNhi a`; monotonicity of `positiveSmallFirstCellQBudget` transports it
to every `N` in the rectangle.  The `k ≥ 3` tail is unchanged and remains the
combined-product endpoint scalar route. -/
theorem LargeTailProductCertificate.ofYUpperEdgeTwoEndpointAndFastUpperEdgeLowerNProductBoundGeThreeNatSignLockComplement
    {xyBound : Nat → Nat → ℚ}
    (hproductBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        3 ≤ k →
        positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct a k
          ≤ xyBound a k)
    (hbudgetTwoUpper :
      ∀ {a : Nat}, 3000 ≤ a →
        positiveSmallFirstCellYUpperEdgeBudget a)
    (hsmallGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) → 3 ≤ k →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k)
    (htemperedGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) → 3 ≤ k →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofYUpperEdgeTwoAndFastUpperEdgeLowerNProductBoundGeThreeNatSignLockComplement
    hproductBound
    (by
      intro a N ha hrect
      exact
        positiveSmallFirstCellQBudget_of_YUpperEdgeBudgetAtUpperEdge
          (a := a) (N := N) hrect (hbudgetTwoUpper ha))
    hsmallGeThree htemperedGeThree

/-- Exact-upper-edge specialization of the endpoint first-cell constructor.

This removes the separate product-bound field when the chosen combined
surrogate is exactly the upper-edge split-factorial product.  It is mainly an
exception-handler surface: the preferred scalable proof can still use a
smaller `xyBound`, but exact upper-edge scalar proofs no longer need to repeat
the definitional product-bound argument. -/
theorem LargeTailProductCertificate.ofYUpperEdgeTwoEndpointAndExactUpperEdgeProductGeThreeNatSignLockComplement
    (hbudgetTwoUpper :
      ∀ {a : Nat}, 3000 ≤ a →
        positiveSmallFirstCellYUpperEdgeBudget a)
    (hsmallGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) → 3 ≤ k →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k =>
              positiveLargeTailProductXUpperEdgeExactBound a k *
                positiveLargeTailProductYUpperEdgeExactBound a k) a k)
    (htemperedGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) → 3 ≤ k →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k =>
              positiveLargeTailProductXUpperEdgeExactBound a k *
                positiveLargeTailProductYUpperEdgeExactBound a k) a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofYUpperEdgeTwoEndpointAndFastUpperEdgeLowerNProductBoundGeThreeNatSignLockComplement
    (xyBound := fun a k =>
      positiveLargeTailProductXUpperEdgeExactBound a k *
        positiveLargeTailProductYUpperEdgeExactBound a k)
    (by
      intro a k _ha _hk _hk3
      unfold positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct
        positiveLargeTailProductXUpperEdgeExactBound
        positiveLargeTailProductYUpperEdgeExactBound
      exact le_rfl)
    hbudgetTwoUpper hsmallGeThree htemperedGeThree

/-- Closed first-cell exact-upper-edge specialization.

This is retained as a compatibility surface for older exact-split artifacts:
choosing the exact upper-edge split-factorial product makes the `xyBound`
product-bound field definitional, while the retained `k = 2` cell is closed
through the sharp own-edge envelope.  It should not be used as the main
completion route.  The exact split-factorial `Y` surrogate loses the dyadic
gain needed in the high-`j` cells; the corrected route proves the actual
`Bq * Qq` raw-cleared predicates and feeds
`LargeTailProductCertificate.ofRawCleared`. -/
theorem LargeTailProductCertificate.ofClosedExactUpperEdgeProductGeThreeNatSignLockComplement
    (hsmallGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) → 3 ≤ k →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k =>
              positiveLargeTailProductXUpperEdgeExactBound a k *
                positiveLargeTailProductYUpperEdgeExactBound a k) a k)
    (htemperedGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) → 3 ≤ k →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k =>
              positiveLargeTailProductXUpperEdgeExactBound a k *
                positiveLargeTailProductYUpperEdgeExactBound a k) a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofClosedSharpOwnEdgeConstTwoEndpointAndFastUpperEdgeLowerNProductBoundGeThreeNatSignLockComplement
    (xyBound := fun a k =>
      positiveLargeTailProductXUpperEdgeExactBound a k *
        positiveLargeTailProductYUpperEdgeExactBound a k)
    (by
      intro a k _ha _hk _hk3
      unfold positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct
        positiveLargeTailProductXUpperEdgeExactBound
        positiveLargeTailProductYUpperEdgeExactBound
      exact le_rfl)
    hsmallGeThree htemperedGeThree

/-- Legacy exact-upper-edge product constructor with the actual `k = 3` cell removed
by the closed form `Bq_three_nonpos`.

This constructor remains useful for auditing older architecture, but it is not
completion-facing.  The `hsmallGeFour` field is false for the exact
split-factorial upper-edge product at `(a,k,j) = (3000,4,2996)`: the coarse
`Y` split contains a `6^j (j-1)!` term, and the outside `2^j` normalization is
not absorbed by the target exponential.  Future product-tail work should
target the actual raw predicates and use `LargeTailProductCertificate.ofRawCleared`
instead. -/
theorem LargeTailProductCertificate.ofClosedExactUpperEdgeProductGeFourNatSignLockComplement
    (hsmallGeFour :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) → 4 ≤ k →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k =>
              positiveLargeTailProductXUpperEdgeExactBound a k *
                positiveLargeTailProductYUpperEdgeExactBound a k) a k)
    (htemperedGeFour :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) → 4 ≤ k →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k =>
              positiveLargeTailProductXUpperEdgeExactBound a k *
                positiveLargeTailProductYUpperEdgeExactBound a k) a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofClosedSharpOwnEdgeConstTwoEndpointAndFastUpperEdgeLowerNProductBoundGeFourNatSignLockComplement
    (xyBound := fun a k =>
      positiveLargeTailProductXUpperEdgeExactBound a k *
        positiveLargeTailProductYUpperEdgeExactBound a k)
    (by
      intro a k _ha _hk _hk4
      unfold positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct
        positiveLargeTailProductXUpperEdgeExactBound
        positiveLargeTailProductYUpperEdgeExactBound
      exact le_rfl)
    hsmallGeFour htemperedGeFour

/-- Exact-upper-edge product constructor with the `k = 3` small branch peeled
off.

The `k = 3` scalar budget is now closed except for the shifted solo-style
`Y` bound at `j = a - 3`.  The tempered branch has no actual `k = 3` case at
`a ≥ 3000`, since `ceilSqrt (posNlo a) ≥ 3`.  The remaining exact-product
tail therefore starts at `k ≥ 4`. -/
theorem LargeTailProductCertificate.ofClosedExactUpperEdgeProductThirdCellAndGeFourNatSignLockComplement
    (hthirdSolo :
      ∀ {a : Nat}, 3000 ≤ a →
        positiveLargeTailSoloGcompClosedFactorialSplitBlockSumFastCleared
          (posJ a 3) (posNhi a))
    (hsmallGeFour :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) → 4 ≤ k →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k =>
              positiveLargeTailProductXUpperEdgeExactBound a k *
                positiveLargeTailProductYUpperEdgeExactBound a k) a k)
    (htemperedGeFour :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) → 4 ≤ k →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k =>
              positiveLargeTailProductXUpperEdgeExactBound a k *
                positiveLargeTailProductYUpperEdgeExactBound a k) a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofClosedExactUpperEdgeProductGeThreeNatSignLockComplement
    (by
      intro a k ha hk hsmall hk3
      by_cases hk_eq : k = 3
      · subst k
        exact
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar_three_of_shiftedSoloFastCleared_large
            ha (hthirdSolo ha)
      · exact hsmallGeFour ha hk hsmall (by omega))
    (by
      intro a k ha hk htempered hnotLock hk3
      by_cases hk_eq : k = 3
      · subst k
        have hceil_ge_three : 3 ≤ ceilSqrt (posNlo a) := by
          have hlt : 2 < ceilSqrt (posNlo a) :=
            lt_ceilSqrt_of_sq_lt (n := posNlo a) (k := 2) (by
              unfold posNlo
              omega)
          omega
        omega
      · exact htemperedGeFour ha hk htempered hnotLock (by omega))

/-- Exact-upper-edge product constructor with the `k = 3` small branch peeled
off using only the shifted index's own upper edge.

Compared with
`LargeTailProductCertificate.ofClosedExactUpperEdgeProductThirdCellAndGeFourNatSignLockComplement`,
this removes the product-edge solo fast assumption.  The edge mismatch
`posNhi a > posNhi (a - 3)` is paid internally by the fixed-factor scalar
budget above, so the remaining shifted solo input is the standard own-edge
fast target at `j = a - 3`. -/
theorem LargeTailProductCertificate.ofClosedExactUpperEdgeProductThirdCellOwnEdgeAndGeFourNatSignLockComplement
    (hthirdSoloOwn :
      ∀ {a : Nat}, 3000 ≤ a →
        positiveLargeTailSoloGcompClosedFactorialSplitBlockSumFastCleared
          (posJ a 3) (posNhi (posJ a 3)))
    (hsmallGeFour :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) → 4 ≤ k →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k =>
              positiveLargeTailProductXUpperEdgeExactBound a k *
                positiveLargeTailProductYUpperEdgeExactBound a k) a k)
    (htemperedGeFour :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) → 4 ≤ k →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k =>
              positiveLargeTailProductXUpperEdgeExactBound a k *
                positiveLargeTailProductYUpperEdgeExactBound a k) a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofClosedExactUpperEdgeProductGeThreeNatSignLockComplement
    (by
      intro a k ha hk hsmall hk3
      by_cases hk_eq : k = 3
      · subst k
        exact
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar_three_of_shiftedSoloOwnEdgeFastCleared_large
            ha (hthirdSoloOwn ha)
      · exact hsmallGeFour ha hk hsmall (by omega))
    (by
      intro a k ha hk htempered hnotLock hk3
      by_cases hk_eq : k = 3
      · subst k
        have hceil_ge_three : 3 ≤ ceilSqrt (posNlo a) := by
          have hlt : 2 < ceilSqrt (posNlo a) :=
            lt_ceilSqrt_of_sq_lt (n := posNlo a) (k := 2) (by
              unfold posNlo
              omega)
          omega
        omega
      · exact htemperedGeFour ha hk htempered hnotLock (by omega))

/-- Split-final-term scalar specialization of the endpoint first-cell
constructor.

This is the completion-facing product split: the retained first cell `k = 2`
is proved by the direct `Qq`/upper-edge-`Y` budget, while the exact
split-factorial scalar product estimate is needed only for the genuine tail
`k ≥ 3`.  This differs from the older compatibility constructor below, which
derives the first-cell budget from the full scalar product package; the split
here records the intended Lean route toward closing the live product
assumption. -/
theorem LargeTailProductCertificate.ofYUpperEdgeTwoEndpointAndClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerNGeThree
    (hbudgetTwoUpper :
      ∀ {a : Nat}, 3000 ≤ a →
        positiveSmallFirstCellYUpperEdgeBudget a)
    (hsmallGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) → 3 ≤ k →
          positiveLargeTailSmallProductClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerN
            a k)
    (htemperedGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) → 3 ≤ k →
          positiveLargeTailTemperedProductClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerN
            a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofYUpperEdgeTwoEndpointAndExactUpperEdgeProductGeThreeNatSignLockComplement
    hbudgetTwoUpper
    (by
      intro a k ha hk hsmall hk3
      have h := hsmallGeThree ha hk hsmall hk3
      simpa [
        positiveLargeTailProductXUpperEdgeExactBound,
        positiveLargeTailProductYUpperEdgeExactBound,
        positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar,
        positiveLargeTailSmallProductClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerN,
        mul_assoc,
      ] using h)
    (by
      intro a k ha hk htempered hnotLock hk3
      have h := htemperedGeThree ha hk htempered hnotLock hk3
      simpa [
        positiveLargeTailProductXUpperEdgeExactBound,
        positiveLargeTailProductYUpperEdgeExactBound,
        positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar,
        positiveLargeTailTemperedProductClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerN,
        mul_assoc,
      ] using h)

/-- Split-final-term scalar specialization with the first-cell scalar budget
closed.

For the live large-tail product route, the retained `k = 2` cell now asks
only for the shifted solo fast-cleared bound.  The scalar comparison between
that bound and the small-branch product exponential is supplied by
`positiveSmallFirstCellShiftedSoloFastExpBudget_of_large`. -/
theorem LargeTailProductCertificate.ofShiftedSoloFirstCellAndClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerNGeThree
    (hshiftedSoloTwoUpper :
      ∀ {a : Nat}, 3000 ≤ a →
        positiveLargeTailSoloGcompClosedFactorialSplitBlockSumFastCleared
          (posJ a 2) (posNhi a))
    (hsmallGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) → 3 ≤ k →
          positiveLargeTailSmallProductClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerN
            a k)
    (htemperedGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) → 3 ≤ k →
          positiveLargeTailTemperedProductClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerN
            a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofYUpperEdgeTwoEndpointAndClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerNGeThree
    (by
      intro a ha
      exact
        positiveSmallFirstCellYUpperEdgeBudget_of_shiftedSoloFastCleared_large
          ha (hshiftedSoloTwoUpper ha))
    hsmallGeThree htemperedGeThree

/-- Product-tail constructor using the scaled shifted-solo first-cell route.

This is the completion-facing replacement for asking the shifted solo theorem
directly at the larger product edge `posNhi a`.  The caller now proves the
ordinary upper-edge solo-style statement at `j = a - 2`, pays the fixed `50`
edge-scaling factor through `positiveSmallFirstCellShiftedSoloFiftyFastExpBudget`,
and supplies the unchanged `k ≥ 3` scalar fields. -/
theorem LargeTailProductCertificate.ofShiftedSoloOwnEdgeFirstCellAndClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerNGeThree
    (hshiftedSoloOwnUpper :
      ∀ {a : Nat}, 3000 ≤ a →
        positiveLargeTailSoloGcompClosedFactorialSplitBlockSumFastCleared
          (posJ a 2) (posNhi (posJ a 2)))
    (hscaledBudgetTwo :
      ∀ {a : Nat}, 3000 ≤ a →
        positiveSmallFirstCellShiftedSoloFiftyFastExpBudget a)
    (hsmallGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) → 3 ≤ k →
          positiveLargeTailSmallProductClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerN
            a k)
    (htemperedGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) → 3 ≤ k →
          positiveLargeTailTemperedProductClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerN
            a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofYUpperEdgeTwoEndpointAndClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerNGeThree
    (by
      intro a ha
      exact
        positiveSmallFirstCellYUpperEdgeBudget_of_shiftedSoloOwnEdgeFastCleared
          ha (hshiftedSoloOwnUpper ha) (hscaledBudgetTwo ha))
    hsmallGeThree htemperedGeThree

/-- Product-tail constructor after closing the fixed-factor first-cell scalar
budget.

The first retained product cell now asks only for the shifted solo fast
upper-edge theorem at `j = a - 2`, `N = posNhi (a - 2)`.  The rectangle-edge
mismatch and the extra scalar factor are discharged by the preceding lemmas. -/
theorem LargeTailProductCertificate.ofShiftedSoloOwnEdgeFirstCellClosedBudgetAndClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerNGeThree
    (hshiftedSoloOwnUpper :
      ∀ {a : Nat}, 3000 ≤ a →
        positiveLargeTailSoloGcompClosedFactorialSplitBlockSumFastCleared
          (posJ a 2) (posNhi (posJ a 2)))
    (hsmallGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) → 3 ≤ k →
          positiveLargeTailSmallProductClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerN
            a k)
    (htemperedGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) → 3 ≤ k →
          positiveLargeTailTemperedProductClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerN
            a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofShiftedSoloOwnEdgeFirstCellAndClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerNGeThree
    hshiftedSoloOwnUpper
    (by
      intro a ha
      exact positiveSmallFirstCellShiftedSoloFiftyFastExpBudget_of_large ha)
    hsmallGeThree htemperedGeThree

/-- Combined-product version of the shifted-solo first-cell route.

This is the preferred completion surface after the `k = 2` cell has been
reduced to the shifted solo upper edge: the genuine `k ≥ 3` tail is supplied
by one combined upper-edge product majorant `xyBound`, not by separate exact
`Gcomp` factor scalar fields.  This records the Lean-side deviation from the
older TeX bookkeeping, while keeping the same normalized combined product
target consumed by `Completion.lean`. -/
theorem LargeTailProductCertificate.ofShiftedSoloOwnEdgeFirstCellClosedBudgetAndFastUpperEdgeLowerNProductBoundGeThreeNatSignLockComplement
    {xyBound : Nat → Nat → ℚ}
    (hshiftedSoloOwnUpper :
      ∀ {a : Nat}, 3000 ≤ a →
        positiveLargeTailSoloGcompClosedFactorialSplitBlockSumFastCleared
          (posJ a 2) (posNhi (posJ a 2)))
    (hproductBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        3 ≤ k →
        positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct a k
          ≤ xyBound a k)
    (hsmallGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) → 3 ≤ k →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k)
    (htemperedGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) → 3 ≤ k →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofYUpperEdgeTwoEndpointAndFastUpperEdgeLowerNProductBoundGeThreeNatSignLockComplement
    (xyBound := xyBound)
    hproductBound
    (by
      intro a ha
      exact
        positiveSmallFirstCellYUpperEdgeBudget_of_shiftedSoloOwnEdgeFastCleared
          ha (hshiftedSoloOwnUpper ha)
          (positiveSmallFirstCellShiftedSoloFiftyFastExpBudget_of_large ha))
    hsmallGeThree htemperedGeThree

/-- Product-tail constructor using the existing fast solo upper-edge
certificate as the first-cell input.

This does not change the mathematical route: the `k = 2` product cell is
still paid for by the shifted solo upper edge.  It only records the Lean-side
reindexing from `a ≥ 3000` to `j = a - 2 ≥ 2998`, so future proof producers
that close the standard fast solo upper-edge certificate can feed the live
product certificate directly. -/
theorem LargeTailProductCertificate.ofSoloFastUpperEdgeBoundCertificateAndFastUpperEdgeLowerNProductBoundGeThreeNatSignLockComplement
    {xyBound : Nat → Nat → ℚ} {soloBound : Nat → ℚ}
    (hsoloFast :
      PositiveSaddleLargeTailSoloFastUpperEdgeBoundCertificate soloBound)
    (hproductBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        3 ≤ k →
        positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct a k
          ≤ xyBound a k)
    (hsmallGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) → 3 ≤ k →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k)
    (htemperedGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) → 3 ≤ k →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofShiftedSoloOwnEdgeFirstCellClosedBudgetAndFastUpperEdgeLowerNProductBoundGeThreeNatSignLockComplement
    (xyBound := xyBound)
    (by
      intro a ha
      exact hsoloFast.toUpperEdge (a := posJ a 2) (by
        unfold posJ
        omega))
    hproductBound hsmallGeThree htemperedGeThree

/-- Compatibility constructor from the existing exact upper-edge/lower-`N`
fast split-final-term scalar package.

This packages that stronger product scalar theorem into the current
completion-facing `LargeTailProductCertificate`.  The adapter now follows the
completion route above: the `k = 2` cell is routed through the sharp first-cell
chain, the actual `k = 3` combined product is discharged by
`Bq_three_nonpos`, and only the `k ≥ 4` small and tempered tails use the exact
upper-edge product scalar fields.  This is a Lean-side correction to the older
split-surrogate route, which treated the third cell as a shifted solo input. -/
theorem LargeTailProductCertificate.ofClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerN
    (product :
      PositiveSaddleLargeTailProductClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerNCertificate) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofClosedExactUpperEdgeProductGeFourNatSignLockComplement
    (by
      intro a k ha hk hsmall hk4
      have h := product.smallScalar (by omega : 2000 < a) hk hsmall
      simpa [
        positiveLargeTailProductXUpperEdgeExactBound,
        positiveLargeTailProductYUpperEdgeExactBound,
        positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar,
        positiveLargeTailSmallProductClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerN,
        mul_assoc,
      ] using h)
    (by
      intro a k ha hk htempered _hnotLock hk4
      have h := product.temperedScalar (by omega : 2000 < a) hk htempered
      simpa [
        positiveLargeTailProductXUpperEdgeExactBound,
        positiveLargeTailProductYUpperEdgeExactBound,
        positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar,
        positiveLargeTailTemperedProductClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerN,
        mul_assoc,
      ] using h)

/-- Direct adapter from the existing product-bound certificate structure to
the completion-facing product certificate.

The supplied `product` certificate proves the upper-edge/lower-`N` scalar
inequalities for every live small and tempered cell, but this adapter consumes
only the cells needed by the corrected completion route: `k = 2` directly,
`k ≥ 4` through the scalar fields, and `k = 3` through `Bq_three_nonpos`.
Generated and hybrid large-tail certificates can therefore feed
`Completion.lean` without reopening the obsolete shifted-third-cell route. -/
theorem LargeTailProductCertificate.ofFastUpperEdgeLowerNProductBoundCertificate
    {xyBound : Nat → Nat → ℚ}
    (product :
      PositiveSaddleLargeTailProductFastUpperEdgeLowerNProductBoundCertificate
        xyBound) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofRawClearedBqPositiveTwoAndGeFourNatSignLockComplement
    (by
      intro a N ha hrect
      have hk : 2 ∈ positiveKRange a := by
        refine mem_positiveKRange.mpr ⟨by omega, ?_⟩
        unfold posKmax
        rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 10)]
        omega
      have hsmallEdge : 2 ≤ ceilSqrt (posNhi a) := by
        have hlt : 1 < ceilSqrt (posNhi a) :=
          lt_ceilSqrt_of_sq_lt (n := posNhi a) (k := 1) (by
            unfold posNhi
            omega)
        omega
      exact
        positiveSmallLargeXYProductRawCleared_of_fastUpperEdgeLowerNProductBound
          (by omega : 2000 < a) hrect hk
          (product.productBound (by omega : 2000 < a) hk)
          (product.smallScalar (by omega : 2000 < a) hk hsmallEdge))
    (by
      intro a N k ha hrect hk hsmallN hk4 _hB
      have hsmallEdge : k ≤ ceilSqrt (posNhi a) :=
        hsmallN.trans (ceilSqrt_mono hrect.2)
      exact
        positiveSmallLargeXYProductRawCleared_of_fastUpperEdgeLowerNProductBound
          (by omega : 2000 < a) hrect hk
          (product.productBound (by omega : 2000 < a) hk)
          (product.smallScalar (by omega : 2000 < a) hk hsmallEdge))
    (by
      intro a N k ha hrect hk htemperedN _hnotLock hk4 _hB
      have htemperedEdge : ceilSqrt (posNlo a) < k :=
        lt_of_le_of_lt (ceilSqrt_mono hrect.1) htemperedN
      exact
        positiveTemperedLargeXYProductRawCleared_of_fastUpperEdgeLowerNProductBound
          (by omega : 2000 < a) hrect hk
          (product.productBound (by omega : 2000 < a) hk)
          (product.temperedScalar (by omega : 2000 < a) hk htemperedEdge))

/-- Separate-`X`/`Y` product-bound certificates also feed the live large-tail
product target directly via their combined product-bound certificate. -/
theorem LargeTailProductCertificate.ofFastUpperEdgeLowerNXYBoundCertificate
    {xBound yBound : Nat → Nat → ℚ}
    (product :
      PositiveSaddleLargeTailProductFastUpperEdgeLowerNXYBoundCertificate
        xBound yBound) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofFastUpperEdgeLowerNProductBoundCertificate
    product.toProductBoundCertificate

/-- Hybrid prefix/large product-bound certificates can be used as a live
large-tail product input.  The prefix chunks in the hybrid package are ignored
by `LargeTailProductCertificate` itself, but are part of the same object used
elsewhere to cover the `2000 < a < 3000` strip. -/
theorem LargeTailProductCertificate.ofFastUpperEdgeLowerNProductBoundHybridCertificate
    {xyBound : Nat → Nat → ℚ} {aLen kLen : Nat}
    (product :
      PositiveSaddleLargeTailProductFastUpperEdgeLowerNProductBoundHybridCertificate
        xyBound aLen kLen) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofFastUpperEdgeLowerNProductBoundCertificate
    product.toProductBoundCertificate

/-- Hybrid separate-factor product certificates can be used as a live
large-tail product input. -/
theorem LargeTailProductCertificate.ofFastUpperEdgeLowerNXYBoundHybridCertificate
    {xBound yBound : Nat → Nat → ℚ} {aLen kLen : Nat}
    (product :
      PositiveSaddleLargeTailProductFastUpperEdgeLowerNXYBoundHybridCertificate
        xBound yBound aLen kLen) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofFastUpperEdgeLowerNXYBoundCertificate
    product.toXYBoundCertificate

/-- Full hybrid separate-factor product certificates can be used as a live
large-tail product input. -/
theorem LargeTailProductCertificate.ofFastUpperEdgeLowerNXYBoundFullHybridCertificate
    {xBound yBound : Nat → Nat → ℚ} {aLen kLen : Nat}
    (product :
      PositiveSaddleLargeTailProductFastUpperEdgeLowerNXYBoundFullHybridCertificate
        xBound yBound aLen kLen) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofFastUpperEdgeLowerNXYBoundCertificate
    product.toXYBoundCertificate

/-- Separate-`X`/`Y` variant of the first-term/remainder product-bound route.

The two factor majorants only serve to prove the combined `xyBound`
upper-edge product bound; the live scalar obligations remain the first
retained raw product cell and the `k ≥ 3` combined-product tail. -/
theorem LargeTailProductCertificate.ofFastUpperEdgeLowerNXYBoundScalarsTwoAndGeThreeNatSignLockComplement
    {xBound yBound : Nat → Nat → ℚ}
    (hxBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        positiveLargeTailProductXClosedFactorialSplitBlockBound
            a (posNhi a) k ≤ xBound a k)
    (hyBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        positiveLargeTailProductYClosedFactorialSplitBlockBound
            a (posNhi a) k ≤ yBound a k)
    (hsmallTwo :
      ∀ {a N : Nat}, 3000 ≤ a → positiveRectangle a N →
        positiveSmallLargeXYProductRawCleared a N 2)
    (hsmallGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) → 3 ≤ k →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k => xBound a k * yBound a k) a k)
    (htemperedGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) → 3 ≤ k →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k => xBound a k * yBound a k) a k) :
    LargeTailProductCertificate := by
  have hproductBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        3 ≤ k →
        positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct a k
          ≤ xBound a k * yBound a k := by
    intro a k ha hk _hk3
    unfold positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct
    have hx := hxBound ha hk
    have hy := hyBound ha hk
    have hYnonneg :
        0 ≤ positiveLargeTailProductYClosedFactorialSplitBlockBound
          a (posNhi a) k :=
      positiveLargeTailProductYClosedFactorialSplitBlockBound_nonneg
        a (posNhi a) k
    have hxBoundNonneg : 0 ≤ xBound a k :=
      (positiveLargeTailProductXClosedFactorialSplitBlockBound_nonneg
        a (posNhi a) k).trans hx
    exact mul_le_mul hx hy hYnonneg hxBoundNonneg
  exact
    LargeTailProductCertificate.ofFastUpperEdgeLowerNProductBoundScalarsTwoAndGeThreeNatSignLockComplement
      (xyBound := fun a k => xBound a k * yBound a k)
      hproductBound hsmallTwo hsmallGeThree htemperedGeThree

/-- Endpoint first-cell variant of the separate-`X`/`Y` product-bound route.

As above, the separate factor bounds only serve to prove a combined
`xyBound`; the `k = 2` cell is supplied by the row-only upper-edge `Y`
budget, and the true product tail starts at `k ≥ 3`. -/
theorem LargeTailProductCertificate.ofYUpperEdgeTwoEndpointAndFastUpperEdgeLowerNXYBoundScalarsGeThreeNatSignLockComplement
    {xBound yBound : Nat → Nat → ℚ}
    (hxBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        positiveLargeTailProductXClosedFactorialSplitBlockBound
            a (posNhi a) k ≤ xBound a k)
    (hyBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        positiveLargeTailProductYClosedFactorialSplitBlockBound
            a (posNhi a) k ≤ yBound a k)
    (hbudgetTwoUpper :
      ∀ {a : Nat}, 3000 ≤ a →
        positiveSmallFirstCellYUpperEdgeBudget a)
    (hsmallGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) → 3 ≤ k →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k => xBound a k * yBound a k) a k)
    (htemperedGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) → 3 ≤ k →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k => xBound a k * yBound a k) a k) :
    LargeTailProductCertificate := by
  have hproductBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        3 ≤ k →
        positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct a k
          ≤ xBound a k * yBound a k := by
    intro a k ha hk _hk3
    unfold positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct
    have hx := hxBound ha hk
    have hy := hyBound ha hk
    have hYnonneg :
        0 ≤ positiveLargeTailProductYClosedFactorialSplitBlockBound
          a (posNhi a) k :=
      positiveLargeTailProductYClosedFactorialSplitBlockBound_nonneg
        a (posNhi a) k
    have hxBoundNonneg : 0 ≤ xBound a k :=
      (positiveLargeTailProductXClosedFactorialSplitBlockBound_nonneg
        a (posNhi a) k).trans hx
    exact mul_le_mul hx hy hYnonneg hxBoundNonneg
  exact
    LargeTailProductCertificate.ofYUpperEdgeTwoEndpointAndFastUpperEdgeLowerNProductBoundGeThreeNatSignLockComplement
      (xyBound := fun a k => xBound a k * yBound a k)
      hproductBound hbudgetTwoUpper hsmallGeThree htemperedGeThree

/-- Convert the live product certificate and its lower-prefix pointwise proof
directly into the large-tail pointwise estimate used by the candidate/reserve
machinery.

This is the route-facing product bridge: for `3000 ≤ a` it uses
`LargeTailProductCertificate`, and for `2000 < a < 3000` it uses the bounded
prefix pointwise field packaged in `BoundedPositiveCertificate`. -/
theorem LargeTailProductCertificate.toPointwise
    (hproduct : LargeTailProductCertificate)
    (hprefix : PositiveSaddleLargeTailProductPrefixPointwise)
    (hsolo : PositiveSaddleLargeTailSoloNormUnitCertificate) :
    PositiveSaddleEntropyShadowLargeExpPointwiseCertificate where
  small := by
    intro a N k ha hrect hk hsmall
    have hXY :
        Xnorm N k * Ynorm N (posJ a k)
          ≤ positiveSmallLargeGcompProductTarget a N k := by
      by_cases haLarge : 3000 ≤ a
      · exact hproduct.largeSmall haLarge hrect hk hsmall
      · have haPrefix : a < 3000 := Nat.lt_of_not_ge haLarge
        exact hprefix.small ha haPrefix hrect hk hsmall
    exact
      normalizedPositiveIfTerm_le_smallEntropyShadowExp_of_XYProductTarget
        ha hrect hk hXY
  tempered := by
    intro a N k ha hrect hk htempered
    have hXY :
        Xnorm N k * Ynorm N (posJ a k)
          ≤ positiveTemperedLargeGcompProductTarget a N k := by
      by_cases haLarge : 3000 ≤ a
      · exact hproduct.largeTempered haLarge hrect hk htempered
      · have haPrefix : a < 3000 := Nat.lt_of_not_ge haLarge
        exact hprefix.tempered ha haPrefix hrect hk htempered
    exact
      normalizedPositiveIfTerm_le_temperedEntropyShadowExp_of_XYProductTarget
        ha hrect hk hXY
  soloBudget := by
    intro a N ha hrect
    exact le_positiveSoloBudget_of_mul_200000000_le_one
      (hsolo.soloNormUnit ha hrect)

/-- The large-tail solo obligation for the current canonical route.

The final assembly only needs a unit budget for the normalized solo term
`normalizedSoloTerm`.  This intentionally diverges from older Lean
proof-production wrappers which asked for
`positiveYgcompBound N a ≤ positiveLargeTailSoloTenSeventhsBound a N`: that
quotient uses a coarse `Eplus`/`Gcomp` majorant and is too lossy as a large
tail target.  The prefix strip still reuses the generated stronger surrogate,
but the analytic `a ≥ 3000` input is the direct final solo budget. -/
structure LargeTailSoloCertificate where
  largeSolo :
    ∀ {a N : Nat}, 3000 ≤ a → positiveRectangle a N →
      (200000000 : ℚ) * normalizedSoloTerm a N ≤ 1

theorem LargeTailSoloCertificate.ofSharpGcompSaddleTenSeventhsCleared
    (hsharp :
      ∀ {a N : Nat}, 3000 ≤ a → positiveRectangle a N →
        positiveLargeTailSoloSharpGcompSaddleTenSeventhsCleared a N) :
    LargeTailSoloCertificate where
  largeSolo := by
    intro a N ha hrect
    exact
      positiveLargeTailSoloNormUnit_of_sharpGcompSaddleTenSeventhsCleared
        (by omega : 2000 < a) hrect (hsharp ha hrect)

theorem LargeTailSoloCertificate.ofSharpGcompClosedFactorialSplitBlockSumTenSeventhsClearedUpperEdge
    (hsharpEdge :
      ∀ {a : Nat}, 3000 ≤ a →
        positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSumTenSeventhsCleared
          a (posNhi a)) :
    LargeTailSoloCertificate :=
  LargeTailSoloCertificate.ofSharpGcompSaddleTenSeventhsCleared
    (by
      intro a N ha hrect
      exact
        positiveLargeTailSoloSharpGcompSaddleTenSeventhsCleared_of_closedFactorialSplitBlockSumTenSeventhsCleared
          (positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSumTenSeventhsCleared_of_upperEdge
            hrect (hsharpEdge ha)))

theorem LargeTailSoloCertificate.ofSharpDeltaBudgetBlockSumTenSeventhsClearedUpperEdge
    (hdeltaEdge :
      ∀ {a : Nat}, 3000 ≤ a →
        (4 : ℚ) * (2 : ℚ)^a *
            positiveLargeTailSoloSharpDeltaBudgetBlockSum a (posNhi a)
          ≤ 29 * (a : ℚ) * c a * (10 / 7 : ℚ)^a) :
    LargeTailSoloCertificate :=
  LargeTailSoloCertificate.ofSharpGcompClosedFactorialSplitBlockSumTenSeventhsClearedUpperEdge
    (by
      intro a ha
      exact
        positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSumTenSeventhsCleared_of_deltaBudgetBlockSum
          (hdeltaEdge ha))

theorem LargeTailSoloCertificate.ofSharpLargeDegreeSplitBudgetBlockSumTenSeventhsCleared
    (hsplit :
      ∀ {a : Nat}, 3000 ≤ a →
        (4 : ℚ) * (2 : ℚ)^a *
            positiveLargeTailSoloSharpLargeDegreeSplitBudgetBlockSum a
          ≤ 29 * (a : ℚ) * c a * (10 / 7 : ℚ)^a) :
    LargeTailSoloCertificate :=
  LargeTailSoloCertificate.ofSharpGcompClosedFactorialSplitBlockSumTenSeventhsClearedUpperEdge
    (by
      intro a ha
      exact
        positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSumTenSeventhsCleared_of_largeDegreeSplitBudgetBlockSum
          ha (hsplit ha))

theorem LargeTailSoloCertificate.ofSharpLargeDegreeRemainderBlockSumTenSeventhsCleared
    (hremainder :
      ∀ {a : Nat}, 3000 ≤ a →
        (4 : ℚ) * (2 : ℚ)^a *
            positiveLargeTailSoloSharpLargeDegreeRemainderBlockSum a
          ≤ (29 / 2 : ℚ) * (a : ℚ) * c a * (10 / 7 : ℚ)^a) :
    LargeTailSoloCertificate :=
  LargeTailSoloCertificate.ofSharpGcompClosedFactorialSplitBlockSumTenSeventhsClearedUpperEdge
    (by
      intro a ha
      exact
        positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSumTenSeventhsCleared_of_largeDegreeRemainderBlockSum
          ha (hremainder ha))

theorem LargeTailSoloCertificate.ofSharpLowDegreeRemainderBlockSumTenSeventhsCleared
    (hlow :
      ∀ {a : Nat}, 3000 ≤ a →
        (4 : ℚ) * (2 : ℚ)^a *
            positiveLargeTailSoloSharpLowDegreeRemainderBlockSum a
          ≤ (29 / 4 : ℚ) * (a : ℚ) * c a * (10 / 7 : ℚ)^a) :
    LargeTailSoloCertificate :=
  LargeTailSoloCertificate.ofSharpGcompClosedFactorialSplitBlockSumTenSeventhsClearedUpperEdge
    (by
      intro a ha
      exact
        positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSumTenSeventhsCleared_of_lowDegreeRemainderBlockSum
          ha (hlow ha))

theorem LargeTailSoloCertificate.ofSharpVeryLowDegreeRemainderBlockSumTenSeventhsCleared
    (hveryLow :
      ∀ {a : Nat}, 3000 ≤ a →
        (4 : ℚ) * (2 : ℚ)^a *
            positiveLargeTailSoloSharpVeryLowDegreeRemainderBlockSum a
          ≤ (29 / 8 : ℚ) * (a : ℚ) * c a * (10 / 7 : ℚ)^a) :
    LargeTailSoloCertificate :=
  LargeTailSoloCertificate.ofSharpGcompClosedFactorialSplitBlockSumTenSeventhsClearedUpperEdge
    (by
      intro a ha
      exact
        positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSumTenSeventhsCleared_of_veryLowDegreeRemainderBlockSum
          ha (hveryLow ha))

theorem LargeTailSoloCertificate.ofSharpDeepLowDegreeRemainderBlockSumTenSeventhsCleared
    (hdeepLow :
      ∀ {a : Nat}, 3000 ≤ a →
        (4 : ℚ) * (2 : ℚ)^a *
            positiveLargeTailSoloSharpDeepLowDegreeRemainderBlockSum a
          ≤ (29 / 16 : ℚ) * (a : ℚ) * c a * (10 / 7 : ℚ)^a) :
    LargeTailSoloCertificate :=
  LargeTailSoloCertificate.ofSharpGcompClosedFactorialSplitBlockSumTenSeventhsClearedUpperEdge
    (by
      intro a ha
      exact
        positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSumTenSeventhsCleared_of_deepLowDegreeRemainderBlockSum
          ha (hdeepLow ha))

/-- The large-tail solo certificate is now closed analytically from the
deep-low remainder bound in `PositiveSaddle`. -/
theorem largeTailSoloCertificate : LargeTailSoloCertificate :=
  LargeTailSoloCertificate.ofSharpDeepLowDegreeRemainderBlockSumTenSeventhsCleared
    (by
      intro a ha
      exact
        positiveLargeTailSoloSharpDeepLowDegreeRemainderBlockSum_scaled_le_sixteenth_target
          (a := a) ha)

theorem LargeTailSoloCertificate.toNormUnitOfPrefixNorm
    (hsolo : LargeTailSoloCertificate)
    (hprefix : PositiveSaddleLargeTailSoloPrefixNormUnit) :
    PositiveSaddleLargeTailSoloNormUnitCertificate where
  soloNormUnit := by
    intro a N ha hrect
    by_cases haLarge : 3000 ≤ a
    · exact hsolo.largeSolo haLarge hrect
    · exact hprefix ha (Nat.lt_of_not_ge haLarge) hrect

theorem LargeTailSoloCertificate.toNormUnit
    {aLen : Nat}
    (hsolo : LargeTailSoloCertificate)
    (hprefix :
      PositiveSaddleLargeTailSoloFastUpperEdgeBoundPrefixChunksCertificate
        positiveLargeTailSoloUpperEdgeExactBound aLen) :
    PositiveSaddleLargeTailSoloNormUnitCertificate :=
  hsolo.toNormUnitOfPrefixNorm
    (positiveSaddleLargeTailSoloPrefixNormUnit_of_fastUpperEdgeBoundPrefixChunks
      hprefix)

/-- Final assembly from the three live obligations.

As each obligation is closed, replace the corresponding parameter here by the
concrete theorem producing it. -/
theorem completion_of_three_inputs
    (hbounded : BoundedPositiveCertificate)
    (hproduct : LargeTailProductCertificate)
    (hsolo : LargeTailSoloCertificate) :
    CoefficientNegativity := by
  let soloNorm : PositiveSaddleLargeTailSoloNormUnitCertificate :=
    hsolo.toNormUnitOfPrefixNorm hbounded.soloPrefixNormUnit
  let pointwise : PositiveSaddleEntropyShadowLargeExpPointwiseCertificate :=
    hproduct.toPointwise hbounded.productPrefixPointwise soloNorm
  exact
    coefficientNegativity_of_positiveSaddleCertificate
      (hbounded.toPositiveSaddleCertificate
        pointwise
        positiveSaddleLargeTailCandidateRawClearedUnitReserveBoundsCertificate_hybridClosed)

/-- Finite-solo bridge for the sharp direct-saddle route.

The finite window still needs a proof of the sharp saddle-cleared predicate,
but after `PositiveSaddle`'s scalar estimate is generalized to `a ≥ 401`,
that predicate is enough to supply the exact bounded solo budget consumed by
`BoundedPositiveCertificate.ofDirectSaddle`. -/
theorem finiteSoloBudget_of_sharpGcompSaddleTenSeventhsCleared
    (hsharp :
      ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        positiveLargeTailSoloSharpGcompSaddleTenSeventhsCleared a N) :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget := by
  intro a N ha h2000 hrect
  have hunit :
      (200000000 : ℚ) * normalizedSoloTerm a N ≤ 1 :=
    positiveLargeTailSoloNormUnit_of_sharpGcompSaddleTenSeventhsCleared_of_ge_401
      ha hrect (hsharp ha h2000 hrect)
  rw [normalizedSoloTerm_eq_dyadic_Ynorm
    (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect)
    (by omega : 1 ≤ a)] at hunit
  exact le_positiveSoloBudget_of_mul_200000000_le_one hunit

/-- Analytic sharp finite-solo saddle estimate on the upper part of the
bounded window.

This is the finite-window payoff from lowering the constant-budget sharp solo
split in `PositiveSaddle` from `a ≥ 2001` to `a ≥ 802`.  The argument is the
same upper-edge monotonicity path used by the solo prefix proof, but it now
applies inside the bounded strip. -/
theorem finiteSoloSharpGcompSaddleTenSeventhsCleared_of_const
    {a N : Nat} (ha : 802 ≤ a) (hrect : positiveRectangle a N) :
    positiveLargeTailSoloSharpGcompSaddleTenSeventhsCleared a N := by
  have hdelta :
      (4 : ℚ) * (2 : ℚ)^a *
          positiveLargeTailSoloSharpDeltaBudgetBlockSum a (posNhi a)
        ≤ 29 * (a : ℚ) * c a * (10 / 7 : ℚ)^a := by
    have hdelta_le :
        positiveLargeTailSoloSharpDeltaBudgetBlockSum a (posNhi a)
          ≤ positiveLargeTailSoloSharpLargeDegreeSplitBudgetBlockSum a :=
      positiveLargeTailSoloSharpDeltaBudgetBlockSum_upperEdge_le_largeDegreeSplit
        (a := a) (by omega : 361 ≤ a)
    have hscale : 0 ≤ (4 : ℚ) * (2 : ℚ)^a := by
      positivity
    exact (mul_le_mul_of_nonneg_left hdelta_le hscale).trans
      (positiveLargeTailSoloSharpLargeDegreeSplitBudgetBlockSum_scaled_le_target_of_const
        (a := a) ha)
  have hEdge :
      positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSumTenSeventhsCleared
        a (posNhi a) :=
    positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSumTenSeventhsCleared_of_deltaBudgetBlockSum
      hdelta
  exact
    positiveLargeTailSoloSharpGcompSaddleTenSeventhsCleared_of_closedFactorialSplitBlockSumTenSeventhsCleared
      (positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSumTenSeventhsCleared_of_upperEdge
        hrect hEdge)

/-- Finite solo after the analytic `802 ≤ a` suffix has been inserted.

The only remaining finite-solo input is now the lower strip `401 ≤ a ≤ 801`.
This is a strict reduction of the earlier `401 ≤ a ≤ 2000` theorem-facing
obligation. -/
theorem finiteSoloBudget_of_sharpGcompSaddleTenSeventhsCleared_lowStrip
    (hsharpLow :
      ∀ {a N : Nat}, 401 ≤ a → a ≤ 801 → positiveRectangle a N →
        positiveLargeTailSoloSharpGcompSaddleTenSeventhsCleared a N) :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget :=
  finiteSoloBudget_of_sharpGcompSaddleTenSeventhsCleared
    (by
      intro a N ha h2000 hrect
      by_cases hupper : 802 ≤ a
      · exact finiteSoloSharpGcompSaddleTenSeventhsCleared_of_const
          (a := a) (N := N) hupper hrect
      · exact hsharpLow ha (by omega : a ≤ 801) hrect)

/-- Current completion theorem after the direct product route.

The finite and prefix product obligations and the large-tail product/solo
obligations are now concrete.  The remaining theorem-facing inputs are exactly
the bounded finite solo budget and the solo prefix norm-unit field. -/
theorem completion_of_directSaddle
    (soloY :
      ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget)
    (soloPrefix : PositiveSaddleLargeTailSoloPrefixNormUnit) :
    CoefficientNegativity :=
  completion_of_three_inputs
    (BoundedPositiveCertificate.ofDirectSaddle soloY soloPrefix)
    LargeTailProductCertificate.ofDirectSaddle
    largeTailSoloCertificate

/-- Current strongest completion wrapper.

All direct-saddle product obligations and all large/prefix solo obligations
are concrete.  The only remaining theorem-facing input is the finite solo
budget for `401 ≤ a ≤ 2000`. -/
theorem completion_of_directSaddle_finiteSolo
    (soloY :
      ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget) :
    CoefficientNegativity :=
  completion_of_directSaddle soloY
    positiveSaddleLargeTailSoloPrefixNormUnit_of_sharpConst

/-- Current strongest completion wrapper after inserting the analytic finite
solo suffix.

All direct-saddle product obligations, all large/prefix solo obligations, and
the finite solo range `802 ≤ a ≤ 2000` are concrete.  The only remaining
theorem-facing input is the sharp finite-solo saddle target on
`401 ≤ a ≤ 801`. -/
theorem completion_of_directSaddle_finiteSolo_lowStrip
    (hsharpLow :
      ∀ {a N : Nat}, 401 ≤ a → a ≤ 801 → positiveRectangle a N →
        positiveLargeTailSoloSharpGcompSaddleTenSeventhsCleared a N) :
    CoefficientNegativity :=
  completion_of_directSaddle_finiteSolo
    (finiteSoloBudget_of_sharpGcompSaddleTenSeventhsCleared_lowStrip
      hsharpLow)

end Prop51
