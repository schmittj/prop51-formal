import Prop51.Main
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
`LargeTailProductCertificate.ofRawCleared`, while the stronger legacy
upper-edge/lower-`N` `Gcomp` scalar route remains available only as a
compatibility constructor below. -/
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
theorem positiveLargeTailProductYUpperEdgeExactBound_two_eq_shiftedSolo
    (a : Nat) :
    positiveLargeTailProductYUpperEdgeExactBound a 2 =
      positiveLargeTailSoloGcompClosedFactorialSplitBlockSum
        (posJ a 2) (posNhi a) := by
  rfl

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
completion-facing `LargeTailProductCertificate`: the `k = 2` cell is routed
through the direct first-cell `Qq` budget above, while the `k ≥ 3` small and
tempered tails are supplied by the old scalar fields.  The final target still
uses the combined actual raw product and the sign-lock split. -/
theorem LargeTailProductCertificate.ofClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerN
    (product :
      PositiveSaddleLargeTailProductClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerNCertificate) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofYUpperEdgeTwoEndpointAndClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerNGeThree
    (by
      intro a ha
      have hk : 2 ∈ positiveKRange a := by
        refine mem_positiveKRange.mpr ⟨by omega, ?_⟩
        unfold posKmax
        rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 10)]
        omega
      have hsmall : 2 ≤ ceilSqrt (posNhi a) := by
        have hlt : 1 < ceilSqrt (posNhi a) :=
          lt_ceilSqrt_of_sq_lt (n := posNhi a) (k := 1) (by
            unfold posNhi
            omega)
        omega
      exact
        positiveSmallFirstCellYUpperEdgeBudget_of_exactSmallProductScalar
          (by omega : 2000 < a)
          (by
            have h := product.smallScalar (by omega : 2000 < a) hk hsmall
            simpa [
              positiveLargeTailProductXUpperEdgeExactBound,
              positiveLargeTailProductYUpperEdgeExactBound,
              positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar,
              positiveLargeTailSmallProductClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerN,
              mul_assoc,
            ] using h))
    (by
      intro a k ha hk hsmall _hk3
      exact product.smallScalar (by omega : 2000 < a) hk hsmall)
    (by
      intro a k ha hk htempered _hnotLock _hk3
      exact product.temperedScalar (by omega : 2000 < a) hk htempered)

/-- Direct adapter from the existing product-bound certificate structure to
the completion-facing product certificate.

This is still stronger than the preferred first-cell/sign-lock-complement
route below: the supplied `product` certificate proves the upper-edge/lower-`N`
scalar inequalities for every live small and tempered cell.  The adapter is
kept because generated and hybrid large-tail certificates already package
exactly these fields, and this theorem lets such packages feed
`Completion.lean` without unpacking their fields by hand. -/
theorem LargeTailProductCertificate.ofFastUpperEdgeLowerNProductBoundCertificate
    {xyBound : Nat → Nat → ℚ}
    (product :
      PositiveSaddleLargeTailProductFastUpperEdgeLowerNProductBoundCertificate
        xyBound) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofFastUpperEdgeLowerNProductBoundScalarsNatSignLockComplement
    (xyBound := xyBound)
    (by
      intro a k ha hk
      exact product.productBound (by omega : 2000 < a) hk)
    (by
      intro a k ha hk hsmall
      exact product.smallScalar (by omega : 2000 < a) hk hsmall)
    (by
      intro a k ha hk htempered _hnotLock
      exact product.temperedScalar (by omega : 2000 < a) hk htempered)

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

end Prop51
