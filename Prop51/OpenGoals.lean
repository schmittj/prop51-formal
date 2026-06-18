import Prop51.Main

namespace Prop51

/-!
`OpenGoals` is the machine-readable dashboard for the remaining route to the
final theorem.

The intended split is `401 ≤ a < 3000` for bounded checking and `3000 ≤ a` for
the analytic tail.  The currently available Lean assembly still has separate
generated interfaces for the old `401 ≤ a ≤ 2000` finite window and the
`2001 ≤ a < 3000` prefix strip; this dashboard packages both on the bounded
side so the product and solo inputs are the genuine large-`a` analytic fields.
-/

/-- The bounded positive-saddle obligation for the current canonical route.

At present this wraps the existing active finite-window certificate together
with the lower-prefix product/solo scalar chunks.  The target shape is a single
checker-backed certificate for all `401 ≤ a < 3000`. -/
structure BoundedPositiveCertificate where
  tangentRowLen : Nat
  soloSaddleRowLen : Nat
  soloBudgetRowLen : Nat
  edgeRowLen : Nat
  tangentNLen : Nat
  soloSaddleNLen : Nat
  soloBudgetNLen : Nat
  tangentKLen : Nat
  edgeKLen : Nat
  cert :
    PositiveSaddleFixedFiniteWindowActiveAnalyticProductTangentSoloNFixedEdgeKChunkedAuditCertificate
      tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      tangentNLen soloSaddleNLen soloBudgetNLen tangentKLen edgeKLen
  productPrefixALen : Nat
  productPrefixKLen : Nat
  productPrefix :
    PositiveSaddleLargeTailProductFastUpperEdgeLowerNProductBoundPrefixChunksCertificate
      (fun a k =>
        positiveLargeTailProductXUpperEdgeExactBound a k *
          positiveLargeTailProductYUpperEdgeExactBound a k)
      productPrefixALen productPrefixKLen
  soloPrefixALen : Nat
  soloPrefix :
    PositiveSaddleLargeTailSoloFastUpperEdgeBoundPrefixChunksCertificate
      positiveLargeTailSoloUpperEdgeExactBound
      soloPrefixALen

/-- The large-tail product obligation for the current canonical route. -/
structure LargeTailProductCertificate where
  largeSmall :
    ∀ {a k : Nat}, 3000 ≤ a →
      k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) →
        positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
          (fun a k =>
            positiveLargeTailProductXUpperEdgeExactBound a k *
              positiveLargeTailProductYUpperEdgeExactBound a k) a k
  largeTempered :
    ∀ {a k : Nat}, 3000 ≤ a →
      k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
        positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
          (fun a k =>
            positiveLargeTailProductXUpperEdgeExactBound a k *
              positiveLargeTailProductYUpperEdgeExactBound a k) a k

theorem LargeTailProductCertificate.toFullHybrid
    {aLen kLen : Nat}
    (hproduct : LargeTailProductCertificate)
    (hprefix :
      PositiveSaddleLargeTailProductFastUpperEdgeLowerNProductBoundPrefixChunksCertificate
        (fun a k =>
          positiveLargeTailProductXUpperEdgeExactBound a k *
            positiveLargeTailProductYUpperEdgeExactBound a k)
        aLen kLen) :
    PositiveSaddleLargeTailProductFastUpperEdgeLowerNXYBoundFullHybridCertificate
      positiveLargeTailProductXUpperEdgeExactBound
      positiveLargeTailProductYUpperEdgeExactBound
      aLen kLen where
  boundPrefixChunks :=
    positiveSaddleLargeTailProductExactUpperEdgePrefixBoundChunksCertificate
      hprefix.aLenPos hprefix.kLenPos
  scalarPrefixChunks := hprefix
  largeXBound := by
    intro a k _ha _hk
    exact le_rfl
  largeYBound := by
    intro a k _ha _hk
    exact le_rfl
  largeSmall := hproduct.largeSmall
  largeTempered := hproduct.largeTempered

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

theorem LargeTailSoloCertificate.toNormUnit
    {aLen : Nat}
    (hsolo : LargeTailSoloCertificate)
    (hprefix :
      PositiveSaddleLargeTailSoloFastUpperEdgeBoundPrefixChunksCertificate
        positiveLargeTailSoloUpperEdgeExactBound aLen) :
    PositiveSaddleLargeTailSoloNormUnitCertificate where
  soloNormUnit := by
    intro a N ha hrect
    by_cases haLarge : 3000 ≤ a
    · exact hsolo.largeSolo haLarge hrect
    · have haPrefix : a < 3000 := Nat.lt_of_not_ge haLarge
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
          positiveYgcompBound N a ≤
            positiveLargeTailSoloTenSeventhsBound a N :=
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

/-- Final assembly from the three live obligations.

As each obligation is closed, replace the corresponding parameter here by the
concrete theorem producing it. -/
theorem completion_of_three_inputs
    (hbounded : BoundedPositiveCertificate)
    (hproduct : LargeTailProductCertificate)
    (hsolo : LargeTailSoloCertificate) :
    CoefficientNegativity := by
  let productBounds :
      PositiveSaddleLargeTailProductBoundsCertificate
        positiveLargeTailProductXBlockBound positiveLargeTailProductYBlockBound
        positiveLargeTailProductXBlockBound positiveLargeTailProductYBlockBound :=
    ((hproduct.toFullHybrid hbounded.productPrefix).toHybridCertificate
      |>.toProductBoundCertificate
      |>.toProductBoundsCertificate)
  let soloNorm : PositiveSaddleLargeTailSoloNormUnitCertificate :=
    hsolo.toNormUnit hbounded.soloPrefix
  let pointwise : PositiveSaddleEntropyShadowLargeExpPointwiseCertificate :=
    positiveSaddleEntropyShadowLargeExpPointwiseCertificate_of_productBounds_soloNormUnit
      productBounds soloNorm
  exact
    coefficientNegativity_of_positiveSaddleTangentProductBudgetCertificate
      (hbounded.cert.toTangentProductBudgetCertificate_of_pointwise
        pointwise
        positiveSaddleLargeTailCandidateRawClearedUnitReserveBoundsCertificate_hybridClosed)

end Prop51
