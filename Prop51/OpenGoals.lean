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

The TeX-side target is the direct `(10/7)^a` solo envelope at the upper
rectangle edge.  Earlier Lean proof-production layers also expose a stronger
`partialExpUpperFast` scalar target; the dashboard keeps that stronger target
only on the bounded prefix side, where it is already part of the generated
certificate, and asks the analytic large-`a` input for the direct
ten-sevenths statement. -/
structure LargeTailSoloCertificate where
  largeSolo :
    ∀ {a : Nat}, 3000 ≤ a →
      positiveLargeTailSoloGcompClosedFactorialSplitBlockSumTenSeventhsCleared
        a (posNhi a)

theorem LargeTailSoloCertificate.toUpperEdgeTenSevenths
    {aLen : Nat}
    (hsolo : LargeTailSoloCertificate)
    (hprefix :
      PositiveSaddleLargeTailSoloFastUpperEdgeBoundPrefixChunksCertificate
        positiveLargeTailSoloUpperEdgeExactBound aLen) :
    ∀ {a : Nat}, 2000 < a →
      positiveLargeTailSoloGcompClosedFactorialSplitBlockSumTenSeventhsCleared
        a (posNhi a) := by
  intro a ha
  by_cases haLarge : 3000 ≤ a
  · exact hsolo.largeSolo haLarge
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
    exact
      positiveLargeTailSoloGcompClosedFactorialSplitBlockSumTenSeventhsCleared_of_fastCleared
        ha hfast

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
  exact
  coefficientNegativity_of_positiveSaddleFixedFiniteWindowActiveAnalyticProductTangentSoloNFixedEdgeKChunkedAuditCertificate
    hbounded.cert
    (positiveSaddleLargeTailAuditCertificate_of_product_soloGcompClosedFactorialSplitBlockSumTenSeventhsCleared_upperEdge
      productBounds
      (hsolo.toUpperEdgeTenSevenths hbounded.soloPrefix))

end Prop51
