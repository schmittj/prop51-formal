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

/-- The large-tail solo obligation for the current canonical route. -/
structure LargeTailSoloCertificate where
  largeSolo :
    ∀ {a : Nat}, 3000 ≤ a →
      positiveLargeTailSoloFastUpperEdgeBoundScalar
        positiveLargeTailSoloUpperEdgeExactBound a

theorem LargeTailSoloCertificate.toFullHybrid
    {aLen : Nat}
    (hsolo : LargeTailSoloCertificate)
    (hprefix :
      PositiveSaddleLargeTailSoloFastUpperEdgeBoundPrefixChunksCertificate
        positiveLargeTailSoloUpperEdgeExactBound aLen) :
    PositiveSaddleLargeTailSoloFastUpperEdgeBoundFullHybridCertificate
      positiveLargeTailSoloUpperEdgeExactBound
      aLen :=
  hprefix.toExactBoundFullHybridCertificate hsolo.largeSolo

/-- Final assembly from the three live obligations.

As each obligation is closed, replace the corresponding parameter here by the
concrete theorem producing it. -/
theorem completion_of_three_inputs
    (hbounded : BoundedPositiveCertificate)
    (hproduct : LargeTailProductCertificate)
    (hsolo : LargeTailSoloCertificate) :
    CoefficientNegativity :=
  coefficientNegativity_of_positiveSaddleFixedFiniteWindowActiveAnalyticProductTangentSoloNFixedEdgeKChunkedTemperedSharpTopOffsetHybridRatioChunkedXYBoundFullHybridSoloBoundFullHybridTail
    hbounded.cert
    (hproduct.toFullHybrid hbounded.productPrefix)
    (hsolo.toFullHybrid hbounded.soloPrefix)

end Prop51
