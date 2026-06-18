import Prop51.Main

namespace Prop51

/-!
`OpenGoals` is the machine-readable dashboard for the remaining route to the
final theorem.

The intended split is `401 ≤ a < 3000` for bounded checking and `3000 ≤ a` for
the analytic tail.  The currently available Lean assembly still packages
`401 ≤ a ≤ 2000` in the finite certificate and the `2001 ≤ a < 3000` prefix in
the full-hybrid product/solo certificates.  This is a Lean-side packaging
difference from the latest TeX route; the next bounded-checker step should merge
those prefixes into `BoundedPositiveCertificate`.
-/

/-- The bounded positive-saddle obligation for the current canonical route.

At present this wraps the existing active finite-window certificate.  The target
shape is a single checker-backed certificate for all `401 ≤ a < 3000`. -/
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

/-- The large-tail product obligation for the current canonical route.

The full-hybrid certificate contains generated prefix chunks below `a = 3000`
and analytic fields for `3000 ≤ a`. -/
structure LargeTailProductCertificate where
  aLen : Nat
  kLen : Nat
  cert :
    PositiveSaddleLargeTailProductFastUpperEdgeLowerNXYBoundFullHybridCertificate
      positiveLargeTailProductXUpperEdgeExactBound
      positiveLargeTailProductYUpperEdgeExactBound
      aLen kLen

/-- The large-tail solo obligation for the current canonical route.

The full-hybrid certificate contains generated prefix chunks below `a = 3000`
and analytic fields for `3000 ≤ a`. -/
structure LargeTailSoloCertificate where
  aLen : Nat
  cert :
    PositiveSaddleLargeTailSoloFastUpperEdgeBoundFullHybridCertificate
      positiveLargeTailSoloUpperEdgeExactBound
      aLen

/-- Final assembly from the three live obligations.

As each obligation is closed, replace the corresponding parameter here by the
concrete theorem producing it. -/
theorem completion_of_three_inputs
    (hbounded : BoundedPositiveCertificate)
    (hproduct : LargeTailProductCertificate)
    (hsolo : LargeTailSoloCertificate) :
    CoefficientNegativity :=
  coefficientNegativity_of_positiveSaddleFixedFiniteWindowActiveAnalyticProductTangentSoloNFixedEdgeKChunkedTemperedSharpTopOffsetHybridRatioChunkedXYBoundFullHybridSoloBoundFullHybridTail
    hbounded.cert hproduct.cert hsolo.cert

end Prop51
