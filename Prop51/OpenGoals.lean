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
    LargeTailProductCertificate where
  largeSmall := by
    intro a N k ha hrect hk hsmallN
    have hsmallEdge : k ≤ ceilSqrt (posNhi a) :=
      hsmallN.trans (ceilSqrt_mono hrect.2)
    have hprod :
        positiveXplusYProductGcompBound a N k
          ≤ positiveSmallLargeGcompProductTarget a N k :=
      positiveXplusYProductGcompBound_le_smallLargeGcompProductTarget_of_fastUpperEdgeLowerN
        (by omega : 2000 < a) hrect hk
        (hsmall ha hk hsmallEdge)
    exact
      (Xnorm_mul_Ynorm_le_of_Xplus_mul_Ynorm
        (XplusYnorm_le_positiveXplusYProductGcompBound a N k)).trans hprod
  largeTempered := by
    intro a N k ha hrect hk htemperedN
    have htemperedEdge : ceilSqrt (posNlo a) < k :=
      lt_of_le_of_lt (ceilSqrt_mono hrect.1) htemperedN
    have hprod :
        positiveXplusYProductGcompBound a N k
          ≤ positiveTemperedLargeGcompProductTarget a N k :=
      positiveXplusYProductGcompBound_le_temperedLargeGcompProductTarget_of_fastUpperEdgeLowerN
        (by omega : 2000 < a) hrect hk
        (htempered ha hk htemperedEdge)
    exact
      (Xnorm_mul_Ynorm_le_of_Xplus_mul_Ynorm
        (XplusYnorm_le_positiveXplusYProductGcompBound a N k)).trans hprod

/-- Convert the live product certificate and its lower-prefix scalar chunks
directly into the large-tail pointwise estimate used by the candidate/reserve
machinery.

This is the route-facing product bridge: for `3000 ≤ a` it uses
`LargeTailProductCertificate`, and for `2000 < a < 3000` it uses the bounded
prefix chunks packaged in `BoundedPositiveCertificate`. -/
theorem LargeTailProductCertificate.toPointwise
    {aLen kLen : Nat}
    (hproduct : LargeTailProductCertificate)
    (hprefix :
      PositiveSaddleLargeTailProductFastUpperEdgeLowerNProductBoundPrefixChunksCertificate
        (fun a k =>
          positiveLargeTailProductXUpperEdgeExactBound a k *
            positiveLargeTailProductYUpperEdgeExactBound a k)
        aLen kLen)
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
  let soloNorm : PositiveSaddleLargeTailSoloNormUnitCertificate :=
    hsolo.toNormUnit hbounded.soloPrefix
  let pointwise : PositiveSaddleEntropyShadowLargeExpPointwiseCertificate :=
    hproduct.toPointwise hbounded.productPrefix soloNorm
  exact
    coefficientNegativity_of_positiveSaddleTangentProductBudgetCertificate
      (hbounded.cert.toTangentProductBudgetCertificate_of_pointwise
        pointwise
        positiveSaddleLargeTailCandidateRawClearedUnitReserveBoundsCertificate_hybridClosed)

end Prop51
