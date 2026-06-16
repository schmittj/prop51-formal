import Prop51.PositiveSaddle

namespace Prop51

/-!
# Default finite-window chunks for the positive-saddle certificate

Generated finite-window §6 certificates can use these 100-row chunks for
`401 ≤ a ≤ 2000`.  The Boolean checks for each chunk remain separate; this
file only proves that the chosen half-open intervals cover the whole finite
window.
-/

/-- Default 100-row chunks covering the finite positive-saddle window
`401 ≤ a ≤ 2000`. -/
def positiveSaddleDefaultChunks : List (Nat × Nat) :=
  [(401, 100), (501, 100), (601, 100), (701, 100),
   (801, 100), (901, 100), (1001, 100), (1101, 100),
   (1201, 100), (1301, 100), (1401, 100), (1501, 100),
   (1601, 100), (1701, 100), (1801, 100), (1901, 100)]

theorem positiveSaddleDefaultChunks_cover :
    PositiveSaddleFiniteWindowChunkCover positiveSaddleDefaultChunks := by
  intro a ha h2000
  by_cases h501 : a < 501
  · refine ⟨(401, 100), ?_, ?_, ?_⟩
    · norm_num [positiveSaddleDefaultChunks]
    · omega
    · omega
  · by_cases h601 : a < 601
    · refine ⟨(501, 100), ?_, ?_, ?_⟩
      · norm_num [positiveSaddleDefaultChunks]
      · omega
      · omega
    · by_cases h701 : a < 701
      · refine ⟨(601, 100), ?_, ?_, ?_⟩
        · norm_num [positiveSaddleDefaultChunks]
        · omega
        · omega
      · by_cases h801 : a < 801
        · refine ⟨(701, 100), ?_, ?_, ?_⟩
          · norm_num [positiveSaddleDefaultChunks]
          · omega
          · omega
        · by_cases h901 : a < 901
          · refine ⟨(801, 100), ?_, ?_, ?_⟩
            · norm_num [positiveSaddleDefaultChunks]
            · omega
            · omega
          · by_cases h1001 : a < 1001
            · refine ⟨(901, 100), ?_, ?_, ?_⟩
              · norm_num [positiveSaddleDefaultChunks]
              · omega
              · omega
            · by_cases h1101 : a < 1101
              · refine ⟨(1001, 100), ?_, ?_, ?_⟩
                · norm_num [positiveSaddleDefaultChunks]
                · omega
                · omega
              · by_cases h1201 : a < 1201
                · refine ⟨(1101, 100), ?_, ?_, ?_⟩
                  · norm_num [positiveSaddleDefaultChunks]
                  · omega
                  · omega
                · by_cases h1301 : a < 1301
                  · refine ⟨(1201, 100), ?_, ?_, ?_⟩
                    · norm_num [positiveSaddleDefaultChunks]
                    · omega
                    · omega
                  · by_cases h1401 : a < 1401
                    · refine ⟨(1301, 100), ?_, ?_, ?_⟩
                      · norm_num [positiveSaddleDefaultChunks]
                      · omega
                      · omega
                    · by_cases h1501 : a < 1501
                      · refine ⟨(1401, 100), ?_, ?_, ?_⟩
                        · norm_num [positiveSaddleDefaultChunks]
                        · omega
                        · omega
                      · by_cases h1601 : a < 1601
                        · refine ⟨(1501, 100), ?_, ?_, ?_⟩
                          · norm_num [positiveSaddleDefaultChunks]
                          · omega
                          · omega
                        · by_cases h1701 : a < 1701
                          · refine ⟨(1601, 100), ?_, ?_, ?_⟩
                            · norm_num [positiveSaddleDefaultChunks]
                            · omega
                            · omega
                          · by_cases h1801 : a < 1801
                            · refine ⟨(1701, 100), ?_, ?_, ?_⟩
                              · norm_num [positiveSaddleDefaultChunks]
                              · omega
                              · omega
                            · by_cases h1901 : a < 1901
                              · refine ⟨(1801, 100), ?_, ?_, ?_⟩
                                · norm_num [positiveSaddleDefaultChunks]
                                · omega
                                · omega
                              · refine ⟨(1901, 100), ?_, ?_, ?_⟩
                                · norm_num [positiveSaddleDefaultChunks]
                                · omega
                                · omega

/-- Constructor for the default chunk cover, leaving only the five families of
Boolean chunk checks to generated certificates. -/
theorem positiveSaddleDefaultFiniteWindowChunks
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true)
    (hsolo :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloGcompRange chunk.1 chunk.2 = true)
    (hedge :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true) :
    PositiveSaddleXplusGcompTangentFiniteWindowChunks
      positiveSaddleDefaultChunks where
  cover := positiveSaddleDefaultChunks_cover
  smallXplusGcompChunks := hsmall
  temperedXplusGcompChunks := htempered
  smallTangentEdgeChunks := htangent
  soloGcompChunks := hsolo
  edgeBudgetChunks := hedge

/-- Direct-tail certificate specialized to the default finite-window chunks. -/
abbrev PositiveSaddleXplusGcompTangentDefaultChunkedRangeCertificate : Prop :=
  PositiveSaddleXplusGcompTangentChunkedRangeCertificate
    positiveSaddleDefaultChunks

/-- Geometric entropy-tail certificate specialized to the default
finite-window chunks. -/
abbrev PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyGeometricCertificate
    (smallExp temperedExp : Nat → Nat → ℚ)
    (smallRatio temperedRatio : Nat → ℚ) : Prop :=
  PositiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricCertificate
    positiveSaddleDefaultChunks smallExp temperedExp smallRatio temperedRatio

/-- Geometric reserve entropy-tail certificate specialized to the default
finite-window chunks. -/
abbrev PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyGeometricReserveCertificate
    (smallExp temperedExp : Nat → Nat → ℚ)
    (smallRatio temperedRatio : Nat → ℚ) : Prop :=
  PositiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricReserveCertificate
    positiveSaddleDefaultChunks smallExp temperedExp smallRatio temperedRatio

/-- Quotient reserve entropy-tail certificate specialized to the default
finite-window chunks. -/
abbrev PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyQuotientReserveCertificate
    (smallExp temperedExp : Nat → Nat → ℚ)
    (smallRatio temperedRatio : Nat → ℚ) : Prop :=
  PositiveSaddleXplusGcompTangentChunkedRangeEntropyQuotientReserveCertificate
    positiveSaddleDefaultChunks smallExp temperedExp smallRatio temperedRatio

/-- Raw-base quotient reserve entropy-tail certificate specialized to the
default finite-window chunks. -/
abbrev PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyRawQuotientReserveCertificate
    (smallExp temperedExp : Nat → Nat → ℚ)
    (smallRatio temperedRatio : Nat → ℚ) : Prop :=
  PositiveSaddleXplusGcompTangentChunkedRangeEntropyRawQuotientReserveCertificate
    positiveSaddleDefaultChunks smallExp temperedExp smallRatio temperedRatio

/-- Mixed-direction geometric reserve entropy-tail certificate specialized to
the default finite-window chunks. -/
abbrev PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyMixedGeometricReserveCertificate
    (smallExp temperedExp : Nat → Nat → ℚ)
    (smallRatio temperedReverseRatio : Nat → ℚ) : Prop :=
  PositiveSaddleXplusGcompTangentChunkedRangeEntropyMixedGeometricReserveCertificate
    positiveSaddleDefaultChunks smallExp temperedExp smallRatio temperedReverseRatio

/-- Mixed-direction raw-quotient reserve entropy-tail certificate specialized
to the default finite-window chunks. -/
abbrev PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyMixedRawQuotientReserveCertificate
    (smallExp temperedExp : Nat → Nat → ℚ)
    (smallRatio temperedReverseRatio : Nat → ℚ) : Prop :=
  PositiveSaddleXplusGcompTangentChunkedRangeEntropyMixedRawQuotientReserveCertificate
    positiveSaddleDefaultChunks smallExp temperedExp smallRatio temperedReverseRatio

/-- Concrete variable-cutoff mixed raw-quotient reserve entropy-tail
certificate specialized to the default finite-window chunks. -/
abbrev PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate
    (smallRatio temperedReverseRatio : Nat → ℚ) : Prop :=
  PositiveSaddleXplusGcompTangentChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate
    positiveSaddleDefaultChunks smallRatio temperedReverseRatio

/-- Concrete split-tempered large-exp raw-quotient reserve entropy-tail
certificate specialized to the default finite-window chunks. -/
abbrev PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
    (temperedSplit : Nat → Nat)
    (smallRatio temperedLowerRatio temperedUpperReverseRatio : Nat → ℚ) :
    Prop :=
  PositiveSaddleXplusGcompTangentChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
    positiveSaddleDefaultChunks temperedSplit smallRatio temperedLowerRatio
    temperedUpperReverseRatio

theorem positiveSaddleDefaultChunkedRangeCertificate
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true)
    (hsolo :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloGcompRange chunk.1 chunk.2 = true)
    (hedge :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (entropyTail :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeCertificate where
  finiteChunks :=
    positiveSaddleDefaultFiniteWindowChunks
      hsmall htempered htangent hsolo hedge
  entropyTail := entropyTail

theorem positiveSaddleDefaultChunkedRangeEntropyGeometricCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true)
    (hsolo :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloGcompRange chunk.1 chunk.2 = true)
    (hedge :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (entropyGeometric :
      PositiveSaddleEntropyShadowExpGeometricBudgetCertificate
        smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyGeometricCertificate
      smallExp temperedExp smallRatio temperedRatio where
  finiteChunks :=
    positiveSaddleDefaultFiniteWindowChunks
      hsmall htempered htangent hsolo hedge
  entropyGeometric := entropyGeometric

theorem positiveSaddleDefaultChunkedRangeEntropyGeometricReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true)
    (hsolo :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloGcompRange chunk.1 chunk.2 = true)
    (hedge :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (entropyGeometricReserve :
      PositiveSaddleEntropyShadowExpGeometricReserveCertificate
        smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyGeometricReserveCertificate
      smallExp temperedExp smallRatio temperedRatio where
  finiteChunks :=
    positiveSaddleDefaultFiniteWindowChunks
      hsmall htempered htangent hsolo hedge
  entropyGeometricReserve := entropyGeometricReserve

theorem positiveSaddleDefaultChunkedRangeEntropyQuotientReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true)
    (hsolo :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloGcompRange chunk.1 chunk.2 = true)
    (hedge :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (entropyQuotientReserve :
      PositiveSaddleEntropyShadowExpQuotientReserveCertificate
        smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio where
  finiteChunks :=
    positiveSaddleDefaultFiniteWindowChunks
      hsmall htempered htangent hsolo hedge
  entropyQuotientReserve := entropyQuotientReserve

theorem positiveSaddleDefaultChunkedRangeEntropyRawQuotientReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true)
    (hsolo :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloGcompRange chunk.1 chunk.2 = true)
    (hedge :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (entropyRawQuotientReserve :
      PositiveSaddleEntropyShadowExpRawQuotientReserveCertificate
        smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyRawQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio where
  finiteChunks :=
    positiveSaddleDefaultFiniteWindowChunks
      hsmall htempered htangent hsolo hedge
  entropyRawQuotientReserve := entropyRawQuotientReserve

theorem positiveSaddleDefaultChunkedRangeEntropyMixedGeometricReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedReverseRatio : Nat → ℚ}
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true)
    (hsolo :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloGcompRange chunk.1 chunk.2 = true)
    (hedge :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (entropyMixedGeometricReserve :
      PositiveSaddleEntropyShadowExpMixedGeometricReserveCertificate
        smallExp temperedExp smallRatio temperedReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyMixedGeometricReserveCertificate
      smallExp temperedExp smallRatio temperedReverseRatio where
  finiteChunks :=
    positiveSaddleDefaultFiniteWindowChunks
      hsmall htempered htangent hsolo hedge
  entropyMixedGeometricReserve := entropyMixedGeometricReserve

theorem positiveSaddleDefaultChunkedRangeEntropyMixedRawQuotientReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedReverseRatio : Nat → ℚ}
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true)
    (hsolo :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloGcompRange chunk.1 chunk.2 = true)
    (hedge :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (entropyMixedRawQuotientReserve :
      PositiveSaddleEntropyShadowExpMixedRawQuotientReserveCertificate
        smallExp temperedExp smallRatio temperedReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyMixedRawQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedReverseRatio where
  finiteChunks :=
    positiveSaddleDefaultFiniteWindowChunks
      hsmall htempered htangent hsolo hedge
  entropyMixedRawQuotientReserve := entropyMixedRawQuotientReserve

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate
    {smallRatio temperedReverseRatio : Nat → ℚ}
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true)
    (hsolo :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloGcompRange chunk.1 chunk.2 = true)
    (hedge :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (entropyLargeMixedRawQuotientReserve :
      PositiveSaddleEntropyShadowLargeExpMixedRawQuotientReserveCertificate
        smallRatio temperedReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate
      smallRatio temperedReverseRatio where
  finiteChunks :=
    positiveSaddleDefaultFiniteWindowChunks
      hsmall htempered htangent hsolo hedge
  entropyLargeMixedRawQuotientReserve := entropyLargeMixedRawQuotientReserve

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate_of_parts
    {smallRatio temperedReverseRatio : Nat → ℚ}
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true)
    (hsolo :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloGcompRange chunk.1 chunk.2 = true)
    (hedge :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise : PositiveSaddleEntropyShadowLargeExpPointwiseCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpMixedRawQuotientReserveBoundsCertificate
        smallRatio temperedReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate
      smallRatio temperedReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate
    hsmall htempered htangent hsolo hedge
    (pointwise.toLargeExpMixedRawQuotientReserveCertificate bounds)

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate_of_gcomp_parts
    {smallRatio temperedReverseRatio : Nat → ℚ}
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true)
    (hsolo :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloGcompRange chunk.1 chunk.2 = true)
    (hedge :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise : PositiveSaddleEntropyShadowLargeExpGcompPointwiseCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpMixedRawQuotientReserveBoundsCertificate
        smallRatio temperedReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate
      smallRatio temperedReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate_of_parts
    hsmall htempered htangent hsolo hedge
    pointwise.toPointwiseCertificate bounds

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate_of_product_parts
    {smallRatio temperedReverseRatio : Nat → ℚ}
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true)
    (hsolo :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloGcompRange chunk.1 chunk.2 = true)
    (hedge :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise : PositiveSaddleEntropyShadowLargeExpProductPointwiseCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpMixedRawQuotientReserveBoundsCertificate
        smallRatio temperedReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate
      smallRatio temperedReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate_of_gcomp_parts
    hsmall htempered htangent hsolo hedge
    pointwise.toGcompPointwiseCertificate bounds

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate_of_crossmul_parts
    {smallRatio temperedReverseRatio : Nat → ℚ}
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true)
    (hsolo :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloGcompRange chunk.1 chunk.2 = true)
    (hedge :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise : PositiveSaddleEntropyShadowLargeExpPointwiseCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpMixedRawQuotientReserveCrossmulBoundsCertificate
        smallRatio temperedReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate
      smallRatio temperedReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate_of_parts
    hsmall htempered htangent hsolo hedge
    pointwise bounds.toBoundsCertificate

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate_of_gcomp_crossmul_parts
    {smallRatio temperedReverseRatio : Nat → ℚ}
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true)
    (hsolo :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloGcompRange chunk.1 chunk.2 = true)
    (hedge :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise : PositiveSaddleEntropyShadowLargeExpGcompPointwiseCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpMixedRawQuotientReserveCrossmulBoundsCertificate
        smallRatio temperedReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate
      smallRatio temperedReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate_of_gcomp_parts
    hsmall htempered htangent hsolo hedge
    pointwise bounds.toBoundsCertificate

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate_of_product_crossmul_parts
    {smallRatio temperedReverseRatio : Nat → ℚ}
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true)
    (hsolo :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloGcompRange chunk.1 chunk.2 = true)
    (hedge :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise : PositiveSaddleEntropyShadowLargeExpProductPointwiseCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpMixedRawQuotientReserveCrossmulBoundsCertificate
        smallRatio temperedReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate
      smallRatio temperedReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate_of_product_parts
    hsmall htempered htangent hsolo hedge
    pointwise bounds.toBoundsCertificate

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate_of_productY_parts
    {smallRatio temperedReverseRatio : Nat → ℚ}
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true)
    (hsolo :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloGcompRange chunk.1 chunk.2 = true)
    (hedge :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise : PositiveSaddleEntropyShadowLargeExpProductPointwiseYCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpMixedRawQuotientReserveBoundsCertificate
        smallRatio temperedReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate
      smallRatio temperedReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate_of_product_parts
    hsmall htempered htangent hsolo hedge
    pointwise.toProductPointwiseCertificate bounds

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate_of_productY_crossmul_parts
    {smallRatio temperedReverseRatio : Nat → ℚ}
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true)
    (hsolo :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloGcompRange chunk.1 chunk.2 = true)
    (hedge :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise : PositiveSaddleEntropyShadowLargeExpProductPointwiseYCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpMixedRawQuotientReserveCrossmulBoundsCertificate
        smallRatio temperedReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate
      smallRatio temperedReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate_of_product_crossmul_parts
    hsmall htempered htangent hsolo hedge
    pointwise.toProductPointwiseCertificate bounds

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
    {temperedSplit : Nat → Nat}
    {smallRatio temperedLowerRatio temperedUpperReverseRatio : Nat → ℚ}
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true)
    (hsolo :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloGcompRange chunk.1 chunk.2 = true)
    (hedge :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (entropyLargeSplitTemperedRawQuotientReserve :
      PositiveSaddleEntropyShadowLargeExpSplitTemperedRawQuotientReserveCertificate
        temperedSplit smallRatio temperedLowerRatio
        temperedUpperReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      temperedSplit smallRatio temperedLowerRatio
      temperedUpperReverseRatio where
  finiteChunks :=
    positiveSaddleDefaultFiniteWindowChunks
      hsmall htempered htangent hsolo hedge
  entropyLargeSplitTemperedRawQuotientReserve :=
    entropyLargeSplitTemperedRawQuotientReserve

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate_of_parts
    {temperedSplit : Nat → Nat}
    {smallRatio temperedLowerRatio temperedUpperReverseRatio : Nat → ℚ}
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true)
    (hsolo :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloGcompRange chunk.1 chunk.2 = true)
    (hedge :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise : PositiveSaddleEntropyShadowLargeExpPointwiseCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpSplitTemperedRawQuotientReserveBoundsCertificate
        temperedSplit smallRatio temperedLowerRatio
        temperedUpperReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      temperedSplit smallRatio temperedLowerRatio
      temperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
    hsmall htempered htangent hsolo hedge
    (pointwise.toLargeExpSplitTemperedRawQuotientReserveCertificate bounds)

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate_of_crossmul_parts
    {temperedSplit : Nat → Nat}
    {smallRatio temperedLowerRatio temperedUpperReverseRatio : Nat → ℚ}
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true)
    (hsolo :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloGcompRange chunk.1 chunk.2 = true)
    (hedge :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise : PositiveSaddleEntropyShadowLargeExpPointwiseCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpSplitTemperedCrossmulBoundsCertificate
        temperedSplit smallRatio temperedLowerRatio
        temperedUpperReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      temperedSplit smallRatio temperedLowerRatio
      temperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate_of_parts
    hsmall htempered htangent hsolo hedge
    pointwise bounds.toBoundsCertificate

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate_of_productY_parts
    {temperedSplit : Nat → Nat}
    {smallRatio temperedLowerRatio temperedUpperReverseRatio : Nat → ℚ}
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true)
    (hsolo :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloGcompRange chunk.1 chunk.2 = true)
    (hedge :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise : PositiveSaddleEntropyShadowLargeExpProductPointwiseYCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpSplitTemperedRawQuotientReserveBoundsCertificate
        temperedSplit smallRatio temperedLowerRatio
        temperedUpperReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      temperedSplit smallRatio temperedLowerRatio
      temperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate_of_parts
    hsmall htempered htangent hsolo hedge
    pointwise.toProductPointwiseCertificate.toGcompPointwiseCertificate.toPointwiseCertificate
    bounds

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate_of_productY_crossmul_parts
    {temperedSplit : Nat → Nat}
    {smallRatio temperedLowerRatio temperedUpperReverseRatio : Nat → ℚ}
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true)
    (hsolo :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloGcompRange chunk.1 chunk.2 = true)
    (hedge :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise : PositiveSaddleEntropyShadowLargeExpProductPointwiseYCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpSplitTemperedCrossmulBoundsCertificate
        temperedSplit smallRatio temperedLowerRatio
        temperedUpperReverseRatio) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      temperedSplit smallRatio temperedLowerRatio
      temperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate_of_productY_parts
    hsmall htempered htangent hsolo hedge
    pointwise bounds.toBoundsCertificate

end Prop51
