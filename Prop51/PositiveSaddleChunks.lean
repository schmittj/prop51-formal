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

/-- Every default finite-window chunk starts inside the proved finite window. -/
theorem positiveSaddleDefaultChunks_lo_ge_401
    {chunk : Nat × Nat} (hchunk : chunk ∈ positiveSaddleDefaultChunks) :
    401 ≤ chunk.1 := by
  simp [positiveSaddleDefaultChunks] at hchunk
  rcases hchunk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-! ## Row-dependent product `N`-chunks -/

/-- Canonical singleton `N`-chunks for the positive rectangle at a fixed row
`a`.

This is not necessarily the most efficient generated-certificate shape, but
it gives a simple built-in cover for the fine-grained table-backed raw product
interface.  Larger generated `N` chunks can still use the parameterized
certificate directly. -/
def positiveProductSingletonNChunks (a : Nat) : List (Nat × Nat) :=
  (positiveNRangeList a).map fun N => (N, 1)

theorem positiveProductSingletonNChunks_cover
    {a N : Nat} (hrect : positiveRectangle a N) :
    ∃ chunk : Nat × Nat,
      chunk ∈ positiveProductSingletonNChunks a ∧
        N ∈ List.range' chunk.1 chunk.2 := by
  refine ⟨(N, 1), ?_, ?_⟩
  · unfold positiveProductSingletonNChunks
    exact List.mem_map.mpr
      ⟨N, mem_positiveNRangeList_of_rectangle hrect, rfl⟩
  · exact (List.mem_range'_1).mpr ⟨le_rfl, by omega⟩

/-! ## Default edge `k`-chunks

The corrected finite edge budget is expensive as a single row check.  These
fixed 20-wide chunks cover every retained `k` for all `a ≤ 2000`; generated
audits can prove each chunk separately and then combine them through the
reducers in `PositiveSaddle.lean`. -/

/-- Default 20-wide `k`-chunks covering `1 ≤ k ≤ 1800`, hence all retained
`k ∈ positiveKRange a` for `a ≤ 2000`. -/
def positiveEdgeDefaultKChunks : Finset (Nat × Nat) :=
  (Finset.range 90).image fun i => (1 + 20 * i, 20)

/-- Common edge scale threshold sufficient for the 90 default reciprocal
`k`-chunk budgets to fit inside `positiveEdgeBudget = 1 / 200000000`. -/
def positiveEdgeUniformScaleMin : Nat := 18000000000

theorem positiveEdgeUniformScaleMin_pos : 0 < positiveEdgeUniformScaleMin := by
  norm_num [positiveEdgeUniformScaleMin]

/-- Row-range check for one default edge `k`-chunk using a row-dependent unit
scale. -/
def checkPositiveEdgeMajorantKChunkUnitRowRange
    (lo len kLo kLen : Nat) (edgeScale : Nat → Nat) : Bool :=
  (List.range' lo len).all fun a =>
    checkPositiveEdgeMajorantKChunkUnit a kLo kLen (edgeScale a)

theorem checkPositiveEdgeMajorantKChunkUnit_of_rowRange
    {lo len a kLo kLen : Nat} {edgeScale : Nat → Nat}
    (h :
      checkPositiveEdgeMajorantKChunkUnitRowRange
        lo len kLo kLen edgeScale = true)
    (ha_lo : lo ≤ a) (ha_hi : a < lo + len) :
    checkPositiveEdgeMajorantKChunkUnit a kLo kLen (edgeScale a) = true := by
  have hall :
      ∀ x ∈ List.range' lo len,
        checkPositiveEdgeMajorantKChunkUnit x kLo kLen (edgeScale x) = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveEdgeMajorantKChunkUnitRowRange] using h)
  exact hall a ((List.mem_range'_1).mpr ⟨ha_lo, ha_hi⟩)

theorem positiveEdgeUniformScale_pos_of_scale_ge
    {scale : Nat} (hscale : positiveEdgeUniformScaleMin ≤ scale) :
    0 < scale := by
  exact positiveEdgeUniformScaleMin_pos.trans_le hscale

theorem positiveEdgeDefaultKChunks_card :
    positiveEdgeDefaultKChunks.card = 90 := by
  unfold positiveEdgeDefaultKChunks
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j h
    simp at h
    omega

theorem positiveEdgeDefaultKChunks_disjoint :
    (positiveEdgeDefaultKChunks : Set (Nat × Nat)).PairwiseDisjoint
      fun chunk => Finset.Ico chunk.1 (chunk.1 + chunk.2) := by
  intro chunk hchunk chunk' hchunk' hne
  have hchunkFin : chunk ∈ positiveEdgeDefaultKChunks := by simpa using hchunk
  have hchunkFin' : chunk' ∈ positiveEdgeDefaultKChunks := by simpa using hchunk'
  rcases Finset.mem_image.mp hchunkFin with ⟨i, _hi, rfl⟩
  rcases Finset.mem_image.mp hchunkFin' with ⟨j, _hj, rfl⟩
  have hij : i ≠ j := by
    intro h
    apply hne
    simp [h]
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · simp [Finset.disjoint_left, Finset.mem_Ico]
    intro x hxi hxj
    omega
  · simp [Finset.disjoint_left, Finset.mem_Ico]
    intro x hxi hxj
    omega

theorem positiveEdgeDefaultKChunks_cover
    {a k : Nat} (ha2000 : a ≤ 2000) (hk : k ∈ positiveKRange a) :
    ∃ chunk : Nat × Nat,
      chunk ∈ positiveEdgeDefaultKChunks ∧
        k ∈ Finset.Ico chunk.1 (chunk.1 + chunk.2) := by
  rcases (mem_positiveKRange.mp hk) with ⟨hk1, hkmax⟩
  have hkhi : k ≤ 1800 := by
    unfold posKmax at hkmax
    omega
  let i := (k - 1) / 20
  have hi : i < 90 := by
    dsimp [i]
    omega
  refine ⟨(1 + 20 * i, 20), ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩
  · simp [Finset.mem_Ico]
    dsimp [i]
    constructor <;> omega

theorem checkPositiveEdgeMajorantKChunkUnit_of_defaultRowChunks
    {edgeScale : Nat → Nat}
    (hchunks :
      ∀ {rowChunk : Nat × Nat}, rowChunk ∈ positiveSaddleDefaultChunks →
        ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveEdgeMajorantKChunkUnitRowRange
            rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2 edgeScale = true)
    {a : Nat} (ha401 : 401 ≤ a) (ha2000 : a ≤ 2000)
    {edgeChunk : Nat × Nat} (hedgeChunk : edgeChunk ∈ positiveEdgeDefaultKChunks) :
    checkPositiveEdgeMajorantKChunkUnit
      a edgeChunk.1 edgeChunk.2 (edgeScale a) = true := by
  rcases positiveSaddleDefaultChunks_cover (a := a) ha401 ha2000 with
    ⟨rowChunk, hrowChunk, hlo, hhi⟩
  exact checkPositiveEdgeMajorantKChunkUnit_of_rowRange
    (hchunks (rowChunk := rowChunk) hrowChunk
      (edgeChunk := edgeChunk) hedgeChunk)
    hlo hhi

theorem positiveEdgeBudget_of_defaultKChunksBounds
    {a : Nat} {budget : Nat × Nat → ℚ}
    (ha401 : 401 ≤ a) (ha2000 : a ≤ 2000)
    (hchunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveEdgeDefaultKChunks →
        positiveEdgeMajorantKChunkSum a chunk.1 chunk.2 ≤ budget chunk)
    (hbudget :
      ∑ chunk ∈ positiveEdgeDefaultKChunks, budget chunk ≤ positiveEdgeBudget) :
    positiveEdgeMajorantSum a ≤ positiveEdgeBudget :=
  positiveEdgeBudget_of_KChunksBounds
    (a := a) (chunks := positiveEdgeDefaultKChunks)
    (budget := budget) ha401 ha2000
    positiveEdgeDefaultKChunks_disjoint
    (fun hk => positiveEdgeDefaultKChunks_cover ha2000 hk)
    hchunks hbudget

theorem positiveEdgeBudget_of_defaultKChunksUnitChecks
    {a : Nat} {scale : Nat × Nat → Nat}
    (ha401 : 401 ≤ a) (ha2000 : a ≤ 2000)
    (hscale :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveEdgeDefaultKChunks →
        0 < scale chunk)
    (hchunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnit
          a chunk.1 chunk.2 (scale chunk) = true)
    (hbudget :
      ∑ chunk ∈ positiveEdgeDefaultKChunks,
        (1 : ℚ) / (scale chunk : ℚ) ≤ positiveEdgeBudget) :
    positiveEdgeMajorantSum a ≤ positiveEdgeBudget :=
  positiveEdgeBudget_of_KChunksUnitChecks
    (a := a) (chunks := positiveEdgeDefaultKChunks)
    (scale := scale) ha401 ha2000
    positiveEdgeDefaultKChunks_disjoint
    (fun hk => positiveEdgeDefaultKChunks_cover ha2000 hk)
    hscale hchunks hbudget

theorem positiveEdgeDefaultKChunks_uniformBudget
    {scale : Nat} (hbudget : (90 : ℚ) / (scale : ℚ) ≤ positiveEdgeBudget) :
    ∑ _chunk ∈ positiveEdgeDefaultKChunks,
      (1 : ℚ) / (scale : ℚ) ≤ positiveEdgeBudget := by
  rw [Finset.sum_const, positiveEdgeDefaultKChunks_card, nsmul_eq_mul]
  change (90 : ℚ) * (1 / (scale : ℚ)) ≤ positiveEdgeBudget
  rw [show (90 : ℚ) * (1 / (scale : ℚ)) = (90 : ℚ) / (scale : ℚ) by ring]
  exact hbudget

theorem positiveEdgeUniformBudget_of_scale_ge
    {scale : Nat} (hscale : positiveEdgeUniformScaleMin ≤ scale) :
    (90 : ℚ) / (scale : ℚ) ≤ positiveEdgeBudget := by
  rw [positiveEdgeBudget_eq_inv_200000000]
  have hscalePosQ : (0 : ℚ) < (scale : ℚ) := by
    exact_mod_cast positiveEdgeUniformScale_pos_of_scale_ge hscale
  rw [div_le_iff₀ hscalePosQ]
  have hscaleQ : (positiveEdgeUniformScaleMin : ℚ) ≤ (scale : ℚ) := by
    exact_mod_cast hscale
  have hmul :=
    mul_le_mul_of_nonneg_left hscaleQ
      (by norm_num : (0 : ℚ) ≤ 1 / 200000000)
  norm_num [positiveEdgeUniformScaleMin] at hmul
  simpa [mul_comm] using hmul

theorem positiveEdgeDefaultKChunks_uniformBudget_of_scale_ge
    {scale : Nat} (hscale : positiveEdgeUniformScaleMin ≤ scale) :
    ∑ _chunk ∈ positiveEdgeDefaultKChunks,
      (1 : ℚ) / (scale : ℚ) ≤ positiveEdgeBudget :=
  positiveEdgeDefaultKChunks_uniformBudget
    (positiveEdgeUniformBudget_of_scale_ge hscale)

theorem positiveEdgeBudget_of_defaultKChunksUniformUnitChecks
    {a scale : Nat}
    (ha401 : 401 ≤ a) (ha2000 : a ≤ 2000) (hscale : 0 < scale)
    (hchunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnit
          a chunk.1 chunk.2 scale = true)
    (hbudget : (90 : ℚ) / (scale : ℚ) ≤ positiveEdgeBudget) :
    positiveEdgeMajorantSum a ≤ positiveEdgeBudget :=
  positiveEdgeBudget_of_defaultKChunksUnitChecks
    (a := a) (scale := fun _ => scale) ha401 ha2000
    (fun {_chunk} _hchunk => hscale)
    hchunks
    (positiveEdgeDefaultKChunks_uniformBudget hbudget)

theorem positiveEdgeBudget_of_defaultKChunksUniformUnitChecks_of_scale_ge
    {a scale : Nat}
    (ha401 : 401 ≤ a) (ha2000 : a ≤ 2000)
    (hscale : positiveEdgeUniformScaleMin ≤ scale)
    (hchunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnit
          a chunk.1 chunk.2 scale = true) :
    positiveEdgeMajorantSum a ≤ positiveEdgeBudget :=
  positiveEdgeBudget_of_defaultKChunksUniformUnitChecks
    ha401 ha2000
    (positiveEdgeUniformScale_pos_of_scale_ge hscale)
    hchunks
    (positiveEdgeUniformBudget_of_scale_ge hscale)

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

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawQuotientReserveCertificate_of_parts
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
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedCrossmulBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate_of_crossmul_parts
    hsmall htempered htangent hsolo hedge
    pointwise bounds.toSplitTemperedCrossmulBoundsCertificate

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawQuotientReserveCertificate_of_productY_parts
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
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedCrossmulBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawQuotientReserveCertificate_of_parts
    hsmall htempered htangent hsolo hedge
    pointwise.toProductPointwiseCertificate.toGcompPointwiseCertificate.toPointwiseCertificate
    bounds

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedLinearReserveCertificate_of_parts
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
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedLinearBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawQuotientReserveCertificate_of_parts
    hsmall htempered htangent hsolo hedge pointwise
    bounds.toCandidateSplitTemperedCrossmulBoundsCertificate

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedLinearReserveCertificate_of_productY_parts
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
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedLinearBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedLinearReserveCertificate_of_parts
    hsmall htempered htangent hsolo hedge
    pointwise.toProductPointwiseCertificate.toGcompPointwiseCertificate.toPointwiseCertificate
    bounds

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedLinearReserveCertificate_of_linearProduct_parts
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
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseLinearCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedLinearBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
    hsmall htempered htangent hsolo hedge
    (pointwise.toLargeExpCandidateSplitTemperedLinearReserveCertificate bounds)

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedLinearReserveCertificate_of_linearProductY_parts
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
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYLinearCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedLinearBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedLinearReserveCertificate_of_linearProduct_parts
    hsmall htempered htangent hsolo hedge
    pointwise.toProductPointwiseLinearCertificate bounds

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedLinearReserveCertificate_of_rawProduct_parts
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
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseRawCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedLinearBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedLinearReserveCertificate_of_linearProduct_parts
    hsmall htempered htangent hsolo hedge
    pointwise.toProductPointwiseLinearCertificate bounds

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedLinearReserveCertificate_of_rawProductY_parts
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
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedLinearBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedLinearReserveCertificate_of_rawProduct_parts
    hsmall htempered htangent hsolo hedge
    pointwise.toProductPointwiseRawCertificate bounds

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedReserveCertificate_of_parts
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
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedLinearReserveCertificate_of_parts
    hsmall htempered htangent hsolo hedge pointwise
    bounds.toLinearBoundsCertificate

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedReserveCertificate_of_productY_parts
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
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedReserveCertificate_of_parts
    hsmall htempered htangent hsolo hedge
    pointwise.toProductPointwiseCertificate.toGcompPointwiseCertificate.toPointwiseCertificate
    bounds

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedReserveCertificate_of_linearProduct_parts
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
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseLinearCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedLinearReserveCertificate_of_linearProduct_parts
    hsmall htempered htangent hsolo hedge pointwise
    bounds.toLinearBoundsCertificate

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedReserveCertificate_of_linearProductY_parts
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
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYLinearCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedReserveCertificate_of_linearProduct_parts
    hsmall htempered htangent hsolo hedge
    pointwise.toProductPointwiseLinearCertificate bounds

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedReserveCertificate_of_rawProduct_parts
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
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseRawCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedLinearReserveCertificate_of_rawProduct_parts
    hsmall htempered htangent hsolo hedge pointwise
    bounds.toLinearBoundsCertificate

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedReserveCertificate_of_rawProductY_parts
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
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedReserveCertificate_of_rawProduct_parts
    hsmall htempered htangent hsolo hedge
    pointwise.toProductPointwiseRawCertificate bounds

/-- Current most concrete generated-audit target for the default finite-window
positive-saddle path.

This packages exactly the artifacts still expected from computation or
rational audits: the five finite-window chunk families, the raw `X+Y`/`Gcomp`
large-exp product estimates with the `Y_a(N)` solo form, and the raw-cleared
candidate split-tempered entropy-tail bounds. -/
structure PositiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedAuditCertificate :
    Prop where
  smallXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true
  smallTangentExpEdgeChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true
  soloGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloGcompRange chunk.1 chunk.2 = true
  edgeBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true
  productPointwiseYRaw :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawCertificate
  candidateSplitTemperedRawCleared :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedBoundsCertificate

theorem PositiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedAuditCertificate.toDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
    (cert :
      PositiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedAuditCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedReserveCertificate_of_rawProductY_parts
    cert.smallXplusYProductGcompChunks
    cert.temperedXplusYProductGcompChunks
    cert.smallTangentExpEdgeChunks
    cert.soloGcompChunks
    cert.edgeBudgetChunks
    cert.productPointwiseYRaw
    cert.candidateSplitTemperedRawCleared

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedUnitReserveCertificate_of_rawProductY_parts
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
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedReserveCertificate_of_rawProductY_parts
    hsmall htempered htangent hsolo hedge
    pointwise bounds.toRawClearedBoundsCertificate

theorem positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedUnitReserveCertificate_of_rawProductYUnitSolo_parts
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
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedUnitReserveCertificate_of_rawProductY_parts
    hsmall htempered htangent hsolo hedge
    pointwise.toProductPointwiseYRawCertificate bounds

/-- Unit-scaled version of the current concrete generated-audit target.

Compared with
`PositiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedAuditCertificate`,
the candidate tail certificate clears the fixed reserve denominator
`positiveEdgeBudget / 4 = 1 / 800000000`. -/
structure PositiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedUnitReserveAuditCertificate :
    Prop where
  smallXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true
  smallTangentExpEdgeChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true
  soloGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloGcompRange chunk.1 chunk.2 = true
  edgeBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true
  productPointwiseYRaw :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

theorem PositiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedUnitReserveAuditCertificate.toDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
    (cert :
      PositiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedUnitReserveAuditCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedUnitReserveCertificate_of_rawProductY_parts
    cert.smallXplusYProductGcompChunks
    cert.temperedXplusYProductGcompChunks
    cert.smallTangentExpEdgeChunks
    cert.soloGcompChunks
    cert.edgeBudgetChunks
    cert.productPointwiseYRaw
    cert.candidateSplitTemperedRawClearedUnitReserve

/-- Unit-scaled solo and reserve version of the current concrete
generated-audit target.

In addition to the candidate tail reserve scaling, the large-exp product
pointwise solo field is stated as `200000000 * solo ≤ 1`. -/
structure PositiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate :
    Prop where
  smallXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true
  smallTangentExpEdgeChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true
  soloGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloGcompRange chunk.1 chunk.2 = true
  edgeBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

theorem PositiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
    (cert :
      PositiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
      positiveLargeExpTemperedSplit positiveLargeExpSmallRatio
      positiveLargeExpTemperedLowerRatio
      positiveLargeExpTemperedUpperReverseRatio :=
  positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedUnitReserveCertificate_of_rawProductYUnitSolo_parts
    cert.smallXplusYProductGcompChunks
    cert.temperedXplusYProductGcompChunks
    cert.smallTangentExpEdgeChunks
    cert.soloGcompChunks
    cert.edgeBudgetChunks
    cert.productPointwiseYRawUnitSolo
    cert.candidateSplitTemperedRawClearedUnitReserve

/-- Default finite-window constructor using cell-level tangent-edge checks and
chunked row checks for the other finite predicates. -/
theorem positiveSaddleDefaultCellEdgeRowsEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          checkPositiveSmallTangentExpEdgeCell a N k = true)
    (hsolo :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloGcompRange chunk.1 chunk.2 = true)
    (hedge :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleXplusGcompTangentCellEdgeRowsCertificate where
  smallXplusGcompRows := by
    intro a ha h2000
    exact checkPositiveSmallXplusYProductGcompRow_of_checkRangeChunks
      hsmall (positiveSaddleDefaultChunks_cover (a := a) ha h2000)
  temperedXplusGcompRows := by
    intro a ha h2000
    exact checkPositiveTemperedXplusYProductGcompRow_of_checkRangeChunks
      htempered (positiveSaddleDefaultChunks_cover (a := a) ha h2000)
  smallTangentEdgeCells := htangent
  soloGcompRows := by
    intro a ha h2000
    exact checkPositiveSoloGcompRow_of_checkRangeChunks
      hsolo (positiveSaddleDefaultChunks_cover (a := a) ha h2000)
  edgeBudgetRows := by
    intro a ha h2000
    exact checkPositiveEdgeBudgetRow_of_checkPositiveEdgeBudgetRangeChunks
      hedge (positiveSaddleDefaultChunks_cover (a := a) ha h2000)
  entropyTail :=
    (pointwise.toProductPointwiseYRawCertificate
      |>.toLargeExpCandidateSplitTemperedRawClearedReserveCertificate
        bounds.toRawClearedBoundsCertificate).entropyTail

/-- Unit-budget final audit target with cell-level tangent-edge finite checks.

This variant is intended for generated certificates when the tangent-edge cell
predicate is fast but full tangent rows or ranges are not. -/
structure PositiveSaddleDefaultCellEdgeEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate :
    Prop where
  smallXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true
  smallTangentExpEdgeCells :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        checkPositiveSmallTangentExpEdgeCell a N k = true
  soloGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloGcompRange chunk.1 chunk.2 = true
  edgeBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

theorem PositiveSaddleDefaultCellEdgeEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeRowsCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    PositiveSaddleXplusGcompTangentCellEdgeRowsCertificate :=
  positiveSaddleDefaultCellEdgeRowsEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    cert.smallXplusYProductGcompChunks
    cert.temperedXplusYProductGcompChunks
    cert.smallTangentExpEdgeCells
    cert.soloGcompChunks
    cert.edgeBudgetChunks
    cert.productPointwiseYRawUnitSolo
    cert.candidateSplitTemperedRawClearedUnitReserve

/-- Default finite-window constructor using cell-level tangent-edge checks and
unit-scaled solo/edge chunk checks. -/
theorem positiveSaddleDefaultCellEdgeUnitBudgetRowsEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          checkPositiveSmallTangentExpEdgeCell a N k = true)
    (hsolo :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloGcompUnitRange chunk.1 chunk.2 = true)
    (hedge :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveEdgeBudgetUnitRange chunk.1 chunk.2 = true)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleXplusGcompTangentCellEdgeUnitBudgetRowsCertificate where
  smallXplusGcompRows := by
    intro a ha h2000
    exact checkPositiveSmallXplusYProductGcompRow_of_checkRangeChunks
      hsmall (positiveSaddleDefaultChunks_cover (a := a) ha h2000)
  temperedXplusGcompRows := by
    intro a ha h2000
    exact checkPositiveTemperedXplusYProductGcompRow_of_checkRangeChunks
      htempered (positiveSaddleDefaultChunks_cover (a := a) ha h2000)
  smallTangentEdgeCells := htangent
  soloGcompUnitRows := by
    intro a ha h2000
    exact checkPositiveSoloGcompUnitRow_of_checkUnitRangeChunks
      hsolo (positiveSaddleDefaultChunks_cover (a := a) ha h2000)
  edgeBudgetUnitRows := by
    intro a ha h2000
    exact checkPositiveEdgeBudgetUnitRow_of_checkPositiveEdgeBudgetUnitRangeChunks
      hedge (positiveSaddleDefaultChunks_cover (a := a) ha h2000)
  entropyTail :=
    (pointwise.toProductPointwiseYRawCertificate
      |>.toLargeExpCandidateSplitTemperedRawClearedReserveCertificate
        bounds.toRawClearedBoundsCertificate).entropyTail

/-- Unit-cleared finite budget audit target with cell-level tangent-edge
checks.

Compared with
`PositiveSaddleDefaultCellEdgeEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`,
the finite solo and edge chunk predicates clear the common denominator
`positiveSoloBudget = positiveEdgeBudget = 1 / 200000000`. -/
structure PositiveSaddleDefaultCellEdgeUnitBudgetRowsEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate :
    Prop where
  smallXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true
  smallTangentExpEdgeCells :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        checkPositiveSmallTangentExpEdgeCell a N k = true
  soloGcompUnitChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloGcompUnitRange chunk.1 chunk.2 = true
  edgeBudgetUnitChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveEdgeBudgetUnitRange chunk.1 chunk.2 = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

theorem PositiveSaddleDefaultCellEdgeUnitBudgetRowsEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeUnitBudgetRowsCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeUnitBudgetRowsEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    PositiveSaddleXplusGcompTangentCellEdgeUnitBudgetRowsCertificate :=
  positiveSaddleDefaultCellEdgeUnitBudgetRowsEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    cert.smallXplusYProductGcompChunks
    cert.temperedXplusYProductGcompChunks
    cert.smallTangentExpEdgeCells
    cert.soloGcompUnitChunks
    cert.edgeBudgetUnitChunks
    cert.productPointwiseYRawUnitSolo
    cert.candidateSplitTemperedRawClearedUnitReserve

/-- Default finite-window constructor using cell-level tangent-edge checks and
semantic finite solo/edge budget fields.

This is the practical audit endpoint while the corresponding executable
solo/edge row checks are too expensive to run directly.  It is mathematically
the same budget interface consumed by `PositiveSaddleTangentProductBudgetCertificate`;
the divergence from the TeX-style fully finite audit is only where these two
finite inequalities are supplied to Lean. -/
theorem positiveSaddleDefaultCellEdgeBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          checkPositiveSmallTangentExpEdgeCell a N k = true)
    (hsolo :
      ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget)
    (hedge :
      ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
        positiveEdgeMajorantSum a ≤ positiveEdgeBudget)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate where
  smallXplusGcompRows := by
    intro a ha h2000
    exact checkPositiveSmallXplusYProductGcompRow_of_checkRangeChunks
      hsmall (positiveSaddleDefaultChunks_cover (a := a) ha h2000)
  temperedXplusGcompRows := by
    intro a ha h2000
    exact checkPositiveTemperedXplusYProductGcompRow_of_checkRangeChunks
      htempered (positiveSaddleDefaultChunks_cover (a := a) ha h2000)
  smallTangentEdgeCells := htangent
  soloY := hsolo
  edgeBudget := hedge
  entropyTail :=
    (pointwise.toProductPointwiseYRawCertificate
      |>.toLargeExpCandidateSplitTemperedRawClearedReserveCertificate
        bounds.toRawClearedBoundsCertificate).entropyTail

/-- Unit-budget large-tail audit target with cell-level tangent-edge checks
and semantic finite solo/edge budget fields.

The finite product predicates remain default chunk booleans; the tangent edge
predicate is supplied cell-by-cell; the finite solo and edge budgets are
ordinary inequalities. -/
structure PositiveSaddleDefaultCellEdgeBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate :
    Prop where
  smallXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true
  smallTangentExpEdgeCells :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        checkPositiveSmallTangentExpEdgeCell a N k = true
  soloY :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget
  edgeBudget :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeMajorantSum a ≤ positiveEdgeBudget
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

theorem PositiveSaddleDefaultCellEdgeBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  positiveSaddleDefaultCellEdgeBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    cert.smallXplusYProductGcompChunks
    cert.temperedXplusYProductGcompChunks
    cert.smallTangentExpEdgeCells
    cert.soloY
    cert.edgeBudget
    cert.productPointwiseYRawUnitSolo
    cert.candidateSplitTemperedRawClearedUnitReserve

/-- Default finite-window constructor using default `k`-chunk edge checks.

This sits between the fully semantic edge-budget endpoint and the currently
too-expensive whole-row edge boolean: each generated row may prove 90 smaller
unit-scaled `k`-chunk checks, together with a rational sum of their declared
budgets. -/
theorem positiveSaddleDefaultCellEdgeKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          checkPositiveSmallTangentExpEdgeCell a N k = true)
    (hsolo :
      ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget)
    (edgeScale : Nat → Nat × Nat → Nat)
    (hedgeScale :
      ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        chunk ∈ positiveEdgeDefaultKChunks → 0 < edgeScale a chunk)
    (hedgeChunks :
      ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        chunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveEdgeMajorantKChunkUnit
            a chunk.1 chunk.2 (edgeScale a chunk) = true)
    (hedgeBudget :
      ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
        ∑ chunk ∈ positiveEdgeDefaultKChunks,
          (1 : ℚ) / (edgeScale a chunk : ℚ) ≤ positiveEdgeBudget)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  positiveSaddleDefaultCellEdgeBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    hsmall htempered htangent hsolo
    (by
      intro a ha h2000
      exact positiveEdgeBudget_of_defaultKChunksUnitChecks
        ha h2000
        (fun {chunk} hchunk => hedgeScale ha h2000 hchunk)
        (fun {chunk} hchunk => hedgeChunks ha h2000 hchunk)
        (hedgeBudget ha h2000))
    pointwise bounds

/-- Audit target using default edge `k`-chunk checks instead of one whole-row
edge-budget boolean. -/
structure PositiveSaddleDefaultCellEdgeKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (edgeScale : Nat → Nat × Nat → Nat) :
    Prop where
  smallXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true
  smallTangentExpEdgeCells :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        checkPositiveSmallTangentExpEdgeCell a N k = true
  soloY :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget
  edgeScalePos :
    ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      chunk ∈ positiveEdgeDefaultKChunks → 0 < edgeScale a chunk
  edgeKChunkUnitChecks :
    ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      chunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnit
          a chunk.1 chunk.2 (edgeScale a chunk) = true
  edgeKChunkBudget :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      ∑ chunk ∈ positiveEdgeDefaultKChunks,
        (1 : ℚ) / (edgeScale a chunk : ℚ) ≤ positiveEdgeBudget
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

theorem PositiveSaddleDefaultCellEdgeKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
    {edgeScale : Nat → Nat × Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  positiveSaddleDefaultCellEdgeKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    cert.smallXplusYProductGcompChunks
    cert.temperedXplusYProductGcompChunks
    cert.smallTangentExpEdgeCells
    cert.soloY
    edgeScale
    cert.edgeScalePos
    cert.edgeKChunkUnitChecks
    cert.edgeKChunkBudget
    cert.productPointwiseYRawUnitSolo
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem positiveSaddleDefaultCellEdgeUniformKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          checkPositiveSmallTangentExpEdgeCell a N k = true)
    (hsolo :
      ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget)
    (edgeScale : Nat → Nat)
    (hedgeScale :
      ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 → 0 < edgeScale a)
    (hedgeChunks :
      ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        chunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveEdgeMajorantKChunkUnit
            a chunk.1 chunk.2 (edgeScale a) = true)
    (hedgeBudget :
      ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
        (90 : ℚ) / (edgeScale a : ℚ) ≤ positiveEdgeBudget)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  positiveSaddleDefaultCellEdgeKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    hsmall htempered htangent hsolo
    (fun a _chunk => edgeScale a)
    (fun {_a} {_chunk} ha h2000 _hchunk => hedgeScale ha h2000)
    (fun {_a} {_chunk} ha h2000 hchunk => hedgeChunks ha h2000 hchunk)
    (fun {_a} ha h2000 =>
      positiveEdgeDefaultKChunks_uniformBudget (hedgeBudget ha h2000))
    pointwise bounds

theorem positiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          checkPositiveSmallTangentExpEdgeCell a N k = true)
    (hsolo :
      ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget)
    (edgeScale : Nat → Nat)
    (hedgeScale :
      ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
        positiveEdgeUniformScaleMin ≤ edgeScale a)
    (hedgeChunks :
      ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        chunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveEdgeMajorantKChunkUnit
            a chunk.1 chunk.2 (edgeScale a) = true)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  positiveSaddleDefaultCellEdgeUniformKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    hsmall htempered htangent hsolo
    edgeScale
    (fun {_a} ha h2000 =>
      positiveEdgeUniformScale_pos_of_scale_ge (hedgeScale ha h2000))
    hedgeChunks
    (fun {_a} ha h2000 =>
      positiveEdgeUniformBudget_of_scale_ge (hedgeScale ha h2000))
    pointwise bounds

theorem positiveSaddleDefaultCellEdgeDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          checkPositiveSmallTangentExpEdgeCell a N k = true)
    (hsoloY :
      ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        Ynorm N a ≤ positiveYBound a N a)
    (hsoloBudget : checkPositiveSoloDisplayedYBoundUnitRange 401 1600 = true)
    (edgeScale : Nat → Nat)
    (hedgeScale :
      ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
        positiveEdgeUniformScaleMin ≤ edgeScale a)
    (hedgeChunks :
      ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        chunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveEdgeMajorantKChunkUnit
            a chunk.1 chunk.2 (edgeScale a) = true)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  positiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    hsmall htempered htangent
    (dyadic_Ynorm_le_positiveSoloBudget_of_displayedYBound_checkUnitRange
      hsoloY hsoloBudget)
    edgeScale hedgeScale hedgeChunks pointwise bounds

theorem positiveSoloDisplayedYBound_of_defaultUnitChunks
    (hchunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true)
    {a N : Nat} (ha : 401 ≤ a) (ha2000 : a ≤ 2000)
    (hrect : positiveRectangle a N) :
    positiveSoloDisplayedYBound a N ≤ positiveSoloBudget := by
  have hrow : checkPositiveSoloDisplayedYBoundUnitRow a = true := by
    exact checkRow_of_checkRangeChunks
      (row := checkPositiveSoloDisplayedYBoundUnitRow)
      (chunks := positiveSaddleDefaultChunks)
      (a := a)
      (by
        intro chunk hmem
        simpa [checkPositiveSoloDisplayedYBoundUnitRange]
          using hchunks (chunk := chunk) hmem)
      (positiveSaddleDefaultChunks_cover (a := a) ha ha2000)
  exact positiveSoloDisplayedYBound_of_checkUnitRow hrow hrect

theorem dyadic_Ynorm_le_positiveSoloBudget_of_displayedYBound_defaultUnitChunks
    (hY :
      ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        Ynorm N a ≤ positiveYBound a N a)
    (hchunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true) :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget := by
  intro a N ha ha2000 hrect
  exact (dyadic_Ynorm_le_positiveSoloDisplayedYBound
      (hY ha ha2000 hrect)).trans
    (positiveSoloDisplayedYBound_of_defaultUnitChunks
      hchunks ha ha2000 hrect)

theorem Ynorm_le_positiveYBound_of_defaultClearedChunks
    (hchunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true) :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      Ynorm N a ≤ positiveYBound a N a := by
  intro a N ha ha2000 hrect
  have hrow : checkPositiveSoloDisplayedYSaddleClearedRow a = true := by
    exact checkRow_of_checkRangeChunks
      (row := checkPositiveSoloDisplayedYSaddleClearedRow)
      (chunks := positiveSaddleDefaultChunks)
      (a := a)
      (by
        intro chunk hmem
        simpa [checkPositiveSoloDisplayedYSaddleClearedRange]
          using hchunks (chunk := chunk) hmem)
      (positiveSaddleDefaultChunks_cover (a := a) ha ha2000)
  exact Ynorm_le_positiveYBound_of_positiveSoloDisplayedYSaddleCleared
    (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect)
    (by omega : 1 ≤ a)
    (positiveSoloDisplayedYSaddleCleared_of_checkRow hrow hrect)

theorem positiveSaddleDefaultCellEdgeDisplayedSoloChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          checkPositiveSmallTangentExpEdgeCell a N k = true)
    (hsoloY :
      ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        Ynorm N a ≤ positiveYBound a N a)
    (hsoloBudgetChunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true)
    (edgeScale : Nat → Nat)
    (hedgeScale :
      ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
        positiveEdgeUniformScaleMin ≤ edgeScale a)
    (hedgeChunks :
      ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        chunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveEdgeMajorantKChunkUnit
            a chunk.1 chunk.2 (edgeScale a) = true)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  positiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    hsmall htempered htangent
    (dyadic_Ynorm_le_positiveSoloBudget_of_displayedYBound_defaultUnitChunks
      hsoloY hsoloBudgetChunks)
    edgeScale hedgeScale hedgeChunks pointwise bounds

theorem positiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    (hsmall :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htempered :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          checkPositiveSmallTangentExpEdgeCell a N k = true)
    (hsoloClearedChunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true)
    (hsoloBudgetChunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true)
    (edgeScale : Nat → Nat)
    (hedgeScale :
      ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
        positiveEdgeUniformScaleMin ≤ edgeScale a)
    (hedgeChunks :
      ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        chunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveEdgeMajorantKChunkUnit
            a chunk.1 chunk.2 (edgeScale a) = true)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  positiveSaddleDefaultCellEdgeDisplayedSoloChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    hsmall htempered htangent
    (Ynorm_le_positiveYBound_of_defaultClearedChunks hsoloClearedChunks)
    hsoloBudgetChunks edgeScale hedgeScale hedgeChunks pointwise bounds

theorem positiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    (hsmallCleared :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXplusYProductGcompClearedRange chunk.1 chunk.2 = true)
    (htemperedCleared :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXplusYProductGcompClearedRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          checkPositiveSmallTangentExpEdgeCell a N k = true)
    (hsoloClearedChunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true)
    (hsoloBudgetChunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true)
    (edgeScale : Nat → Nat)
    (hedgeScale :
      ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
        positiveEdgeUniformScaleMin ≤ edgeScale a)
    (hedgeChunks :
      ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        chunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveEdgeMajorantKChunkUnit
            a chunk.1 chunk.2 (edgeScale a) = true)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  positiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    (fun {chunk} hchunk =>
      checkPositiveSmallXplusYProductGcompRange_of_checkClearedRange
        (positiveSaddleDefaultChunks_lo_ge_401 hchunk)
        (hsmallCleared (chunk := chunk) hchunk))
    (fun {chunk} hchunk =>
      checkPositiveTemperedXplusYProductGcompRange_of_checkClearedRange
        (positiveSaddleDefaultChunks_lo_ge_401 hchunk)
        (htemperedCleared (chunk := chunk) hchunk))
    htangent hsoloClearedChunks hsoloBudgetChunks
    edgeScale hedgeScale hedgeChunks pointwise bounds

/-- Exact-product variant of
`positiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunks...`.

The finite product chunks here check the actual denominator-cleared
`Bq * Qq` inequalities, not the independent `Xplus`/`Gcomp` product
majorants.  This is the preferred generated-certificate target for the
finite product fields. -/
theorem positiveSaddleDefaultCellEdgeDisplayedSoloRawProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    (hsmallRawCleared :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSmallXYProductRawClearedRange chunk.1 chunk.2 = true)
    (htemperedRawCleared :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveTemperedXYProductRawClearedRange chunk.1 chunk.2 = true)
    (htangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          checkPositiveSmallTangentExpEdgeCell a N k = true)
    (hsoloClearedChunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true)
    (hsoloBudgetChunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true)
    (edgeScale : Nat → Nat)
    (hedgeScale :
      ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
        positiveEdgeUniformScaleMin ≤ edgeScale a)
    (hedgeChunks :
      ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        chunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveEdgeMajorantKChunkUnit
            a chunk.1 chunk.2 (edgeScale a) = true)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleRawProductTangentCellEdgeBudgetCertificate where
  smallXYRawClearedRows := by
    intro a ha h2000
    exact checkRow_of_checkRangeChunks
      (row := checkPositiveSmallXYProductRawClearedRow)
      (chunks := positiveSaddleDefaultChunks)
      (a := a)
      (by
        intro chunk hmem
        simpa [checkPositiveSmallXYProductRawClearedRange]
          using hsmallRawCleared (chunk := chunk) hmem)
      (positiveSaddleDefaultChunks_cover (a := a) ha h2000)
  temperedXYRawClearedRows := by
    intro a ha h2000
    exact checkRow_of_checkRangeChunks
      (row := checkPositiveTemperedXYProductRawClearedRow)
      (chunks := positiveSaddleDefaultChunks)
      (a := a)
      (by
        intro chunk hmem
        simpa [checkPositiveTemperedXYProductRawClearedRange]
          using htemperedRawCleared (chunk := chunk) hmem)
      (positiveSaddleDefaultChunks_cover (a := a) ha h2000)
  smallTangentEdgeCells := htangent
  soloY :=
    dyadic_Ynorm_le_positiveSoloBudget_of_displayedYBound_defaultUnitChunks
      (Ynorm_le_positiveYBound_of_defaultClearedChunks hsoloClearedChunks)
      hsoloBudgetChunks
  edgeBudget := by
    intro a ha h2000
    exact positiveEdgeBudget_of_defaultKChunksUniformUnitChecks_of_scale_ge
      ha h2000 (hedgeScale ha h2000)
      (fun {chunk} hchunk => hedgeChunks (a := a) (chunk := chunk)
        ha h2000 hchunk)
  entropyTail :=
    (pointwise.toProductPointwiseYRawCertificate
      |>.toLargeExpCandidateSplitTemperedRawClearedReserveCertificate
        bounds.toRawClearedBoundsCertificate).entropyTail

/-- Fine-grained table-backed product certificate.

The exact raw product checks are too expensive as whole-row booleans.  This
interface lets generated certificates provide, for each finite-window row
`a`, a cover of the positive `N`-rectangle by half-open chunks and then check
each `N`-chunk against the default 20-wide retained-`k` chunks.  The checker
itself uses shared `c`, `B`, and `Q` tables at each `(a,N)`. -/
structure PositiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate
    (productNChunks : Nat → List (Nat × Nat)) : Prop where
  productNChunksCover :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      ∃ chunk : Nat × Nat,
        chunk ∈ productNChunks a ∧ N ∈ List.range' chunk.1 chunk.2
  smallXYTableChunks :
    ∀ {a : Nat} {nChunk kChunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      nChunk ∈ productNChunks a → kChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveSmallXYProductRawClearedTableNRangeKChunk
          a nChunk.1 nChunk.2 kChunk.1 kChunk.2 = true
  temperedXYTableChunks :
    ∀ {a : Nat} {nChunk kChunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      nChunk ∈ productNChunks a → kChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveTemperedXYProductRawClearedTableNRangeKChunk
          a nChunk.1 nChunk.2 kChunk.1 kChunk.2 = true
  smallTangentEdgeCells :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        checkPositiveSmallTangentExpEdgeCell a N k = true
  soloY :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget
  edgeBudget :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeMajorantSum a ≤ positiveEdgeBudget
  entropyTail :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0

theorem positiveSaddleRawProductTableSingletonNChunkedTangentCellEdgeBudgetCertificate_of_parts
    (hsmall :
      ∀ {a : Nat} {nChunk kChunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        nChunk ∈ positiveProductSingletonNChunks a →
        kChunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveSmallXYProductRawClearedTableNRangeKChunk
            a nChunk.1 nChunk.2 kChunk.1 kChunk.2 = true)
    (htempered :
      ∀ {a : Nat} {nChunk kChunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        nChunk ∈ positiveProductSingletonNChunks a →
        kChunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveTemperedXYProductRawClearedTableNRangeKChunk
            a nChunk.1 nChunk.2 kChunk.1 kChunk.2 = true)
    (htangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          checkPositiveSmallTangentExpEdgeCell a N k = true)
    (hsolo :
      ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget)
    (hedge :
      ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
        positiveEdgeMajorantSum a ≤ positiveEdgeBudget)
    (hentropy :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0) :
    PositiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate
      positiveProductSingletonNChunks where
  productNChunksCover := by
    intro _a _N _ha _ha2000 hrect
    exact positiveProductSingletonNChunks_cover hrect
  smallXYTableChunks := hsmall
  temperedXYTableChunks := htempered
  smallTangentEdgeCells := htangent
  soloY := hsolo
  edgeBudget := hedge
  entropyTail := hentropy

theorem PositiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate.toTangentProductBudgetCertificate
    {productNChunks : Nat → List (Nat × Nat)}
    (cert :
      PositiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate
        productNChunks) :
    PositiveSaddleTangentProductBudgetCertificate where
  smallXYTangent := by
    intro a N k ha ha2000 hrect hk hsmall _hB
    rcases cert.productNChunksCover ha ha2000 hrect with
      ⟨nChunk, hnChunk, hNmem⟩
    rcases positiveEdgeDefaultKChunks_cover ha2000 hk with
      ⟨kChunk, hkChunk, hkMem⟩
    have hraw : positiveSmallXYProductRawCleared a N k :=
      positiveSmallXYProductRawCleared_of_checkTableNRangeKChunk
        (by omega : 1 ≤ a)
        (cert.smallXYTableChunks ha ha2000 hnChunk hkChunk)
        hNmem hrect hkMem hk hsmall
    exact positiveSmallXYProductTangentBound_of_rawCleared
      (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect)
      (by omega : 1 ≤ a) hk hraw
  smallTangentEdge := by
    intro a N k ha ha2000 hrect hk hsmall
    exact positiveSmallTangentExpEdgeGap_of_checkCell
      (cert.smallTangentEdgeCells ha ha2000 hrect hk hsmall)
  temperedXY := by
    intro a N k ha ha2000 hrect hk htempered _hB
    rcases cert.productNChunksCover ha ha2000 hrect with
      ⟨nChunk, hnChunk, hNmem⟩
    rcases positiveEdgeDefaultKChunks_cover ha2000 hk with
      ⟨kChunk, hkChunk, hkMem⟩
    have hraw : positiveTemperedXYProductRawCleared a N k :=
      positiveTemperedXYProductRawCleared_of_checkTableNRangeKChunk
        (by omega : 1 ≤ a)
        (cert.temperedXYTableChunks ha ha2000 hnChunk hkChunk)
        hNmem hrect hkMem hk htempered
    exact positiveTemperedXYProductBound_of_rawCleared
      (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect)
      (by omega : 1 ≤ a) hk hraw
  soloY := cert.soloY
  edgeBudget := cert.edgeBudget
  entropyTail := cert.entropyTail

/-- Table-backed exact-product constructor with the current finite solo,
edge, and entropy-tail audit inputs.

The finite product side uses the corrected raw `Bq * Qq` table checks.  This
is the practical generated-certificate route replacing the older independent
`Xplus`/`Gcomp` product route, whose product inequalities are intentionally
stronger than the combined-exponent target. -/
theorem positiveSaddleRawProductTableChunkedDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    {productNChunks : Nat → List (Nat × Nat)}
    (hcover :
      ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        ∃ chunk : Nat × Nat,
          chunk ∈ productNChunks a ∧ N ∈ List.range' chunk.1 chunk.2)
    (hsmall :
      ∀ {a : Nat} {nChunk kChunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        nChunk ∈ productNChunks a → kChunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveSmallXYProductRawClearedTableNRangeKChunk
            a nChunk.1 nChunk.2 kChunk.1 kChunk.2 = true)
    (htempered :
      ∀ {a : Nat} {nChunk kChunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        nChunk ∈ productNChunks a → kChunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveTemperedXYProductRawClearedTableNRangeKChunk
            a nChunk.1 nChunk.2 kChunk.1 kChunk.2 = true)
    (htangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          checkPositiveSmallTangentExpEdgeCell a N k = true)
    (hsoloClearedChunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true)
    (hsoloBudgetChunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true)
    (edgeScale : Nat → Nat)
    (hedgeScale :
      ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
        positiveEdgeUniformScaleMin ≤ edgeScale a)
    (hedgeChunks :
      ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        chunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveEdgeMajorantKChunkUnit
            a chunk.1 chunk.2 (edgeScale a) = true)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate
      productNChunks where
  productNChunksCover := hcover
  smallXYTableChunks := hsmall
  temperedXYTableChunks := htempered
  smallTangentEdgeCells := htangent
  soloY :=
    dyadic_Ynorm_le_positiveSoloBudget_of_displayedYBound_defaultUnitChunks
      (Ynorm_le_positiveYBound_of_defaultClearedChunks hsoloClearedChunks)
      hsoloBudgetChunks
  edgeBudget := by
    intro a ha h2000
    exact positiveEdgeBudget_of_defaultKChunksUniformUnitChecks_of_scale_ge
      ha h2000 (hedgeScale ha h2000)
      (fun {chunk} hchunk => hedgeChunks (a := a) (chunk := chunk)
        ha h2000 hchunk)
  entropyTail :=
    (pointwise.toProductPointwiseYRawCertificate
      |>.toLargeExpCandidateSplitTemperedRawClearedReserveCertificate
        bounds.toRawClearedBoundsCertificate).entropyTail

/-- Singleton-`N` specialization of the table-backed exact-product
constructor.  Generated certificates can still use larger row-dependent
`N`-chunks through the parameterized constructor above. -/
theorem positiveSaddleRawProductTableSingletonNChunkedDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    (hsmall :
      ∀ {a : Nat} {nChunk kChunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        nChunk ∈ positiveProductSingletonNChunks a →
        kChunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveSmallXYProductRawClearedTableNRangeKChunk
            a nChunk.1 nChunk.2 kChunk.1 kChunk.2 = true)
    (htempered :
      ∀ {a : Nat} {nChunk kChunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        nChunk ∈ positiveProductSingletonNChunks a →
        kChunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveTemperedXYProductRawClearedTableNRangeKChunk
            a nChunk.1 nChunk.2 kChunk.1 kChunk.2 = true)
    (htangent :
      ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          checkPositiveSmallTangentExpEdgeCell a N k = true)
    (hsoloClearedChunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true)
    (hsoloBudgetChunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
        checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true)
    (edgeScale : Nat → Nat)
    (hedgeScale :
      ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
        positiveEdgeUniformScaleMin ≤ edgeScale a)
    (hedgeChunks :
      ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
        chunk ∈ positiveEdgeDefaultKChunks →
          checkPositiveEdgeMajorantKChunkUnit
            a chunk.1 chunk.2 (edgeScale a) = true)
    (pointwise :
      PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate)
    (bounds :
      PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate) :
    PositiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate
      positiveProductSingletonNChunks :=
  positiveSaddleRawProductTableChunkedDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    (productNChunks := positiveProductSingletonNChunks)
    (fun {_a _N} _ha _h2000 hrect =>
      positiveProductSingletonNChunks_cover hrect)
    hsmall htempered htangent
    hsoloClearedChunks hsoloBudgetChunks
    edgeScale hedgeScale hedgeChunks pointwise bounds

/-- Audit target using the same edge unit scale for every default `k`-chunk
in a fixed row `a`.

This is a generated-certificate convenience wrapper around
`PositiveSaddleDefaultCellEdgeKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`:
instead of providing a scale and reciprocal budget for each of the 90 chunks,
it is enough to provide one positive scale per row and the single budget check
`90 / scale ≤ positiveEdgeBudget`. -/
structure PositiveSaddleDefaultCellEdgeUniformKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (edgeScale : Nat → Nat) :
    Prop where
  smallXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true
  smallTangentExpEdgeCells :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        checkPositiveSmallTangentExpEdgeCell a N k = true
  soloY :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget
  edgeScalePos :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 → 0 < edgeScale a
  edgeKChunkUnitChecks :
    ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      chunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnit
          a chunk.1 chunk.2 (edgeScale a) = true
  edgeKChunkBudget :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      (90 : ℚ) / (edgeScale a : ℚ) ≤ positiveEdgeBudget
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Same uniform edge-scale audit target, with the reciprocal-budget field
replaced by the natural lower bound
`positiveEdgeUniformScaleMin ≤ edgeScale a`.

This is a Lean-side generated-certificate convenience: the definition of
`positiveEdgeUniformScaleMin` proves exactly the rational inequality required
by the sibling uniform-budget endpoint. -/
structure PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (edgeScale : Nat → Nat) :
    Prop where
  smallXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true
  smallTangentExpEdgeCells :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        checkPositiveSmallTangentExpEdgeCell a N k = true
  soloY :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget
  edgeScaleLarge :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeUniformScaleMin ≤ edgeScale a
  edgeKChunkUnitChecks :
    ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      chunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnit
          a chunk.1 chunk.2 (edgeScale a) = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Preferred generated-audit wrapper with the finite solo input split in the
same shape as the TeX proof: prove the displayed tempered `Y_a(N)` saddle
bound, and discharge the remaining rational budget by the unit-scaled
displayed-solo range check. -/
structure PositiveSaddleDefaultCellEdgeDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (edgeScale : Nat → Nat) :
    Prop where
  smallXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true
  smallTangentExpEdgeCells :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        checkPositiveSmallTangentExpEdgeCell a N k = true
  soloYDisplayed :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      Ynorm N a ≤ positiveYBound a N a
  soloYBudget :
    checkPositiveSoloDisplayedYBoundUnitRange 401 1600 = true
  edgeScaleLarge :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeUniformScaleMin ≤ edgeScale a
  edgeKChunkUnitChecks :
    ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      chunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnit
          a chunk.1 chunk.2 (edgeScale a) = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Displayed-solo audit wrapper using the default finite-window chunks for
the rational solo-budget check.  This is the practical variant of the
displayed-solo endpoint: the `Y_a(N)` saddle estimate remains a semantic
field, while the budget side is split into the same 100-row chunks used by
the product checks. -/
structure PositiveSaddleDefaultCellEdgeDisplayedSoloChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (edgeScale : Nat → Nat) :
    Prop where
  smallXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true
  smallTangentExpEdgeCells :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        checkPositiveSmallTangentExpEdgeCell a N k = true
  soloYDisplayed :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      Ynorm N a ≤ positiveYBound a N a
  soloYBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true
  edgeScaleLarge :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeUniformScaleMin ≤ edgeScale a
  edgeKChunkUnitChecks :
    ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      chunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnit
          a chunk.1 chunk.2 (edgeScale a) = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Displayed-solo audit wrapper with both finite solo sub-obligations
chunked over the default 100-row cover.

The saddle field is the denominator-cleared displayed `Y_a(N)` inequality,
and the budget field is the unit-scaled displayed-solo budget.  This is the
lowest-level current Lean target for the finite solo side; it is still a
finite certificate route, not a proof of the analytic saddle estimate from
first principles. -/
structure PositiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (edgeScale : Nat → Nat) :
    Prop where
  smallXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true
  smallTangentExpEdgeCells :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        checkPositiveSmallTangentExpEdgeCell a N k = true
  soloYSaddleClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true
  soloYBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true
  edgeScaleLarge :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeUniformScaleMin ≤ edgeScale a
  edgeKChunkUnitChecks :
    ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      chunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnit
          a chunk.1 chunk.2 (edgeScale a) = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Displayed-solo audit wrapper with denominator-cleared finite product
chunks.

This is a lower-level variant of
`PositiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`:
the small and tempered product fields clear the `X`/`Y` `Gcomp`
normalization denominators before evaluation, while converting back to the
same normalized product row checks used by the established proof chain. -/
structure PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (edgeScale : Nat → Nat) :
    Prop where
  smallXplusYProductGcompClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompClearedRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompClearedRange chunk.1 chunk.2 = true
  smallTangentExpEdgeCells :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        checkPositiveSmallTangentExpEdgeCell a N k = true
  soloYSaddleClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true
  soloYBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true
  edgeScaleLarge :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeUniformScaleMin ≤ edgeScale a
  edgeKChunkUnitChecks :
    ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      chunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnit
          a chunk.1 chunk.2 (edgeScale a) = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Displayed-solo audit wrapper with exact raw-product cleared chunks.

This is the corrected finite product endpoint after the independent
`Xplus`/`Gcomp` product check was found to be too strong.  The product chunks
check the actual denominator-cleared `Bq * Qq` inequalities, and the wrapper
converts to `PositiveSaddleRawProductTangentCellEdgeBudgetCertificate`. -/
structure PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (edgeScale : Nat → Nat) :
    Prop where
  smallXYProductRawClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXYProductRawClearedRange chunk.1 chunk.2 = true
  temperedXYProductRawClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXYProductRawClearedRange chunk.1 chunk.2 = true
  smallTangentExpEdgeCells :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        checkPositiveSmallTangentExpEdgeCell a N k = true
  soloYSaddleClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true
  soloYBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true
  edgeScaleLarge :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeUniformScaleMin ≤ edgeScale a
  edgeKChunkUnitChecks :
    ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      chunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnit
          a chunk.1 chunk.2 (edgeScale a) = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Displayed-solo audit wrapper with table-backed exact raw-product chunks.

This is the concrete generated-certificate target for the corrected finite
product route.  The product fields are checked against the shared
`c`/`B`/`Q` tables on singleton `N` chunks and the default 20-wide retained
`k` chunks; the rest of the finite and large-tail inputs are the same as in
the displayed-solo raw-product endpoint. -/
structure PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (edgeScale : Nat → Nat) :
    Prop where
  smallXYProductRawClearedTableChunks :
    ∀ {a : Nat} {nChunk kChunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      nChunk ∈ positiveProductSingletonNChunks a →
      kChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveSmallXYProductRawClearedTableNRangeKChunk
          a nChunk.1 nChunk.2 kChunk.1 kChunk.2 = true
  temperedXYProductRawClearedTableChunks :
    ∀ {a : Nat} {nChunk kChunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      nChunk ∈ positiveProductSingletonNChunks a →
      kChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveTemperedXYProductRawClearedTableNRangeKChunk
          a nChunk.1 nChunk.2 kChunk.1 kChunk.2 = true
  smallTangentExpEdgeCells :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        checkPositiveSmallTangentExpEdgeCell a N k = true
  soloYSaddleClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true
  soloYBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true
  edgeScaleLarge :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeUniformScaleMin ≤ edgeScale a
  edgeKChunkUnitChecks :
    ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      chunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnit
          a chunk.1 chunk.2 (edgeScale a) = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Table-backed exact raw-product wrapper with the remaining finite
tangent and edge checks also chunked.

This is the most compact corrected finite-window target: product checks use
singleton `N` table chunks and default retained-`k` chunks, tangent and solo
checks use the default 100-row chunks, and every edge row-chunk check uses the
fixed scale `positiveEdgeUniformScaleMin`.  It stays on the actual
`Bq * Qq` product route rather than the stronger independent `Gcomp` product
audit route. -/
structure PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate :
    Prop where
  smallXYProductRawClearedTableChunks :
    ∀ {a : Nat} {nChunk kChunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      nChunk ∈ positiveProductSingletonNChunks a →
      kChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveSmallXYProductRawClearedTableNRangeKChunk
          a nChunk.1 nChunk.2 kChunk.1 kChunk.2 = true
  temperedXYProductRawClearedTableChunks :
    ∀ {a : Nat} {nChunk kChunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      nChunk ∈ positiveProductSingletonNChunks a →
      kChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveTemperedXYProductRawClearedTableNRangeKChunk
          a nChunk.1 nChunk.2 kChunk.1 kChunk.2 = true
  smallTangentExpEdgeChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true
  soloYSaddleClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true
  soloYBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true
  edgeKChunkUnitRowRanges :
    ∀ {rowChunk : Nat × Nat}, rowChunk ∈ positiveSaddleDefaultChunks →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnitRowRange
          rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2
            (fun _ => positiveEdgeUniformScaleMin) = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Latest default-chunk finite-window audit wrapper.

Compared with
`PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`,
this also chunks the tangent-edge finite check over the default 100-row cover.
The wrapper converts those range checks back into the cell booleans expected
by the established cell-edge certificate. -/
structure PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (edgeScale : Nat → Nat) :
    Prop where
  smallXplusYProductGcompClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompClearedRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompClearedRange chunk.1 chunk.2 = true
  smallTangentExpEdgeChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true
  soloYSaddleClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true
  soloYBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true
  edgeScaleLarge :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeUniformScaleMin ≤ edgeScale a
  edgeKChunkUnitChecks :
    ∀ {a : Nat} {chunk : Nat × Nat}, 401 ≤ a → a ≤ 2000 →
      chunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnit
          a chunk.1 chunk.2 (edgeScale a) = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Default-chunk finite-window audit wrapper with row-chunked edge
`k`-chunk checks.

This replaces the row-indexed edge `k`-chunk family by executable checks over
each default row chunk and each default edge `k`-chunk.  The scale lower bound
is still kept as a simple row-wise semantic field, which is typically
immediate for a generated or constant `edgeScale`. -/
structure PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (edgeScale : Nat → Nat) :
    Prop where
  smallXplusYProductGcompClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompClearedRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompClearedRange chunk.1 chunk.2 = true
  smallTangentExpEdgeChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true
  soloYSaddleClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true
  soloYBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true
  edgeScaleLarge :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeUniformScaleMin ≤ edgeScale a
  edgeKChunkUnitRowRanges :
    ∀ {rowChunk : Nat × Nat}, rowChunk ∈ positiveSaddleDefaultChunks →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnitRowRange
          rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2 edgeScale = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

/-- Constant-scale version of the latest default-chunk audit wrapper.

All edge `k`-chunk checks use `positiveEdgeUniformScaleMin`, whose reciprocal
budget has already been proved to fit inside `positiveEdgeBudget`.  This is
the most compact current generated-certificate target for the finite window:
it has no semantic finite-budget fields and no row-dependent edge-scale data. -/
structure PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate :
    Prop where
  smallXplusYProductGcompClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallXplusYProductGcompClearedRange chunk.1 chunk.2 = true
  temperedXplusYProductGcompClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveTemperedXplusYProductGcompClearedRange chunk.1 chunk.2 = true
  smallTangentExpEdgeChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true
  soloYSaddleClearedChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYSaddleClearedRange chunk.1 chunk.2 = true
  soloYBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ positiveSaddleDefaultChunks →
      checkPositiveSoloDisplayedYBoundUnitRange chunk.1 chunk.2 = true
  edgeKChunkUnitRowRanges :
    ∀ {rowChunk : Nat × Nat}, rowChunk ∈ positiveSaddleDefaultChunks →
      ∀ {edgeChunk : Nat × Nat}, edgeChunk ∈ positiveEdgeDefaultKChunks →
        checkPositiveEdgeMajorantKChunkUnitRowRange
          rowChunk.1 rowChunk.2 edgeChunk.1 edgeChunk.2
            (fun _ => positiveEdgeUniformScaleMin) = true
  productPointwiseYRawUnitSolo :
    PositiveSaddleEntropyShadowLargeExpProductPointwiseYRawUnitSoloCertificate
  candidateSplitTemperedRawClearedUnitReserve :
    PositiveSaddleEntropyShadowLargeExpCandidateSplitTemperedRawClearedUnitReserveBoundsCertificate

theorem PositiveSaddleDefaultCellEdgeUniformKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeUniformKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  positiveSaddleDefaultCellEdgeUniformKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    cert.smallXplusYProductGcompChunks
    cert.temperedXplusYProductGcompChunks
    cert.smallTangentExpEdgeCells
    cert.soloY
    edgeScale
    cert.edgeScalePos
    cert.edgeKChunkUnitChecks
    cert.edgeKChunkBudget
    cert.productPointwiseYRawUnitSolo
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toUniformKChunkBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleDefaultCellEdgeUniformKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale where
  smallXplusYProductGcompChunks := cert.smallXplusYProductGcompChunks
  temperedXplusYProductGcompChunks := cert.temperedXplusYProductGcompChunks
  smallTangentExpEdgeCells := cert.smallTangentExpEdgeCells
  soloY := cert.soloY
  edgeScalePos := by
    intro a ha h2000
    exact positiveEdgeUniformScale_pos_of_scale_ge (cert.edgeScaleLarge ha h2000)
  edgeKChunkUnitChecks := cert.edgeKChunkUnitChecks
  edgeKChunkBudget := by
    intro a ha h2000
    exact positiveEdgeUniformBudget_of_scale_ge (cert.edgeScaleLarge ha h2000)
  productPointwiseYRawUnitSolo := cert.productPointwiseYRawUnitSolo
  candidateSplitTemperedRawClearedUnitReserve :=
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toUniformLargeScaleKChunkBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale where
  smallXplusYProductGcompChunks := cert.smallXplusYProductGcompChunks
  temperedXplusYProductGcompChunks := cert.temperedXplusYProductGcompChunks
  smallTangentExpEdgeCells := cert.smallTangentExpEdgeCells
  soloY :=
    dyadic_Ynorm_le_positiveSoloBudget_of_displayedYBound_checkUnitRange
      cert.soloYDisplayed cert.soloYBudget
  edgeScaleLarge := cert.edgeScaleLarge
  edgeKChunkUnitChecks := cert.edgeKChunkUnitChecks
  productPointwiseYRawUnitSolo := cert.productPointwiseYRawUnitSolo
  candidateSplitTemperedRawClearedUnitReserve :=
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toUniformLargeScaleKChunkBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale where
  smallXplusYProductGcompChunks := cert.smallXplusYProductGcompChunks
  temperedXplusYProductGcompChunks := cert.temperedXplusYProductGcompChunks
  smallTangentExpEdgeCells := cert.smallTangentExpEdgeCells
  soloY :=
    dyadic_Ynorm_le_positiveSoloBudget_of_displayedYBound_defaultUnitChunks
      cert.soloYDisplayed cert.soloYBudgetChunks
  edgeScaleLarge := cert.edgeScaleLarge
  edgeKChunkUnitChecks := cert.edgeKChunkUnitChecks
  productPointwiseYRawUnitSolo := cert.productPointwiseYRawUnitSolo
  candidateSplitTemperedRawClearedUnitReserve :=
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toDisplayedSoloChunksAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleDefaultCellEdgeDisplayedSoloChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale where
  smallXplusYProductGcompChunks := cert.smallXplusYProductGcompChunks
  temperedXplusYProductGcompChunks := cert.temperedXplusYProductGcompChunks
  smallTangentExpEdgeCells := cert.smallTangentExpEdgeCells
  soloYDisplayed :=
    Ynorm_le_positiveYBound_of_defaultClearedChunks
      cert.soloYSaddleClearedChunks
  soloYBudgetChunks := cert.soloYBudgetChunks
  edgeScaleLarge := cert.edgeScaleLarge
  edgeKChunkUnitChecks := cert.edgeKChunkUnitChecks
  productPointwiseYRawUnitSolo := cert.productPointwiseYRawUnitSolo
  candidateSplitTemperedRawClearedUnitReserve :=
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toDisplayedSoloClearedChunksAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale where
  smallXplusYProductGcompChunks := by
    intro chunk hchunk
    exact checkPositiveSmallXplusYProductGcompRange_of_checkClearedRange
      (positiveSaddleDefaultChunks_lo_ge_401 hchunk)
      (cert.smallXplusYProductGcompClearedChunks hchunk)
  temperedXplusYProductGcompChunks := by
    intro chunk hchunk
    exact checkPositiveTemperedXplusYProductGcompRange_of_checkClearedRange
      (positiveSaddleDefaultChunks_lo_ge_401 hchunk)
      (cert.temperedXplusYProductGcompClearedChunks hchunk)
  smallTangentExpEdgeCells := cert.smallTangentExpEdgeCells
  soloYSaddleClearedChunks := cert.soloYSaddleClearedChunks
  soloYBudgetChunks := cert.soloYBudgetChunks
  edgeScaleLarge := cert.edgeScaleLarge
  edgeKChunkUnitChecks := cert.edgeKChunkUnitChecks
  productPointwiseYRawUnitSolo := cert.productPointwiseYRawUnitSolo
  candidateSplitTemperedRawClearedUnitReserve :=
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toRawProductTangentCellEdgeBudgetCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleRawProductTangentCellEdgeBudgetCertificate :=
  positiveSaddleDefaultCellEdgeDisplayedSoloRawProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    cert.smallXYProductRawClearedChunks
    cert.temperedXYProductRawClearedChunks
    cert.smallTangentExpEdgeCells
    cert.soloYSaddleClearedChunks
    cert.soloYBudgetChunks
    edgeScale
    cert.edgeScaleLarge
    cert.edgeKChunkUnitChecks
    cert.productPointwiseYRawUnitSolo
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toRawProductTableChunkedTangentCellEdgeBudgetCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate
      positiveProductSingletonNChunks :=
  positiveSaddleRawProductTableSingletonNChunkedDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
    cert.smallXYProductRawClearedTableChunks
    cert.temperedXYProductRawClearedTableChunks
    cert.smallTangentExpEdgeCells
    cert.soloYSaddleClearedChunks
    cert.soloYBudgetChunks
    edgeScale
    cert.edgeScaleLarge
    cert.edgeKChunkUnitChecks
    cert.productPointwiseYRawUnitSolo
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toTangentProductBudgetCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleTangentProductBudgetCertificate :=
  cert.toRawProductTableChunkedTangentCellEdgeBudgetCertificate
    |>.toTangentProductBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toTangentProductBudgetCertificate.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleTangentProductBudgetCertificate
    cert.toTangentProductBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toRawProductTableSingletonNChunksAuditCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
      (fun _ => positiveEdgeUniformScaleMin) where
  smallXYProductRawClearedTableChunks :=
    cert.smallXYProductRawClearedTableChunks
  temperedXYProductRawClearedTableChunks :=
    cert.temperedXYProductRawClearedTableChunks
  smallTangentExpEdgeCells := by
    intro a N k ha h2000 hrect hk hsmall
    have hrow : checkPositiveSmallTangentExpEdgeRow a = true := by
      exact checkPositiveSmallTangentExpEdgeRow_of_checkRangeChunks
        cert.smallTangentExpEdgeChunks
        (positiveSaddleDefaultChunks_cover (a := a) ha h2000)
    exact decide_eq_true
      (positiveSmallTangentExpEdgeGap_of_checkRow hrow hrect hk hsmall)
  soloYSaddleClearedChunks := cert.soloYSaddleClearedChunks
  soloYBudgetChunks := cert.soloYBudgetChunks
  edgeScaleLarge := by
    intro _a _ha _h2000
    exact le_rfl
  edgeKChunkUnitChecks := by
    intro a edgeChunk ha h2000 hedgeChunk
    exact checkPositiveEdgeMajorantKChunkUnit_of_defaultRowChunks
      cert.edgeKChunkUnitRowRanges ha h2000 hedgeChunk
  productPointwiseYRawUnitSolo := cert.productPointwiseYRawUnitSolo
  candidateSplitTemperedRawClearedUnitReserve :=
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toRawProductTableChunkedTangentCellEdgeBudgetCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    PositiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate
      positiveProductSingletonNChunks :=
  cert.toRawProductTableSingletonNChunksAuditCertificate
    |>.toRawProductTableChunkedTangentCellEdgeBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toTangentProductBudgetCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    PositiveSaddleTangentProductBudgetCertificate :=
  cert.toRawProductTableChunkedTangentCellEdgeBudgetCertificate
    |>.toTangentProductBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toTangentProductBudgetCertificate.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleTangentProductBudgetCertificate
    cert.toTangentProductBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toProductClearedChunksAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale where
  smallXplusYProductGcompClearedChunks :=
    cert.smallXplusYProductGcompClearedChunks
  temperedXplusYProductGcompClearedChunks :=
    cert.temperedXplusYProductGcompClearedChunks
  smallTangentExpEdgeCells := by
    intro a N k ha h2000 hrect hk hsmall
    have hrow : checkPositiveSmallTangentExpEdgeRow a = true := by
      exact checkPositiveSmallTangentExpEdgeRow_of_checkRangeChunks
        cert.smallTangentExpEdgeChunks
        (positiveSaddleDefaultChunks_cover (a := a) ha h2000)
    exact decide_eq_true
      (positiveSmallTangentExpEdgeGap_of_checkRow hrow hrect hk hsmall)
  soloYSaddleClearedChunks := cert.soloYSaddleClearedChunks
  soloYBudgetChunks := cert.soloYBudgetChunks
  edgeScaleLarge := cert.edgeScaleLarge
  edgeKChunkUnitChecks := cert.edgeKChunkUnitChecks
  productPointwiseYRawUnitSolo := cert.productPointwiseYRawUnitSolo
  candidateSplitTemperedRawClearedUnitReserve :=
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toTangentChunksAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale where
  smallXplusYProductGcompClearedChunks :=
    cert.smallXplusYProductGcompClearedChunks
  temperedXplusYProductGcompClearedChunks :=
    cert.temperedXplusYProductGcompClearedChunks
  smallTangentExpEdgeChunks := cert.smallTangentExpEdgeChunks
  soloYSaddleClearedChunks := cert.soloYSaddleClearedChunks
  soloYBudgetChunks := cert.soloYBudgetChunks
  edgeScaleLarge := cert.edgeScaleLarge
  edgeKChunkUnitChecks := by
    intro a edgeChunk ha h2000 hedgeChunk
    exact checkPositiveEdgeMajorantKChunkUnit_of_defaultRowChunks
      cert.edgeKChunkUnitRowRanges ha h2000 hedgeChunk
  productPointwiseYRawUnitSolo := cert.productPointwiseYRawUnitSolo
  candidateSplitTemperedRawClearedUnitReserve :=
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toTangentEdgeChunksAuditCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
      (fun _ => positiveEdgeUniformScaleMin) where
  smallXplusYProductGcompClearedChunks :=
    cert.smallXplusYProductGcompClearedChunks
  temperedXplusYProductGcompClearedChunks :=
    cert.temperedXplusYProductGcompClearedChunks
  smallTangentExpEdgeChunks := cert.smallTangentExpEdgeChunks
  soloYSaddleClearedChunks := cert.soloYSaddleClearedChunks
  soloYBudgetChunks := cert.soloYBudgetChunks
  edgeScaleLarge := by
    intro a ha h2000
    exact le_rfl
  edgeKChunkUnitRowRanges := cert.edgeKChunkUnitRowRanges
  productPointwiseYRawUnitSolo := cert.productPointwiseYRawUnitSolo
  candidateSplitTemperedRawClearedUnitReserve :=
    cert.candidateSplitTemperedRawClearedUnitReserve

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toUniformLargeScaleKChunkBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    edgeScale :=
  cert.toDisplayedSoloChunksAuditCertificate.toUniformLargeScaleKChunkBudgetAuditCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toUniformLargeScaleKChunkBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale :=
  cert.toDisplayedSoloClearedChunksAuditCertificate.toUniformLargeScaleKChunkBudgetAuditCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toUniformLargeScaleKChunkBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale :=
  cert.toProductClearedChunksAuditCertificate.toUniformLargeScaleKChunkBudgetAuditCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toUniformLargeScaleKChunkBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale :=
  cert.toTangentChunksAuditCertificate.toUniformLargeScaleKChunkBudgetAuditCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toUniformLargeScaleKChunkBudgetAuditCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        (fun _ => positiveEdgeUniformScaleMin) :=
  cert.toTangentEdgeChunksAuditCertificate.toUniformLargeScaleKChunkBudgetAuditCertificate

theorem PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  cert.toUniformKChunkBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  cert.toUniformLargeScaleKChunkBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  cert.toUniformLargeScaleKChunkBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  cert.toUniformLargeScaleKChunkBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  cert.toUniformLargeScaleKChunkBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  cert.toUniformLargeScaleKChunkBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  cert.toUniformLargeScaleKChunkBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate :=
  cert.toUniformLargeScaleKChunkBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate

theorem PositiveSaddleDefaultCellEdgeUniformKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeUniformKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentCellEdgeBudgetCertificate.toCertificate

theorem PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentCellEdgeBudgetCertificate.toCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentCellEdgeBudgetCertificate.toCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentCellEdgeBudgetCertificate.toCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentCellEdgeBudgetCertificate.toCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentCellEdgeBudgetCertificate.toCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentCellEdgeBudgetCertificate.toCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentCellEdgeBudgetCertificate.toCertificate

theorem PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentCellEdgeBudgetCertificate.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeUniformKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeUniformKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeDisplayedSoloChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem PositiveSaddleDefaultCellEdgeKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toCertificate
    {edgeScale : Nat → Nat × Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentCellEdgeBudgetCertificate.toCertificate

theorem unorm_tail_of_positiveSaddleDefaultCellEdgeKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat × Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

end Prop51
