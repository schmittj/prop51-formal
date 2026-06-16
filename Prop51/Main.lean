/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Main statements

This file isolates the target theorem of the project and records exactly
what is proved so far.  It deliberately imports only the definition layer and
the finite certificates.

## The target

`CoefficientNegativity` is the full Chen–Larson Proposition 5.1 coefficient
statement (arXiv:2603.23850): for every genus `g ≥ 2` with `g ≡ 0, 2 (mod 3)`
and every positive partition `μ` of `2g - 2`, the coefficient
`b_{⌊g/3⌋+1}(μ)` is negative (in particular nonzero, which is the hypothesis
of Proposition 5.1 there).

## Status

* `coefficientNegativity_of_g_le_1199` : proved — the enumeration (`g ≤ 23`),
  the exact-rational certificate (`9 ≤ a ≤ 60`), the verified dyadic
  interval certificate (`61 ≤ a ≤ 400`, Layer B), and the Layer A majorant
  bridge `b_a(μ) ≤ U_a(N)` (paper eq. 8) together cover every relevant
  genus `g ≤ 1199` and every positive partition.
* `a ≥ 401` (effective analytic bound): formalized as a family of conditional
  positive-saddle certificates.  The sign-lock side is closed; the preferred
  current finite-window interface uses table-backed exact raw-product chunks,
  tangent-edge cells, displayed-solo chunks, and default unit-cleared edge
  `k`-chunks.  The most concrete exposed endpoint also chunks the
  tangent-edge and edge checks and fixes the edge scale to
  `positiveEdgeUniformScaleMin`; final assembly is exposed below by
  `coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`.
  A concrete instance of that audit certificate would upgrade the capstone to
  full `CoefficientNegativity`.
-/
import Prop51.Defs
import Prop51.Partitions
import Prop51.CertificateSmall
import Prop51.CertificateExact
import Prop51.PartitionsComplete
import Prop51.Majorant
import Prop51.CertificateInterval
import Prop51.PositiveSaddleChunks

namespace Prop51

/-- `μ` is a positive partition of `n`: a list of positive parts summing to
`n`.  (Order is irrelevant to `bCoeff`, which only uses the multiset of
parts; we do not impose sortedness.) -/
def IsPartitionOf (μ : List Nat) (n : Nat) : Prop :=
  μ.sum = n ∧ ∀ m ∈ μ, 1 ≤ m

/-- **The target statement.**  Negativity of the Chen–Larson Proposition 5.1
coefficient for all relevant genera and all positive partitions.  Proving
this proposition (sorry-free, with the power-series bridge of Layer A) is the
goal of this repository. -/
def CoefficientNegativity : Prop :=
  ∀ g : Nat, 2 ≤ g → g % 3 ≠ 1 →
    ∀ μ : List Nat, IsPartitionOf μ (2*g - 2) →
      bCoeff μ (g/3 + 1) < 0

/-- What is currently machine-checked towards `CoefficientNegativity` for
small genus: every *generated* partition for every relevant `g ≤ 23`.
Upgrading `∀ μ ∈ partitions (2g-2)` to `∀ μ, IsPartitionOf μ (2g-2)` needs
the generator-completeness lemma plus permutation-invariance of `bCoeff`
(ROADMAP, Layer A′). -/
theorem coefficientNegativity_of_g_le_23 :
    ∀ g < 24, 2 ≤ g → g % 3 ≠ 1 →
      ∀ μ ∈ partitions (2*g - 2), bCoeff μ (g/3 + 1) < 0 :=
  bCoeff_neg_g_le_23

/-- **Small-genus case of the target, in full generality**: for every
relevant `g ≤ 23` and *every* positive partition `μ` of `2g-2` (arbitrary
order, arbitrary list representation), the Chen–Larson coefficient is
negative.  Combines the machine-checked enumeration with generator
completeness (`mem_partitions_iff`) and permutation-invariance of `bCoeff`. -/
theorem coefficientNegativity_of_g_le_23' :
    ∀ g < 24, 2 ≤ g → g % 3 ≠ 1 →
      ∀ μ : List Nat, IsPartitionOf μ (2*g - 2) →
        bCoeff μ (g/3 + 1) < 0 := by
  intro g hg h2 hres μ hμ
  obtain ⟨hsum, hpos⟩ := hμ
  obtain ⟨μ', hperm, hpair⟩ := exists_sorted_perm μ
  have hmem : μ' ∈ partitions (2*g - 2) := by
    rw [mem_partitions_iff]
    refine ⟨by rw [← hperm.sum_eq]; exact hsum, hpair, ?_⟩
    exact fun x hx => hpos x (hperm.mem_iff.mpr hx)
  rw [bCoeff_perm hperm]
  exact bCoeff_neg_g_le_23 g hg h2 hres μ' hmem

/-- **The capstone of Layers 0+A**: for every genus `2 ≤ g ≤ 179` with
`g ≡ 0, 2 (mod 3)` and *every* positive partition `μ` of `2g-2`, the
Chen–Larson Proposition 5.1 coefficient is negative.

Combines: the small-genus enumeration (`g ≤ 23`), the exact-rational
majorant certificate (`9 ≤ a ≤ 60`, i.e. `24 ≤ g ≤ 179`), and the majorant
inequality `b_a(μ) ≤ N c_a · Unorm a N` of `Prop51.Majorant`.  The
quantification over `μ` is the honest predicate form (`IsPartitionOf`). -/
theorem coefficientNegativity_of_g_le_179 :
    ∀ g, 2 ≤ g → g ≤ 179 → g % 3 ≠ 1 →
      ∀ μ : List Nat, IsPartitionOf μ (2*g - 2) →
        bCoeff μ (g/3 + 1) < 0 := by
  intro g h2 h179 hres μ hμp
  obtain ⟨hsum, hpos⟩ := hμp
  rcases Nat.lt_or_ge g 24 with hg | hg
  · exact coefficientNegativity_of_g_le_23' g hg h2 hres μ ⟨hsum, hpos⟩
  · have hmap := sum_map_add_one μ
    have hlen := length_le_sum μ hpos
    have hne : 1 ≤ μ.length := by
      rcases μ with - | ⟨x, l⟩
      · exfalso; simp at hsum; omega
      · simp
    have hNval : (μ.map (· + 1)).sum = (2*g - 2) + μ.length := by
      rw [hmap, hsum]
    refine bCoeff_neg_of_unorm μ (g/3 + 1) ((μ.map (· + 1)).sum)
      hpos rfl (by omega) (by omega) ?_
    exact unorm_neg_9_60 (g/3 + 1) (by omega) (by omega)
      ((μ.map (· + 1)).sum) (by omega) (by omega)

/-- **The capstone of Layers 0+A+B**: for every genus `2 ≤ g ≤ 1199` with
`g ≡ 0, 2 (mod 3)` and *every* positive partition `μ` of `2g-2`, the
Chen–Larson Proposition 5.1 coefficient is negative.

Extends `coefficientNegativity_of_g_le_179` with the verified dyadic
interval certificate `unorm_neg_61_400` (`61 ≤ a ≤ 400`, i.e.
`180 ≤ g ≤ 1199`); the partition-to-rectangle bookkeeping
(`N = 2g-2+n`, `6a-7 ≤ N ≤ 12a-8`) is the same `omega` argument. -/
theorem coefficientNegativity_of_g_le_1199 :
    ∀ g, 2 ≤ g → g ≤ 1199 → g % 3 ≠ 1 →
      ∀ μ : List Nat, IsPartitionOf μ (2*g - 2) →
        bCoeff μ (g/3 + 1) < 0 := by
  intro g h2 h1199 hres μ hμp
  rcases Nat.lt_or_ge g 180 with hg | hg
  · exact coefficientNegativity_of_g_le_179 g h2 (by omega) hres μ hμp
  · obtain ⟨hsum, hpos⟩ := hμp
    have hmap := sum_map_add_one μ
    have hlen := length_le_sum μ hpos
    have hne : 1 ≤ μ.length := by
      rcases μ with - | ⟨x, l⟩
      · exfalso; simp at hsum; omega
      · simp
    have hNval : (μ.map (· + 1)).sum = (2*g - 2) + μ.length := by
      rw [hmap, hsum]
    refine bCoeff_neg_of_unorm μ (g/3 + 1) ((μ.map (· + 1)).sum)
      hpos rfl (by omega) (by omega) ?_
    exact unorm_neg_61_400 (g/3 + 1) (by omega) (by omega)
      ((μ.map (· + 1)).sum) (by omega) (by omega)

/-- Conditional large-genus capstone: once Layer C proves `Unorm a N < 0`
throughout the post-certificate rectangle `a ≥ 401`, the Chen–Larson
coefficient is negative for every relevant `g ≥ 1200`. -/
theorem coefficientNegativity_of_g_ge_1200_of_unorm_tail
    (htail :
      ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0) :
    ∀ g, 1200 ≤ g → g % 3 ≠ 1 →
      ∀ μ : List Nat, IsPartitionOf μ (2*g - 2) →
        bCoeff μ (g/3 + 1) < 0 := by
  intro g hg1200 hres μ hμp
  obtain ⟨hsum, hpos⟩ := hμp
  have hmap := sum_map_add_one μ
  have hlen := length_le_sum μ hpos
  have hne : 1 ≤ μ.length := by
    rcases μ with - | ⟨x, l⟩
    · exfalso; simp at hsum; omega
    · simp
  have hNval : (μ.map (· + 1)).sum = (2*g - 2) + μ.length := by
    rw [hmap, hsum]
  refine bCoeff_neg_of_unorm μ (g/3 + 1) ((μ.map (· + 1)).sum)
    hpos rfl (by omega) (by omega) ?_
  exact htail (g/3 + 1) (by omega) ((μ.map (· + 1)).sum)
    (by omega) (by omega)

/-- Conditional final theorem: the only remaining input is the large-`a`
majorant negativity statement. -/
theorem coefficientNegativity_of_unorm_tail
    (htail :
      ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0) :
    CoefficientNegativity := by
  intro g h2 hres μ hμp
  rcases Nat.lt_or_ge g 1200 with hg | hg
  · exact coefficientNegativity_of_g_le_1199 g h2 (by omega) hres μ hμp
  · exact coefficientNegativity_of_g_ge_1200_of_unorm_tail htail
      g hg hres μ hμp

/-- Final assembly from the packaged §6 positive-saddle certificate. -/
theorem coefficientNegativity_of_positiveSaddleCertificate
    {soloBound : Nat → ℚ} (cert : PositiveSaddleCertificate soloBound) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleCertificate cert)

/-- Final assembly from the raw-summand version of the §6 positive-saddle
certificate. -/
theorem coefficientNegativity_of_positiveSaddleRawCertificate
    {soloBound : Nat → ℚ} (cert : PositiveSaddleRawCertificate soloBound) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleRawCertificate cert)

/-- Final assembly from the factorized TeX-style version of the §6
positive-saddle certificate. -/
theorem coefficientNegativity_of_positiveSaddleFactorCertificate
    {soloBound : Nat → ℚ} (cert : PositiveSaddleFactorCertificate soloBound) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleFactorCertificate cert)

/-- Final assembly from the scalar-product version of the §6 positive-saddle
certificate. -/
theorem coefficientNegativity_of_positiveSaddleScalarCertificate
    {soloBound : Nat → ℚ} (cert : PositiveSaddleScalarCertificate soloBound) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleScalarCertificate cert)

/-- Final assembly from the budgeted scalar-product version of the §6
positive-saddle certificate. -/
theorem coefficientNegativity_of_positiveSaddleScalarBudgetCertificate
    (cert : PositiveSaddleScalarBudgetCertificate) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleScalarBudgetCertificate cert)

/-- Final assembly from the combined `X*Y` product version of the §6
positive-saddle certificate. -/
theorem coefficientNegativity_of_positiveSaddleCombinedProductBudgetCertificate
    (cert : PositiveSaddleCombinedProductBudgetCertificate) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleCombinedProductBudgetCertificate cert)

/-- Final assembly from the corrected tangent-line actual-`N` combined product
version of the §6 positive-saddle certificate. -/
theorem coefficientNegativity_of_positiveSaddleTangentProductBudgetCertificate
    (cert : PositiveSaddleTangentProductBudgetCertificate) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleTangentProductBudgetCertificate cert)

/-- Final assembly from the corrected tangent certificate with row-level
boolean finite checks for the small edge and edge budget. -/
theorem coefficientNegativity_of_positiveSaddleTangentCheckedRowsCertificate
    (cert : PositiveSaddleTangentCheckedRowsCertificate) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleTangentCheckedRowsCertificate cert)

/-- Final assembly from the corrected tangent certificate with row-level
boolean finite checks for the small edge, solo bound, and edge budget. -/
theorem coefficientNegativity_of_positiveSaddleTangentFullyCheckedRowsCertificate
    (cert : PositiveSaddleTangentFullyCheckedRowsCertificate) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleTangentFullyCheckedRowsCertificate cert)

/-- Final assembly from the `\overline B`/`Xplus` tangent certificate with
row-level boolean finite checks for the small edge, solo bound, and edge
budget. -/
theorem coefficientNegativity_of_positiveSaddleXplusTangentFullyCheckedRowsCertificate
    (cert : PositiveSaddleXplusTangentFullyCheckedRowsCertificate) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusTangentFullyCheckedRowsCertificate cert)

/-- Final assembly from the row-checked `Xplus`/`Gcomp` tangent certificate,
where the finite-window small/tempered saddle products, small edge, solo bound,
and edge budget are all represented by row booleans. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentFullyCheckedRowsCertificate
    (cert : PositiveSaddleXplusGcompTangentFullyCheckedRowsCertificate) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentFullyCheckedRowsCertificate cert)

/-- Final assembly from the `Xplus`/`Gcomp` finite-window certificate with
cell-level tangent-edge checks. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentCellEdgeRowsCertificate
    (cert : PositiveSaddleXplusGcompTangentCellEdgeRowsCertificate) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentCellEdgeRowsCertificate cert)

/-- Final assembly from the `Xplus`/`Gcomp` finite-window certificate with
cell-level tangent-edge checks and unit-cleared finite solo/edge row checks. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentCellEdgeUnitBudgetRowsCertificate
    (cert : PositiveSaddleXplusGcompTangentCellEdgeUnitBudgetRowsCertificate) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentCellEdgeUnitBudgetRowsCertificate cert)

/-- Final assembly from the `Xplus`/`Gcomp` finite-window certificate with
cell-level tangent-edge checks and semantic finite solo/edge budgets. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentCellEdgeBudgetCertificate
    (cert : PositiveSaddleXplusGcompTangentCellEdgeBudgetCertificate) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentCellEdgeBudgetCertificate cert)

/-- Final assembly from the row-checked `Xplus`/`Gcomp` finite-window
certificate together with the geometric entropy-shadow tail certificate for
`a > 2000`. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentRowsEntropyGeometricCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRowsEntropyGeometricCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentRowsEntropyGeometricCertificate cert)

/-- Final assembly from the row-checked `Xplus`/`Gcomp` finite-window
certificate together with the reserve form of the geometric entropy-shadow tail
certificate for `a > 2000`. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentRowsEntropyGeometricReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRowsEntropyGeometricReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentRowsEntropyGeometricReserveCertificate cert)

/-- Final assembly from the row-checked `Xplus`/`Gcomp` finite-window
certificate together with quotient-ratio reserve checks for the large-`a`
entropy-shadow tail. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentRowsEntropyQuotientReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRowsEntropyQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentRowsEntropyQuotientReserveCertificate cert)

/-- Final assembly from the row-checked `Xplus`/`Gcomp` finite-window
certificate together with raw-base quotient-ratio reserve checks for the
large-`a` entropy-shadow tail. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentRowsEntropyRawQuotientReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRowsEntropyRawQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentRowsEntropyRawQuotientReserveCertificate cert)

/-- Final assembly from the row-checked `Xplus`/`Gcomp` finite-window
certificate together with a mixed-direction geometric reserve certificate for
the large-`a` entropy-shadow tail. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentRowsEntropyMixedGeometricReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedReverseRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRowsEntropyMixedGeometricReserveCertificate
      smallExp temperedExp smallRatio temperedReverseRatio) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentRowsEntropyMixedGeometricReserveCertificate cert)

/-- Final assembly from the row-checked `Xplus`/`Gcomp` finite-window
certificate together with a mixed-direction raw-quotient reserve certificate
for the large-`a` entropy-shadow tail. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentRowsEntropyMixedRawQuotientReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedReverseRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRowsEntropyMixedRawQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedReverseRatio) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentRowsEntropyMixedRawQuotientReserveCertificate cert)

/-- Final assembly from the range-checked `Xplus`/`Gcomp` finite-window
certificate. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentFullyCheckedRangeCertificate
    (cert : PositiveSaddleXplusGcompTangentFullyCheckedRangeCertificate) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentFullyCheckedRangeCertificate cert)

/-- Final assembly from range booleans for the finite window plus the
geometric entropy-shadow tail certificate for `a > 2000`. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentRangeEntropyGeometricCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRangeEntropyGeometricCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentRangeEntropyGeometricCertificate cert)

/-- Final assembly from range booleans for the finite window plus the reserve
form of the geometric entropy-shadow tail certificate for `a > 2000`. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentRangeEntropyGeometricReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRangeEntropyGeometricReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentRangeEntropyGeometricReserveCertificate cert)

/-- Final assembly from range booleans for the finite window plus quotient-ratio
reserve checks for the large-`a` entropy-shadow tail. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentRangeEntropyQuotientReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRangeEntropyQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentRangeEntropyQuotientReserveCertificate cert)

/-- Final assembly from range booleans for the finite window plus raw-base
quotient-ratio reserve checks for the large-`a` entropy-shadow tail. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentRangeEntropyRawQuotientReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRangeEntropyRawQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentRangeEntropyRawQuotientReserveCertificate cert)

/-- Final assembly from range booleans for the finite window plus a
mixed-direction geometric reserve certificate for the large-`a`
entropy-shadow tail. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentRangeEntropyMixedGeometricReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedReverseRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRangeEntropyMixedGeometricReserveCertificate
      smallExp temperedExp smallRatio temperedReverseRatio) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentRangeEntropyMixedGeometricReserveCertificate cert)

/-- Final assembly from range booleans for the finite window plus a
mixed-direction raw-quotient reserve certificate for the large-`a`
entropy-shadow tail. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentRangeEntropyMixedRawQuotientReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedReverseRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRangeEntropyMixedRawQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedReverseRatio) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentRangeEntropyMixedRawQuotientReserveCertificate cert)

/-- Final assembly from generated chunk range checks for the finite window. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentChunkedRangeCertificate
    {chunks : List (Nat × Nat)}
    (cert : PositiveSaddleXplusGcompTangentChunkedRangeCertificate chunks) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentChunkedRangeCertificate cert)

/-- Final assembly from generated chunk range checks plus the geometric
entropy-shadow tail certificate for `a > 2000`. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricCertificate
    {chunks : List (Nat × Nat)}
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricCertificate
      chunks smallExp temperedExp smallRatio temperedRatio) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricCertificate cert)

/-- Final assembly from generated chunk range checks plus the reserve form of
the geometric entropy-shadow tail certificate for `a > 2000`. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricReserveCertificate
    {chunks : List (Nat × Nat)}
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricReserveCertificate
      chunks smallExp temperedExp smallRatio temperedRatio) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricReserveCertificate cert)

/-- Final assembly from generated chunk range checks plus quotient-ratio
reserve checks for the large-`a` entropy-shadow tail. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentChunkedRangeEntropyQuotientReserveCertificate
    {chunks : List (Nat × Nat)}
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentChunkedRangeEntropyQuotientReserveCertificate
      chunks smallExp temperedExp smallRatio temperedRatio) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentChunkedRangeEntropyQuotientReserveCertificate cert)

/-- Final assembly from generated chunk range checks plus raw-base
quotient-ratio reserve checks for the large-`a` entropy-shadow tail. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentChunkedRangeEntropyRawQuotientReserveCertificate
    {chunks : List (Nat × Nat)}
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentChunkedRangeEntropyRawQuotientReserveCertificate
      chunks smallExp temperedExp smallRatio temperedRatio) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentChunkedRangeEntropyRawQuotientReserveCertificate cert)

/-- Final assembly from generated chunk range checks plus a mixed-direction
geometric reserve certificate for the large-`a` entropy-shadow tail. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentChunkedRangeEntropyMixedGeometricReserveCertificate
    {chunks : List (Nat × Nat)}
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedReverseRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentChunkedRangeEntropyMixedGeometricReserveCertificate
      chunks smallExp temperedExp smallRatio temperedReverseRatio) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentChunkedRangeEntropyMixedGeometricReserveCertificate cert)

/-- Final assembly from generated chunk range checks plus a mixed-direction
raw-quotient reserve certificate for the large-`a` entropy-shadow tail. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentChunkedRangeEntropyMixedRawQuotientReserveCertificate
    {chunks : List (Nat × Nat)}
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedReverseRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentChunkedRangeEntropyMixedRawQuotientReserveCertificate
      chunks smallExp temperedExp smallRatio temperedReverseRatio) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentChunkedRangeEntropyMixedRawQuotientReserveCertificate cert)

/-- Final assembly from generated chunk range checks plus the concrete
variable-cutoff mixed raw-quotient reserve certificate for the large-`a`
entropy-shadow tail. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate
    {chunks : List (Nat × Nat)}
    {smallRatio temperedReverseRatio : Nat → ℚ}
    (cert :
      PositiveSaddleXplusGcompTangentChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate
        chunks smallRatio temperedReverseRatio) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate cert)

/-- Final assembly from generated chunk range checks plus the concrete
split-tempered large-exp raw-quotient reserve certificate for the large-`a`
entropy-shadow tail. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
    {chunks : List (Nat × Nat)}
    {temperedSplit : Nat → Nat}
    {smallRatio temperedLowerRatio temperedUpperReverseRatio : Nat → ℚ}
    (cert :
      PositiveSaddleXplusGcompTangentChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
        chunks temperedSplit smallRatio temperedLowerRatio
        temperedUpperReverseRatio) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate cert)

/-- Final assembly from the default generated chunk cover. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentDefaultChunkedRangeCertificate
    (cert : PositiveSaddleXplusGcompTangentDefaultChunkedRangeCertificate) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentChunkedRangeCertificate cert)

/-- Final assembly from the default generated chunk cover plus the geometric
entropy-shadow tail certificate for `a > 2000`. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyGeometricCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyGeometricCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricCertificate cert)

/-- Final assembly from the default generated chunk cover plus the reserve
form of the geometric entropy-shadow tail certificate for `a > 2000`. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyGeometricReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyGeometricReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricReserveCertificate cert)

/-- Final assembly from the default generated chunk cover plus quotient-ratio
reserve checks for the large-`a` entropy-shadow tail. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyQuotientReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentChunkedRangeEntropyQuotientReserveCertificate cert)

/-- Final assembly from the default generated chunk cover plus raw-base
quotient-ratio reserve checks for the large-`a` entropy-shadow tail. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyRawQuotientReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyRawQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentChunkedRangeEntropyRawQuotientReserveCertificate cert)

/-- Final assembly from the default generated chunk cover plus a
mixed-direction geometric reserve certificate for the large-`a`
entropy-shadow tail. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyMixedGeometricReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedReverseRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyMixedGeometricReserveCertificate
      smallExp temperedExp smallRatio temperedReverseRatio) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentChunkedRangeEntropyMixedGeometricReserveCertificate cert)

/-- Final assembly from the default generated chunk cover plus a
mixed-direction raw-quotient reserve certificate for the large-`a`
entropy-shadow tail. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyMixedRawQuotientReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedReverseRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyMixedRawQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedReverseRatio) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentChunkedRangeEntropyMixedRawQuotientReserveCertificate cert)

/-- Final assembly from the default generated chunk cover plus the concrete
variable-cutoff mixed raw-quotient reserve certificate for the large-`a`
entropy-shadow tail. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate
    {smallRatio temperedReverseRatio : Nat → ℚ}
    (cert :
      PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate
        smallRatio temperedReverseRatio) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentChunkedRangeEntropyLargeExpMixedRawQuotientReserveCertificate cert)

/-- Final assembly from the default generated chunk cover plus the concrete
split-tempered large-exp raw-quotient reserve certificate for the large-`a`
entropy-shadow tail. -/
theorem coefficientNegativity_of_positiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
    {temperedSplit : Nat → Nat}
    {smallRatio temperedLowerRatio temperedUpperReverseRatio : Nat → ℚ}
    (cert :
      PositiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
        temperedSplit smallRatio temperedLowerRatio
        temperedUpperReverseRatio) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXplusGcompTangentChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate cert)

/-- Final assembly from the current most concrete generated-audit shape:
default finite-window chunks, raw product-level large-exp estimates, and
raw-cleared candidate split-tempered entropy-tail bounds. -/
theorem coefficientNegativity_of_positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedAuditCertificate
    (cert :
      PositiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedAuditCertificate) :
    CoefficientNegativity :=
  coefficientNegativity_of_positiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
    cert.toDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate

/-- Final assembly from the unit-scaled version of the current generated-audit
shape.  The reserve inequalities in the candidate tail are stated as
`800000000 * term ≤ 1`. -/
theorem coefficientNegativity_of_positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedUnitReserveAuditCertificate
    (cert :
      PositiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedUnitReserveAuditCertificate) :
    CoefficientNegativity :=
  coefficientNegativity_of_positiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
    cert.toDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate

/-- Final assembly from the fully unit-budgeted current generated-audit shape:
the product-pointwise solo field is `200000000 * solo ≤ 1`, and the candidate
tail reserve fields are `800000000 * term ≤ 1`. -/
theorem coefficientNegativity_of_positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (cert :
      PositiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    CoefficientNegativity :=
  coefficientNegativity_of_positiveSaddleXplusGcompTangentDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate
    cert.toDefaultChunkedRangeEntropyLargeExpSplitTemperedRawQuotientReserveCertificate

/-- Final assembly from the unit-budget audit shape with cell-level tangent
edge checks and chunked product/solo/edge checks. -/
theorem coefficientNegativity_of_positiveSaddleDefaultCellEdgeEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    CoefficientNegativity :=
  coefficientNegativity_of_positiveSaddleXplusGcompTangentCellEdgeRowsCertificate
    cert.toXplusGcompTangentCellEdgeRowsCertificate

/-- Final assembly from the unit-budget audit shape with cell-level tangent
edge checks and unit-cleared finite solo/edge chunks. -/
theorem coefficientNegativity_of_positiveSaddleDefaultCellEdgeUnitBudgetRowsEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeUnitBudgetRowsEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    CoefficientNegativity :=
  coefficientNegativity_of_positiveSaddleXplusGcompTangentCellEdgeUnitBudgetRowsCertificate
    (positiveSaddleDefaultCellEdgeUnitBudgetRowsEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetCertificate_of_parts
      cert.smallXplusYProductGcompChunks
      cert.temperedXplusYProductGcompChunks
      cert.smallTangentExpEdgeCells
      cert.soloGcompUnitChunks
      cert.edgeBudgetUnitChunks
      cert.productPointwiseYRawUnitSolo
      cert.candidateSplitTemperedRawClearedUnitReserve)

/-- Final assembly from the unit-budget large-tail audit shape with cell-level
tangent edge checks and semantic finite solo/edge budgets. -/
theorem coefficientNegativity_of_positiveSaddleDefaultCellEdgeBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    CoefficientNegativity :=
  coefficientNegativity_of_positiveSaddleXplusGcompTangentCellEdgeBudgetCertificate
    (PositiveSaddleDefaultCellEdgeBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
      cert)

/-- Final assembly from the unit-budget large-tail audit shape with cell-level
tangent edge checks, semantic finite solo budgets, and default `k`-chunk
unit-cleared finite edge budgets. -/
theorem coefficientNegativity_of_positiveSaddleDefaultCellEdgeKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat × Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    CoefficientNegativity :=
  coefficientNegativity_of_positiveSaddleXplusGcompTangentCellEdgeBudgetCertificate
    (PositiveSaddleDefaultCellEdgeKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
      cert)

/-- Final assembly from the unit-budget large-tail audit shape with cell-level
tangent edge checks, semantic finite solo budgets, and default `k`-chunk
unit-cleared finite edge budgets using one scale per row. -/
theorem coefficientNegativity_of_positiveSaddleDefaultCellEdgeUniformKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeUniformKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    CoefficientNegativity :=
  coefficientNegativity_of_positiveSaddleXplusGcompTangentCellEdgeBudgetCertificate
    (PositiveSaddleDefaultCellEdgeUniformKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
      cert)

/-- Final assembly from the unit-budget large-tail audit shape with cell-level
tangent edge checks, semantic finite solo budgets, and default `k`-chunk
unit-cleared finite edge budgets using one sufficiently large scale per row. -/
theorem coefficientNegativity_of_positiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    CoefficientNegativity :=
  coefficientNegativity_of_positiveSaddleXplusGcompTangentCellEdgeBudgetCertificate
    (PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
      cert)

/-- Final assembly from the preferred large-scale edge audit shape with the
finite solo input split into the displayed `Y_a(N)` saddle bound and its
unit-scaled rational budget check. -/
theorem coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    CoefficientNegativity :=
  coefficientNegativity_of_positiveSaddleXplusGcompTangentCellEdgeBudgetCertificate
    (PositiveSaddleDefaultCellEdgeDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
      cert)

/-- Final assembly from the displayed-solo route with the rational finite solo
budget split over the default 100-row chunks. -/
theorem coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    CoefficientNegativity :=
  coefficientNegativity_of_positiveSaddleXplusGcompTangentCellEdgeBudgetCertificate
    (PositiveSaddleDefaultCellEdgeDisplayedSoloChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
      cert)

/-- Final assembly from the displayed-solo route with both finite solo
sub-obligations split over the default 100-row chunks: the cleared displayed
`Y_a(N)` saddle inequality and the unit-scaled displayed-solo budget. -/
theorem coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    CoefficientNegativity :=
  coefficientNegativity_of_positiveSaddleXplusGcompTangentCellEdgeBudgetCertificate
    (PositiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
      cert)

/-- Final assembly from the displayed-solo route with both finite solo
sub-obligations and both finite product checks split over the default 100-row
chunks, using denominator-cleared finite product inequalities. -/
theorem coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    CoefficientNegativity :=
  coefficientNegativity_of_positiveSaddleXplusGcompTangentCellEdgeBudgetCertificate
    (PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
      cert)

/-- Final assembly from the corrected exact-product finite route: product
checks are denominator-cleared `Bq * Qq` inequalities over the default
100-row chunks, while tangent-edge and displayed-solo checks use the current
cell/chunk interfaces. -/
theorem coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    CoefficientNegativity :=
  coefficientNegativity_of_positiveSaddleTangentProductBudgetCertificate
    (PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toRawProductTangentCellEdgeBudgetCertificate
      cert |>.toTangentProductBudgetCertificate)

/-- Final assembly from the fine-grained table-backed exact-product route.
The finite product checks are supplied over a row-dependent `N`-chunk cover
and the default 20-wide retained-`k` chunks, avoiding whole-row product
booleans. -/
theorem coefficientNegativity_of_positiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate
    {productNChunks : Nat → List (Nat × Nat)}
    (cert :
      PositiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate
        productNChunks) :
    CoefficientNegativity :=
  coefficientNegativity_of_positiveSaddleTangentProductBudgetCertificate
    cert.toTangentProductBudgetCertificate

/-- Final assembly from the concrete table-backed exact-product route using
the built-in singleton `N` chunks, displayed-solo chunks, and uniform
large-scale edge `k`-chunk budget. -/
theorem coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    CoefficientNegativity :=
  coefficientNegativity_of_positiveSaddleTangentProductBudgetCertificate
    cert.toTangentProductBudgetCertificate

/-- Final assembly from the concrete table-backed exact-product route with
singleton `N` chunks, tangent-edge row chunks, displayed-solo chunks, and
fixed-scale edge row chunks. -/
theorem coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    CoefficientNegativity :=
  coefficientNegativity_of_positiveSaddleTangentProductBudgetCertificate
    cert.toTangentProductBudgetCertificate

/-- Final assembly from the parameterized table-backed exact-product route
whose generated finite product side may use arbitrary row-dependent `N`
chunks, while tangent, displayed-solo, and edge checks use the default
fixed-scale chunk interfaces. -/
theorem coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {productNChunks : Nat → List (Nat × Nat)}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productNChunks) :
    CoefficientNegativity :=
  coefficientNegativity_of_positiveSaddleTangentProductBudgetCertificate
    cert.toTangentProductBudgetCertificate

/-- Final assembly from the fixed-width `N`-chunk table-product route.  Product
checks are supplied over default row chunks, fixed-width row-dependent
`N`-chunks, and default retained-`k` chunks. -/
theorem coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        nLen) :
    CoefficientNegativity :=
  coefficientNegativity_of_positiveSaddleTangentProductBudgetCertificate
    cert.toTangentProductBudgetCertificate

/-- Final assembly from the fixed-width `N`-chunk table-product route with an
independent product row cover.  This lets generated product checks use row
chunks smaller than the default 100-row chunks used by tangent, solo, and
edge checks. -/
theorem coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductRowChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {productRowChunks : List (Nat × Nat)} {nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductRowChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productRowChunks nLen) :
    CoefficientNegativity :=
  coefficientNegativity_of_positiveSaddleTangentProductBudgetCertificate
    cert.toTangentProductBudgetCertificate

/-- Final assembly from the fixed-width `N`-chunk table-product route with
independent product and tangent row covers.  This is useful when generated
product checks and corrected tangent-edge checks require different row
granularities. -/
theorem coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductTangentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {productRowChunks tangentRowChunks : List (Nat × Nat)} {nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductTangentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productRowChunks tangentRowChunks nLen) :
    CoefficientNegativity :=
  coefficientNegativity_of_positiveSaddleTangentProductBudgetCertificate
    cert.toTangentProductBudgetCertificate

/-- Final assembly from the fixed-width `N`-chunk table-product route with
independent fixed product-row and tangent-row lengths. -/
theorem coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedProductTangentRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {productRowLen tangentRowLen nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedProductTangentRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productRowLen tangentRowLen nLen) :
    CoefficientNegativity :=
  coefficientNegativity_of_positiveSaddleTangentProductBudgetCertificate
    cert.toTangentProductBudgetCertificate

/-- Final assembly from the fixed-width `N`-chunk table-product route with
independent row covers for all finite range-check families. -/
theorem coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksIndependentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {productRowChunks tangentRowChunks soloSaddleRowChunks
      soloBudgetRowChunks edgeRowChunks : List (Nat × Nat)} {nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksIndependentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        productRowChunks tangentRowChunks soloSaddleRowChunks
        soloBudgetRowChunks edgeRowChunks nLen) :
    CoefficientNegativity :=
  coefficientNegativity_of_positiveSaddleTangentProductBudgetCertificate
    cert.toTangentProductBudgetCertificate

/-- Final assembly from the fully fixed-width product chunk route.  Product
checks use fixed-width row chunks and fixed-width `N` chunks, while tangent,
displayed-solo, and edge checks use the default fixed-scale chunk interfaces. -/
theorem coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedRowNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {rowLen nLen : Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedRowNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        rowLen nLen) :
    CoefficientNegativity :=
  coefficientNegativity_of_positiveSaddleTangentProductBudgetCertificate
    cert.toTangentProductBudgetCertificate

/-- Final assembly from the currently lowest-level default finite-window
route: product checks, tangent-edge checks, and displayed-solo checks are all
split over the default 100-row chunks, with denominator-cleared finite product
inequalities. -/
theorem coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    CoefficientNegativity :=
  coefficientNegativity_of_positiveSaddleXplusGcompTangentCellEdgeBudgetCertificate
    (PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
      cert)

/-- Final assembly from the default finite-window route whose finite product,
tangent-edge, displayed-solo, and edge `k`-chunk checks are all split over
default row chunks. -/
theorem coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    {edgeScale : Nat → Nat}
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
        edgeScale) :
    CoefficientNegativity :=
  coefficientNegativity_of_positiveSaddleXplusGcompTangentCellEdgeBudgetCertificate
    (PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
      cert)

/-- Final assembly from the fixed-scale version of the current default
finite-window route.  All edge `k`-chunk checks use
`positiveEdgeUniformScaleMin`, so no row-dependent scale data remains in the
finite certificate. -/
theorem coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate
    (cert :
      PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate) :
    CoefficientNegativity :=
  coefficientNegativity_of_positiveSaddleXplusGcompTangentCellEdgeBudgetCertificate
    (PositiveSaddleDefaultCellEdgeDisplayedSoloProductClearedTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate.toXplusGcompTangentCellEdgeBudgetCertificate
      cert)

/-- Final assembly from the actual-`N` combined `X*Y` product version of the
§6 positive-saddle certificate. -/
theorem coefficientNegativity_of_positiveSaddleAtProductBudgetCertificate
    (cert : PositiveSaddleAtProductBudgetCertificate) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleAtProductBudgetCertificate cert)

/-- Final assembly from the actual-`N` combined product certificate whose
small upper-edge replacement is stated as the cancellable exponential-gap
inequality. -/
theorem coefficientNegativity_of_positiveSaddleAtExpBudgetCertificate
    (cert : PositiveSaddleAtExpBudgetCertificate) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleAtExpBudgetCertificate cert)

/-- Final assembly from the plateau-anchor positive-saddle certificate. -/
theorem coefficientNegativity_of_positiveSaddleAtAnchorBudgetCertificate
    (cert : PositiveSaddleAtAnchorBudgetCertificate) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleAtAnchorBudgetCertificate cert)

/-- Final assembly from the decomposed `X`/`Y` saddle-bound version of the
§6 positive-saddle certificate. -/
theorem coefficientNegativity_of_positiveSaddleXYCertificate
    {soloBound : Nat → ℚ}
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    (cert : PositiveSaddleXYCertificate soloBound
      smallXBound smallYBound temperedXBound temperedYBound) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleXYCertificate cert)

end Prop51
