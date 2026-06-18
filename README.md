# prop51-formal

Formal verification (Lean 4 + mathlib) of the coefficient-negativity theorem
behind **Chen–Larson, Proposition 5.1** (*Independence of tautological classes
and cohomological stability for strata of differentials*,
[arXiv:2603.23850](https://arxiv.org/abs/2603.23850)), together with the
LaTeX proof document and the computational certificates it relies on.

## The theorem

Let `C(t) = Σ_k (6k)!/((3k)!(2k)!) (t/72)^k` and, for a positive partition
`μ = (m_1, …, m_n)` of `2g-2`, let

```
b_a(μ) = [t^a]  Π_i C(t/(m_i+1)) / C(t)^(2g-2+n),    a = ⌊g/3⌋ + 1 .
```

**Target** (`Prop51.CoefficientNegativity` in `Prop51/Main.lean`): for every
`g ≥ 2` with `g ≡ 0, 2 (mod 3)` and every positive partition `μ` of `2g-2`,
`b_a(μ) < 0`.  In particular the coefficient is nonzero, which is the
hypothesis of Chen–Larson Proposition 5.1; via their geometric reduction it
yields their Conjecture 1.4 for holomorphic abelian strata in those residue
classes — for *all* genera, extending their computer verification (`g ≤ 30`).

The proof (see `paper/prop51.tex`) has three layers:

| layer | range | method | formal status |
|---|---|---|---|
| enumeration | `g ≤ 23` (`a ≤ 8`) | exact rationals over all partitions | **proved** (`CertificateSmall.lean`) |
| majorant, exact | `9 ≤ a ≤ 60` | exact rationals, 10,764 pairs | **proved** (`CertificateExact.lean`) |
| majorant, interval | `61 ≤ a ≤ 400` | verified 192-bit dyadic intervals, 470,220 pairs | **proved** (`Prop51Kernel.lean` + `IntervalCert.lean` + 8 `native_decide` chunks) |
| effective tail | `a ≥ 401` | explicit sign-lock `C₂ = 2215` + positive-saddle audit certificate | **conditional assembly proved** (sign-lock closed; remaining work is a concrete positive-saddle audit certificate) |

## What is machine-checked today

All Lean proofs are sorry-free.  Headline theorems:

* `Prop51.bCoeff_neg_g_le_23` — `b_a(μ) < 0` for every generated partition,
  every relevant `g ≤ 23` (≈150k partitions; cardinalities cross-checked
  against p(n)).
* `Prop51.unorm_neg_9_60` — the normalized majorant `U_a(N)/(N c_a)` is
  negative on the entire rectangle `9 ≤ a ≤ 60`, `6a-7 ≤ N ≤ 12a-8`,
  with the exact corner value pinned at `(9,100)`.
* `Prop51.unorm_neg_9_400` — the certificate range assembled: exact
  rationals for `9 ≤ a ≤ 60`, *verified dyadic interval arithmetic* for
  `61 ≤ a ≤ 400` (`Prop51Kernel.lean` is a self-contained, Mathlib-free
  interval kernel — 192-bit outward-rounded dyadic floats, the working
  precision of the reference Arb run — whose enclosure semantics over `ℚ`
  is proved in `Prop51/Dyadic.lean`/`IntervalCert.lean`).
* **`Prop51.coefficientNegativity_of_g_le_1199`** — the capstone: for every
  `2 ≤ g ≤ 1199` with `g ≡ 0,2 (mod 3)` and every positive partition of
  `2g-2`, the Proposition 5.1 coefficient is negative.  Layer A (the
  power-series bridge `Cseries = expSeries c`, the official characterization
  `C^N · Σ b_a X^a = Π C(X/qᵢ)`, and the majorant inequality) and the Layer B
  soundness theory are fully formalized with **no computational axioms**;
  only the finite certificates use `native_decide`.
* **Canonical remaining proof-facing route**:
  `Prop51.coefficientNegativity_of_positiveSaddleFixedFiniteWindowActiveCombinedProductNKChunkedTangentSoloNFixedEdgeKChunkedRefinedAtomicBoundsAuditCertificate`
  is the intended final conditional endpoint for `a ≥ 401`: it combines the
  corrected row-active fixed-edge combined-product finite-window certificate
  with
  `Prop51.PositiveSaddleLargeTailRefinedAtomicBoundsAuditCertificate`,
  separating product bounds, solo bounds, and the one-dimensional large-tail
  candidate atoms.  This Lean interface intentionally refines the LaTeX
  raw-cleared adjacent-step presentation: the small step is the closed
  raw-base half certificate, and the two tempered step atoms are quotient-form
  raw-exp ratio targets.  It converts back to the atomic-bounds route
  `Prop51.coefficientNegativity_of_positiveSaddleFixedFiniteWindowActiveCombinedProductNKChunkedTangentSoloNFixedEdgeKChunkedAtomicBoundsAuditCertificate`.
  The non-active fixed-edge route is retained as an audit/profiling sibling;
  the active wrapper is a Lean proof-production optimization of the same
  finite-window inequalities.
  Older long-named capstones below are retained as audit and profiling
  alternatives, not as competing final routes.
* `Prop51.coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksIndependentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`
  — an older table-backed large-`a` conditional capstone: table-backed
  exact finite product chunks using a fixed-width row-dependent `N` cover and
  independent row covers for product, tangent, displayed-solo saddle,
  displayed-solo budget, and edge `k`-chunk checks, the default 20-wide
  retained-`k` chunks, a fixed edge scale, and the raw-cleared large-tail reserve
  certificate imply full
  `CoefficientNegativity`.  The intermediate
  `RawProductTableSingletonNChunksUniformLargeScale...` sibling keeps
  tangent-edge cell checks and a row-dependent edge scale.  The older
  `Prop51.coefficientNegativity_of_positiveSaddleDefaultCellEdgeKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`
  keeps a semantic finite solo budget and the older product staging.
  The sibling theorem
  `Prop51.coefficientNegativity_of_positiveSaddleDefaultCellEdgeUniformKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`
  is the same route with one edge unit scale per row; the further sibling
  `Prop51.coefficientNegativity_of_positiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`
  replaces the rational reciprocal-budget proof by the natural lower bound
  `Prop51.positiveEdgeUniformScaleMin ≤ edgeScale a`.  The displayed-solo
  variant
  `Prop51.coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`
  additionally splits the finite solo input into the TeX-shaped
  `Ynorm N a ≤ positiveYBound a N a` saddle bound and a unit-scaled rational
  budget check; the `DisplayedSoloChunks` sibling uses the same default
  100-row chunks for that budget check.  The
  `DisplayedSoloClearedChunks` sibling is the current lowest-level finite
  solo audit target: it also chunks the denominator-cleared displayed
  `Y_a(N)` saddle inequality.  For the product fields, the corrected current
  endpoint is
  `Prop51.coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`:
  it checks the exact denominator-cleared `Bq * Qq` product inequalities
  against the combined-exponent targets.  For generated finite product
  certificates, the finer-grained table-backed entry point
  `Prop51.coefficientNegativity_of_positiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate`
  is the practical target: it shares `c`, `B`, and `Q` tables at each
  `(a,N)` and splits product checks by a row-dependent `N`-chunk cover and
  the default 20-wide retained-`k` chunks.  `Prop51.positiveProductSingletonNChunks`
  provides a built-in singleton `N`-cover.  For generated audits, the
  `RawProductTableFixedNChunksProductTangentRowChunksFixedScale...` capstone
  packages row-range product checks using `Prop51.positiveProductFixedNChunks`
  and lets the corrected tangent-edge range checks use a separate row cover.
  The fully independent
  `RawProductTableFixedNChunksIndependentRowChunksFixedScale...` capstone
  additionally lets the displayed-solo saddle, displayed-solo budget, and edge
  finite range checks use their own row covers.  The final `N` chunk may
  harmlessly overrun the positive rectangle.  When fixed row lengths are
  enough for all finite check families, the
  `RawProductTableFixedFiniteRowNChunksFixedScale...` capstone supplies all
  row covers from `Prop51.positiveSaddleFixedRowChunks`.  Its split
  `Prop51.PositiveSaddleFixedFiniteWindowAuditCertificate` /
  `Prop51.PositiveSaddleLargeTailAuditCertificate` form keeps generated
  finite-window `native_decide` proofs separate from the remaining large-`a`
  analytic inputs.  If each whole finite family is small enough to evaluate
  at once, `Prop51.PositiveSaddleFixedFiniteWindowAllChunksAuditCertificate`
  packages one Boolean per finite family; `scripts/positive_saddle_fixed_finite_template.py`
  emits either that theorem shape or a `split-fields` version that dispatches
  each field by fixed row and edge chunk indices.  The
  `Prop51.PositiveSaddleFixedFiniteWindowCellTangentAuditCertificate` sibling
  keeps tangent checks at cell granularity, which is the practical shape when
  tangent row-range booleans are too large for `native_decide`; the same
  script emits it with `--strategy cell-tangent`.  The fully generated
  `Prop51.PositiveSaddleFixedFiniteWindowChunkedTangentAuditCertificate`
  additionally splits tangent by fixed row, `N`, and small-`k` chunks; use
  `--strategy chunked-tangent` to emit that target.  The finer
  `Prop51.PositiveSaddleFixedFiniteWindowProductNChunkedTangentAuditCertificate`
  also splits product by a uniform product `N`-chunk index; use
  `--strategy product-n-chunked-tangent` when product row-range checks are
  still too coarse.  The same script can emit one concrete cacheable chunk
  theorem at a time with `--emit-single-chunk`, which is the practical mode
  for large generated finite witnesses; pass `--use-single-chunk-theorems`
  to assemble the product-`N` chunked certificate from those names, or
  `--emit-single-chunk-suite` to emit the atom theorems and assembled
  certificate in one Lean module.  Use `--emit-single-chunk-manifest` to list
  the same atom names, global atom indices, and per-atom emit commands as JSON
  for batch proof production; add `--manifest-shard-count n` to include the
  balanced shard start/stop plan in the same file.  Use
  `--dry-run-active-counts` before manifest production to estimate how many
  row-local atoms can actually meet the finite positive rectangle.  For the
  fixed-edge combined strategy, pass `--active-row-covers` to make the
  generated certificate, manifest, and shard emission use those row-local `N`
  and retained-`k` covers instead of the global atom order.  Shard emission now
  computes its `[start, stop)` slice directly from the index formulas, so
  `--emit-single-chunk-shard` does not materialize the full manifest first.
  Lean
  also exposes
  `Prop51.PositiveSaddleFixedFiniteWindowProductTangentSoloNChunkedAuditCertificate`,
  which further splits tangent and displayed-solo checks by fixed `N`-chunk
  index when whole-row `N` scans are too large; emit it with
  `--strategy product-tangent-solo-n-chunked`.  The proof-production
  refinement
  `Prop51.PositiveSaddleFixedFiniteWindowProductNKChunkedTangentSoloNChunkedAuditCertificate`
  additionally splits product checks by `Prop51.positiveProductFixedKChunks`;
  emit it with `--strategy product-nk-tangent-solo-n-chunked` and choose
  `--product-k-len` independently of the default edge chunks.  This is still
  mathematically the same finite certificate target: the finer product
  `k`-atoms are assembled back into the existing 20-wide edge-product
  obligations.  In local profiling, one-row product atoms with
  `--n-len 10 --product-k-len 1` compile in roughly 13-15 seconds at
  `a = 401`, whereas the 20-wide product atom at `--n-len 10` did not finish
  in the earlier timeout.  Edge atoms now have the reusable semantic cover
  `Prop51.positiveEdgeFixedKChunks`: local profiling showed a 1600-row
  default 20-wide edge atom timing out, row lengths 2/5/10/20 taking roughly
  8/21/39/82 seconds, and one-wide retained-`k` edge atoms with
  `Prop51.positiveEdgeFixedKScale 1` compiling in about 1-6 seconds.  The
  further
  `PositiveSaddleFixedFiniteWindowCombinedProductNKChunkedTangentSoloNChunkedAuditCertificate`
  wrapper shares each table-backed `(a,N)` product pass between the small and
  tempered regimes; emit it with
  `--strategy combined-product-nk-tangent-solo-n-chunked` and
  `--emit-single-chunk product-combined`.  This is a Lean proof-production
  optimization of the same inequalities: the conversion extracts the separate
  small and tempered fields expected by the existing certificate.  In the
  same local sample, one combined product atom replaces the two separate
  small/tempered product atoms and compiles in about 15 seconds.  The
  fixed-edge refinement
  `PositiveSaddleFixedFiniteWindowCombinedProductNKChunkedTangentSoloNFixedEdgeKChunkedAuditCertificate`
  consumes `Prop51.positiveEdgeFixedKChunks` directly; emit it with
  `--strategy combined-product-nk-tangent-solo-n-fixed-edge-k-chunked` and
  choose `--edge-k-len` independently.  This avoids reconstructing the older
  default 20-wide edge booleans from fine edge atoms.  Lean also now exposes
  the row-active sibling
  `PositiveSaddleFixedFiniteWindowActiveCombinedProductNKChunkedTangentSoloNFixedEdgeKChunkedAuditCertificate`:
  its product/tangent/solo `N` indices and product/edge retained-`k` chunks
  are local to each row range, then reduce to the same tangent-product budget
  certificate.  This records a proof-production optimization beyond the
  TeX-style fixed global cover; the generator emits this route with
  `--active-row-covers`, including active manifests and active shard slices.
  Final assembly adapters mirror the fixed-edge tail interface family,
  including parts, product/solo bounds, atomic/refined bounds, grouped
  raw-cleared reserves, and the quotient/crossmul ten-sevenths tail shapes.
  The
  remaining large-tail inputs can also be supplied through
  `Prop51.PositiveSaddleLargeTailPartsAuditCertificate`, which splits the
  product-small, product-tempered, solo, adjacent-step, and unit-reserve
  analytic targets before reassembling the existing
  `Prop51.PositiveSaddleLargeTailAuditCertificate`.  This is only a
  proof-production decomposition of the same inequalities.  The product
  subtargets can now be supplied through
  `Prop51.PositiveSaddleLargeTailProductBoundsCertificate`, which splits each
  raw product inequality into separate `Bplus` and `Qplus/Y` saddle bounds
  plus a scalar product comparison.  The solo subtarget similarly has the
  `Prop51.PositiveSaddleLargeTailSoloYBoundCertificate` split between a
  `Y_a(N)` saddle bound and the dyadic unit budget.  On the product `X` side,
  `Prop51.BplusqGcompBound_eq_linear_BplusNonlinearGcompBound_sum` and
  `Prop51.BplusNonlinearGcompBound_le_Gcomp_sum` open the executable
  `BplusqGcompBound` recurrence into the explicit helper
  `Prop51.positiveLargeTailXGcompBlockSum`, with packaged bound
  `Prop51.BplusqGcompBound_le_positiveLargeTailXGcompBlockSum`.  The `Y`
  side has the matching helper
  `Prop51.QqEplusGcompBound_le_positiveLargeTailYGcompBlockSum`, and
  `Prop51.PositiveSaddleLargeTailProductBlockSumCertificate` reduces the
  product certificate to the two explicit block-sum scalar product
  comparisons.  These scalar obligations are named
  `Prop51.positiveLargeTailSmallProductBlockSumScalar` and
  `Prop51.positiveLargeTailTemperedProductBlockSumScalar`, with
  `Prop51.PositiveSaddleLargeTailProductBlockSumScalarCertificate` packaging
  exactly those two families.  The wrapper
  `Prop51.positiveSaddleLargeTailAuditCertificate_of_productBlockSumScalars_soloGcompBlockSumCleared`
  is the most reduced current large-tail assembly interface for the explicit
  product and solo block-sum route; the sibling
  `Prop51.positiveSaddleLargeTailAuditCertificate_of_productBlockSum_soloGcompBlockSumCleared`
  accepts the already-assembled block-sum product certificate.  The recursive
  `Gcomp` factors in these block sums can now be replaced by the closed
  Lemma 3.1 all-range majorant `Prop51.GcompClosedBound`: product-side
  scalar fields are packaged by
  `Prop51.PositiveSaddleLargeTailProductClosedBlockSumScalarCertificate`, and
  the corresponding audit wrapper is
  `Prop51.positiveSaddleLargeTailAuditCertificate_of_productClosedBlockSumScalars_soloGcompClosedBlockSumCleared`.
  The aliases `Prop51.positiveLargeTailXGcompClosedActiveBlockSum`,
  `Prop51.positiveLargeTailYGcompClosedActiveBlockSum`, and
  `Prop51.positiveLargeTailSoloGcompClosedActiveBlockSum` remove the inactive
  zero `GcompClosedBound` terms while proving equality to the all-range sums;
  `Prop51.PositiveSaddleLargeTailProductClosedActiveBlockSumScalarCertificate`
  and
  `Prop51.positiveSaddleLargeTailAuditCertificate_of_productClosedActiveBlockSumScalars_soloGcompClosedActiveBlockSumCleared`
  expose that active form as a large-tail audit input.  The further
  factorial-only target
  `Prop51.PositiveSaddleLargeTailProductClosedFactorialBlockSumScalarCertificate`
  and wrapper
  `Prop51.positiveSaddleLargeTailAuditCertificate_of_productClosedFactorialBlockSumScalars_soloGcompClosedFactorialBlockSumCleared`
  replace the active `GcompClosedBound` terms by the explicit Lemma 3.1
  factorial expression.  This is a Lean proof-production refinement of the
  TeX block-sum estimate.  The sibling split-final-term target
  `Prop51.PositiveSaddleLargeTailProductClosedFactorialSplitBlockSumScalarCertificate`
  and wrapper
  `Prop51.positiveSaddleLargeTailAuditCertificate_of_productClosedFactorialSplitBlockSumScalars_soloGcompClosedFactorialSplitBlockSumCleared`
  expose the same factorial expression with the final linear-exponential term
  split off from the active positive block; this is a Lean-facing
  normalization of the same large-tail estimate.  This split route now also
  constructs the preferred concrete
  `Prop51.PositiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate`
  before converting to the audit certificate.  The fast-evaluator sibling
  `Prop51.PositiveSaddleLargeTailProductClosedFactorialSplitBlockSumScalarFastExpCertificate`
  uses `partialExpUpperFast` for the small/tempered exponential factors, and
  the solo target
  `Prop51.positiveLargeTailSoloGcompClosedFactorialSplitBlockSumFastCleared`
  does the same for the solo `8a` exponential shell; both rewrite back to the
  canonical split-final-term target before entering the audit certificate.
  The sibling fast-product/solo-envelope route keeps the fast split product
  fields but asks directly for the solo envelope
  `Prop51.positiveYgcompBound N a ≤ Prop51.positiveLargeTailSoloTenSeventhsBound a N`,
  matching the actual solo field of the hybrid-ratio audit certificate.
  A more structured sibling keeps the same final `(10/7)^a` solo budget but
  asks for the split-final-term factorial solo sum in the cleared form
  `Prop51.positiveLargeTailSoloGcompClosedFactorialSplitBlockSumTenSeventhsCleared`;
  this is another Lean proof-production target, weaker than the
  `partialExpUpperFast` solo shell and converted internally to the same solo
  envelope.  The bridge
  `Prop51.positiveLargeTailSoloGcompClosedFactorialSplitBlockSumTenSeventhsCleared_of_fastCleared`
  now also lets a proof of the stronger fast solo shell feed this direct
  `(10/7)^a` target.  Its upper-edge reduction
  `Prop51.positiveLargeTailSoloGcompClosedFactorialSplitBlockSumTenSeventhsCleared_of_upperEdge`
  proves that it is enough to supply this direct solo check at
  `N = posNhi a`, with monotonicity filling the positive rectangle.
  A Lean-only strengthened product sibling
  `Prop51.PositiveSaddleLargeTailProductClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerNCertificate`
  asks for the fast split-final-term product scalar checks only at the upper
  rectangle edge, while deliberately keeping the right-hand `N` factor at
  `posNlo a`.  This is stronger than the TeX scalar comparison and is
  documented in code; the conversion uses monotonicity of the closed
  factorial product bound and the lower rectangle bound `posNlo a ≤ N`.  The
  structured refined-atomic sibling
  `Prop51.PositiveSaddleLargeTailTemperedRawExpRatioTenSeventhsClosedReserveSoloUpperEdgeProductUpperEdgeLowerNBoundsAuditCertificate`
  combines this product witness with the upper-edge split-factorial
  ten-sevenths solo check and the two quotient-form tempered raw-exp atoms,
  then converts back to the canonical refined atomic-bounds route.
  The preferred concrete hybrid-ratio sibling
  `Prop51.PositiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloUpperEdgeProductUpperEdgeLowerNBoundsAuditCertificate`
  has only the strengthened product and upper-edge split-factorial
  ten-sevenths solo fields; the candidate side is filled by the generated
  prefix raw-budget/exp-ratio certificates and the proved upper-middle
  reverse target.
  The matching top-level
  coefficient capstones are
  `Prop51.coefficientNegativity_of_positiveSaddleFixedFiniteWindowCombinedProductNKChunkedTangentSoloNFixedEdgeKChunkedClosedFactorialBlockSumTail`
  and its row-active sibling
  `Prop51.coefficientNegativity_of_positiveSaddleFixedFiniteWindowActiveCombinedProductNKChunkedTangentSoloNFixedEdgeKChunkedClosedFactorialBlockSumTail`,
  plus the corresponding `...ClosedFactorialSplitBlockSumTail` pair for the
  split-final-term certificate shape, and `...ClosedFactorialSplitBlockSumFastTail`
  for the fast-evaluator certificate shape.  The direct solo-envelope variant
  is exposed as `...ClosedFactorialSplitBlockSumFastProductSoloEnvelopeTail`;
  the structured direct ten-sevenths solo variant is exposed as
  `...ClosedFactorialSplitBlockSumFastProductSoloTenSeventhsTail`, with
  `...ClosedFactorialSplitBlockSumFastProductUpperEdgeLowerNSoloTenSeventhsUpperEdgeTail`
  exposing the direct audit route for the strengthened product/upper-edge
  solo target.  The stronger fast-solo upper-edge bridge is exposed as
  `...ClosedFactorialSplitBlockSumFastProductUpperEdgeLowerNSoloFastUpperEdgeTail`.
  The canonical refined-atomic version is exposed as
  `...TemperedRawExpRatioTenSeventhsClosedReserveSoloUpperEdgeProductUpperEdgeLowerNBoundsAuditCertificate`,
  while the preferred concrete hybrid-ratio version is exposed as
  `...TemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloUpperEdgeProductUpperEdgeLowerNBoundsAuditCertificate`.
  For final
  assembly from
  these lower-level product and solo proofs,
  `Prop51.PositiveSaddleLargeTailBoundsPartsAuditCertificate` bundles those
  bound certificates with the grouped candidate step/reserve fields.  The finer
  `Prop51.PositiveSaddleLargeTailAtomicPartsAuditCertificate` additionally
  splits the six candidate entropy-reserve fields into separate atomic
  one-dimensional inequality families, while
  `Prop51.PositiveSaddleLargeTailAtomicBoundsAuditCertificate` bundles the
  product/solo bound certificates with those atomic candidate fields.  The
  proof-facing
  `Prop51.PositiveSaddleLargeTailRefinedAtomicBoundsAuditCertificate` bundles
  the same product/solo bounds with the smaller refined candidate certificate
  using the small raw-base half and tempered raw-exp ratio atoms.  Existing
  grouped raw-cleared unit-reserve proofs can also be split back into those
  atomic candidate fields; the convenience wrapper
  `Prop51.PositiveSaddleLargeTailRawClearedUnitBoundsAuditCertificate` accepts
  product/solo bounds together with that grouped raw-cleared unit-reserve
  proof and converts to the atomic-bounds route.  The core large-tail audit
  certificate also exposes reverse parts and atomic-parts views for audit.
  The small adjacent-step atom can be supplied in the still smaller
  `Prop51.PositiveSaddleLargeTailCandidateSmallRawBaseHalfCertificate` form:
  Lean now proves the pure raw-base half-quotient theorem
  `Prop51.positiveEntropyShadowBaseStepRawBaseHalf_of_small_branch` directly
  from the rational `(1+1/n)^n ≤ 68/25` bound and the small-cutoff linear gap,
  and packages it as
  `Prop51.positiveSaddleLargeTailCandidateSmallRawBaseHalfCertificate`.  The
  conversion theorem then restores the original raw-cleared small-step field
  using monotonicity of the small large-exp factor.  Constructors such as
  `Prop51.positiveSaddleLargeTailCandidateRefinedAtomicCertificate_of_temperedRawExpRatios`
  and
  `Prop51.positiveSaddleLargeTailRefinedAtomicBoundsAuditCertificate_of_temperedRawExpRatios`
  fill this closed small-step atom automatically, so the live refined
  candidate obligations are the two tempered ratio atoms and the three
  reserve atoms.  The corresponding tail wrapper
  `Prop51.PositiveSaddleLargeTailTemperedRawExpRatioReserveBoundsAuditCertificate`
  and final theorem
  `Prop51.coefficientNegativity_of_positiveSaddleFixedFiniteWindowCombinedProductNKChunkedTangentSoloNFixedEdgeKChunkedTemperedRawExpRatioReserveBoundsAuditCertificate`
  expose exactly this reduced obligation set.  Lean also exposes the stricter
  proof-production wrapper
  `Prop51.PositiveSaddleLargeTailTemperedRawExpRatioReserveEnvelopeBoundsAuditCertificate`,
  where the three reserve atoms are split into explicit large-exp envelope
  bounds and entropy-shadow base-times-envelope unit budgets; this records the
  reserve-envelope estimate that is implicit in the TeX write-up as a named
  Lean obligation.  Generated final assemblies can target it with
  `--final-tail-tempered-raw-exp-ratio-reserve-envelope-bounds`.  The small
  first-reserve budget side is now closed: Lean proves
  `Prop51.positiveSmallFirstReserveThreeHalvesEnvelopeUnit`, so the theorem
  `Prop51.positiveSaddleLargeTailCandidateSmallFirstReserveEnvelopeCertificate_threeHalves`
  reduces that atom to the single exponential-envelope estimate
  `positiveSmallLargeExp a 1 ≤ (3/2)^a`.  Lean further reduces that estimate
  to the standalone shell bound
  `partialExpUpper ((3/10) * a) a ≤ (3/2)^a`, via
  `Prop51.positiveSmallExponentUpper_one_le_three_tenths_self` and
  `Prop51.positiveSmallLargeExp_one_le_threeHalvesExpBound_of_partialExpUpper_threeTenths`.
  Lean then compares that shell termwise with the weighted multichoose
  expression
  `Prop51.partialExpUpperNegativeBinomialShell a (3/10)`, and closes that
  expression by bounding it with the complete negative-binomial series
  `(10/7)^a ≤ (3/2)^a`.  The closed reserve-facing wrappers are
  `Prop51.positiveSmallLargeExp_one_le_threeHalvesExpBound` and
  `Prop51.positiveSaddleLargeTailCandidateSmallFirstReserveEnvelopeCertificate_threeHalves_closed`.
  Lean also exposes reduced tail wrappers
  `Prop51.PositiveSaddleLargeTailTemperedRawExpRatioTemperedReserveBoundsAuditCertificate`
  and
  `Prop51.PositiveSaddleLargeTailTemperedRawExpRatioTemperedReserveEnvelopeBoundsAuditCertificate`,
  where the small first-reserve atom is filled automatically and the live
  reserve inputs are only the two tempered endpoint atoms or envelopes.
  For the endpoint envelope route, Lean first proves both tempered large-exp
  bounds against the coarse `(3/2)^a` envelope, but the useful reserve target
  is the sharper `(10/7)^a` envelope coming from the same
  negative-binomial shell.  The practical constructors are
  `Prop51.positiveSaddleLargeTailCandidateTemperedLowerFirstReserveEnvelopeCertificate_tenSevenths`
  and
  `Prop51.positiveSaddleLargeTailCandidateTemperedUpperLastReserveEnvelopeCertificate_tenSevenths`;
  both endpoint unit budgets are now closed by Lean-side coarse dyadic
  estimates,
  `Prop51.positiveTemperedLowerFirstTenSeventhsEnvelopeUnit` and
  `Prop51.positiveTemperedUpperLastTenSeventhsEnvelopeUnit`.  The combined
  reserve wrappers are
  `Prop51.positiveSaddleLargeTailCandidateTemperedLowerFirstReserveEnvelopeCertificate_tenSevenths_closed`,
  `Prop51.positiveSaddleLargeTailCandidateTemperedUpperLastReserveEnvelopeCertificate_tenSevenths_closed`,
  `Prop51.positiveSaddleLargeTailCandidateReserveEnvelopeCertificate_temperedTenSevenths_closed`,
  and
  `Prop51.positiveSaddleLargeTailCandidateUnitReserveCertificate_temperedTenSevenths_closed`.
  The closed reserve audit-facing wrappers
  `Prop51.PositiveSaddleLargeTailTemperedRawExpRatioTenSeventhsClosedReserveBoundsAuditCertificate`
  and
  `Prop51.PositiveSaddleLargeTailTemperedRawExpCrossmulTenSeventhsClosedReserveBoundsAuditCertificate`;
  expose only the product bounds, a solo bound certificate, and the two
  tempered adjacent-step atoms.  Lean further fixes the solo scalar budget to
  the envelope
  `Prop51.positiveLargeTailSoloTenSeventhsBound a N =
  (29/2) * (a/N) * (10/7)^a`.  The preferred audit-facing wrappers are now
  `Prop51.PositiveSaddleLargeTailTemperedRawExpRatioTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate`
  and
  `Prop51.PositiveSaddleLargeTailTemperedRawExpCrossmulTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate`;
  they expose product bounds, the analytic saddle estimate
  `positiveYgcompBound N a ≤ positiveLargeTailSoloTenSeventhsBound a N`, and
  the two tempered adjacent-step atoms.  The solo estimate can now also be
  supplied through the denominator-cleared
  `Prop51.positiveLargeTailSoloGcompSaddleCleared` target; the theorem
  `Prop51.positiveYgcompBound_le_positiveLargeTailSoloTenSeventhsBound_of_gcompSaddleCleared`
  converts it back to the displayed `(10/7)^a` envelope, and
  `Prop51.positiveSaddleLargeTailAuditCertificate_of_product_soloGcompSaddleCleared`
  exposes this as the current proof-facing large-tail wrapper.  The same
  target opens into the TeX-shaped linear/nonlinear finite sum
  `Prop51.positiveLargeTailSoloGcompSaddleSumCleared` via
  `Prop51.positiveLargeTailSoloGcompSaddleCleared_iff_sumCleared`, using
  `Prop51.QqEplusGcompBound_eq_linear_EplusGcompBound_sum`.  The nonlinear
  recurrence can be opened once more by
  `Prop51.EplusGcompBound_le_Gcomp_sum`, yielding the explicit double-sum
  target `Prop51.positiveLargeTailSoloGcompBlockSumCleared` and the audit
  wrapper
  `Prop51.positiveSaddleLargeTailAuditCertificate_of_product_soloGcompBlockSumCleared`.
  The solo double sum also has a closed-composition target
  `Prop51.positiveLargeTailSoloGcompClosedBlockSumCleared`, with
  `Prop51.positiveSaddleLargeTailSoloYBoundCertificate_tenSevenths_of_gcompClosedBlockSumCleared`
  converting it to the same `(10/7)^a` solo envelope.
  The older
  staging wrappers
  `Prop51.PositiveSaddleLargeTailTemperedRawExpRatioTenSeventhsReserveEnvelopeBoundsAuditCertificate`
  and
  `Prop51.PositiveSaddleLargeTailTemperedRawExpCrossmulTenSeventhsReserveEnvelopeBoundsAuditCertificate`
  still expose both endpoint unit-budget fields, with quotient-form or
  denominator-cleared tempered adjacent-step atoms respectively; both fields
  can now be filled by the closed theorems above.
  For the
  lower-tempered
  adjacent-step atom, Lean proves that the lower-side tempered large-exp
  factor decreases up to `Prop51.positiveLargeExpTemperedSplit`; this
  monotonicity is useful bookkeeping, but the pure raw-base ratio alone is
  too strong near the split.  The official remaining target is therefore
  still the raw-cleared field
  `Prop51.PositiveSaddleLargeTailCandidateTemperedLowerRawStepCertificate`,
  where the quantitative decrease of the large-exp factor must be used
  together with the entropy-shadow raw quotient.  The equivalent proof-facing
  reduced target is now exposed as
  `Prop51.PositiveSaddleLargeTailCandidateTemperedLowerRawExpRatioCertificate`;
  its field is the honest quotient inequality for
  `rawQuotient * positiveTemperedLargeExp(a,r+1) /
  positiveTemperedLargeExp(a,r)`, and Lean converts it back to the
  raw-cleared step.  The upper-tempered reverse step has the analogous
  quotient-form interface
  `Prop51.PositiveSaddleLargeTailCandidateTemperedUpperReverseRawExpRatioCertificate`.
  For generated rational audits, Lean also exposes the denominator-cleared
  equivalents
  `Prop51.PositiveSaddleLargeTailCandidateTemperedLowerRawExpCrossmulCertificate`
  and
  `Prop51.PositiveSaddleLargeTailCandidateTemperedUpperReverseRawExpCrossmulCertificate`;
  the adapters to the quotient interfaces are proved from positivity of the
  tempered large-exp factors and the raw base quotient.  Lean now also exposes
  the proof-production split
  `Prop51.PositiveSaddleLargeTailCandidateTemperedLowerRawUpperExpFactorCertificate`,
  using the proved raw quotient envelope
  `Prop51.positiveEntropyShadowBaseStepRawUpperBound`, and
  `Prop51.PositiveSaddleLargeTailCandidateTemperedUpperReverseFactorCertificate`,
  which separates the inverse raw quotient from the reverse large-exp quotient.
  This factorization is not a new mathematical route; it records the remaining
  quantitative estimates in smaller Lean-facing pieces.  The most reduced
  current Lean targets are
  `Prop51.PositiveSaddleLargeTailCandidateTemperedLowerExpTargetCertificate`
  and
  `Prop51.PositiveSaddleLargeTailCandidateTemperedUpperReverseExpTargetCertificate`,
  which ask only for the two displayed large-exp quotient estimates after the
  raw quotient bookkeeping has been discharged.  Division-free variants
  `Prop51.PositiveSaddleLargeTailCandidateTemperedLowerExpTargetCrossmulCertificate`
  and
  `Prop51.PositiveSaddleLargeTailCandidateTemperedUpperReverseExpTargetCrossmulCertificate`
  are also available for generated or denominator-cleared analytic audits.
  The upper target is now closed in Lean on the far upper branch
  `3 * a ≤ 5 * r`, using exponent monotonicity together with the exact raw
  entropy-shadow lower bound.  The reduced upper input is
  `Prop51.PositiveSaddleLargeTailCandidateTemperedUpperReverseMiddleExpTargetCrossmulCertificate`,
  whose field only covers the middle band `5 * r < 3 * a`; its adapter fills
  the far branch automatically.  This is a Lean-side refinement of the same
  raw-cleared reverse-step argument, not a separate route from the TeX proof.
  The lower target is already closed on the front subrange
  `8 * (r + 1) ≤ a` by
  `Prop51.positiveTemperedLargeExp_lowerExpQuotientTarget_of_eight_mul_succ_le`;
  the hard lower work is therefore concentrated closer to
  `Prop51.positiveLargeExpTemperedSplit`.  For that reduced obligation use
  `Prop51.PositiveSaddleLargeTailCandidateTemperedLowerNearSplitExpTargetCrossmulCertificate`,
  whose adapter fills the front subrange automatically.
  A sharper lower route is also exposed through
  `Prop51.PositiveSaddleLargeTailCandidateTemperedLowerRawTwoUpperCertificate`
  and
  `Prop51.PositiveSaddleLargeTailCandidateTemperedLowerSharpTopExpTargetCrossmulCertificate`:
  the former is now closed in Lean from the exact raw power-product estimate
  `Prop51.positiveSaddleLargeTailCandidateTemperedLowerRawPowerProductCertificate`,
  and the latter only has to handle the top strip `a < 3 * (r + 1)`.
  This top-strip target also has the constant-width offset form
  `Prop51.PositiveSaddleLargeTailCandidateTemperedLowerSharpTopOffsetExpTargetCrossmulCertificate`,
  whose adapter reduces it to the ten families `r = a/3 + t`, `t < 10`.
  The convenience wrappers
  `Prop51.positiveSaddleLargeTailCandidateRefinedAtomicCertificate_of_temperedLowerSharpTopExpTarget_upperExpTarget_temperedReserves`
  and
  `Prop51.positiveSaddleLargeTailCandidateRefinedAtomicCertificate_of_temperedLowerSharpTopExpTarget_upperExpTarget_temperedReserveEnvelopes`
  therefore take no separate lower raw-side certificate.
  At the product/solo-bounds audit level, the corresponding reduced route is
  exposed by
  `Prop51.PositiveSaddleLargeTailTemperedSharpTopOffsetExpTargetTemperedReserveBoundsAuditCertificate`
  and its envelope, `(10/7)^a`, closed-reserve, and solo-envelope variants.
  These Lean interfaces are slightly more fine-grained than the TeX
  raw-cleared adjacent-step statement: the lower raw power-product bound is
  proved once in Lean, and the remaining lower large-exp work is exactly the
  ten top-strip offset families.
  The finite generator can target these split
  final-theorem interfaces with `--emit-final --final-tail-parts`,
  `--final-tail-bounds-parts`,
  `--final-tail-atomic-parts`, `--final-tail-atomic-bounds`, or
  `--final-tail-raw-cleared-unit-bounds`; use
  `--final-tail-refined-atomic-bounds` for the explicit refined atomic route
  above, `--final-tail-closed-factorial-block-sum` for the reduced
  factorial-only product/solo block-sum tail target,
  `--final-tail-closed-factorial-split-block-sum` for the split-final-term
  factorial-only product/solo block-sum target,
  `--final-tail-closed-factorial-split-block-sum-fast` for the fast-evaluator
  version of that split target,
  `--final-tail-closed-factorial-split-block-sum-fast-product-solo-envelope`
  for the fast product target with a direct solo envelope, or
  `--final-tail-closed-factorial-split-block-sum-fast-product-solo-ten-sevenths`
  for the fast product target with the split-final-term solo sum cleared
  directly against `(10/7)^a`; use
  `--final-tail-closed-factorial-split-block-sum-fast-product-solo-ten-sevenths-upper-edge`
  for the same target when the solo proof is supplied only at `N = posNhi a`,
  `--final-tail-tempered-raw-exp-ratio-reserve-bounds` for the
  route that fills the small step in Lean but still accepts all three reserve
  atoms, or `--final-tail-tempered-raw-exp-ratio-tempered-reserve-bounds` for
  the route that also fills the small first reserve in Lean.  Use
  `--final-tail-tempered-raw-exp-ratio-reserve-envelope-bounds` when all three
  reserve atoms are supplied through separate exponential envelope bounds, or
  `--final-tail-tempered-raw-exp-ratio-tempered-reserve-envelope-bounds` when
  only the two remaining tempered reserve atoms are supplied through
  envelope bounds.  Use
  `--final-tail-tempered-raw-exp-crossmul-tempered-reserve-bounds` or
  `--final-tail-tempered-raw-exp-crossmul-tempered-reserve-envelope-bounds`
  for the same reduced tail routes with denominator-cleared tempered
  adjacent-step atoms.  Use
  `--final-tail-tempered-raw-exp-ratio-ten-sevenths-reserve-envelope-bounds`
  or
  `--final-tail-tempered-raw-exp-crossmul-ten-sevenths-reserve-envelope-bounds`
  for the concrete `(10/7)^a` endpoint-envelope variants, and use
  `--final-tail-tempered-raw-exp-ratio-ten-sevenths-closed-reserve-bounds`
  or
  `--final-tail-tempered-raw-exp-crossmul-ten-sevenths-closed-reserve-bounds`
  for the variants where both endpoint reserve budgets are filled in Lean.
  Use
  `--final-tail-tempered-raw-exp-ratio-ten-sevenths-closed-reserve-solo-envelope-bounds`
  or
  `--final-tail-tempered-raw-exp-crossmul-ten-sevenths-closed-reserve-solo-envelope-bounds`
  for the preferred variants where the endpoint reserve budgets and the solo
  scalar budget are filled in Lean.  The sharper lower top-strip route uses
  `--final-tail-tempered-sharp-top-offset-exp-target-tempered-reserve-bounds`,
  `--final-tail-tempered-sharp-top-offset-exp-target-tempered-reserve-envelope-bounds`,
  `--final-tail-tempered-sharp-top-offset-exp-target-ten-sevenths-reserve-envelope-bounds`,
  `--final-tail-tempered-sharp-top-offset-exp-target-ten-sevenths-closed-reserve-bounds`,
  or the most reduced
  `--final-tail-tempered-sharp-top-offset-exp-target-ten-sevenths-closed-reserve-solo-envelope-bounds`.
  The Lean constructors also accept the reduced upper-middle target through
  `Prop51.positiveSaddleLargeTailCandidateRefinedAtomicCertificate_of_temperedLowerSharpTopOffsetExpTarget_upperMiddleExpTarget_temperedReserves`,
  its envelope analogue, and the corresponding bounds-level wrappers; these
  replace the full upper exp-target field by the middle-band-only field above.
  The generator exposes these reduced upper-middle wrappers with
  `--final-tail-tempered-sharp-top-offset-upper-middle-exp-target-tempered-reserve-bounds`,
  its tempered-reserve-envelope and `(10/7)^a` variants, and the most reduced
  `--final-tail-tempered-sharp-top-offset-upper-middle-exp-target-ten-sevenths-closed-reserve-solo-envelope-bounds`.
  A further Lean-side hybrid lower route is exposed by
  `Prop51.PositiveSaddleLargeTailCandidateTemperedLowerSharpTopOffsetHybridRawExpCertificate`.
  It records the deliberate refinement that the separated lower sharp-offset
  large-exp target is too strong in the short prefix `2000 < a < 3000`, so
  the finite-prefix top strip is checked by the original combined raw-exp
  crossmul inequality, while the front subrange is filled in Lean and
  `3000 ≤ a` uses the separated ten-offset large-exp target.  The
  corresponding final-style wrapper is
  `Prop51.PositiveSaddleLargeTailTemperedSharpTopOffsetHybridRawExpUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate`,
  and the generator flag is
  `--final-tail-tempered-sharp-top-offset-hybrid-raw-exp-upper-middle-exp-target-ten-sevenths-closed-reserve-solo-envelope-bounds`.
  Certificate producers can also split the finite prefix through the Boolean
  `(a,t)` chunk checker
  `Prop51.checkPositiveTemperedLowerPrefixTopOffsetRawExpCrossmulChunk`, with
  assembly by
  `Prop51.PositiveSaddleLargeTailCandidateTemperedLowerSharpTopOffsetHybridRawExpChunkedCertificate`.
  The corresponding final wrapper is
  `Prop51.PositiveSaddleLargeTailTemperedSharpTopOffsetHybridRawExpChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate`,
  exposed by
  `--final-tail-tempered-sharp-top-offset-hybrid-raw-exp-chunked-upper-middle-exp-target-ten-sevenths-closed-reserve-solo-envelope-bounds`.
  The combined raw-exp prefix atoms are intentionally no longer the preferred
  proof-production target: even with the tail-recursive evaluator for
  `partialExpUpper`, exact `native_decide` must still expand the `8a`
  exponential shell.  The newer split route uses the row-dependent prefix quotient
  target
  `Prop51.positiveTemperedLowerPrefixTopOffsetExpRatioTarget a =
  1 - 213/(5a)`,
  checks only the raw budget with
  `Prop51.checkPositiveTemperedLowerPrefixTopOffsetRawBudgetChunk`, and
  reassembles through
  `Prop51.PositiveSaddleLargeTailCandidateTemperedLowerSharpTopOffsetHybridRatioChunkedCertificate`.
  The raw-only prefix budget is already packaged in
  `Prop51.PositiveSaddlePrefixRawBudget` as
  `Prop51.positiveSaddleLargeTailCandidateTemperedLowerPrefixTopOffsetRawBudgetChunksCertificate`
  for one chunk covering `a = 2001..2999`, `t = 0..9`.  The target is
  deliberately row-dependent: the earlier constant `2447/2500` is too strong
  for the large-exp quotient near `a = 3000`.  The corresponding explicit
  large-exp quotient certificate now has a reduced proof-production checker
  `Prop51.checkPositiveTemperedLowerPrefixTopOffsetExpRatioReducedChunk`,
  which compares a cutoff-`700` numerator majorant to the target times an
  `800`-term denominator prefix and converts through
  `Prop51.PositiveSaddleLargeTailCandidateTemperedLowerPrefixTopOffsetExpRatioChunksCertificate.toExpRatioCertificate`;
  `Prop51.PositiveSaddlePrefixExpRatio`,
  `Prop51.PositiveSaddlePrefixExpRatio2`,
  `Prop51.PositiveSaddlePrefixExpRatio3`,
  `Prop51.PositiveSaddlePrefixExpRatio4`, and
  `Prop51.PositiveSaddlePrefixExpRatio5` contain all twenty generated 50-row
  chunks, and `Prop51.PositiveSaddlePrefixExpRatioCertificate` packages them
  as
  `Prop51.positiveSaddleLargeTailCandidateTemperedLowerPrefixTopOffsetExpRatioCertificate`;
  the final-style wrapper is
  `Prop51.PositiveSaddleLargeTailTemperedSharpTopOffsetHybridRatioChunkedUpperMiddleExpTargetTenSeventhsClosedReserveSoloEnvelopeBoundsAuditCertificate`.
  The upper-middle input to this wrapper is now concrete in Lean as
  `Prop51.positiveSaddleLargeTailCandidateTemperedUpperReverseMiddleExpTargetCrossmulCertificate`;
  `Prop51.positiveSaddleLargeTailAuditCertificate_of_product_solo` is the
  corresponding large-tail audit constructor whose remaining arguments are
  the product bounds and the solo `Y` envelope.  The finite generator targets
  this preferred ratio/raw-budget chunked final route with
  `--final-tail-tempered-sharp-top-offset-hybrid-ratio-chunked-upper-middle-exp-target-ten-sevenths-closed-reserve-solo-envelope-bounds`.
  For the concrete strengthened product plus upper-edge solo tail whose
  candidate side is already closed by those certificates, use
  `--final-tail-tempered-sharp-top-offset-hybrid-ratio-chunked-ten-sevenths-closed-reserve-solo-upper-edge-product-upper-edge-lower-n-bounds`.
  If the solo witness is produced in the stronger fast-shell form at
  `N = posNhi a`, use
  `--final-tail-closed-factorial-split-block-sum-fast-product-upper-edge-lower-n-solo-fast-upper-edge`.
  Use
  repeated `--extra-import` flags
  when the atom theorems live in separately built Lean modules.  Before
  emitting a full manifest, run the same command with `--dry-run-counts` to
  print formula-based atom counts without materializing the atom list, or with
  `--dry-run-active-counts` to also report the row-local active-geometry
  estimate, skipped-vs-global totals, and `row_samples` at `a = 401, 1000,
  2000`.  Those active estimates have a matching Lean certificate interface
  and first-class active manifest/shard emission for the fixed-edge combined
  strategy.
  `--emit-single-chunk-shard --shard-index i --shard-count n` emits balanced
  atom modules using the same global ordering as
  `--emit-single-chunk-manifest`.
  When
  common product-row and tangent-row lengths are enough, the
  `RawProductTableFixedProductTangentRowNChunksFixedScale...` capstone
  supplies both row covers from `Prop51.positiveSaddleFixedRowChunks`.  When a
  common product row length and `N` length are enough but tangent can stay on
  the default chunks, the
  `RawProductTableFixedRowNChunksTangentEdgeChunksFixedScale...` capstone
  also supplies the product row cover from `Prop51.positiveSaddleFixedRowChunks`.
  The fully parameterized
  `RawProductTableNChunksTangentEdgeChunksFixedScale...` capstone is
  available for custom row-dependent `N` chunk families.
  The older
  `DisplayedSoloProductCleared...`/fixed-scale `Gcomp` wrappers remain in
  Lean as audit interfaces for the stronger independent-majorant route, but
  that route is too strong for the finite window: direct checks already fail
  at `a = 401`, `N = 6*401 - 7`, `k = 1`.
* Spec lemmas (`Prop51/Defs.lean`): the computational definitions satisfy
  their defining recurrences (`c_succ_succ`, `cList_getD_eq`, …) — these
  carry no computational axioms.

## Trust model

Certificate theorems are proved by `native_decide`, so they depend on the
axioms `Lean.ofReduceBool` and `Lean.trustCompiler` (evaluation by the Lean
compiler) in addition to the three standard axioms.  `scripts/AxiomsReport.lean` prints the axioms of
every headline theorem; CI fails if anything beyond
`propext, Classical.choice, Quot.sound, Lean.ofReduceBool, Lean.trustCompiler` appears, or if any
`sorry` is present.  Definitional/spec lemmas use no computational axioms.

## Building

```sh
lake exe cache get   # fetch prebuilt mathlib oleans
lake build           # builds everything incl. the native_decide certificates
lake env lean scripts/AxiomsReport.lean   # axiom audit
```

Pinned: Lean `v4.27.0`, mathlib `v4.27.0`.  On WSL, build from a clone on the
Linux filesystem (e.g. `~/lean/`), not from `/mnt/c` — I/O there dominates
build time.

## Repository layout

```
Prop51Kernel.lean  executable interval kernel (no Mathlib; natively precompiled)
Prop51/            Lean library (Defs, soundness theory, certificates, Main)
scripts/           axiom report, constants check, saddle scans/templates
paper/             the LaTeX proof document (tenth revision + errata)
certificates/      external Arb certificate package (192-bit, 9 ≤ a ≤ 400)
blueprint/         (planned) Lean blueprint
ROADMAP.md         formalization plan: Layers A, A′, B, C
```

## Relation to the paper

`paper/prop51.tex` is the human proof this repository formalizes.  Two
*errata* against its tenth revision, found during formalization review, are
recorded in `paper/ERRATA.md` (neither affects the conclusions).
