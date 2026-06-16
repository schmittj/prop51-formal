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
* `Prop51.coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksIndependentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`
  — the current most practical large-`a` conditional capstone: table-backed
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
  the same atom names and indices as JSON for batch proof production.  Lean
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
  in the earlier timeout.  The further
  `PositiveSaddleFixedFiniteWindowCombinedProductNKChunkedTangentSoloNChunkedAuditCertificate`
  wrapper shares each table-backed `(a,N)` product pass between the small and
  tempered regimes; emit it with
  `--strategy combined-product-nk-tangent-solo-n-chunked` and
  `--emit-single-chunk product-combined`.  This is a Lean proof-production
  optimization of the same inequalities: the conversion extracts the separate
  small and tempered fields expected by the existing certificate.  In the
  same local sample, one combined product atom replaces the two separate
  small/tempered product atoms and compiles in about 15 seconds.  The
  remaining large-tail inputs can also be supplied through
  `Prop51.PositiveSaddleLargeTailPartsAuditCertificate`, which splits the
  product-small, product-tempered, solo, adjacent-step, and unit-reserve
  analytic targets before reassembling the existing
  `Prop51.PositiveSaddleLargeTailAuditCertificate`.  This is only a
  proof-production decomposition of the same inequalities.  The finite
  generator can target this split final-theorem interface with
  `--emit-final --final-tail-parts`.  When
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
