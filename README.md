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
* `Prop51.coefficientNegativity_of_positiveSaddleDefaultCellEdgeKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`
  — the current most practical large-`a` conditional capstone: default finite
  product chunks, tangent-edge cell checks, semantic finite solo budgets,
  default unit-cleared edge `k`-chunks, and the raw-cleared large-tail reserve
  certificate imply full `CoefficientNegativity`.
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
  against the combined-exponent targets.  The older
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
scripts/           axiom report, constants check, corrected saddle scan
paper/             the LaTeX proof document (tenth revision + errata)
certificates/      external Arb certificate package (192-bit, 9 ≤ a ≤ 400)
blueprint/         (planned) Lean blueprint
ROADMAP.md         formalization plan: Layers A, A′, B, C
```

## Relation to the paper

`paper/prop51.tex` is the human proof this repository formalizes.  Two
*errata* against its tenth revision, found during formalization review, are
recorded in `paper/ERRATA.md` (neither affects the conclusions).
