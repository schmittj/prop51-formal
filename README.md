# Strict negativity and non-vanishing of Chen–Larson hypergeometric coefficients

[![CI](https://github.com/schmittj/prop51-formal/actions/workflows/ci.yml/badge.svg)](https://github.com/schmittj/prop51-formal/actions/workflows/ci.yml)
![Lean](https://img.shields.io/badge/Lean-4.27.0-blue)
![Mathlib](https://img.shields.io/badge/Mathlib-v4.27.0-blue)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-green.svg)](LICENSE)

Complete, machine-checked proofs — in **Lean 4 + Mathlib** — of the coefficient
(non-)vanishing behind **Chen–Larson, Propositions 5.1 and 5.2**
(*Independence of tautological classes and cohomological stability for strata of
differentials*, [arXiv:2603.23850](https://arxiv.org/abs/2603.23850)). The
repository contains the Lean formalization, the LaTeX paper, and the
computational certificates, with continuous integration that rebuilds the
production proof closure and audits its axioms.

Proposition 5.2 is formalized in its **corrected** form: the series printed in
the preprint (arXiv v1, equation (5.4)) used the constant term `1` where Ionel's
relation (Proposition 1.7, equation (1.13)) gives `κ₀ = 2g − 2`, which changes the
coefficient. The repository proves the corrected non-vanishing statement; the
correction follows directly from the published formulas, and the authors
additionally agreed with it in private correspondence (June 2026). The public
arXiv v1 is not yet updated.

## The theorem

Let

```
C(t) = Σ_{r≥0} (6r)! / ((3r)! (2r)!) · (t/72)^r .
```

**Main theorem.** For every `g ≥ 2` with `g ≡ 0, 2 (mod 3)`, writing
`a = ⌊g/3⌋ + 1`, and for every positive partition `μ = (m_1, …, m_n)` of `2g-2`,

```
[t^a]  Π_i C(t/(m_i+1)) / C(t)^(2g-2+n)  <  0 .
```

In particular this coefficient is nonzero — the hypothesis of Chen–Larson
Proposition 5.1 — so via their geometric reduction it yields their
Conjecture 1.4 for holomorphic abelian strata in the residue classes
`g ≡ 0, 2 (mod 3)`. The remaining class `g ≡ 1 (mod 3)` is their
Proposition 5.2, handled (in corrected form) below — so **all residue classes,
hence all genera** (for positive holomorphic abelian partitions), are now
covered, well beyond their computer check (`g ≤ 30`).

The public Lean statement is `Prop51.chenLarsonCoefficient_neg` in
[`Prop51/Theorem.lean`](Prop51/Theorem.lean); that small file also names the
series `C`, gives its coefficient formula, and proves the generating-function
identity `C(t)^N · B_μ(t) = Π_i C(t/(m_i+1))` that pins the formal object to the
one in the paper.

**Proposition 5.2 (corrected, `g ≡ 1 mod 3`).** Writing `g = 3a − 2`,
`M = 2g − 2 = 6a − 6`, `q_i = m_i + 1`, `N = Σ_i q_i`, `s_r = Σ_i q_i^(−r)`, and
`L = C'/C`: for every `a ≥ 2` and every positive partition `μ` of `M`, the
corrected coefficient `[t^a] B_μ(t)·D_μ^cor(t)` is **nonzero** (and strictly
negative for `a ≥ 14`), where `B_μ(t) = Π_i C(t/q_i) / C(t)^N` is the
Proposition 5.1 quotient and
`D_μ^cor(t) = M − 2(N − s₁)·t − 12·t²·(N·L(t) − Σ_i q_i^(−2)·L(t/q_i))` is the
corrected source factor obtained by pulling back Ionel's relation (the factor
printed in the preprint is the same with the leading `M` replaced by `1`). The
public Lean statements are `Prop52.chenLarsonProp52Coefficient_nonvanishing` and
`Prop52.chenLarsonProp52Coefficient_neg` in
[`Prop52/Theorem.lean`](Prop52/Theorem.lean), stated directly as coefficients of
`B_μ(t)·D_μ^cor(t)`.
The formal bridge `Prop52.sourceCorrectedCoeff_eq` in
[`Prop52/Source.lean`](Prop52/Source.lean) identifies it in degree `a` with the
marked coefficient `[t^a] B_μ·(M − K_μ)`, `K_μ = Σ_i m_i·Φ(t/q_i)`,
`Φ = 2t + 12·t²·L`, because `M = 6a − 6`. The decisive step is then
`T^cor = T^old + (2g − 3)·b_a`, reducing the corrected coefficient to two sign
inputs already controlled by the Proposition 5.1 analysis.

## Verify it yourself

```sh
lake exe cache get   # download the prebuilt Mathlib oleans
lake build           # check the Prop 5.1 and 5.2 production proof closure (native_decide certs incl.)
lake env lean scripts/PublicAxiomsReport.lean   # print the axioms the result depends on
```

If a matching Lean/Mathlib Lake package tree already exists locally, reuse it
instead of cloning Mathlib again:

```sh
./scripts/use-local-lake-packages.sh /path/to/existing/.lake/packages
lake build
```

Use this only with the same Lean/Mathlib versions recorded above.

Both proofs are **`sorry`-free**. `#print axioms` for the final theorems —
`Prop51.chenLarsonCoefficient_neg` and
`Prop52.chenLarsonProp52Coefficient_nonvanishing` —
reports exactly

```
propext, Classical.choice, Quot.sound,      -- the standard Mathlib axioms
Lean.ofReduceBool, Lean.trustCompiler        -- from the finite native_decide certificates
```

and nothing else — no project-specific axiom and no floating-point assumption.
CI fails if any of the audited public theorems depends on `sorryAx` or on an
axiom outside this documented list.

## Trust model

Almost all of the argument is checked by Lean's small logical kernel. The
finitely many large computations (partition enumeration, exact rational and
192-bit dyadic-interval certificates) are run by `native_decide`, which compiles
the finite Boolean check to machine code and executes it; this is what makes the
millions of certificate cases feasible, in exchange for trusting the Lean
compiler on those steps (`Lean.ofReduceBool`, `Lean.trustCompiler`). The
192-bit interval kernel is Lean's own — the external Arb run is **not** trusted.

## Repository layout

```
paper/             the LaTeX paper(s) and compiled PDF; archive/ holds superseded notes
Prop51/Theorem.lean   Prop 5.1 public facade: the series, the identity, the final theorems
Prop51/Statement.lean concise statement of the Proposition 5.1 target
Prop51/            the Prop 5.1 proof library (series bridge, majorant, sign lock, direct saddle, …)
Prop52/Theorem.lean   Prop 5.2 public facade: the two genus-indexed source theorems
Prop52/Source.lean    source coefficient, source-marked bridge, source theorem layer, g=4 checks
Prop52/Statement.lean the corrected Proposition 5.2 coefficient and target statements
Prop52/            the Prop 5.2 proof library (correction identity, finite/modular checks, Gamma tail, mid-range intervals)
Prop51Kernel.lean  the Mathlib-free, natively-compiled interval kernel
scripts/           axiom reports, constants checks, certificate generators
certificates/      the external 192-bit Arb certificate package (9 ≤ a ≤ 400)
docs/              FORMALIZATION.md (layer-by-layer guide) and the AI-development record
docs/DEVELOPMENT_HISTORY.md   the (now complete) layered formalization plan
```

## Paper and provenance

- [`paper/prop51.tex`](paper/prop51.tex) (and `prop51.pdf`) is the human-readable
  proof, with a section documenting the long-horizon generative-AI development
  and the precise trust boundary.
- [`docs/FORMALIZATION.md`](docs/FORMALIZATION.md) is the detailed, layer-by-layer
  map from the paper to the Lean code.
- [`docs/ai-correspondence/`](docs/ai-correspondence/) archives the most relevant
  AI review exchanges referenced in the paper.

## License

The Lean code and repository are licensed under **Apache 2.0** ([`LICENSE`](LICENSE)).
The paper (`paper/`) is licensed under **CC BY 4.0** ([`paper/LICENSE`](paper/LICENSE)).
A machine-readable citation is in [`CITATION.cff`](CITATION.cff).
