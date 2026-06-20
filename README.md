# Strict negativity of a Chen–Larson hypergeometric coefficient

[![CI](https://github.com/schmittj/prop51-formal/actions/workflows/ci.yml/badge.svg)](https://github.com/schmittj/prop51-formal/actions/workflows/ci.yml)
![Lean](https://img.shields.io/badge/Lean-4.27.0-blue)
![Mathlib](https://img.shields.io/badge/Mathlib-v4.27.0-blue)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-green.svg)](LICENSE)

A complete, machine-checked proof — in **Lean 4 + Mathlib** — of the coefficient
negativity behind **Chen–Larson, Proposition 5.1**
(*Independence of tautological classes and cohomological stability for strata of
differentials*, [arXiv:2603.23850](https://arxiv.org/abs/2603.23850)). The
repository contains the Lean formalization, the LaTeX paper, and the
computational certificates, with continuous integration that rebuilds every
proof and audits its axioms.

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
Conjecture 1.4 for holomorphic abelian strata, **for all genera in the residue
classes `g ≡ 0, 2 (mod 3)`** (the `g ≡ 1` case uses a different series, their
Proposition 5.2, and is not treated), extending their computer verification
(`g ≤ 30`).

The public Lean statement is `Prop51.chenLarsonCoefficient_neg` in
[`Prop51/Theorem.lean`](Prop51/Theorem.lean); that small file also names the
series `C`, gives its coefficient formula, and proves the generating-function
identity `C(t)^N · B_μ(t) = Π_i C(t/(m_i+1))` that pins the formal object to the
one in the paper.

## Verify it yourself

```sh
lake exe cache get   # download the prebuilt Mathlib oleans
lake build           # check every proof, including the native_decide certificates
lake env lean scripts/PublicAxiomsReport.lean   # print the axioms the result depends on
```

The proof is **`sorry`-free**. `#print axioms` for the final theorem reports
exactly

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
paper/             the LaTeX paper (paper/prop51.tex) and compiled PDF; archive/ holds superseded notes
Prop51/Theorem.lean   public facade: the series, the identity, the final theorems
Prop51/Statement.lean concise statement of the target proposition
Prop51/            the proof library (series bridge, majorant, sign lock, direct saddle, …)
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
