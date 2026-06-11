# Blueprint (planned)

This directory will hold the [leanblueprint](https://github.com/PatrickMassot/leanblueprint)
sources once Layer A lands: a dependency-graphed, web-rendered version of
`paper/prop51.tex` with `\lean{}`/`\leanok` annotations tying every lemma to
its Lean counterpart.

Until then, the authoritative map from paper to Lean is:

| paper (tenth revision) | Lean | status |
|---|---|---|
| §1 defs, eq. (3)–(7) | `Prop51/Defs.lean` (`c`, `expCoeff`, `bCoeff`, `Unorm`) | done (recurrence form) |
| §1 eq. (1)–(2) power series (`Cseries = expSeries c`, `bSeries_official`) | `Prop51/ExpSeries.lean`, `Prop51/Bridge.lean`, `Prop51/BCoeffSeries.lean` | **done** |
| §1 eq. (8) majorant inequality `b ≤ U` | Layer A remainder (`ROADMAP.md`) | open |
| §2 Lemma 2.1, Lemma 2.2 (binomial reciprocals) | Layer C | open |
| §3 composition lemma (eq. 19) | Layer C | open |
| §4 Δ-envelope (R ≤ 20) | Layer C | open |
| §5 effective sign-lock (C₂ = 2215) | Layer C | open |
| §6 positive part (saddle regimes + window scan) | Layer C + `scripts/positive_saddle_scan.py` | open |
| §7 finite certificates: a ≤ 8 | `Prop51/CertificateSmall.lean` | **done** |
| §7 finite certificates: 9 ≤ a ≤ 60 (exact layer) | `Prop51/CertificateExact.lean` | **done** |
| §7 finite certificates: 9 ≤ a ≤ 400 (Arb) | `certificates/` (external) → Layer B | open |
| §8 final theorem | `Prop51/Main.lean` (`CoefficientNegativity`) | stated |

To bootstrap the web blueprint later: `pip install leanblueprint && leanblueprint new`.
