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
| §1 eq. (7)–(8) majorant inequality `b ≤ U` (`bCoeff_le_U`, `bCoeff_neg_of_unorm`) | `Prop51/Majorant.lean` | **done** |
| §2 Lemma 2.1, Lemma 2.2 (binomial reciprocals) | Layer C | open |
| §3 composition lemma (eq. 19) | Layer C | open |
| §4 Δ-envelope (R ≤ 20) | Layer C | open |
| §5 effective sign-lock (C₂ = 2215) | Layer C | open |
| §6 positive part (saddle regimes + window scan) | Layer C + `scripts/positive_saddle_scan.py` | open |
| §7 finite certificates: a ≤ 8 | `Prop51/CertificateSmall.lean` | **done** |
| §7 finite certificates: 9 ≤ a ≤ 60 (exact layer) | `Prop51/CertificateExact.lean` | **done** |
| §7 finite certificates: 9 ≤ a ≤ 400 (Arb) | `Prop51Kernel.lean` (interval kernel) + `Prop51/Dyadic.lean`, `Prop51/IntervalCert.lean` (soundness) + `Prop51/CertificateInterval*.lean` (`unorm_neg_9_400`) | **done** |
| §8 final theorem | `Prop51/Main.lean` (`CoefficientNegativity`; proved through `g ≤ 1199` by `coefficientNegativity_of_g_le_1199`) | stated; open = Layer C |

To bootstrap the web blueprint later: `pip install leanblueprint && leanblueprint new`.
