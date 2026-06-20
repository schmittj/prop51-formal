# Decisive AI outputs — prop51-formal

*Verbatim excerpts of the decisive AI outputs; trimmed to the load-bearing portion; lightly redacted.*

---

### Stuck diagnosis (Claude Opus 4.8, 19 Jun)

> ## Bottom line up front
>
> 1. **The mathematics is sound.** I read the full tenth-revision paper (`paper/prop51.tex`). The strategy has no fundamental obstruction; every gap found in prior audits was a fixable constant/range bug and was fixed, with *enormous* numerical slack everywhere. The one genuinely soft spot is exactly where the formalization is stuck (the §6 positive-part saddle bounds) — but it's soft as in "tedious to formalize," not "possibly false."
> 2. **The worker is making real, verified progress *and* is stuck in a local minimum** — both are true, on different parts. The hard analytic half (sign-lock) is genuinely done and compiles; the §6 positive-part / large-tail **product** certificate is in a textbook reduction-thrash.
> 3. **The build compiles** (I verified — see below), the codebase is **sorry-free with a clean axiom surface**, so the claimed progress is real, not vaporware.
>
> [...]
>
> **Root cause.** The worker can always produce a plausible "progress" commit by adding one more adapter/qualifier, so it never has to confront the one hard thing: proving the explicit §6 saddle-product inequality. It's avoiding the analytic lemma by (a) endlessly refining the reduction, and (b) trying a finite `native_decide` checker — which its own profiling shows costs ~1 minute per single bounded row (≈2600 rows ⇒ infeasible). So: the *thrash* is not "normal necessary process" — it's a real dead-end pattern. But the *project* is genuinely ~85–90% done, and the remaining 10–15% is well-identified.

---

### Direct-saddle repair report (Codex CLI, 19 Jun)

> I read `answer_by_gptpro.md` carefully. Its main correction matches the current code direction: do not use the exact upper-edge product constructor; use the raw-cleared `Bq * Qq` route. The direct product route is already wired through `SaddleDirect`, `PositiveSaddleLargeTailProductPrefixPointwise.ofDirectSaddle`, and `LargeTailProductCertificate.ofDirectSaddle`.
>
> [...] Added the wrapper reducing the remaining completion input to the sharp finite-solo strip `401 ≤ a ≤ 801`. [...] Next substantive step: use the new Δ estimate to build a looser `2/3` middle/proportional solo split for the remaining `401 ≤ a ≤ 801` range, while staying within the existing constant budget. That should be the path toward closing finite solo without generated row tables.

---

### Closure report (Codex CLI, 19 Jun)

> Completed the formalization goal and marked it complete.
>
> What changed:
> - `Prop51.coefficientNegativity : Prop51.CoefficientNegativity` is now a closed theorem in [Prop51/Completion.lean](prop51/prop51-formal/Prop51/Completion.lean).
> - The finite-solo low strip is closed via the direct-saddle route.
> - README, ROADMAP, `OpenGoals`, `Main`, and `scripts/AxiomsReport.lean` now reflect the closed theorem rather than the earlier conditional route.
>
> [...]
>
> - Explicit final check:
>   `Prop51.coefficientNegativity : Prop51.CoefficientNegativity`
>   with axioms `[propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]`.
