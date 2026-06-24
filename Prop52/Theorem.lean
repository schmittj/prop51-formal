/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Public facade for the corrected Chen--Larson Proposition 5.2

This is the human-facing entry point.  It states the two assumption-free public
theorems and the executable `g = 4` sanity checks, and nothing else of
substance.  The staged reduction that proves them lives in `Prop52.Assembly`;
the heavy finite and analytic inputs live in `Prop52.Finite`,
`Prop52.MidBridge`, and the `Prop52.Gamma*` modules; the Proposition 5.1
quotient sign input is `Prop51.bCoeff_neg_of_rectangle`.

## What the theorem says

For `g ≡ 1 (mod 3)`, write `g = 3a - 2` and `M = 2g - 2 = 6a - 6`.  Chen--Larson's
*printed* Proposition 5.2 used the constant term `1` where Ionel's relation gives
`κ₀ = 2g - 2 = M`.  The *corrected* coefficient is

  `correctedCoeff a μ = [t^a] F_μ(t) · (M - K_μ(t))`,

defined in `Prop52.Statement` as `M * Prop51.bCoeff μ a - markedConvolution μ a`.
The decisive identity `correctedCoeff_eq_printedCoeff_add` (in `Prop52.Assembly`)
reads `T^cor = T^old + (M - 1) · b_a`: for `a ≥ 14` both summands are strictly
negative (`T^old` by the printed-series proof, `b_a` by the Proposition 5.1
rectangle), so the correction only deepens the sign; the finitely many
`2 ≤ a ≤ 13` are checked exactly.

## Reviewer's checklist (to ascertain the final theorem is correct)

* the target statement `CorrectedCoeffNonvanishing` is defined in
  `Prop52.Statement` (∀ `a ≥ 2`, ∀ positive partition `μ` of `M a`,
  `correctedCoeff a μ ≠ 0`);
* `correctedCoeff_nonvanishing` below has exactly that type and takes no
  hypotheses;
* `scripts/PublicAxiomsReport.lean` reports it depends only on
  `propext, Classical.choice, Quot.sound, Lean.ofReduceBool, Lean.trustCompiler`;
* the executable `g = 4` checks at the end match the worked example of the
  corrected note (`b₂ = -195/8`, `T^old = 45/8`, `T^cor = -465/4`).
-/

import Prop52.Assembly

namespace Prop52

/-- **Corrected Chen--Larson Proposition 5.2: non-vanishing.**

Assumption-free.  For every `a ≥ 2` and every positive partition `μ` of
`M = 6a - 6`, the corrected coefficient is nonzero.  The finite ranges, the
Proposition 5.1 rectangle input, the mid-range interval certificate, the Gamma
lower bound, the Taylor truncation residue, and the real exponential
power-series identity are all closed in Lean (assembled in `Prop52.Assembly`). -/
theorem correctedCoeff_nonvanishing : CorrectedCoeffNonvanishing :=
  correctedCoeff_nonvanishing_of_eSeriesHasSum printedTailERealSeriesHasSum

/-- **Corrected Chen--Larson Proposition 5.2: strict negativity for `a ≥ 14`.**

Assumption-free.  For `a ≥ 14` and every positive partition `μ` of `M = 6a - 6`,
the corrected coefficient is `< 0`. -/
theorem correctedCoeff_neg
    {a : Nat} (ha : 14 ≤ a)
    {μ : List Nat} (hμ : Prop51.IsPartitionOf μ (M a)) :
    correctedCoeff a μ < 0 :=
  correctedCoeff_neg_of_eSeriesHasSum printedTailERealSeriesHasSum ha hμ

/-! ## Executable checks for the smallest corrected example

For `g = 4` (`a = 2`) and `μ = (1⁶)`, the corrected note records
`[t²]F_μ = -195/8`, printed coefficient `45/8`, corrected coefficient `-465/4`;
and indeed `-465/4 - 45/8 = 5 · (-195/8) = (M - 1) · b_a`. -/

example : Prop51.bCoeff [1, 1, 1, 1, 1, 1] 2 = -195 / 8 := by native_decide

example : printedCoeff [1, 1, 1, 1, 1, 1] 2 = 45 / 8 := by native_decide

example : correctedCoeff 2 [1, 1, 1, 1, 1, 1] = -465 / 4 := by native_decide

end Prop52
