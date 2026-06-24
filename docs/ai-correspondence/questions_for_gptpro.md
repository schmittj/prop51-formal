# Questions for GPT Pro

Current Lean state after reading `answer_by_gptpro.md`:

```lean
theorem completion_of_directSaddle_finiteSolo
    (soloY :
      ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget) :
    CoefficientNegativity
```

The direct raw-cleared product path and the large/prefix solo path are already
wired in Lean.  The latest GPT Pro note correctly says to use
`PositiveSaddleLargeTailProductPrefixPointwise.ofRawCleared` and
`LargeTailProductCertificate.ofRawCleared`; that is now the current route.
The remaining exposed input is finite solo for `401 ≤ a ≤ 801`.

I added a Lean bridge reducing finite solo to the sharp saddle-cleared target:

```lean
theorem finiteSoloBudget_of_sharpGcompSaddleTenSeventhsCleared
    (hsharp :
      ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
        positiveLargeTailSoloSharpGcompSaddleTenSeventhsCleared a N) :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget
```

The analytic constant-budget suffix has now been lowered to `a ≥ 802`, so the
main missing proof can be any Lean-friendly proof of:

```lean
∀ {a N : Nat}, 401 ≤ a → a ≤ 801 → positiveRectangle a N →
  positiveLargeTailSoloSharpGcompSaddleTenSeventhsCleared a N
```

Equivalently, it is enough to prove the upper-edge version:

```lean
∀ {a : Nat}, 401 ≤ a → a ≤ 801 →
  positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSumTenSeventhsCleared
    a (posNhi a)
```

or the delta-budget upper-edge version:

```lean
∀ {a : Nat}, 401 ≤ a → a ≤ 801 →
  (4 : ℚ) * (2 : ℚ)^a *
      positiveLargeTailSoloSharpDeltaBudgetBlockSum a (posNhi a)
    ≤ 29 * (a : ℚ) * c a * (10 / 7 : ℚ)^a
```

Relevant Lean facts already available:

- `positiveLargeTailSoloSharpDeltaBudgetBlockSum_upperEdge_le_largeDegreeSplit`
  reduces the upper edge to
  `positiveLargeTailSoloSharpLargeDegreeSplitBudgetBlockSum a`.
- `positiveLargeTailSoloSharpLargeDegreeSplitBudgetBlockSum_scaled_le_target_of_const`
  proves the target for `a ≥ 802`.
- The bottleneck for closing the remaining finite solo proof is now the low
  strip `401 ≤ a ≤ 801`.  The very-low/deep-low crude bounds have been lowered
  to `a ≥ 401`; the remaining issue is finding the shortest theorem-facing
  route to discharge the sharp saddle target in this finite strip.

Finite displayed-solo generation currently looks too slow:

- existing `10` rows by first `20` N-values budget atom:
  about 31 seconds;
- existing `10` rows by first `20` N-values saddle atom with cached scaled exp:
  about 115 seconds;
- one `100` rows by `100` N-values budget/saddle probe timed out at 240 seconds.

Questions:

1. What is the most direct analytic proof of the sharp finite-solo target for
   `401 ≤ a ≤ 801`, preferably by modifying the existing sharp split and not
   introducing a large generated table?
2. If a hybrid proof is best, what threshold should the analytic proof cover
   and what finite residue should be generated?
3. Is there a sharper finite-window scalar/envelope than `(10/7)^a` that makes
   the deep-low/tiny proof easier below `2001`, while still fitting the
   `positiveSoloBudget = 1 / 200000000` budget?
4. If generation is unavoidable, can the displayed-solo saddle checker be
   replaced by a row-level or interval-level rational certificate that avoids
   evaluating all `N` cells?

---

## Prop52 truncation question, 2026-06-24

The corrected Proposition 5.2 Lean development has now closed:

- the finite corrected range `2 ≤ a ≤ 13`;
- the printed mid-range certificate `14 ≤ a ≤ 149`;
- the Proposition 5.1 rectangle bridge used in the correction identity;
- the Gamma retained-bracket lower bound;
- the Gamma integration-by-parts identity, including the infinity endpoint,
  integrability, and origin-continuity endpoint;
- the rational residue budget pieces appearing in the Taylor--Gamma
  truncation proof.

The current public facade has been reduced to one remaining analytic input:

```lean
def PrintedTailGammaTruncationErrorBound : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      |printedTailWGammaIntegral μ a -
          printedTailWTruncGammaIntegral μ a| ≤
        (truncationResiduePiecesLhs μ a : ℝ)
```

From this, Lean proves both:

```lean
theorem correctedCoeff_nonvanishing_of_gammaTruncationError :
    PrintedTailGammaTruncationErrorBound → CorrectedCoeffNonvanishing

theorem correctedCoeff_neg_of_gammaTruncationError :
    PrintedTailGammaTruncationErrorBound →
      ∀ {a : Nat}, 14 ≤ a →
      ∀ {μ : List Nat}, Prop51.IsPartitionOf μ (M a) →
        correctedCoeff a μ < 0
```

The main concern is the upper-event part of the paper's truncation lemma.  The
paper uses the analytic estimate `\widehat W(x₂) < 920` to bound the full tail
of

```text
W(t) = exp(-L(t)) (1 - J(t)).
```

However, the current Lean certificate

```lean
def PrintedTailWPointBoundX2 : Prop := ...
```

is deliberately only a finite-prefix bound through degree `a`.  That finite
prefix is enough for bounding `|omega_a|`, but it is not obviously enough for
the analytic expectation tail

```text
|E W(t_X) - sum_{s≤r0} gamma_s omega_s|.
```

Questions:

1. Is the paper's truncation lemma intended to use a genuinely full analytic
   majorant `\widehat W(x₂)`, rather than the finite prefix through degree
   `a`?  If yes, should the Lean route prove a new full real bound
   `exp(L_abs(x₂)) * (1 + J_abs(x₂)) ≤ 920` from the existing finite polynomial
   bounds on `L_abs(x₂)` and `J_abs(x₂)`?
2. Is there a coefficient-window reformulation that avoids proving a full
   analytic majorant, i.e. a way to compare only the degree-`≤ a` Borel/Gamma
   transform to the coefficient target without ever estimating the infinite
   tail of `W`?
3. If the full analytic route is best, what is the shortest Lean-friendly
   proof of the required tail inequality?  One possible route is:
   prove `|omega_s| ≤ printedTailWAbsCoeff_s` for all `s`, prove
   `∑' printedTailWAbsCoeff_s x₂^s =
     exp(L_abs(x₂)) * (1 + J_abs(x₂))`, and then use the geometric factor
   `(x₁/x₂)^(r0+1)=2^-(r0+1)`.
4. Is there an easier real-variable Taylor remainder estimate for
   `exp(-L(t))(1-J(t))` on `0 ≤ t ≤ x₁` that avoids formalizing infinite
   power-series evaluation?
