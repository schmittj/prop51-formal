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
