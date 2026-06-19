# Questions for GPT Pro

The current Lean dashboard is still:

```lean
theorem coefficientNegativity
    (hbounded : BoundedPositiveCertificate)
    (hproduct : LargeTailProductCertificate) :
    CoefficientNegativity
```

After reading `completion_advice2.md`, I benchmarked the direct exact
raw-product finite route.  A single contiguous atom

```lean
checkPositiveXYProductRawClearedTableFixedNIndexRowRangeKChunk
  20 401 1 0 1 5 = true
```

does compile, but takes about 50s and 2.84GB.  Smaller atoms:

- `nLen = 1, kLen = 1`: about 3.2s, 2.83GB.
- `nLen = 10, kLen = 1`: about 17s, 2.83GB.
- `nLen = 10, kLen = 5`: about 25s, 2.84GB.

This makes a full exact finite grid possible only with very many shards and a
careful build plan, so the analytic saddle lemma route is much more attractive.

Please supply the most Lean-friendly proof outline for the two product saddle
inequalities below, with explicit monotonicity or ratio steps and constants
that can be formalized by rational arithmetic.

1. Finite bounded product, small branch:

```lean
∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
  k ∈ positiveKRange a → k ≤ ceilSqrt N → 0 < Bq N k →
    Xnorm N k * Ynorm N (posJ a k)
      ≤ positiveSmallXYProductBound a N k
```

The tangent route has the slightly sharper target
`positiveSmallXYProductTangentBound a N k`; either is useful.

2. Finite bounded product, tempered branch:

```lean
∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
  k ∈ positiveKRange a → ceilSqrt N < k → 0 < Bq N k →
    Xnorm N k * Ynorm N (posJ a k)
      ≤ positiveTemperedXYProductBound a N k
```

3. Large tail product, starting at `k ≥ 4`, for the frozen constructor:

```lean
LargeTailProductCertificate
  .ofClosedExactUpperEdgeProductGeFourNatSignLockComplement
```

It requires `hsmallGeFour` and `htemperedGeFour` for
`positiveLargeTailProductXUpperEdgeExactBound a k *
 positiveLargeTailProductYUpperEdgeExactBound a k`.

Most useful would be a proof that avoids expanding a number of summands
proportional to `a`: for example a first-term-plus-ratio bound, endpoint
monotonicity in `a,k`, or a simple rational surrogate `xyBound` strong enough
for both scalar fields.
