# Errata against the tenth revision (`prop51.tex`)

Found during formalization review; neither affects the conclusions.

1. **§6 / `prop51_tenth_positive_saddle_certificate.py`: N-coverage of the
   window scan.**  The script scans only `N = 12a-8` per `a`, asserting this
   is "the monotone worst case".  That is correct for the small-`k` majorant
   (increasing in `N`) but not for the tempered majorant, which scales as
   `96/N` (decreasing in `N`); the regime cutoff `k† = ⌈√N⌉` also moves with
   `N`.  Sound repair (costs < a factor 2.5): evaluate the small-regime
   formula at `N = 12a-8` for all `k ≤ ⌈√(12a-8)⌉` and the tempered formula
   at `N = 6a-7` for all `k > ⌈√(6a-7)⌉`, and take the maximum — this
   dominates every `N` in the rectangle.  Implemented in
   `scripts/positive_saddle_scan.py`; the worst summed majorant remains
   ≈ 1e-16, far below the `1e-8` target of Lemma 6.1.  The lemma statement
   needs no change; the proof's citation of the scan should reference the
   corrected script.

2. **§6, eq. (Y-tempered) at the low-`j` corner.**  At `j ≈ 0.1a` the bottom
   gas term `N e^{1.6}/(12 j²)` slightly exceeds the displayed `+1` exponent
   allowance (e.g. ≈ 1.18 at `(a,N,j) = (401,4804,41)`); the slack constant
   `14.5` absorbs it, as claimed.  A clarifying half-sentence in the proof
   ("the constant 14.5 absorbs the excess of the bottom gas over e¹ for
   j ≥ 0.1a") would make the line auditable without recomputation.
   (Numerically verified: no violations of (B-tempered)/(Y-tempered)/the
   small-k bound against true recurrence values at both N edges, a = 401.)

## Formalization notes

These are intentional Lean-vs-TeX differences rather than errors in the
mathematical argument.

1. **§5 P2/P4 drift constant.**  The TeX uses the sharper decimal
   `v_s = 1-D_s ≤ 1.095s/m²`.  The current Lean proof derives the coarser
   rational bound `v_s ≤ (28/25)s/m² = 1.12s/m²` from the rationalized
   `d`-ratio estimate.  The P4 small-term reserve has been recomputed with
   `28/25`; the total `784/m²` P4 budget still checks.

2. **§5 exponential tilts.**  The TeX writes the `Π_s` estimates with
   `exp(0.2237s)`.  The Lean development remains in `ℚ`, using
   `(gammaTilt/zetaMax)^s` as a rational surrogate and the identity
   `zetaMax^s(gammaTilt/zetaMax)^s = gammaTilt^s` in weighted sums.
   The pointwise product/log estimates now introduce a small documented
   real-analysis bridge: Lean proves `log Π_s ≤ L_s`, certifies
   `exp(0.2237) ≤ gammaTilt/zetaMax` by Taylor remainder arithmetic, and then
   converts back to the rational weighted budgets.

3. **§5 P1/P4 bridge structure.**  Lean packages the budget algebra through
   named bridge lemmas (`piResidualBridgeBound` for P1 and `piUBridgeBound`
   for P4), with closed near-range wrappers from the product/log estimate.
   This matches the TeX proof strategy while keeping the Poisson budget
   algebra separate from the analytic product estimate.
