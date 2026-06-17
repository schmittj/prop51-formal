# Formalization roadmap

Goal: a sorry-free proof of `Prop51.CoefficientNegativity` (`Prop51/Main.lean`),
with the axiom footprint documented by `scripts/AxiomsReport.lean`.

## Layer A — the power-series bridge (statement-level, pure ℚ)

Connect the recurrence-defined objects to the official power series.
No real analysis; everything is coefficient identities over ℚ.

- [x] `A r := (6r)!/((3r)!(2r)!·72^r)` and the ratio identity
      `(k+1)·A_{k+1} = 6(k+1/6)(k+5/6)·A_k` (clears to integers).
- [x] exp-characterization: for `F` with `F₀ = 1`, `n·F_n = Σ_{j≤n} j·L_j·F_{n-j}`
      iff `F = exp(Σ L_r t^r)` as `PowerSeries ℚ` (uniqueness by strong
      induction; existence = our `expList`).
- [x] the bridge identity `r·A_r = Σ_{j=1}^r j·c_j·A_{r-j}` (i.e. `c = log C`;
      from the hypergeometric ratio + the Riccati recurrence — the one real
      lemma of this layer; verified numerically to r = 40 exactly).
- [x] `bCoeff μ a = PowerSeries.coeff a (Π_i C(t/qᵢ) * (C^N)⁻¹)`.
- [x] majorant inequality `b_a(μ) ≤ U_a(N)` (paper eq. 8): coefficientwise
      domination `P_k(μ) ≤ Q_k(N)` by induction on the exp-recurrence
      (monotonicity in the exponent α over ℚ≥0), plus sign bookkeeping.
- [x] `c_pos`, `c_r ≤ A_r` (via the bridge identity).
- [x] (Layer C prep) `d`-normalization `c_r = 6^r (r-1)! d_r`, `d`
      nondecreasing, `5/36 ≤ d_r ≤ 4/25` — done, `Prop51/DNorm.lean`
      (see Layer C below for the rationalization).

## Layer A′ — partition quantifier upgrade

- [ ] `mem_partitions_iff`: completeness of the generator
      (`μ ∈ partitions n ↔ μ.sum = n ∧ sorted-desc ∧ positive parts`).
- [ ] permutation-invariance of `bCoeff` (it factors through the multiset of
      parts); upgrade `bCoeff_neg_g_le_23` to the `IsPartitionOf` form.
- [ ] optional: align with `Mathlib.Combinatorics.Partition` / `Nat.Partition`.

## Layer B — interval certificate `61 ≤ a ≤ 400` — **done**

- [x] verified dyadic interval arithmetic: `Prop51Kernel.lean` (executable,
      Mathlib-free, natively precompiled) + `Prop51/Dyadic.lean` (enclosure
      semantics over `ℚ`; 192-bit mantissas with outward rounding, the
      working precision of the reference Arb run).  Hand-rolled rather than
      girving/interval: the soundness statements stay in `ℚ`, no extra
      dependency, and rounding soundness reduces to floor/ceil facts.
- [x] interval port of the recurrences with per-`N` shared tables
      (`bTab`/`qTab`); the *unnormalized* `B`/`Q` recurrences are tracked
      directly (termwise a constant rescale of the certificate's `X`/`Y`
      form, so numerically identical), which lets soundness reuse the exact
      `expList` specs of Layer A verbatim.  Sign handling via `DI.hull0`
      (hull with `{0}`) — strictly conservative, no interval sign decision.
- [x] `native_decide` over all 470,220 pairs `61 ≤ a ≤ 400` (the 10,764
      pairs `a ≤ 60` stay with the exact certificate): 8 equal-work chunks
      (`CertificateInterval1-8.lean`, ~4 min each, parallel under
      `lake build`), assembled into `unorm_neg_61_400` / `unorm_neg_9_400`,
      capstone `coefficientNegativity_of_g_le_1199`.

## Layer C — the effective tail `a ≥ 401`

The paper's §§2–6 with explicit constants.  **Design decision (2026-06-12):
everything is rationalized — no `Real`, no `π`, no `e`, no Mathlib analysis.**
Each transcendental ingredient of the paper is replaced by a rational
surrogate, with the constant degradation absorbed by the sign-lock budget
(`2215` allowed vs. `20340` available — an order of magnitude of slack):

* `d_r ≤ 1/(2π)`  →  `d_r ≤ 4/25` via the exact `F`-ratio
  `1 + 5/(36r(r+1))` plus a Weierstrass product bound (`Π(1+xᵢ) ≤ 1/(1−Σxᵢ)`),
  pinned at `F₃·(108/103) = 0.15935 ≤ 0.16`;
* `1/π²` in the increment control  →  `(4/25)² · 4 = 64/625`;
* Stirling `r! ≥ (r/e)^r`  →  `r! ≥ (25r/68)^r`, by induction from
  `(1+1/n)^n ≤ Σ 1/k! ≤ 68/25` (binomial theorem + partial sum + geometric
  tail — all in ℚ);
* `exp` evaluations at rational points  →  partial sums + geometric tail
  majorants (`Σ_{t≤T} y^t/t! ≤ Σ_{t<T₀} y^t/t! + (y^{T₀}/T₀!)/(1−y/T₀)`,
  uniform in `T`); the infinite Poisson moments of §5 are finite sums here
  (`s ≤ m/3`), bounded by such surrogates;
* the alternating leading term `e^{-ζ}(1-2/m)`  →  a truncated alternating
  sum with first-omitted-term remainder (parity trick), reduced to a
  one-variable polynomial inequality on `0 ≤ ζ ≤ 50/27`;
* the §6 window scan  →  `native_decide` over exact rationals / the Layer B
  dyadic kernel; the `a > 2000` entropy tail  →  checked rational shadows of
  the binomial denominator.  Lean now has both the simple product bound
  `choose_ge_pow_div_pow : ((n:ℚ)/(k:ℚ))^k ≤ C(n,k)` and the log-free
  entropy analogue
  `choose_ge_entropy_shadow :
   n^n / ((n+1) k^k (n-k)^(n-k)) ≤ C(n,k)`, specialized as
  `positiveBinomDen_ge_entropyShadowBound` with reciprocal majorant
  `positiveBinomRatio_le_entropyShadowBound` and simplified ratio form
  `positiveBinomRatio_le_entropyShadowRatio`.  The latter records the TeX
  entropy mechanism without introducing real `exp/log` into this layer.
  The same reciprocal is also available in the paper's `j=a-k` notation as
  `positiveBinomRatio_le_entropyShadowPosJBound`, with small/tempered
  summand shells `positiveSmallEntropyShadowMajorantTerm` and
  `positiveTemperedEntropyShadowMajorantTerm`.  Endpoint bookkeeping is
  covered by `positiveBinomRatio_le_entropyShadowPosJBound_one`, and the
  retained range has the uniform wrapper
  `positiveBinomRatio_le_entropyShadowPosJBound_of_mem_large`.

Status:

- [x] reciprocal-binomial lemmas (paper Lemma 2.2): `Σ 1/C(n,i) ≤ 4/n`,
      middle-term variant `≤ 10/(n(n-1))` (`Prop51/BinomRecip.lean`).
- [x] `d`-normalization (paper Lemma 2.1, rationalized): recurrence,
      monotonicity, `5/36 ≤ d_r ≤ 4/25`, increment control
      `d_r − d_{r-1} ≤ (64/625)/(r(r-1))`, telescoped ratio bound
      `1 − (2304/3125)s/(m(m-s)) ≤ d_{m-s}/d_m ≤ 1`; workhorse bounds
      `(5/36)·6^r(r-1)! ≤ c_r ≤ (4/25)·6^r(r-1)!` (`Prop51/DNorm.lean`).
- [x] composition lemma (paper Lemma 3.1): `G_r(p) ≤ 4^{r-1}(p-2r+1)!`
      in recursive convolution form (`Prop51/Composition.lean`).
- [x] rational Stirling lower bound `r! ≥ (25r/68)^r` and the partial-exp
      majorant machinery: `Σ_{t<T} y^t/t! ≤ Σ_{t<T₀} y^t/t!
      + (y^{T₀}/T₀!)/(1−y/T₀)` uniformly in `T`; `(1+1/n)^n ≤ 68/25` via
      the binomial theorem and `Σ 1/k! ≤ 1631/600`
      (`Prop51/ExpBounds.lean`).
- [x] `H`-power machinery (`Prop51/HPow.lean`): the exponential formula
      `expCoeff L p = Σ_{r≤p} [t^p]((mk L)^r)/r!` (finite, via the
      θ-power rule `θ(G^{r+1}) = (r+1)·G^r·θG` and a double-sum swap);
      the power bound `|[t^p]G^r| ≤ M^r 6^p Gcomp r p` for `L` supported
      in degrees ≥ 2 with `|L_j| ≤ M·6^j(j-1)!` (the `Gcomp` recursion
      consumed verbatim); `hpow r p = [t^p]H^r` with `hpow_eq_zero` for
      `p < 2r`; the exact block split
      `E⁻_p(N) = -N c_p + Σ_{r=2}^p (-N)^r [t^p]H^r/r!` and the residual
      bound `|E⁻_p + N c_p| ≤ Σ_{r≥2} (4N/25)^r 6^p Gcomp r p / r!`.
- [x] Δ-envelope scaffold (`Prop51/Envelope.lean`): rationalized
      `DeltaRat` with coefficient `(36/5)(4/25)^r4^{r-1}`, block domination
      from `Gcomp_le` and `c_lb`, and the normalized bridge
      `|E⁻_p/(-Nc_p)-1| ≤ DeltaRat p N`.
- [x] the Δ-envelope numerics (Lemma 4.1, `Envelope.lean`): from
      `Eminus_residual_le`, the normalized bound `|ε_p| ≤ 13.2/m` for
      `p ≥ 2m/3`, `N ≤ 40m/3`, `m ≥ 361` — geometric domination by the
      `r = 2` block (ratio ≤ `(16N/25)/(3(p-2r)(p-2r+1)) ≤ 17.1/p`) plus
      the rational far tail `r > p/4` via `factorial_lb` and
      `(p-1)!/(p-2r+1)! ≥ (2r-1)!`.
      Lean now proves the split, the near-range geometric majorant, the
      rational far-tail geometric bound, `DeltaRat_le_final_envelope`, and
      `Eminus_normalized_residual_le_final`.
- [x] sign-lock §5 (`Prop51/SignLock.lean`): exact finite decomposition
      of `−X_m` and the non-boundary
      `(-ζ)^s/s!·Π_s D_s·(-E^-_{m-s}/(Nc_{m-s}))` summand factorization
      are done; this is also converted to `(1+ε_{m-s})`.  The `Π_s`
      product now has recurrence/product forms, positivity, `Π_s ≥ 1`,
      and the nonnegative extracted residual
      `Π_s - 1 - e₁(s)/m ≥ 0`.  The completed Δ-envelope is exposed as
      `|ε_{m-s}| ≤ 66/(5m)` for `3s ≤ m`.  The final
      rational positivity margin against `2215` is done via a 10-term
      alternating surrogate at `50/27`.  Rational Poisson/partial-exp first
      and second moment bounds are in place, including sharper zeroth/first
      caps for P3a; P2 (`d`-drift) is proved with budget `13/m²`.  P3a now
      has endpoint correction notation, `D_2` ratio-control, pointwise
      recentering control, and weighted budget `184/m²`.  P3b now has the
      sharpened large-`n` reciprocal-binomial estimate, the non-endpoint
      two-block majorant bridge, the pointwise `36.6/m²` cap, and weighted
      budget `234/m²`.  P3c now has an explicit three-and-more-block tail
      majorant, a pointwise `89/m²` cap, and weighted budget `573/m²`.
      P1 now has the higher Poisson moment machinery, the weighted
      `426/m²` numerical majorant budget for the explicit gamma-residual
      terms, plus a closed near-range bridge from the pointwise product/log
      estimate through `piResidualBridgeBound`.  The rational arithmetic
      bounds behind the paper's `L_s ≤ 1.168e₁(s)/m` and `L_s < 0.2237s`
      product estimates are formalized.  The real logarithm bridge now proves
      `log Π_s ≤ L_s`, Taylor-certifies
      `exp(0.2237) ≤ gammaTilt/zetaMax`, and closes both the P1 quadratic
      residual estimate and the P4 `Π_s-1 ≤ L_s·(gammaTilt/zetaMax)^s`
      estimate in the near range.  P4 now has the dominant cross-term
      numerical reserve, and the smaller `u_s v_s`, `v_s|ε_p|`, and
      `v_s|ε_p|u_s` pieces are expanded explicitly inside the `3/2·m⁻²`
      allowance, giving the `784/m²` budget;
      the abstract product-cross inequality has also been bridged to those
      four weighted P4 budget terms.  The formalized near-range `d`-drift
      gives the slightly coarser but sufficient `v_s ≤ (28/25)s/m²`, and the
      `v_s|ε_p|` bridge input is closed.  The closed P1/P4 actual weighted
      bridges are now summed with P2/P3 into a `2214/m²` near-range component
      audit, and a conditional `w_s` near-range theorem records exactly the
      remaining nonlinear recentering hypothesis.  The exact endpoint
      extraction from the `E^-_p` block expansion is now formalized:
      `[t^p]H^2` is split into its two endpoint products plus the middle
      two-block sum, and `ε_p + twoEndpointCorrection` is rewritten as the
      middle two-block normalized contribution plus the `r ≥ 3` tail.  The
      middle two-block absolute-value bridge to the P3b majorant is now
      proved, and the exact `r ≥ 3` tail is reduced to a rationalized
      Δ-tail sum.  The P3c comparison is now closed: the near part of that
      Δ-tail is controlled by a `27/25` geometric multiplier from the `r=3`
      term, and the far slice is bounded by the exact reserve
      `DeltaRatFar ≤ (4/575)·DeltaRatTerm₃`.  Consequently the nonlinear
      recentering hypothesis is discharged and the actual near-range `w_s`
      audit is proved with budget `2214/m²`.  The far-tail work now has the
      exact omitted-tail definition, a rational proof of the finite Poisson
      `2.04` first-omitted-term allowance, the finite-recurrence replacement
      for the TeX truncated saddle estimate `|E^-_p| ≤ 600(6m)^p` for
      `p ≤ 2m/3`, and the algebraic reduction from the actual coefficient
      tail to the displayed saddle/Stirling scalar.  The scalar is now
      certified by an `N`-free envelope, exact endpoint checks at
      `m = 361,362,363`, and a rational three-step contraction; consequently
      the near audit plus the actual far tail is assembled unconditionally as
      a `2215/m²` error-budget wrapper.  The final sign-lock decomposition is
      now split as near alternating base + near signed error + far signed tail,
      and the completed error audit is connected to `Xnorm ≤ -margin`; the
      remaining §5 input is the alternating-base lower bound for
      `signLockNearBase`.  That input is now further reduced to the 12-term
      prefix inequality `signLockBasePrefix ... 12`; the paired alternating
      tail `signLockBaseTailFrom12` is proved nonnegative from adjacent
      even/odd pairs.  The 12-term prefix is also split as
      `A(z)+C(z)/m`, with a formal endpoint-denominator reduction showing
      that it remains only to certify the pure prefix `A(z)` and the
      `m = 361` scalar prefix uniformly for `0 ≤ z ≤ 50/27`; both
      one-variable checks are now certified by explicit rational Bernstein
      coefficient lists, giving the unconditional `Xnorm` sign-lock theorem.
- [ ] positive part §6: rational saddle bounds (`ρ` chosen rational),
      two regimes + `native_decide` window scan `401 ≤ a ≤ 2000`,
      entropy tail for `a > 2000`.  The corrected two-edge rectangle
      bookkeeping and the retained range `1 ≤ k ≤ floor(0.9a)` are now
      formalized in `Prop51/PositiveSaddle.lean`; that file also defines the
      executable rational small/tempered edge summand majorants and proves
      their finite-window exponent cutoffs for `401 ≤ a ≤ 2000`.  The
      abstract reducer from pointwise small/tempered saddle estimates at an
      arbitrary `N` in the rectangle to the corrected two-edge scan is also
      in place, as is the algebraic bridge restricting the guarded raw
      positive sum to `k ≤ floor(0.9a)` once the large-`k` sign-lock
      nonpositivity is available.  `Unorm` is now rewritten as
      `Xnorm + normalizedSoloTerm + normalizedPositiveRangeSum`, with a
      conditional theorem bounding the retained positive sum by the corrected
      edge scan.  The rectangle arithmetic needed to feed the sign-lock
      theorem into the large-`k` exclusion (`k ≥ 361`, `N ≤ 40k/3`) is now
      packaged as a reusable interface.  The final rational margin
      `expNegLower50(1-2/a)-2215/a²` and the `10^-8` positive target are now
      formalized, including the exact proof that the margin dominates the
      target for every `a ≥ 401`; the large-`a` `Unorm < 0` assembly is
      reduced to the remaining `Xnorm` lower bound, pointwise saddle
      estimates, and positive-envelope certificate.  Lean also records the
      main translation interface from §5 to §6: a single uniform theorem
      `Xnorm N m ≤ -signLockMargin m` supplies both the main `m = a`
      negative term and the large-`k` sign-lock exclusion.  This bridge now
      consumes the completed sign-lock theorem directly, while the older
      conditional bridges exposing `signLockNearBase` and the 12-term prefix
      obligations are retained for auditability.  The positive-envelope
      interface now also has a parameterized solo-term bound, matching the
      TeX split between the retained positive summands and the separate
      `2^{-a-1}Y_a(N)` saddle estimate.  These remaining obligations are
      now bundled as `PositiveSaddleCertificate`, split into the finite
      window `401 ≤ a ≤ 2000` and the `a > 2000` entropy tail, and
      `Main.lean` exposes the direct capstone
      `coefficientNegativity_of_positiveSaddleCertificate`.  There is also
      a raw-summand variant `PositiveSaddleRawCertificate` that removes the
      guarded `B_k > 0` bookkeeping from the analytic saddle obligations.
      The direct entropy-tail field now has its own reusable reduction:
      `positiveCustomEdgeMajorantSum`,
      `Unorm_neg_of_signLock_and_customEnvelopeBound`, and
      `PositiveSaddleCustomTailCertificate.entropyTail` let the `a > 2000`
      proof use entropy-tail-specific rational summand bounds instead of the
      finite-window `partialExpUpper` scan terms.  The entropy-shadow
      specialization is named
      `PositiveSaddleEntropyShadowTailCertificate.entropyTail`, with the
      budgeted half-target split exposed as
      `PositiveSaddleEntropyShadowBudgetCertificate.entropyTail`.  This
      records the Lean-side loose solo/edge budget; it is weaker than the
      TeX solo estimate but follows the same final positivity margin.  The
      retained edge budget can now be split by regime through
      `positiveEntropyShadowSmallBranchSum`,
      `positiveEntropyShadowTemperedBranchSum`, and
      `PositiveSaddleEntropyShadowSplitBudgetCertificate.entropyTail`,
      matching the paper's small/tempered entropy-tail decomposition.
      Lean also has retained-range positivity hooks for the rational
      entropy-shadow reciprocal and for the small/tempered summands once the
      final exponential surrogate supplies nonnegativity.  To avoid tying the
      true `a > 2000` tail to the finite-window `partialExpUpper` shell, Lean
      also exposes parameterized exponential factors via
      `positiveSmallEntropyShadowExpMajorantTerm`,
      `positiveTemperedEntropyShadowExpMajorantTerm`, and
      `PositiveSaddleEntropyShadowExpSplitBudgetCertificate.entropyTail`.
      Public geometric-chain helpers
      `geom_chain_Icc_sum_le_geom` and
      `geom_chain_Icc_sum_le_inv_one_sub` are available for reducing these
      branch budgets to first-term and successor-ratio checks; the branch
      sums have exact active-range rewrites such as
      `positiveEntropyShadowExpSmallBranchSum_eq_Icc` and
      `positiveEntropyShadowExpTemperedBranchSum_eq_Icc`, plus direct
      first-term/ratio budget lemmas
      `positiveEntropyShadowExpSmallBranchSum_le_inv_one_sub_of_ratio` and
      `positiveEntropyShadowExpTemperedBranchSum_le_inv_one_sub_of_ratio`;
      reserve-form wrappers are also available when the first term is proved
      below `budget * (1 - ratio)`.
      for `a > 2000`, the interval bookkeeping is discharged by
      `positiveSmallBranch_hi_nonempty_of_large` and
      `positiveTemperedBranch_start_le_posKmax_of_large`.  The resulting
      first-term/ratio certificate is
      `PositiveSaddleEntropyShadowExpGeometricBudgetCertificate.entropyTail`.
      This large-tail certificate is also wired into the most concrete
      row-checked finite-window path as
      `PositiveSaddleXplusGcompTangentRowsEntropyGeometricCertificate`, with
      final assembly exposed by
      `coefficientNegativity_of_positiveSaddleXplusGcompTangentRowsEntropyGeometricCertificate`.
      The raw side now has the exact §6 factorization
      `B_k Q_{a-k}/(N c_a) = (N/2)R_{k,a}2^{-(a-k)}X_kY_{a-k}` in Lean,
      together with wrappers reducing the small/tempered raw obligations to
      factorized bounds only in the case `B_k(N)>0`; this is packaged as
      `PositiveSaddleFactorCertificate`, which converts to the raw and final
      certificate interfaces.  The coefficient-ratio step is also formalized:
      `R_{k,a}` is bounded by the reciprocal binomial prefactor using the
      existing `c_lb`/`c_ub` estimates, and a product bridge reduces the
      factorized summand to separate `X_k(N)` and `Y_{a-k}(N)` bounds; the
      decomposed interface is packaged as `PositiveSaddleXYCertificate`.
      The executable small/tempered majorants also have reciprocal-binomial
      normal forms, matching the scalar shape produced by this bridge.
      Lean now also proves monotonicity of the rational `partialExpUpper`
      surrogate and uses it to move the small-regime exponent from the actual
      `N` to the upper rectangle edge; the lower/upper edge denominator
      comparisons are packaged separately.  The products of the displayed
      small/tempered `X` and `Y` constants are now isolated as scalar bounds
      and proved to sit below the executable majorant terms; this is exposed
      as `PositiveSaddleScalarCertificate`.  Lean also has a budgeted variant
      `PositiveSaddleScalarBudgetCertificate`: the solo term is assigned the
      loose half-target budget `positiveSoloBudget = positiveTarget/2`
      (weaker than the TeX `exp(-0.49a)` estimate, and documented in code),
      leaving the finite scan as the single edge obligation
      `positiveEdgeMajorantSum a ≤ positiveEdgeBudget`.  Lean also keeps
      audit definitions for the paper's displayed `X`/`Y` saddle-bound shapes
      with constants `8.9`, `7.3`, and `14.5`, plus normal forms for their
      products.  These displayed products are not currently exposed as a
      certificate path: multiplying two independent `partialExpUpper`
      surrogates is slightly too strong for the executable majorants, so the
      sound target remains the combined scalar-product estimate.  Lean records
      this with the exact audit witness
      `positiveSmallDisplayedExpEdge_not_le_combined_example`.  The corrected
      intermediate target is `PositiveSaddleCombinedProductBudgetCertificate`,
      which asks directly for combined `X_k(N) * Y_{a-k}(N)` bounds with the
      single executable exponent and converts to the scalar-budget certificate.
      A first actual-`N` split using `ceilSqrt N` is kept as an audit trail,
      but it is not the viable final route: Lean records the failing top-plateau
      cell as `positiveSmallExpEdgeGapAtCeil_topPlateau_not`.  The corrected
      actual-`N` target is
      `PositiveSaddleTangentProductBudgetCertificate`, which uses the rational
      tangent-line square-root surrogate
      `positiveSmallXYProductTangentBound` and the finite edge condition
      `positiveSmallTangentExpEdgeGap`; it converts to
      `PositiveSaddleCombinedProductBudgetCertificate`.  Lean also exposes
      `checkPositiveSmallTangentExpEdgeCell`/`AtN`/`Row`/`Range` with soundness
      down to this finite-window tangent edge field.  For the separate corrected
      edge budget, Lean exposes
      `checkPositiveEdgeBudgetRow`/`checkPositiveEdgeBudgetRange` and soundness
      lemmas for the finite corrected-edge budget.  The row-oriented interface
      `PositiveSaddleTangentCheckedRowsCertificate` packages these two boolean
      row checks together with the remaining analytic fields, matching the
      intended generated-certificate workflow.  The solo `Y_a` term now has an
      analogous exact `Qq` split into the linear exponential and the nonlinear
      `Eplus` coefficients, an explicit `Eplus`/`Gcomp` upper bound, and
      `checkPositiveSoloGcompRow`; the stronger
      `PositiveSaddleTangentFullyCheckedRowsCertificate` replaces the analytic
      solo field by this row check.  The positive `X` side now also records
      the paper's `\overline B` majorant route in Lean: `Bplusq` and
      `XplusNorm` are defined from `[X^k]C(X)^N`, an absolute exp-recurrence
      comparison proves `|Xnorm| ≤ XplusNorm`, and
      `PositiveSaddleXplusTangentFullyCheckedRowsCertificate` lets the
      remaining small/tempered saddle products be proved for
      `XplusNorm * Ynorm` instead of directly for `Xnorm * Ynorm`.  The
      `Xplus` side now also has its own linear/nonlinear split
      `Bplusq_eq_linear_BplusNonlinear_sum`, a `Gcomp` coefficient majorant,
      and the normalized executable upper bound
      `positiveXplusGcompBound`.  Combining this with the existing
      `QqEplusGcompBound` gives the explicit product bound
      `positiveXplusYProductGcompBound`, row checkers for the small tangent
      and tempered product targets, and the stronger
      `PositiveSaddleXplusGcompTangentFullyCheckedRowsCertificate`; in that
      interface the finite window is reduced to boolean row checks plus the
      separate entropy tail for `a > 2000`.  This independent `Gcomp`
      product route is now marked as audit-only: its product inequalities are
      stronger than the combined-exponent target and fail already in the
      first finite row (`a = 401`, `N = 6*401 - 7`, `k = 1`).  Lean therefore
      also exposes the exact raw-product cleared predicates
      `positiveSmallXYProductRawCleared` and
      `positiveTemperedXYProductRawCleared`, which keep the actual
      `Bq * Qq` product and convert directly to
      `PositiveSaddleTangentProductBudgetCertificate`.  Since whole-row
      raw-product scans are still too slow, Lean now also has table-backed
      product checkers that share `cList a`, `BListQ`, and `QListQ` at each
      `(a,N)` and split the finite product scan by half-open `N` chunks and
      the default 20-wide `k` chunks:
      `PositiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate`,
      exposed by
      `coefficientNegativity_of_positiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate`.
      The helper `positiveProductSingletonNChunks` gives a canonical
      singleton `N`-cover and
      `positiveSaddleRawProductTableSingletonNChunkedTangentCellEdgeBudgetCertificate_of_parts`
      fills the cover field for that shape.  The concrete generated-audit
      capstone
      `PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`,
      with final assembly theorem
      `coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`,
      combines the singleton table product chunks with the displayed-solo
      chunk fields, the uniform large-scale edge `k`-chunk budget, and the
      raw-cleared large-tail reserve certificates.  The further concrete
      endpoint
      `PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`,
      with final assembly theorem
      `coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`,
      also chunks tangent-edge checks over the default row chunks and uses
      row-chunked edge checks at the fixed scale
      `positiveEdgeUniformScaleMin`.  Larger generated `N` chunks can use
      the parameterized
      `PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`
      directly; `positiveProductFixedNChunks` supplies a reusable fixed-width
      row-dependent cover when generated checks choose a common `N` chunk
      length.  The fixed-width row-range product wrapper
      `PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`,
      with final assembly theorem
      `coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`,
      packages those row-range product checks directly.
      Since product checks may need finer row chunks than tangent/solo/edge,
      the preferred generated-product endpoint is the independent product-row
      variant
      `PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductRowChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`,
      with final assembly theorem
      `coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductRowChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`.
      If corrected tangent-edge range checks also need a different row
      granularity, the more flexible endpoint is
      `PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductTangentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`,
      with final assembly theorem
      `coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductTangentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`.
      When fixed product-row and tangent-row lengths are enough, the
      wrapper
      `PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedProductTangentRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`,
      with final assembly theorem
      `coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedProductTangentRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`,
      supplies both covers via `positiveSaddleFixedRowChunks`.
      For the most flexible generated finite-window shape, Lean now exposes
      `PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksIndependentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`,
      with final assembly theorem
      `coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksIndependentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`;
      this gives product, tangent, displayed-solo saddle, displayed-solo
      budget, and edge checks independent row covers.
      If fixed row lengths are enough for those five finite families, the
      wrapper
      `PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedFiniteRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`,
      with final assembly theorem
      `coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedFiniteRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`,
      supplies all five covers via `positiveSaddleFixedRowChunks`.
      When a common product row length and common `N` length are enough, the
      fully fixed-width wrapper
      `PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedRowNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`,
      with final assembly theorem
      `coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedRowNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`,
      supplies the product row cover via `positiveSaddleFixedRowChunks`.
      Lean also has
      full-range and chunked range-certificate variants for generated
      finite-window proofs, with `Prop51/PositiveSaddleChunks.lean` providing
      a default 100-row cover of `401 ≤ a ≤ 2000`.  An older concrete final
      audit endpoint is
      `PositiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`,
      with final assembly exposed as
      `coefficientNegativity_of_positiveSaddleDefaultChunkedRangeEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`.
      It packages five default finite-window chunk booleans, raw large-exp
      product estimates against `BplusqGcompBound * QqEplusGcompBound`, a
      unit-scaled solo check `200000000 * solo ≤ 1`, and the candidate
      split-tempered entropy tail with the raw base quotient denominator and
      fixed reserve budgets cleared (`800000000 * reserveTerm ≤ 1`).  The
      remaining proof-producing work is therefore: generate or prove the five
      finite chunk families, prove the two raw product inequalities plus the
      unit solo bound for all `a > 2000`, and prove the six one-dimensional
      candidate split-tempered step/reserve inequalities.  Lean also exposes
      the alternate endpoint
      `PositiveSaddleDefaultCellEdgeEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`,
      whose final assembly theorem is
      `coefficientNegativity_of_positiveSaddleDefaultCellEdgeEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`.
      This keeps product/solo/edge as chunked row booleans but supplies the
      corrected tangent-edge finite proof by individual cell booleans; local
      probing showed single tangent cells are practical for `native_decide`,
      while product cells, solo cells, and edge rows remain too slow for that
      direct approach.
      A denominator-cleared variant,
      `PositiveSaddleDefaultCellEdgeUnitBudgetRowsEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`,
      with final assembly theorem
      `coefficientNegativity_of_positiveSaddleDefaultCellEdgeUnitBudgetRowsEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`,
      keeps the finite solo/edge checks executable but states them as
      `200000000 * bound ≤ 1`, matching the unit-scaled large-tail reserve
      style.
      The preferred practical audit route is now
      `PositiveSaddleDefaultCellEdgeBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`,
      with final assembly theorem
      `coefficientNegativity_of_positiveSaddleDefaultCellEdgeBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`.
      This keeps the default product chunks and tangent cell checks, but
      supplies the finite solo and edge budgets as explicit Lean inequalities
      instead of executable row booleans.  This is a technical Lean staging
      divergence from the TeX-style finite audit, recorded in the code; the
      mathematical inequalities consumed downstream are the same
      `positiveSoloBudget` and `positiveEdgeBudget` bounds.
      The edge side of this staging has now been tightened again: the current
      preferred edge-budget endpoint is
      `PositiveSaddleDefaultCellEdgeKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`,
      with final assembly theorem
      `coefficientNegativity_of_positiveSaddleDefaultCellEdgeKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`.
      It keeps the semantic finite solo bound but replaces the semantic edge
      budget by default disjoint 20-wide `k`-chunks covering every retained
      `k` for `a ≤ 2000`; each chunk is proved by a unit-cleared check
      `checkPositiveEdgeMajorantKChunkUnit`, and the declared reciprocal
      budgets are summed in Lean.  The remaining finite-window divergence
      from the TeX-style fully executable audit is therefore concentrated in
      the solo bound, while the corrected edge scan has a generated-audit
      path that avoids the slow whole-row boolean.  A lighter sibling
      endpoint,
      `PositiveSaddleDefaultCellEdgeUniformKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`,
      uses one edge unit scale per row and reduces the reciprocal-budget field
      to the single inequality `90 / scale ≤ positiveEdgeBudget`; the
      parallel `PositiveSaddleDefaultCellEdgeUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`
      then discharges that rational inequality from the natural threshold
      `positiveEdgeUniformScaleMin ≤ scale`.  The finite solo side now also
      has a TeX-shaped staging endpoint,
      `PositiveSaddleDefaultCellEdgeDisplayedSoloUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`:
      it replaces the opaque semantic solo inequality by the displayed
      saddle field `Ynorm N a ≤ positiveYBound a N a` plus the executable
      unit-scaled range budget `checkPositiveSoloDisplayedYBoundUnitRange`.
      The practical generated-certificate sibling
      `PositiveSaddleDefaultCellEdgeDisplayedSoloChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`
      splits that solo budget over the default 100-row chunks.  The still
      lower-level
      `PositiveSaddleDefaultCellEdgeDisplayedSoloClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`
      also chunks the denominator-cleared displayed `Y_a(N)` saddle
      inequality, so the finite solo side is no longer a normalized
      `Ynorm` field.  The corrected finite product target is now the exact
      raw-product wrapper
      `PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`,
      with final assembly theorem
      `coefficientNegativity_of_positiveSaddleDefaultCellEdgeDisplayedSoloRawProductClearedChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`.
      It chunks the denominator-cleared actual `Bq * Qq` small/tempered
      product checks, keeps tangent-edge checks at cell granularity, and
      checks each default edge `k`-chunk using a row scale bounded below by
      `positiveEdgeUniformScaleMin`.  For actual generated product proofs,
      prefer the finer
      `PositiveSaddleRawProductTableChunkedTangentCellEdgeBudgetCertificate`,
      where the product side is split by row-dependent `N` chunks and default
      `k` chunks instead of asking Lean to evaluate a whole product row.  The
      concrete singleton-`N` generated-audit wrapper
      `PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksUniformLargeScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`
      has a still more concrete fixed-scale/chunked-edge sibling,
      `PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableSingletonNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`,
      and a fixed-width row-range product sibling,
      `PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`.
      The independent product-row fixed-width endpoint
      `PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductRowChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`
      remains available when product chunks use a common positive `N` length
      and a custom product row cover.  The currently most flexible finite
      generated target is
      `PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksProductTangentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`,
      which additionally gives the corrected tangent-edge range checks their
      own row cover.  If displayed-solo or edge checks also need independent
      row granularity, use
      `PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedNChunksIndependentRowChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`.
      If that fully independent setup still uses fixed row lengths, use
      `PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedFiniteRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`.
      Generated finite-window proofs can now target the shorter split
      `PositiveSaddleFixedFiniteWindowAuditCertificate` and combine it with
      `PositiveSaddleLargeTailAuditCertificate`; if each whole finite family
      is practical as one Boolean, target
      `PositiveSaddleFixedFiniteWindowAllChunksAuditCertificate` instead.
      The script `scripts/positive_saddle_fixed_finite_template.py` emits
      both the all-chunks theorem shape and a `split-fields` dispatch shape
      for fixed row and `N` lengths.  Since tangent row-range booleans are
      still too large, the practical sibling
      `PositiveSaddleFixedFiniteWindowCellTangentAuditCertificate` keeps the
      tangent proof at cell granularity; the script emits this with
      `--strategy cell-tangent`.  The fully generated sibling
      `PositiveSaddleFixedFiniteWindowChunkedTangentAuditCertificate` splits
      tangent by fixed row, `N`, and small-`k` chunks and is emitted with
      `--strategy chunked-tangent`.  The finer generated sibling
      `PositiveSaddleFixedFiniteWindowProductNChunkedTangentAuditCertificate`
      also splits product by a uniform product `N`-chunk index and is emitted
      with `--strategy product-n-chunked-tangent`.  For proof production,
      the same script can emit one cacheable chunk theorem at a time with
      `--emit-single-chunk`; `--use-single-chunk-theorems` then assembles the
      final finite certificate from those names, while
      `--emit-single-chunk-suite` emits the atom theorems and assembled
      certificate in one Lean module.  The manifest mode
      `--emit-single-chunk-manifest` emits the same atom list as JSON with
      global atom indices and per-atom emit commands for batching and coverage
      checks; add `--manifest-shard-count n` to include the balanced shard
      start/stop plan in that JSON.  Before asking for the full manifest,
      `--dry-run-counts` prints the same field-level atom counts from closed
      formulas without materializing the atom list; use this first when
      changing row, `N`, or `k` lengths.  The finer Lean endpoint
      `PositiveSaddleFixedFiniteWindowProductTangentSoloNChunkedAuditCertificate`
      also splits tangent and both displayed-solo finite checks by fixed
      `N`-chunk index and is emitted with
      `--strategy product-tangent-solo-n-chunked`; this records the local
      profiling result that
      product/edge atoms are viable at one-row/one-`N` or one-row/one-`k`
      granularity, while tangent and solo whole-`N` row atoms remain too
      large.  The displayed-solo saddle atom now uses the table-backed
      `QListQ (cList a) N a` evaluator, proved equal to `Qq N a`, which makes
      the single-point fixed-`N` atom practical.  The next proof-production
      endpoint,
      `PositiveSaddleFixedFiniteWindowProductNKChunkedTangentSoloNChunkedAuditCertificate`,
      also splits product checks by `positiveProductFixedKChunks`, emitted
      with `--strategy product-nk-tangent-solo-n-chunked` and
      `--product-k-len`.  This is a Lean-level refinement of the same
      finite-window proof obligation: the finer product `k` chunks are
      reassembled into the default 20-wide edge-product chunks.  Local samples
      at `a = 401` show one-row product atoms with `--n-len 10
      --product-k-len 1` compile in roughly 13-15 seconds, where the earlier
      20-wide product atom at `--n-len 10` timed out.  The combined-product
      sibling
      `PositiveSaddleFixedFiniteWindowCombinedProductNKChunkedTangentSoloNChunkedAuditCertificate`,
      emitted with `--strategy combined-product-nk-tangent-solo-n-chunked`,
      runs one shared-table product atom and extracts both the small and
      tempered obligations.  This does not change the TeX-side inequalities;
      it only avoids proving separate small and tempered product atoms for
      the same `(a,N)` tables.  In the same sample, one combined atom compiles
      in about 15 seconds, replacing two separate 13-15 second atoms.
      Edge proof production now has the semantic finer-`k` cover
      `positiveEdgeFixedKChunks` with scale `positiveEdgeFixedKScale`: a
      1600-row default 20-wide edge atom timed out, row lengths 2/5/10/20
      took roughly 8/21/39/82 seconds, and one-wide retained-`k` edge atoms
      with `positiveEdgeFixedKScale 1` compile in about 1-6 seconds.  The
      wrapper
      `PositiveSaddleFixedFiniteWindowCombinedProductNKChunkedTangentSoloNFixedEdgeKChunkedAuditCertificate`
      now consumes these fine edge chunks directly through
      `positiveEdgeBudget_of_fixedKChunksUniformUnitChecks`; emit it with
      `--strategy combined-product-nk-tangent-solo-n-fixed-edge-k-chunked`
      and choose `--edge-k-len`.  This is still only a Lean
      proof-production refinement of the same edge majorant budget.
      The large-tail side now also has
      `PositiveSaddleLargeTailPartsAuditCertificate`, which decomposes the
      two non-finite certificate fields into product-small, product-tempered,
      solo, adjacent-step, and unit-reserve subtargets and then reassembles
      the existing `PositiveSaddleLargeTailAuditCertificate`.  This is not a
      mathematical change, but it gives the remaining analytic proof work
      smaller Lean interfaces.  The large-tail product fields can now be
      supplied through `PositiveSaddleLargeTailProductBoundsCertificate`,
      which further splits each raw product inequality into separate `Bplus`
      and `Qplus/Y` saddle bounds plus a scalar product comparison, matching
      the TeX-style saddle-bound staging more closely.  The solo field can
      likewise be supplied through `PositiveSaddleLargeTailSoloYBoundCertificate`,
      splitting the `Y_a(N)` saddle bound from the dyadic unit budget.
      `PositiveSaddleLargeTailBoundsPartsAuditCertificate` bundles those
      lower-level product and solo bound certificates with the grouped
      candidate step/reserve certificates for final assembly.  The
      finite generator emits final theorems against this split interface with
      `--emit-final --final-tail-parts` or `--final-tail-bounds-parts`.
      The still finer
      `PositiveSaddleLargeTailAtomicPartsAuditCertificate` splits the six
      candidate entropy-reserve fields into atomic small-step,
      lower-tempered-step, upper-tempered-step, and three reserve-family
      certificates.  `PositiveSaddleLargeTailAtomicBoundsAuditCertificate`
      is the fully split product/solo/candidate wrapper; emit final theorems
      against the atomic route with
      `--emit-final --final-tail-atomic-parts` or
      `--final-tail-atomic-bounds`.  The new proof-facing
      `PositiveSaddleLargeTailRefinedAtomicBoundsAuditCertificate` keeps the
      same product/solo bound split but replaces the raw-cleared step atoms by
      the closed small raw-base half target and the two tempered raw-exp ratio
      targets; generated finite files can target it with
      `--emit-final --final-tail-refined-atomic-bounds`, and it converts back
      to the canonical atomic-bounds route.  This quotient-form step split is
      a deliberate Lean refinement of the raw-cleared LaTeX presentation.
      Grouped
      raw-cleared unit-reserve
      candidate proofs can now be split back into the six atomic fields, so
      existing grouped proof production can still feed this final route; the
      convenience wrapper
      `PositiveSaddleLargeTailRawClearedUnitBoundsAuditCertificate` bundles
      product/solo bounds with that grouped candidate proof and is available
      to generated final theorems through
      `--final-tail-raw-cleared-unit-bounds`.  The small adjacent-step atom
      has also been closed further: Lean proves the pure raw-base
      half-quotient inequality
      `2 * positiveEntropyShadowBaseStepRawNumerator a r ≤
      positiveEntropyShadowBaseStepRawDenominator a r` in
      `positiveEntropyShadowBaseStepRawBaseHalf_of_small_branch`, packages it
      as `positiveSaddleLargeTailCandidateSmallRawBaseHalfCertificate`, and
      then uses decreasingness of the small large-exp factor to restore the
      original raw-cleared small-step field.  The constructors
      `positiveSaddleLargeTailCandidateRefinedAtomicCertificate_of_temperedRawExpRatios`
      and
      `positiveSaddleLargeTailRefinedAtomicBoundsAuditCertificate_of_temperedRawExpRatios`
      now fill this closed small-step atom automatically, leaving the two
      tempered ratio atoms and three reserve atoms as the live refined
      candidate obligations.  The wrapper
      `PositiveSaddleLargeTailTemperedRawExpRatioReserveBoundsAuditCertificate`
      and generator flag
      `--final-tail-tempered-raw-exp-ratio-reserve-bounds` expose exactly
      this reduced final tail interface.  Lean now also exposes the stricter
      reserve-envelope wrapper
      `PositiveSaddleLargeTailTemperedRawExpRatioReserveEnvelopeBoundsAuditCertificate`
      and generator flag
      `--final-tail-tempered-raw-exp-ratio-reserve-envelope-bounds`; this
      records the TeX reserve-envelope step as separate exponential-envelope
      and base-times-envelope unit-budget obligations before converting back
      to the same reduced tail route.  The small first-reserve budget side is
      now closed under the concrete envelope `(3/2)^a` by
      `positiveSmallFirstReserveThreeHalvesEnvelopeUnit`; the constructor
      `positiveSaddleLargeTailCandidateSmallFirstReserveEnvelopeCertificate_threeHalves`
      leaves only the analytic bound
      `positiveSmallLargeExp a 1 ≤ (3/2)^a` for that reserve atom.  Lean now
      also proves `positiveSmallExponentUpper a 1 ≤ (3/10) * a` and the
      wrapper
      `positiveSmallLargeExp_one_le_threeHalvesExpBound_of_partialExpUpper_threeTenths`,
      reducing the analytic side to the standalone rational shell envelope
      `partialExpUpper ((3/10) * a) a ≤ (3/2)^a`.  The
      `partialExpUpperNegativeBinomialShell` comparison reduces this to a
      weighted multichoose shell, and Lean closes the shell by comparing its
      finite prefix plus constant tail with the complete negative-binomial
      series `(10/7)^a`.  The reserve-facing closed wrappers are
      `positiveSmallLargeExp_one_le_threeHalvesExpBound` and
      `positiveSaddleLargeTailCandidateSmallFirstReserveEnvelopeCertificate_threeHalves_closed`.
      For the
      lower-tempered
      adjacent-step atom, Lean proves `positiveTemperedLargeExp` decreases on
      the lower side of the split, but the pure raw-base `(4a-1)/(4a)` ratio
      is too strong near the split.  The remaining official target is the
      original raw-cleared lower-step field, using that large-exp decrease
      quantitatively together with the entropy-shadow raw quotient.  The
      proof-facing reduced interface
      `PositiveSaddleLargeTailCandidateTemperedLowerRawExpRatioCertificate`
      records exactly the quotient inequality for
      `rawQuotient * positiveTemperedLargeExp(a,r+1) /
      positiveTemperedLargeExp(a,r)` and converts it back to the raw-cleared
      field.  The upper-tempered reverse step has the analogous
      `PositiveSaddleLargeTailCandidateTemperedUpperReverseRawExpRatioCertificate`
      interface.  Because the small first reserve is now closed, Lean also
      exposes the reduced candidate/audit wrappers
      `positiveSaddleLargeTailCandidateRefinedAtomicCertificate_of_temperedRawExpRatios_temperedReserves`,
      `PositiveSaddleLargeTailTemperedRawExpRatioTemperedReserveBoundsAuditCertificate`,
      and
      `PositiveSaddleLargeTailTemperedRawExpRatioTemperedReserveEnvelopeBoundsAuditCertificate`.
      These leave only the two tempered quotient-step atoms and the two
      tempered endpoint reserve atoms, or their envelope versions, as live
      candidate-side inputs.  The generator flags are
      `--final-tail-tempered-raw-exp-ratio-tempered-reserve-bounds` and
      `--final-tail-tempered-raw-exp-ratio-tempered-reserve-envelope-bounds`.
      Lean now also provides cross-multiplied versions of those two tempered
      quotient-step atoms,
      `PositiveSaddleLargeTailCandidateTemperedLowerRawExpCrossmulCertificate`
      and
      `PositiveSaddleLargeTailCandidateTemperedUpperReverseRawExpCrossmulCertificate`.
      This is a proof-production shape only: the adapters divide by positive
      tempered large-exp and raw-base factors to recover the quotient fields.
      The corresponding reduced audit wrappers and generator flags are
      `PositiveSaddleLargeTailTemperedRawExpCrossmulTemperedReserveBoundsAuditCertificate`,
      `PositiveSaddleLargeTailTemperedRawExpCrossmulTemperedReserveEnvelopeBoundsAuditCertificate`,
      `--final-tail-tempered-raw-exp-crossmul-tempered-reserve-bounds`, and
      `--final-tail-tempered-raw-exp-crossmul-tempered-reserve-envelope-bounds`.
      If a proof already has the core
      `PositiveSaddleLargeTailAuditCertificate`,
      Lean also exposes reverse parts and atomic-parts views for audit.  If
      generated atom theorems are split over separate Lean modules, pass
      repeated `--extra-import` options when emitting the assembly theorem.
      The generator also has
      `--emit-single-chunk-shard --shard-index i --shard-count n` for
      balanced atom modules in the same global order as the manifest.
      If common fixed product-row and tangent-row lengths are enough, use the
      `PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedProductTangentRowNChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`
      wrapper.  If one common product row length is enough and tangent checks
      can stay on the default chunks, use the
      `PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableFixedRowNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`
      wrapper instead.  If product chunks are generated in
      custom larger row-dependent `N` intervals, use the parameterized
      `PositiveSaddleDefaultCellEdgeDisplayedSoloRawProductTableNChunksTangentEdgeChunksFixedScaleKChunkBudgetEntropyLargeExpCandidateSplitTemperedRawClearedUnitBudgetAuditCertificate`
      endpoint instead.  The helper `positiveProductFixedNChunks` proves the
      corresponding cover for fixed-width `N` chunks.
      The fixed-scale
      `DisplayedSoloProductClearedTangentEdgeChunks...` endpoint remains in
      Lean as the fully chunked version of the stronger `Gcomp` product audit
      route, not as the expected final product certificate.  The remaining
      non-finite inputs are still the large-`a` raw product/solo pointwise
      certificate and the raw-cleared unit-reserve entropy-tail certificate.
- [ ] assembly: `U_a(N) < 0` for `a ≥ 401`; combine with Layers B/A into
      the final `CoefficientNegativity`.  The combination step itself is now
      formalized as `coefficientNegativity_of_unorm_tail`, so the remaining
      assembly input is exactly the large-`a` rectangle theorem for `Unorm`.

## Infrastructure

- [ ] blueprint (`blueprint/`, leanblueprint) with dependency graph.
- [ ] kernel-`decide` variants of small certificates where feasible
      (removes `Lean.ofReduceBool` for those; document which remain native).
- [ ] CI: build + axiom audit (done), `--quick` saddle scan (done),
      doc-gen (later).
