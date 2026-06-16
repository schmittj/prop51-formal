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
  dyadic kernel; the `a > 2000` entropy tail  →  `C(n,k) ≥ (n/k)^k`.

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
      `positiveEdgeMajorantSum a ≤ positiveEdgeBudget`.  A further
      `PositiveSaddleDisplayedBudgetCertificate` fixes the paper's displayed
      `X`/`Y` saddle-bound shapes with constants `8.9`, `7.3`, and `14.5`;
      its explicit product fields mark the remaining proof that the product
      of two rational exponential surrogates fits below the single combined
      surrogate used by the executable majorants.  Those product obligations
      are now also factored through `PositiveSaddleExpEdgeBudgetCertificate`,
      whose remaining fields are the pure exponential/edge inequalities
      after all common scalar prefactors have been cancelled.
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
