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
- [ ] sign-lock §5 (`Prop51/SignLock.lean`): exact finite decomposition
      of `−X_m` and the non-boundary
      `(-ζ)^s/s!·Π_s D_s·(-E^-_{m-s}/(Nc_{m-s}))` summand factorization
      are done; this is also converted to `(1+ε_{m-s})`, with the completed
      Δ-envelope exposed as `|ε_{m-s}| ≤ 66/(5m)` for `3s ≤ m`.  The final
      rational positivity margin against `2215` is done via a 10-term
      alternating surrogate at `50/27`.  Remaining: prove the P1–P4 pieces
      (Poisson moments via partial-exp majorants) and tails.
- [ ] positive part §6: rational saddle bounds (`ρ` chosen rational),
      two regimes + `native_decide` window scan `401 ≤ a ≤ 2000`,
      entropy tail for `a > 2000`.
- [ ] assembly: `U_a(N) < 0` for `a ≥ 401`; combine with Layers B/A into
      the final `CoefficientNegativity`.

## Infrastructure

- [ ] blueprint (`blueprint/`, leanblueprint) with dependency graph.
- [ ] kernel-`decide` variants of small certificates where feasible
      (removes `Lean.ofReduceBool` for those; document which remain native).
- [ ] CI: build + axiom audit (done), `--quick` saddle scan (done),
      doc-gen (later).
