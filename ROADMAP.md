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
- [ ] (moved to Layer C prep) `d`-normalization `c_r = 6^r (r-1)! d_r`, `d`
      nondecreasing, `d_r ≤ 0.16` (rationalized: `β_r ≤ β_{r₀}·exp(5/(36 r₀))`
      with `β_{r₀}` exact — avoids Γ-reflection / π entirely).

## Layer A′ — partition quantifier upgrade

- [ ] `mem_partitions_iff`: completeness of the generator
      (`μ ∈ partitions n ↔ μ.sum = n ∧ sorted-desc ∧ positive parts`).
- [ ] permutation-invariance of `bCoeff` (it factors through the multiset of
      parts); upgrade `bCoeff_neg_g_le_23` to the `IsPartitionOf` form.
- [ ] optional: align with `Mathlib.Combinatorics.Partition` / `Nat.Partition`.

## Layer B — interval certificate `61 ≤ a ≤ 400`

- [ ] verified dyadic interval arithmetic (`Int` mantissa, fixed precision
      ≥ 128 bits; add/mul/div with directed rounding + soundness lemmas), or
      adapt [girving/interval](https://github.com/girving/interval)
      (64-bit; plain doubles empirically reproduce the 192-bit Arb values to
      1e-12, so 64-bit may suffice — prototype on the `N = 4792` column).
- [ ] interval port of the `X/Y` recurrences with per-`N` shared tables;
      conservative sign handling exactly as in
      `certificates/prop51_A400_certificate_package.zip`.
- [ ] `native_decide` over all 480,984 pairs (budget: the Python/Arb run
      takes 11 s on 24 cores; expect minutes single-threaded in Lean).

## Layer C — the effective tail `a ≥ 401`

Real analysis with explicit constants; the paper's §§4–6.

- [ ] effective Stirling bounds (from `stirlingSeq` antitonicity, or
      elementary `(n/e)^n ≤ n!` inductions) and `exp` evaluation bounds
      (`Real.exp_bound`-style Taylor remainders at rational points).
- [ ] Lemma 2.1 chain + reciprocal-binomial lemmas (finite combinatorics).
- [ ] composition lemma (eq. 19) — finite induction, already paper-complete.
- [ ] Δ-envelope (Lemma 4.1, R ≤ 20) incl. the one-variable far-tail check.
- [ ] sign-lock §5: P1–P4 + tails ⇒ `C₂ = 2215` (the long grind; the paper's
      P-pieces map 1:1 to Lean lemmas; all weighted sums are finite sums plus
      explicit geometric tails).
- [ ] positive part §6: two saddle regimes + entropy tail; replace the
      scripted window scan by a Lean-checked finite computation
      (cf. `scripts/positive_saddle_scan.py`, corrected two-edge version).
- [ ] assembly: `U_a(N) < 0` for `a ≥ 401`; combine with Layers B/A.

## Infrastructure

- [ ] blueprint (`blueprint/`, leanblueprint) with dependency graph.
- [ ] kernel-`decide` variants of small certificates where feasible
      (removes `Lean.ofReduceBool` for those; document which remain native).
- [ ] CI: build + axiom audit (done), `--quick` saddle scan (done),
      doc-gen (later).
