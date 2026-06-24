/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Public facade for the corrected Chen--Larson Proposition 5.2

This file is the human-facing checkpoint for the `g ≡ 1 (mod 3)` case.  It
first pins the power series and coefficient formulas appearing in the paper, and
then states the final source-shaped theorems.
-/

import Prop51.Theorem
import Prop52.Source

namespace Prop52

open PowerSeries

/-- The Chen--Larson hypergeometric series
`C(X) = sum_k (6k)! / ((3k)! (2k)! 72^k) X^k`. -/
noncomputable abbrev chenLarsonC : ℚ⟦X⟧ :=
  Prop51.chenLarsonC

/-- Coefficient form of the definition of `chenLarsonC`. -/
theorem coeff_chenLarsonC (k : Nat) :
    coeff k chenLarsonC =
      (Nat.factorial (6*k) : ℚ) /
        ((Nat.factorial (3*k) : ℚ) *
          (Nat.factorial (2*k) : ℚ) * 72^k) :=
  Prop51.coeff_chenLarsonC k

/-- The Proposition 5.1 quotient series `B_μ(X)`. -/
noncomputable abbrev chenLarsonSeries (μ : List Nat) : ℚ⟦X⟧ :=
  Prop51.chenLarsonSeries μ

/-- The quotient-series identity
`C(X)^N * B_μ(X) = prod_i C(X/(m_i+1))`, with `N = sum_i (m_i+1)`. -/
theorem chenLarsonSeries_spec (μ : List Nat) :
    chenLarsonC ^ ((μ.map (· + 1)).sum) * chenLarsonSeries μ =
      (μ.map fun mi =>
        rescale (((mi + 1 : Nat) : ℚ)⁻¹) chenLarsonC).prod :=
  Prop51.chenLarsonSeries_spec μ

/-- The coefficient called `b_a(μ)` in the paper is the coefficient of
`B_μ(X)`. -/
theorem coeff_chenLarsonSeries (μ : List Nat) (a : Nat) :
    coeff a (chenLarsonSeries μ) = Prop51.bCoeff μ a := by
  simp [chenLarsonSeries, Prop51.chenLarsonSeries, Prop51.bSeries]

/-- `N μ = sum_i (m_i + 1)`, the exponent of `C(X)` in the quotient. -/
theorem N_spec (μ : List Nat) :
    N μ = (μ.map (· + 1)).sum := rfl

/-- `sPower μ r = sum_i (m_i+1)^(-r)`. -/
theorem sPower_spec (μ : List Nat) (r : Nat) :
    sPower μ r =
      (μ.map fun mi : Nat => 1 / ((mi + 1 : Nat) : ℚ)^r).sum := rfl

/-- The corrected source factor `D^cor_{μ,lead}(X)`.

For the geometric Proposition 5.2 coefficient the leading term is
`lead = M a = 6a - 6 = 2g - 2`; the auxiliary printed coefficient uses
`lead = 1`. -/
noncomputable abbrev chenLarsonProp52SourceFactor
    (lead : ℚ) (μ : List Nat) : ℚ⟦X⟧ :=
  mk (sourceFactorCoeff lead μ)

/-- Constant term of the source factor. -/
theorem coeff_sourceFactor_zero (lead : ℚ) (μ : List Nat) :
    coeff 0 (chenLarsonProp52SourceFactor lead μ) = lead := by
  simp [chenLarsonProp52SourceFactor, sourceFactorCoeff]

/-- Linear term of the source factor:
`-2 * (N - s_1)`. -/
theorem coeff_sourceFactor_one (lead : ℚ) (μ : List Nat) :
    coeff 1 (chenLarsonProp52SourceFactor lead μ) =
      -2 * ((N μ : ℚ) - sPower μ 1) := by
  simp [chenLarsonProp52SourceFactor, sourceFactorCoeff]

/-- Higher terms of the source factor:
the coefficient of `X^(r+2)` is
`-12 * (r+1) * c_(r+1) * (N - s_(r+2))`. -/
theorem coeff_sourceFactor_succ_succ (lead : ℚ) (μ : List Nat) (r : Nat) :
    coeff (r + 2) (chenLarsonProp52SourceFactor lead μ) =
      -12 * ((r + 1 : Nat) : ℚ) * Prop51.c (r + 1) *
        ((N μ : ℚ) - sPower μ (r + 2)) := by
  simp [chenLarsonProp52SourceFactor, sourceFactorCoeff]

/-- The source coefficient used below is exactly the coefficient of
`D^cor_{μ,lead}(X) * B_μ(X)`.  This is the code-level `[X^a] B_μ D^cor_μ`
pinning for corrected Proposition 5.2. -/
theorem coeff_sourceFactor_mul_chenLarsonSeries
    (lead : ℚ) (μ : List Nat) (a : Nat) :
    coeff a (chenLarsonProp52SourceFactor lead μ * chenLarsonSeries μ) =
      sourceCoeff lead μ a := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j =>
        coeff i (chenLarsonProp52SourceFactor lead μ) *
          coeff j (chenLarsonSeries μ)) a]
  simp [sourceCoeff, chenLarsonProp52SourceFactor, coeff_chenLarsonSeries]

/-- Since power series over `ℚ` commute, the same coefficient is
`[X^a] B_μ(X) * D^cor_{μ,lead}(X)`. -/
theorem coeff_chenLarsonSeries_mul_sourceFactor
    (lead : ℚ) (μ : List Nat) (a : Nat) :
    coeff a (chenLarsonSeries μ * chenLarsonProp52SourceFactor lead μ) =
      sourceCoeff lead μ a := by
  rw [mul_comm, coeff_sourceFactor_mul_chenLarsonSeries]

/-- For `g ≡ 1 (mod 3)`, the source leading term
`M (g / 3 + 1)` is the geometric number `2g - 2`. -/
theorem M_genus_spec {g : Nat} (hmod : g % 3 = 1) :
    M (g / 3 + 1) = 2 * g - 2 := by
  have hdecomp : g = 3 * (g / 3) + 1 := by
    have h := Nat.mod_add_div g 3
    omega
  simp [M]
  omega

/-- Corrected Chen--Larson Proposition 5.2 source coefficient: non-vanishing
for every genus `g ≥ 2` with `g ≡ 1 (mod 3)`. -/
theorem chenLarsonProp52Coefficient_nonvanishing
    {g : Nat} (hg : 2 ≤ g) (hmod : g % 3 = 1)
    {μ : List Nat} (hμ : Prop51.IsPartitionOf μ (2 * g - 2)) :
    coeff (g / 3 + 1)
      (chenLarsonSeries μ *
        chenLarsonProp52SourceFactor (M (g / 3 + 1)) μ) ≠ 0 := by
  rw [coeff_chenLarsonSeries_mul_sourceFactor]
  have hM : M (g / 3 + 1) = 2 * g - 2 := M_genus_spec hmod
  have ha : 2 ≤ g / 3 + 1 := by
    have hdecomp : g = 3 * (g / 3) + 1 := by
      have h := Nat.mod_add_div g 3
      omega
    omega
  have hμ' : Prop51.IsPartitionOf μ (M (g / 3 + 1)) := by
    simpa [hM] using hμ
  exact sourceCorrectedCoeff_nonvanishing (g / 3 + 1) ha μ hμ'

/-- Corrected Chen--Larson Proposition 5.2 source coefficient: strict
negativity in the large range `g ≥ 40`, `g ≡ 1 (mod 3)`. -/
theorem chenLarsonProp52Coefficient_neg
    {g : Nat} (hg : 40 ≤ g) (hmod : g % 3 = 1)
    {μ : List Nat} (hμ : Prop51.IsPartitionOf μ (2 * g - 2)) :
    coeff (g / 3 + 1)
      (chenLarsonSeries μ *
        chenLarsonProp52SourceFactor (M (g / 3 + 1)) μ) < 0 := by
  rw [coeff_chenLarsonSeries_mul_sourceFactor]
  have hM : M (g / 3 + 1) = 2 * g - 2 := M_genus_spec hmod
  have ha : 14 ≤ g / 3 + 1 := by
    have hdecomp : g = 3 * (g / 3) + 1 := by
      have h := Nat.mod_add_div g 3
      omega
    omega
  have hμ' : Prop51.IsPartitionOf μ (M (g / 3 + 1)) := by
    simpa [hM] using hμ
  exact sourceCorrectedCoeff_neg ha hμ'

end Prop52
