/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Public facade for the Chen--Larson Proposition 5.1 coefficient theorem

This is the small file intended for external inspection.  It names the
hypergeometric series from Chen--Larson, states the quotient series identity
proved in the formalization, and exposes the final coefficient-negativity and
nonvanishing theorems.
-/

import Prop51.BCoeffSeries
import Prop51.Completion

namespace Prop51

open PowerSeries

/-- The hypergeometric series
`C(X) = sum_k (6k)! / ((3k)! (2k)! 72^k) X^k`
from Chen--Larson Proposition 5.1. -/
noncomputable abbrev chenLarsonC : ℚ⟦X⟧ :=
  Cseries

/-- Coefficient form of the definition of `chenLarsonC`. -/
theorem coeff_chenLarsonC (k : Nat) :
    coeff k chenLarsonC =
      (Nat.factorial (6*k) : ℚ) /
        ((Nat.factorial (3*k) : ℚ) *
          (Nat.factorial (2*k) : ℚ) * 72^k) := by
  simp [chenLarsonC, Cseries, Aseq]

/-- The Chen--Larson quotient generating series associated with a list of
positive parts `μ`.  The theorem below applies when `μ` is a positive
partition of `2g - 2`. -/
noncomputable abbrev chenLarsonSeries (μ : List Nat) : ℚ⟦X⟧ :=
  bSeries μ

/-- Characterization by the generating function appearing in Chen--Larson
Proposition 5.1:

`C(X)^N * B_μ(X) = prod_i C(X/(m_i+1))`, where
`N = sum_i (m_i+1)`. -/
theorem chenLarsonSeries_spec (μ : List Nat) :
    chenLarsonC ^ ((μ.map (· + 1)).sum) * chenLarsonSeries μ =
      (μ.map fun mi =>
        rescale (((mi + 1 : Nat) : ℚ)⁻¹) chenLarsonC).prod := by
  simpa [chenLarsonC, chenLarsonSeries, prodSeries, qq]
    using bSeries_official μ

/-- The relevant Chen--Larson coefficient is strictly negative for every
positive partition in the two residue classes covered by Proposition 5.1. -/
theorem chenLarsonCoefficient_neg
    {g : Nat} (hg : 2 ≤ g) (hmod : g % 3 ≠ 1)
    {μ : List Nat} (hμ : IsPartitionOf μ (2 * g - 2)) :
    coeff (g / 3 + 1) (chenLarsonSeries μ) < 0 := by
  simpa [chenLarsonSeries, bSeries]
    using coefficientNegativity g hg hmod μ hμ

/-- In particular, the coefficient required by Chen--Larson Proposition 5.1
is nonzero. -/
theorem chenLarsonCoefficient_ne_zero
    {g : Nat} (hg : 2 ≤ g) (hmod : g % 3 ≠ 1)
    {μ : List Nat} (hμ : IsPartitionOf μ (2 * g - 2)) :
    coeff (g / 3 + 1) (chenLarsonSeries μ) ≠ 0 :=
  ne_of_lt (chenLarsonCoefficient_neg hg hmod hμ)

end Prop51
