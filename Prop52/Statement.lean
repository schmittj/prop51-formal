/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Corrected Chen--Larson Proposition 5.2 coefficient

This file contains the exact rational coefficient formulas needed to state the
corrected Proposition 5.2 nonvanishing theorem.  The geometry supplies this
coefficient for genera `g = 3*a - 2`, where `M = 2*g - 2 = 6*a - 6` and `μ`
is a positive partition of `M`.
-/

import Prop51.Statement

namespace Prop52

/-- For `g = 3*a - 2`, the partition weight is `M = 2*g - 2 = 6*a - 6`. -/
def M (a : Nat) : Nat :=
  6*a - 6

/-- The exponent `N = sum_i (m_i+1)` attached to a partition list. -/
def N (μ : List Nat) : Nat :=
  (μ.map (· + 1)).sum

/-- The coefficients of `Phi(t) = 2*t + 12*t^2*C'(t)/C(t)`. -/
def phiCoeff : Nat → ℚ
  | 0 => 0
  | 1 => 2
  | r + 2 => 12 * ((r + 1 : Nat) : ℚ) * Prop51.c (r + 1)

/-- `w_r = sum_i (q_i-1) q_i^{-r}`, with `q_i = m_i+1`.

Since `q_i - 1 = m_i`, this is written directly in terms of the partition
parts. -/
def markedWeight (μ : List Nat) (r : Nat) : ℚ :=
  (μ.map fun mi : Nat => (mi : ℚ) / ((mi + 1 : Nat) : ℚ)^r).sum

/-- The coefficient of `t^r` in `K_μ(t) = sum_i (q_i-1) Phi(t/q_i)`. -/
def markedCoeff (μ : List Nat) (r : Nat) : ℚ :=
  phiCoeff r * markedWeight μ r

/-- The convolution contribution `[t^a] F_μ(t) K_μ(t)`. -/
def markedConvolution (μ : List Nat) (a : Nat) : ℚ :=
  ((List.range a).map fun k : Nat =>
    markedCoeff μ (k + 1) * Prop51.bCoeff μ (a - (k + 1))).sum

/-- The printed Proposition 5.2 coefficient after the marked-numerator
rewrite, namely `[t^a] F_μ(t) * (1 - K_μ(t))`.

This is retained because the corrected proof uses the already-established sign
of the printed-series coefficient as one input. -/
def printedCoeff (μ : List Nat) (a : Nat) : ℚ :=
  Prop51.bCoeff μ a - markedConvolution μ a

/-- The corrected Proposition 5.2 coefficient:
`[t^a] F_μ(t) * (M - K_μ(t))`. -/
def correctedCoeff (a : Nat) (μ : List Nat) : ℚ :=
  (M a : ℚ) * Prop51.bCoeff μ a - markedConvolution μ a

/-- Large-range sign statement for the printed-series coefficient. -/
def PrintedCoeffNegativityLarge : Prop :=
  ∀ a : Nat, 14 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      printedCoeff μ a < 0

/-- Large-range sign statement for the corrected coefficient. -/
def CorrectedCoeffNegativityLarge : Prop :=
  ∀ a : Nat, 14 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      correctedCoeff a μ < 0

/-- Full nonvanishing statement needed for corrected Proposition 5.2. -/
def CorrectedCoeffNonvanishing : Prop :=
  ∀ a : Nat, 2 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      correctedCoeff a μ ≠ 0

/-- Finite-range nonvanishing statement for corrected Proposition 5.2. -/
def CorrectedCoeffFiniteNonvanishing : Prop :=
  ∀ a : Nat, 2 ≤ a → a ≤ 13 →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      correctedCoeff a μ ≠ 0

end Prop52
