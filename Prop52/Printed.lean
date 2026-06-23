/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Large-range arithmetic for the printed Proposition 5.2 coefficient

This module records exact rational arithmetic from the printed-series
large-range argument.  The analytic estimates proving the lower bound are not
yet formalized here; the final rational margin used to close the proof is.
-/

import Prop52.Statement
import Mathlib.Tactic

namespace Prop52

/-! ## Printed sign range split -/

/-- The interval-certificate range of the printed coefficient proof. -/
def PrintedCoeffNegativityMid : Prop :=
  ∀ a : Nat, 14 ≤ a → a ≤ 149 →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      printedCoeff μ a < 0

/-- The large-tail range of the printed coefficient proof. -/
def PrintedCoeffNegativityTail : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      printedCoeff μ a < 0

theorem printedCoeffNegativityLarge_of_mid_tail
    (hmid : PrintedCoeffNegativityMid)
    (htail : PrintedCoeffNegativityTail) :
    PrintedCoeffNegativityLarge := by
  intro a ha μ hμ
  by_cases h149 : a ≤ 149
  · exact hmid a ha h149 μ hμ
  · exact htail a (by omega) μ hμ

/-! ## Final large-range margin -/

/-- The explicit lower margin appearing at the end of the human large-tail
argument:

`9/(40(a-2)) - (36*delta+4)/a^2`, with
`36*delta+4 = 95444/3125`.

The formal expression is kept rational and uses coercions from `Nat` to `ℚ`.
-/
def printedLargeMargin (a : Nat) : ℚ :=
  9 / (40 * ((a : ℚ) - 2)) - (95444 / 3125) / ((a : ℚ)^2)

/-- Exact positivity of the final large-tail margin for `a >= 150`.

This is the arithmetic sentence in the paper after the analytic estimates:
at `a = 150` the margin is `3389201 / 20812500000`, and the lower bound only
improves for larger `a`.  The proof below avoids decimals by clearing
denominators and reducing to a positive quadratic. -/
theorem printedLargeMargin_pos (a : Nat) (ha : 150 ≤ a) :
    0 < printedLargeMargin a := by
  unfold printedLargeMargin
  have haQ : (150 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
  have ha_pos : (0 : ℚ) < (a : ℚ) := by nlinarith
  have ha2_pos : (0 : ℚ) < (a : ℚ) - 2 := by nlinarith
  have ha_sq_pos : (0 : ℚ) < (a : ℚ)^2 := sq_pos_of_ne_zero (by nlinarith)
  have hquad :
      0 < 28125 * (a : ℚ)^2 - 3817760 * (a : ℚ) + 7635520 := by
    have hshift : 0 ≤ (a : ℚ) - 150 := by nlinarith
    have hsquare : 0 ≤ ((a : ℚ) - 150)^2 := sq_nonneg _
    have hdecomp :
        28125 * (a : ℚ)^2 - 3817760 * (a : ℚ) + 7635520 =
          28125 * ((a : ℚ) - 150)^2 +
            4619740 * ((a : ℚ) - 150) + 67784020 := by
      ring
    rw [hdecomp]
    nlinarith
  have hmul :
      95444 / 3125 / ((a : ℚ)^2) < 9 / (40 * ((a : ℚ) - 2)) := by
    field_simp [ne_of_gt ha_sq_pos, ne_of_gt ha2_pos]
    nlinarith
  linarith

theorem printedLargeMargin_pos_150 :
    printedLargeMargin 150 = 3389201 / 20812500000 := by
  norm_num [printedLargeMargin]

/-! ## Exact factorial-gas constants

The following declarations mirror the first block of
`verify_prop52_tail_constants.py`.  They certify the four finite prefix sums
over `4 <= r <= 75` and the elementary geometric-tail budgets starting at
`r = 76`.
-/

def factorialGasPrefixTerm (base r : Nat) (weighted : Bool) : ℚ :=
  (((Nat.factorial (r - 1) * base^r * 150^4 : Nat) : ℚ) / (150 : ℚ)^r) *
    if weighted then (r : ℚ) else 1

def factorialGasPrefix (base : Nat) (weighted : Bool) : ℚ :=
  ((List.range 72).map fun i : Nat => factorialGasPrefixTerm base (i + 4) weighted).sum

theorem factorialGas_prefix_base4 :
    factorialGasPrefix 4 false < 1727 := by
  native_decide

theorem factorialGas_prefix_base4_weighted :
    factorialGasPrefix 4 true < 7128 := by
  native_decide

theorem factorialGas_prefix_base2 :
    factorialGasPrefix 2 false < 102 := by
  native_decide

theorem factorialGas_prefix_base2_weighted :
    factorialGasPrefix 2 true < 412 := by
  native_decide

theorem factorialGas_tail_base4_first :
    (((48 * 76^4 * 3^76 : Nat) : ℚ) / (4 : ℚ)^76) < 3 / 5 := by
  native_decide

theorem factorialGas_tail_base4_ratio :
    (((3 * 77^4 : Nat) : ℚ) / ((4 * 76^4 : Nat) : ℚ)) < 4 / 5 := by
  native_decide

theorem factorialGas_tail_base4_weighted_first :
    (((48 * 76^5 * 3^76 : Nat) : ℚ) / (4 : ℚ)^76) < 39 := by
  native_decide

theorem factorialGas_tail_base4_weighted_ratio :
    (((3 * 77^5 : Nat) : ℚ) / ((4 * 76^5 : Nat) : ℚ)) < 13 / 16 := by
  native_decide

theorem factorialGas_tail_base2_first :
    (((48 * 76^4 * 3^76 : Nat) : ℚ) / (8 : ℚ)^76) < 1 / 2 := by
  native_decide

theorem factorialGas_tail_base2_ratio :
    (((3 * 77^4 : Nat) : ℚ) / ((8 * 76^4 : Nat) : ℚ)) < 1 / 2 := by
  native_decide

theorem factorialGas_tail_base2_weighted_first :
    (((48 * 76^5 * 3^76 : Nat) : ℚ) / (8 : ℚ)^76) < 1 / 2 := by
  native_decide

theorem factorialGas_tail_base2_weighted_ratio :
    (((3 * 77^5 : Nat) : ℚ) / ((8 * 76^5 : Nat) : ℚ)) < 1 / 2 := by
  native_decide

theorem factorialGas_prefix_tail_base4 :
    factorialGasPrefix 4 false + 3 < 1730 := by
  native_decide

theorem factorialGas_prefix_tail_base4_weighted :
    factorialGasPrefix 4 true + 208 < 7340 := by
  native_decide

theorem factorialGas_prefix_tail_base2 :
    factorialGasPrefix 2 false + 1 < 103 := by
  native_decide

theorem factorialGas_prefix_tail_base2_weighted :
    factorialGasPrefix 2 true + 1 < 413 := by
  native_decide

/-! ## Taylor--Gamma truncation arithmetic -/

def truncationResidueRhs (a : Nat) : ℚ :=
  let p := a / 2
  let r0 := a - p - 1
  let S := a / 8
  920 / (2 : ℚ)^(r0 + 1) +
    2 * (5 / 6 : ℚ)^a +
    9 * (9 / 10 : ℚ)^(a - S) +
    920 * (a : ℚ) * (3 / 10 : ℚ)^(S + 1)

theorem truncationResidue_150 :
    truncationResidueRhs 150 < 1 / (150 : ℚ)^2 := by native_decide

theorem truncationResidue_151 :
    truncationResidueRhs 151 < 1 / (151 : ℚ)^2 := by native_decide

theorem truncationResidue_152 :
    truncationResidueRhs 152 < 1 / (152 : ℚ)^2 := by native_decide

theorem truncationResidue_153 :
    truncationResidueRhs 153 < 1 / (153 : ℚ)^2 := by native_decide

theorem truncationResidue_154 :
    truncationResidueRhs 154 < 1 / (154 : ℚ)^2 := by native_decide

theorem truncationResidue_155 :
    truncationResidueRhs 155 < 1 / (155 : ℚ)^2 := by native_decide

theorem truncationResidue_156 :
    truncationResidueRhs 156 < 1 / (156 : ℚ)^2 := by native_decide

theorem truncationResidue_157 :
    truncationResidueRhs 157 < 1 / (157 : ℚ)^2 := by native_decide

/-! ## Endpoint arithmetic for the `x₀` and `x₂` majorants -/

def endpointM : Nat := 6 * 150 - 6

def endpointN : Nat := 150 - 12

def x0Endpoint1 : ℚ :=
  (5 * (endpointM : ℚ)) / (24 * endpointN) +
    (88 * (endpointM : ℚ)) / (125 * endpointN^2)

def x0Endpoint2 : ℚ :=
  (5 * (endpointM : ℚ)) / (24 * endpointN) +
    (36 * (endpointM : ℚ)) / (25 * endpointN^2)

def x0Endpoint3 : ℚ :=
  (endpointM : ℚ) / (6 * endpointN) +
    (11 * (endpointM : ℚ)) / (100 * endpointN^2)

def x0Endpoint4 : ℚ :=
  (endpointM : ℚ) / (6 * endpointN) +
    (72 * (endpointM : ℚ)) / (325 * endpointN^2)

theorem x0Endpoint1_lt : x0Endpoint1 < 7 / 5 := by native_decide

theorem x0Endpoint2_lt : x0Endpoint2 < 3 / 2 := by native_decide

theorem x0Endpoint3_lt : x0Endpoint3 < 11 / 10 := by native_decide

theorem x0Endpoint4_lt : x0Endpoint4 < 11 / 10 := by native_decide

def x2Endpoint1 : ℚ :=
  5 * (149 : ℚ) / 150 +
    (8 * (endpointM : ℚ) / 25) *
      (16 / (150 : ℚ)^2 + 128 / (150 : ℚ)^3 + 1730 / (150 : ℚ)^4)

def x2Endpoint2 : ℚ :=
  5 * (149 : ℚ) / 150 +
    (8 * (endpointM : ℚ) / 25) *
      (32 / (150 : ℚ)^2 + 384 / (150 : ℚ)^3 + 7340 / (150 : ℚ)^4)

def x2Endpoint3 : ℚ :=
  4 * (149 : ℚ) / 150 +
    (8 * (endpointM : ℚ) / 25) *
      (4 / (150 : ℚ)^2 + 16 / (150 : ℚ)^3 + 103 / (150 : ℚ)^4)

def x2Endpoint4 : ℚ :=
  4 * (149 : ℚ) / 150 +
    (8 * (endpointM : ℚ) / 25) *
      (8 / (150 : ℚ)^2 + 48 / (150 : ℚ)^3 + 413 / (150 : ℚ)^4)

theorem x2Endpoint1_lt : x2Endpoint1 < 26 / 5 := by native_decide

theorem x2Endpoint2_lt : x2Endpoint2 < 11 / 2 := by native_decide

theorem x2Endpoint3_lt : x2Endpoint3 < 81 / 20 := by native_decide

theorem x2Endpoint4_lt : x2Endpoint4 < 41 / 10 := by native_decide

end Prop52
