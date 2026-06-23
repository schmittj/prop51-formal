/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Large-range arithmetic for the printed Proposition 5.2 coefficient

This module records exact rational arithmetic from the printed-series
large-range argument.  The analytic estimates proving the lower bound are not
yet formalized here; the final rational margin used to close the proof is.
-/

import Prop52.Statement
import Prop51.Majorant
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

/-! ## Normalized large-tail assembly

The printed proof of the range `a >= 150` proves a normalized lower bound

`printedLargeMargin a <= -T_a(μ)/(N(μ) c_a)`,

where `T_a(μ)` is `printedCoeff μ a`.  The declarations in this section
separate that remaining analytic inequality from the final sign extraction.
-/

/-- The remaining normalized analytic target for the printed large-tail range.

This is the exact final inequality in the human proof after the
Gamma/truncation/error estimates have been assembled. -/
def PrintedTailNormalizedLowerBound : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      printedLargeMargin a ≤
        (-printedCoeff μ a) / (((N μ : Nat) : ℚ) * Prop51.c a)

private theorem printedTail_N_pos {a : Nat} {μ : List Nat}
    (ha : 150 ≤ a) (hμ : Prop51.IsPartitionOf μ (M a)) :
    0 < N μ := by
  obtain ⟨hsum, _hpos⟩ := hμ
  have hN : N μ = M a + μ.length := by
    unfold N
    rw [Prop51.sum_map_add_one, hsum]
  have hM : 0 < M a := by
    unfold M
    omega
  omega

private theorem printedTail_den_pos {a : Nat} {μ : List Nat}
    (ha : 150 ≤ a) (hμ : Prop51.IsPartitionOf μ (M a)) :
    0 < (((N μ : Nat) : ℚ) * Prop51.c a) := by
  have hN : (0 : ℚ) < ((N μ : Nat) : ℚ) := by
    exact_mod_cast printedTail_N_pos (a := a) (μ := μ) ha hμ
  have hc : 0 < Prop51.c a := Prop51.c_pos a (by omega)
  exact mul_pos hN hc

/-- Closing the printed large-tail sign from the normalized lower bound. -/
theorem printedCoeffNegativityTail_of_normalizedLowerBound
    (hbound : PrintedTailNormalizedLowerBound) :
    PrintedCoeffNegativityTail := by
  intro a ha μ hμ
  have hmargin_pos : 0 < printedLargeMargin a := printedLargeMargin_pos a ha
  have hnorm :
      0 < (-printedCoeff μ a) / (((N μ : Nat) : ℚ) * Prop51.c a) :=
    lt_of_lt_of_le hmargin_pos (hbound a ha μ hμ)
  have hden_pos :
      0 < (((N μ : Nat) : ℚ) * Prop51.c a) :=
    printedTail_den_pos (a := a) (μ := μ) ha hμ
  have hneg_pos : 0 < -printedCoeff μ a := by
    have hmul :
        0 < ((-printedCoeff μ a) / (((N μ : Nat) : ℚ) * Prop51.c a)) *
          (((N μ : Nat) : ℚ) * Prop51.c a) :=
      mul_pos hnorm hden_pos
    rwa [div_mul_cancel₀ _ hden_pos.ne'] at hmul
  linarith

theorem printedCoeffNegativityLarge_of_mid_normalizedTail
    (hmid : PrintedCoeffNegativityMid)
    (htail : PrintedTailNormalizedLowerBound) :
    PrintedCoeffNegativityLarge :=
  printedCoeffNegativityLarge_of_mid_tail hmid
    (printedCoeffNegativityTail_of_normalizedLowerBound htail)

/-! ## Gamma-margin arithmetic -/

def gammaExponentBound (a : Nat) : ℚ :=
  5 / 4 + 5 / (2 * ((a : ℚ) - 3)) +
    96 * (a : ℚ)^2 / (25 * ((a : ℚ) - 5)^3)

private theorem gammaExponentBound_poly_pos (a : Nat) (ha : 150 ≤ a) :
    0 < 100 * (a : ℚ)^4 - 14480 * (a : ℚ)^3 + 110040 * (a : ℚ)^2 -
      410000 * (a : ℚ) + 662500 := by
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hshift : 0 ≤ (a : ℚ) - 150 := by nlinarith
  have hsq : 0 ≤ ((a : ℚ) - 150)^2 := sq_nonneg _
  have hcube : 0 ≤ ((a : ℚ) - 150)^3 := by positivity
  have hfour : 0 ≤ ((a : ℚ) - 150)^4 := by positivity
  have hdecomp :
      100 * (a : ℚ)^4 - 14480 * (a : ℚ)^3 + 110040 * (a : ℚ)^2 -
          410000 * (a : ℚ) + 662500 =
        100 * ((a : ℚ) - 150)^4 + 45520 * ((a : ℚ) - 150)^3 +
          7094040 * ((a : ℚ) - 150)^2 + 405202000 * ((a : ℚ) - 150) +
          4170062500 := by
    ring
  rw [hdecomp]
  nlinarith

/-- The rational endpoint in the Gamma-margin proof is uniformly below
`13/10` for all `a >= 150`. -/
theorem gammaExponentBound_lt (a : Nat) (ha : 150 ≤ a) :
    gammaExponentBound a < 13 / 10 := by
  unfold gammaExponentBound
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have h3 : (0 : ℚ) < (a : ℚ) - 3 := by nlinarith
  have h5 : (0 : ℚ) < (a : ℚ) - 5 := by nlinarith
  have hpoly := gammaExponentBound_poly_pos a ha
  field_simp [h3.ne', h5.ne']
  ring_nf
  nlinarith

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

def truncationResidueScaled (a : Nat) : ℚ :=
  (a : ℚ)^2 * truncationResidueRhs a

private def truncationResidueScaledTerm1 (a : Nat) : ℚ :=
  (a : ℚ)^2 * (920 / (2 : ℚ)^(a - a/2))

private def truncationResidueScaledTerm2 (a : Nat) : ℚ :=
  (a : ℚ)^2 * (2 * (5/6 : ℚ)^a)

private def truncationResidueScaledTerm3 (a : Nat) : ℚ :=
  (a : ℚ)^2 * (9 * (9/10 : ℚ)^(a - a/8))

private def truncationResidueScaledTerm4 (a : Nat) : ℚ :=
  (a : ℚ)^2 * (920 * (a : ℚ) * (3/10 : ℚ)^(a/8 + 1))

private theorem truncationResidueScaled_eq_terms (a : Nat) (ha : 150 ≤ a) :
    truncationResidueScaled a =
      truncationResidueScaledTerm1 a +
      truncationResidueScaledTerm2 a +
      truncationResidueScaledTerm3 a +
      truncationResidueScaledTerm4 a := by
  unfold truncationResidueScaled truncationResidueRhs
    truncationResidueScaledTerm1 truncationResidueScaledTerm2
    truncationResidueScaledTerm3 truncationResidueScaledTerm4
  dsimp only
  have hr0 : a - a / 2 - 1 + 1 = a - a / 2 := by omega
  rw [hr0]
  ring_nf

private theorem truncationResidueScaledTerm1_step8 (a : Nat) (ha : 150 ≤ a) :
    truncationResidueScaledTerm1 (a + 8) ≤ truncationResidueScaledTerm1 a := by
  unfold truncationResidueScaledTerm1
  have hdiv : (a + 8) / 2 = a / 2 + 4 := by
    simpa [show 8 = 4 * 2 by norm_num] using
      Nat.add_mul_div_right a 4 (by decide : 0 < 2)
  have hexp : a + 8 - (a + 8) / 2 = (a - a/2) + 4 := by
    rw [hdiv]
    omega
  rw [hexp, pow_add]
  norm_num
  have hpoly : (((a + 8 : Nat) : ℚ)^2 / 16 ≤ (a : ℚ)^2) := by
    push_cast
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  have hnonneg : 0 ≤ 920 / (2 : ℚ) ^ (a - a / 2) := by positivity
  calc
    ((a : ℚ) + 8) ^ 2 * (920 / ((2 : ℚ) ^ (a - a / 2) * 16))
        = (((a + 8 : Nat) : ℚ)^2 / 16) *
            (920 / (2 : ℚ) ^ (a - a / 2)) := by
            push_cast
            ring
    _ ≤ (a : ℚ)^2 * (920 / (2 : ℚ) ^ (a - a / 2)) :=
      mul_le_mul_of_nonneg_right hpoly hnonneg

private theorem truncationResidueScaledTerm2_step8 (a : Nat) (ha : 150 ≤ a) :
    truncationResidueScaledTerm2 (a + 8) ≤ truncationResidueScaledTerm2 a := by
  unfold truncationResidueScaledTerm2
  rw [pow_add]
  norm_num
  have hpoly :
      (((a + 8 : Nat) : ℚ)^2 * (390625 / 839808 : ℚ) ≤ (a : ℚ)^2 * 2) := by
    push_cast
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  have hnonneg : 0 ≤ (5 / 6 : ℚ) ^ a := by positivity
  calc
    ((a : ℚ) + 8) ^ 2 * (2 * ((5 / 6 : ℚ) ^ a * (390625 / 1679616)))
        = (((a + 8 : Nat) : ℚ)^2 * (390625 / 839808 : ℚ)) *
            (5 / 6 : ℚ) ^ a := by
            push_cast
            ring
    _ ≤ ((a : ℚ)^2 * 2) * (5 / 6 : ℚ) ^ a :=
      mul_le_mul_of_nonneg_right hpoly hnonneg
    _ = (a : ℚ)^2 * (2 * (5 / 6 : ℚ) ^ a) := by ring

private theorem truncationResidueScaledTerm3_step8 (a : Nat) (ha : 150 ≤ a) :
    truncationResidueScaledTerm3 (a + 8) ≤ truncationResidueScaledTerm3 a := by
  unfold truncationResidueScaledTerm3
  have hdiv : (a + 8) / 8 = a / 8 + 1 := by
    simpa only [one_mul] using Nat.add_mul_div_right a 1 (by decide : 0 < 8)
  have hexp : a + 8 - (a + 8) / 8 = (a - a/8) + 7 := by
    rw [hdiv]
    omega
  rw [hexp, pow_add]
  norm_num
  have hpoly : (((a + 8 : Nat) : ℚ)^2 * ((9/10 : ℚ)^7) ≤ (a : ℚ)^2) := by
    norm_num
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  have hnonneg : 0 ≤ 9 * (9 / 10 : ℚ) ^ (a - a / 8) := by positivity
  calc
    ((a : ℚ) + 8) ^ 2 *
        (9 * ((9 / 10 : ℚ) ^ (a - a / 8) * (4782969 / 10000000)))
        = (((a + 8 : Nat) : ℚ)^2 * ((9/10 : ℚ)^7)) *
            (9 * (9 / 10 : ℚ) ^ (a - a / 8)) := by
            push_cast
            norm_num
            ring
    _ ≤ (a : ℚ)^2 * (9 * (9 / 10 : ℚ) ^ (a - a / 8)) :=
      mul_le_mul_of_nonneg_right hpoly hnonneg

private theorem truncationResidueScaledTerm4_step8 (a : Nat) (ha : 150 ≤ a) :
    truncationResidueScaledTerm4 (a + 8) ≤ truncationResidueScaledTerm4 a := by
  unfold truncationResidueScaledTerm4
  have hdiv : (a + 8) / 8 = a / 8 + 1 := by
    simpa only [one_mul] using Nat.add_mul_div_right a 1 (by decide : 0 < 8)
  rw [hdiv]
  rw [show a / 8 + 1 + 1 = a / 8 + 2 by omega, pow_succ]
  ring_nf
  have hpoly : (((a + 8 : Nat) : ℚ)^3 * (3/10 : ℚ) ≤ (a : ℚ)^3) := by
    push_cast
    ring_nf
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  have hnonneg : 0 ≤ 276 * (3 / 10 : ℚ) ^ (a / 8) := by positivity
  calc
    ((8 + a : Nat) : ℚ) ^ 3 * (3 / 10 : ℚ) ^ (a / 8) * (414 / 5)
        = (((a + 8 : Nat) : ℚ)^3 * (3 / 10 : ℚ)) *
            (276 * (3 / 10 : ℚ) ^ (a / 8)) := by
            push_cast
            ring
    _ ≤ (a : ℚ)^3 * (276 * (3 / 10 : ℚ) ^ (a / 8)) :=
      mul_le_mul_of_nonneg_right hpoly hnonneg
    _ = (a : ℚ)^3 * (3 / 10 : ℚ) ^ (a / 8) * 276 := by ring

/-- The scaled truncation residue decreases when `a` is increased by eight.

This is the formal version of the paper's parity/mod-eight monotonicity
argument for the four exponential tail terms. -/
theorem truncationResidueScaled_step8 (a : Nat) (ha : 150 ≤ a) :
    truncationResidueScaled (a + 8) ≤ truncationResidueScaled a := by
  rw [truncationResidueScaled_eq_terms (a + 8) (by omega),
    truncationResidueScaled_eq_terms a ha]
  nlinarith [truncationResidueScaledTerm1_step8 a ha,
    truncationResidueScaledTerm2_step8 a ha,
    truncationResidueScaledTerm3_step8 a ha,
    truncationResidueScaledTerm4_step8 a ha]

private theorem truncationResidueScaled_150 : truncationResidueScaled 150 < 1 := by
  unfold truncationResidueScaled
  norm_num
  nlinarith [truncationResidue_150]

private theorem truncationResidueScaled_151 : truncationResidueScaled 151 < 1 := by
  unfold truncationResidueScaled
  norm_num
  nlinarith [truncationResidue_151]

private theorem truncationResidueScaled_152 : truncationResidueScaled 152 < 1 := by
  unfold truncationResidueScaled
  norm_num
  nlinarith [truncationResidue_152]

private theorem truncationResidueScaled_153 : truncationResidueScaled 153 < 1 := by
  unfold truncationResidueScaled
  norm_num
  nlinarith [truncationResidue_153]

private theorem truncationResidueScaled_154 : truncationResidueScaled 154 < 1 := by
  unfold truncationResidueScaled
  norm_num
  nlinarith [truncationResidue_154]

private theorem truncationResidueScaled_155 : truncationResidueScaled 155 < 1 := by
  unfold truncationResidueScaled
  norm_num
  nlinarith [truncationResidue_155]

private theorem truncationResidueScaled_156 : truncationResidueScaled 156 < 1 := by
  unfold truncationResidueScaled
  norm_num
  nlinarith [truncationResidue_156]

private theorem truncationResidueScaled_157 : truncationResidueScaled 157 < 1 := by
  unfold truncationResidueScaled
  norm_num
  nlinarith [truncationResidue_157]

/-- Uniform truncation-residue bound for every `a >= 150`, assembled from the
eight endpoint checks and the mod-eight monotonicity step. -/
theorem truncationResidue_bound (a : Nat) (ha : 150 ≤ a) :
    truncationResidueRhs a < 1 / (a : ℚ)^2 := by
  have hscaled : truncationResidueScaled a < 1 := by
    refine Nat.strong_induction_on a ?_ ha
    intro a ih ha
    by_cases hle : a ≤ 157
    · interval_cases a <;> first
        | exact truncationResidueScaled_150
        | exact truncationResidueScaled_151
        | exact truncationResidueScaled_152
        | exact truncationResidueScaled_153
        | exact truncationResidueScaled_154
        | exact truncationResidueScaled_155
        | exact truncationResidueScaled_156
        | exact truncationResidueScaled_157
    · have hprev_ge : 150 ≤ a - 8 := by omega
      have hprev_lt : a - 8 < a := by omega
      have hprev : truncationResidueScaled (a - 8) < 1 :=
        ih (a - 8) hprev_lt hprev_ge
      have hstep :
          truncationResidueScaled ((a - 8) + 8) ≤ truncationResidueScaled (a - 8) :=
        truncationResidueScaled_step8 (a - 8) hprev_ge
      have hadd : (a - 8) + 8 = a := by omega
      rw [hadd] at hstep
      exact lt_of_le_of_lt hstep hprev
  unfold truncationResidueScaled at hscaled
  have ha_sq_pos : (0 : ℚ) < (a : ℚ)^2 := by
    have ha_pos : (0 : ℚ) < (a : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 150) ha)
    positivity
  rw [lt_div_iff₀ ha_sq_pos]
  nlinarith

/-! ## Uniform endpoint arithmetic for the `x₀` and `x₂` majorants -/

def printedTailMrat (a : Nat) : ℚ :=
  6 * (a : ℚ) - 6

def printedTailX0Bound1 (a : Nat) : ℚ :=
  (5 * printedTailMrat a) / (24 * ((a : ℚ) - 12)) +
    (88 * printedTailMrat a) / (125 * ((a : ℚ) - 12)^2)

def printedTailX0Bound2 (a : Nat) : ℚ :=
  (5 * printedTailMrat a) / (24 * ((a : ℚ) - 12)) +
    (36 * printedTailMrat a) / (25 * ((a : ℚ) - 12)^2)

def printedTailX0Bound3 (a : Nat) : ℚ :=
  printedTailMrat a / (6 * ((a : ℚ) - 12)) +
    (11 * printedTailMrat a) / (100 * ((a : ℚ) - 12)^2)

def printedTailX0Bound4 (a : Nat) : ℚ :=
  printedTailMrat a / (6 * ((a : ℚ) - 12)) +
    (72 * printedTailMrat a) / (325 * ((a : ℚ) - 12)^2)

theorem printedTailX0Bound1_lt (a : Nat) (ha : 150 ≤ a) :
    printedTailX0Bound1 a < 7 / 5 := by
  unfold printedTailX0Bound1 printedTailMrat
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hn_pos : (0 : ℚ) < (a : ℚ) - 12 := by nlinarith
  field_simp [hn_pos.ne']
  nlinarith

theorem printedTailX0Bound2_lt (a : Nat) (ha : 150 ≤ a) :
    printedTailX0Bound2 a < 3 / 2 := by
  unfold printedTailX0Bound2 printedTailMrat
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hn_pos : (0 : ℚ) < (a : ℚ) - 12 := by nlinarith
  field_simp [hn_pos.ne']
  nlinarith

theorem printedTailX0Bound3_lt (a : Nat) (ha : 150 ≤ a) :
    printedTailX0Bound3 a < 11 / 10 := by
  unfold printedTailX0Bound3 printedTailMrat
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hn_pos : (0 : ℚ) < (a : ℚ) - 12 := by nlinarith
  field_simp [hn_pos.ne']
  nlinarith

theorem printedTailX0Bound4_lt (a : Nat) (ha : 150 ≤ a) :
    printedTailX0Bound4 a < 11 / 10 := by
  unfold printedTailX0Bound4 printedTailMrat
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hn_pos : (0 : ℚ) < (a : ℚ) - 12 := by nlinarith
  field_simp [hn_pos.ne']
  nlinarith

def printedTailX2Bound1 (a : Nat) : ℚ :=
  5 * ((a : ℚ) - 1) / (a : ℚ) +
    (8 * printedTailMrat a / 25) *
      (16 / (a : ℚ)^2 + 128 / (a : ℚ)^3 + 1730 / (a : ℚ)^4)

def printedTailX2Bound2 (a : Nat) : ℚ :=
  5 * ((a : ℚ) - 1) / (a : ℚ) +
    (8 * printedTailMrat a / 25) *
      (32 / (a : ℚ)^2 + 384 / (a : ℚ)^3 + 7340 / (a : ℚ)^4)

def printedTailX2Bound3 (a : Nat) : ℚ :=
  4 * ((a : ℚ) - 1) / (a : ℚ) +
    (8 * printedTailMrat a / 25) *
      (4 / (a : ℚ)^2 + 16 / (a : ℚ)^3 + 103 / (a : ℚ)^4)

def printedTailX2Bound4 (a : Nat) : ℚ :=
  4 * ((a : ℚ) - 1) / (a : ℚ) +
    (8 * printedTailMrat a / 25) *
      (8 / (a : ℚ)^2 + 48 / (a : ℚ)^3 + 413 / (a : ℚ)^4)

private theorem printedTailX2Bound1_poly_pos (a : Nat) (ha : 150 ≤ a) :
    0 < 25 * (a : ℚ)^4 - 3215 * (a : ℚ)^3 - 26880 * (a : ℚ)^2 -
      384480 * (a : ℚ) + 415200 := by
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hshift : 0 ≤ (a : ℚ) - 150 := by nlinarith
  have hsq : 0 ≤ ((a : ℚ) - 150)^2 := sq_nonneg _
  have hcube : 0 ≤ ((a : ℚ) - 150)^3 := by positivity
  have hfour : 0 ≤ ((a : ℚ) - 150)^4 := by positivity
  have hdecomp :
      25 * (a : ℚ)^4 - 3215 * (a : ℚ)^3 - 26880 * (a : ℚ)^2 -
          384480 * (a : ℚ) + 415200 =
        25 * ((a : ℚ) - 150)^4 + 11785 * ((a : ℚ) - 150)^3 +
          1901370 * ((a : ℚ) - 150)^2 + 112039020 * ((a : ℚ) - 150) +
          1143568200 := by
    ring
  rw [hdecomp]
  nlinarith

private theorem printedTailX2Bound2_poly_pos (a : Nat) (ha : 150 ≤ a) :
    0 < 25 * (a : ℚ)^4 - 2822 * (a : ℚ)^3 - 33792 * (a : ℚ)^2 -
      667776 * (a : ℚ) + 704640 := by
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hshift : 0 ≤ (a : ℚ) - 150 := by nlinarith
  have hsq : 0 ≤ ((a : ℚ) - 150)^2 := sq_nonneg _
  have hcube : 0 ≤ ((a : ℚ) - 150)^3 := by positivity
  have hfour : 0 ≤ ((a : ℚ) - 150)^4 := by positivity
  have hdecomp :
      25 * (a : ℚ)^4 - 2822 * (a : ℚ)^3 - 33792 * (a : ℚ)^2 -
          667776 * (a : ℚ) + 704640 =
        25 * ((a : ℚ) - 150)^4 + 12178 * ((a : ℚ) - 150)^3 +
          2071308 * ((a : ℚ) - 150)^2 + 136209624 * ((a : ℚ) - 150) +
          2272218240 := by
    ring
  rw [hdecomp]
  nlinarith

private theorem printedTailX2Bound3_poly_pos (a : Nat) (ha : 150 ≤ a) :
    0 < 25 * (a : ℚ)^4 - 1840 * (a : ℚ)^3 - 11520 * (a : ℚ)^2 -
      83520 * (a : ℚ) + 98880 := by
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hshift : 0 ≤ (a : ℚ) - 150 := by nlinarith
  have hsq : 0 ≤ ((a : ℚ) - 150)^2 := sq_nonneg _
  have hcube : 0 ≤ ((a : ℚ) - 150)^3 := by positivity
  have hfour : 0 ≤ ((a : ℚ) - 150)^4 := by positivity
  have hdecomp :
      25 * (a : ℚ)^4 - 1840 * (a : ℚ)^3 - 11520 * (a : ℚ)^2 -
          83520 * (a : ℚ) + 98880 =
        25 * ((a : ℚ) - 150)^4 + 13160 * ((a : ℚ) - 150)^3 +
          2535480 * ((a : ℚ) - 150)^2 + 209760480 * ((a : ℚ) - 150) +
          6174620880 := by
    ring
  rw [hdecomp]
  nlinarith

private theorem printedTailX2Bound4_poly_pos (a : Nat) (ha : 150 ≤ a) :
    0 < 25 * (a : ℚ)^4 - 2840 * (a : ℚ)^3 - 19200 * (a : ℚ)^2 -
      175200 * (a : ℚ) + 198240 := by
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hshift : 0 ≤ (a : ℚ) - 150 := by nlinarith
  have hsq : 0 ≤ ((a : ℚ) - 150)^2 := sq_nonneg _
  have hcube : 0 ≤ ((a : ℚ) - 150)^3 := by positivity
  have hfour : 0 ≤ ((a : ℚ) - 150)^4 := by positivity
  have hdecomp :
      25 * (a : ℚ)^4 - 2840 * (a : ℚ)^3 - 19200 * (a : ℚ)^2 -
          175200 * (a : ℚ) + 198240 =
        25 * ((a : ℚ) - 150)^4 + 12160 * ((a : ℚ) - 150)^3 +
          2077800 * ((a : ℚ) - 150)^2 + 139864800 * ((a : ℚ) - 150) +
          2613168240 := by
    ring
  rw [hdecomp]
  nlinarith

theorem printedTailX2Bound1_lt (a : Nat) (ha : 150 ≤ a) :
    printedTailX2Bound1 a < 26 / 5 := by
  unfold printedTailX2Bound1 printedTailMrat
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have ha_pos : (0 : ℚ) < (a : ℚ) := by nlinarith
  have hpoly := printedTailX2Bound1_poly_pos a ha
  field_simp [ha_pos.ne']
  ring_nf
  nlinarith

theorem printedTailX2Bound2_lt (a : Nat) (ha : 150 ≤ a) :
    printedTailX2Bound2 a < 11 / 2 := by
  unfold printedTailX2Bound2 printedTailMrat
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have ha_pos : (0 : ℚ) < (a : ℚ) := by nlinarith
  have hpoly := printedTailX2Bound2_poly_pos a ha
  field_simp [ha_pos.ne']
  ring_nf
  nlinarith

theorem printedTailX2Bound3_lt (a : Nat) (ha : 150 ≤ a) :
    printedTailX2Bound3 a < 81 / 20 := by
  unfold printedTailX2Bound3 printedTailMrat
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have ha_pos : (0 : ℚ) < (a : ℚ) := by nlinarith
  have hpoly := printedTailX2Bound3_poly_pos a ha
  field_simp [ha_pos.ne']
  ring_nf
  nlinarith

theorem printedTailX2Bound4_lt (a : Nat) (ha : 150 ≤ a) :
    printedTailX2Bound4 a < 41 / 10 := by
  unfold printedTailX2Bound4 printedTailMrat
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have ha_pos : (0 : ℚ) < (a : ℚ) := by nlinarith
  have hpoly := printedTailX2Bound4_poly_pos a ha
  field_simp [ha_pos.ne']
  ring_nf
  nlinarith

/-- Final rational arithmetic for the first absolute-moment budget:
`exp(7/5) < 203/50` and `exp(26/5) < 182` reduce the displayed bound below
`9`. -/
theorem printedTailAbsoluteMoment0_budget :
    (203 / 50 : ℚ) * (21 / 10) +
        (182 : ℚ) * (101 / 20) / (2 : ℚ)^13 < 9 := by
  norm_num

/-- Final rational arithmetic for the weighted absolute-moment budget,
reduced below `18`. -/
theorem printedTailAbsoluteMoment1_budget :
    (203 / 50 : ℚ) * (17 / 4) +
        (182 : ℚ) * (255 / 8) / (2 : ℚ)^13 < 18 := by
  norm_num

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
