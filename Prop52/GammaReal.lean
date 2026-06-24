/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Scalar real-exponential constants for the Prop52 Gamma margin

The Gamma-margin proof is algebraized in `Prop52.GammaMoment` up to the
finite factorial-ratio moment bound.  This file records the tiny real
exponential endpoint used after Jensen's inequality in the printed proof.
-/

import Prop52.GammaMoment
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Prop52

open Finset
open MeasureTheory Set

/-- Jensen's inequality in the exact form needed for the Gamma margin.  The
specific Gamma expectation is not hidden here: callers must still provide the
integrability assumptions and the bound on the mean of `f`. -/
theorem real_exp_neg_le_integral_exp_neg_of_integral_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ} {C : ℝ}
    (hf : Integrable f μ)
    (hexp : Integrable (fun x => Real.exp (-f x)) μ)
    (hmean : ∫ x, f x ∂ μ ≤ C) :
    Real.exp (-C) ≤ ∫ x, Real.exp (-f x) ∂ μ := by
  have hJ :
      Real.exp (∫ x, -f x ∂ μ) ≤ ∫ x, Real.exp (-f x) ∂ μ := by
    simpa [Function.comp_def] using
      (convexOn_exp.map_integral_le (s := univ) (g := Real.exp)
        (f := fun x => -f x)
        Real.continuous_exp.continuousOn isClosed_univ
        (Filter.Eventually.of_forall fun _ => mem_univ _)
        hf.neg hexp)
  have hmean_neg : -C ≤ ∫ x, -f x ∂ μ := by
    rw [integral_neg]
    linarith
  exact (Real.exp_le_exp_of_le hmean_neg).trans hJ

/-- The scalar prefactor conversion in the Gamma margin:
`(5/(6(a-2))) * (27/100) = 9/(40(a-2))`. -/
theorem gammaPrefactor_lower_of_expLower
    (a : Nat) (ha : 150 ≤ a) {Z : ℝ}
    (hZ : (27 / 100 : ℝ) ≤ Z) :
    9 / (40 * ((a : ℝ) - 2)) ≤
      (5 / (6 * ((a : ℝ) - 2))) * Z := by
  have hden : (0 : ℝ) < (a : ℝ) - 2 := by
    have haR : (150 : ℝ) ≤ a := by exact_mod_cast ha
    nlinarith
  rw [show 9 / (40 * ((a : ℝ) - 2)) =
      (5 / (6 * ((a : ℝ) - 2))) * (27 / 100 : ℝ) by
        field_simp [hden.ne']
        ring]
  exact mul_le_mul_of_nonneg_left hZ (by positivity)

/-- A three-term Taylor upper bound for `exp(3/10)`. -/
theorem real_exp_three_tenths_le :
    Real.exp (3 / 10 : ℝ) ≤ 1351 / 1000 := by
  have h := Real.exp_bound' (x := (3 / 10 : ℝ))
    (by norm_num) (by norm_num) (n := 3) (by norm_num)
  calc
    Real.exp (3 / 10 : ℝ)
        ≤ (∑ m ∈ range 3, (3 / 10 : ℝ) ^ m / (m.factorial : ℝ)) +
            (3 / 10 : ℝ) ^ 3 * (3 + 1) /
              ((Nat.factorial 3 : Nat) * 3 : ℝ) := h
    _ = 1351 / 1000 := by
      norm_num [sum_range_succ, Nat.factorial]

/-- Scalar endpoint used in the Gamma lower-tail estimate at `λ=1/2`. -/
theorem real_exp_one_half_lt_five_thirds :
    Real.exp (1 / 2 : ℝ) < 5 / 3 := by
  have h := Real.exp_bound' (x := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (n := 3) (by norm_num)
  calc
    Real.exp (1 / 2 : ℝ)
        ≤ (∑ m ∈ range 3, (1 / 2 : ℝ) ^ m / (m.factorial : ℝ)) +
            (1 / 2 : ℝ) ^ 3 * (3 + 1) /
              ((Nat.factorial 3 : Nat) * 3 : ℝ) := h
    _ = 119 / 72 := by
      norm_num [sum_range_succ, Nat.factorial]
    _ < 5 / 3 := by norm_num

/-- Scalar endpoint used in the Gamma lower-tail estimate with
`λ <= 4/7`. -/
theorem real_exp_three_sevenths_lt_sixty_three_fortieths :
    Real.exp (3 / 7 : ℝ) < 63 / 40 := by
  have h := Real.exp_bound' (x := (3 / 7 : ℝ))
    (by norm_num) (by norm_num) (n := 3) (by norm_num)
  calc
    Real.exp (3 / 7 : ℝ)
        ≤ (∑ m ∈ range 3, (3 / 7 : ℝ) ^ m / (m.factorial : ℝ)) +
            (3 / 7 : ℝ) ^ 3 * (3 + 1) /
              ((Nat.factorial 3 : Nat) * 3 : ℝ) := h
    _ = 1055 / 686 := by
      norm_num [sum_range_succ, Nat.factorial]
    _ < 63 / 40 := by norm_num

/-- Scalar endpoint for the printed `x₂` majorant:
`exp(26/5) < 182`.  We prove a weak `<=` form, which is the form needed by
the product estimate `exp(L(x₂)) (1+J(x₂)) <= 920`. -/
theorem real_exp_twenty_six_fifths_le :
    Real.exp (26 / 5 : ℝ) ≤ 182 := by
  let xR : ℝ := 26 / 5
  let xC : ℂ := (xR : ℂ)
  let S : ℝ :=
    ∑ m ∈ Finset.range 11, xR ^ m / ((m.factorial : Nat) : ℝ)
  let SC : ℂ :=
    ∑ m ∈ Finset.range 11, xC ^ m / ((m.factorial : Nat) : ℂ)
  have hx : ‖xC‖ / ((11 : Nat).succ : ℝ) ≤ 1 / 2 := by
    dsimp [xC, xR]
    norm_num [Complex.normSq, Complex.normSq_apply]
  have hC := Complex.exp_bound' (x := xC) (n := 11) hx
  have hSC : (S : ℂ) = SC := by
    dsimp [S, SC, xC]
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun m _hm => ?_
    rw [Complex.ofReal_div, Complex.ofReal_pow]
    norm_num
  have hnorm_eq : ‖Complex.exp xC - SC‖ =
      |Real.exp xR - S| := by
    rw [← hSC]
    have hcast :
        Complex.exp xC - (S : ℂ) =
          ((Real.exp xR - S : ℝ) : ℂ) := by
      simp [xC, Complex.ofReal_sub, Complex.ofReal_exp]
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  have hxnorm : ‖xC‖ = xR := by
    dsimp [xC, xR]
    norm_num [Complex.normSq, Complex.normSq_apply]
  have hC' :
      |Real.exp xR - S| ≤
        xR ^ 11 / (((11 : Nat).factorial : Nat) : ℝ) * 2 := by
    rw [← hnorm_eq]
    simpa [SC, hxnorm] using hC
  have hle :
      Real.exp xR ≤
        S + xR ^ 11 / (((11 : Nat).factorial : Nat) : ℝ) * 2 := by
    have hleft : Real.exp xR - S ≤ |Real.exp xR - S| := le_abs_self _
    have hsub :
        Real.exp xR - S ≤
          xR ^ 11 / (((11 : Nat).factorial : Nat) : ℝ) * 2 :=
      hleft.trans hC'
    linarith
  calc
    Real.exp (26 / 5 : ℝ) = Real.exp xR := rfl
    _ ≤ S + xR ^ 11 / (((11 : Nat).factorial : Nat) : ℝ) * 2 := hle
    _ ≤ 182 := by
      norm_num [S, xR, Finset.sum_range_succ, Nat.factorial]

/-- The scalar exponential endpoint used by the printed Gamma/Jensen margin. -/
theorem real_exp_thirteen_tenths_lt :
    Real.exp (13 / 10 : ℝ) < 100 / 27 := by
  have h1 : Real.exp (1 : ℝ) < 2.7182818286 := Real.exp_one_lt_d9
  have h03 := real_exp_three_tenths_le
  rw [show (13 / 10 : ℝ) = 1 + 3 / 10 by norm_num, Real.exp_add]
  have hprod :
      Real.exp (1 : ℝ) * Real.exp (3 / 10 : ℝ) <
        (2.7182818286 : ℝ) * (1351 / 1000 : ℝ) :=
    mul_lt_mul_of_pos_of_nonneg' h1 h03 (Real.exp_pos _) (by norm_num)
  exact hprod.trans (by norm_num)

/-- Equivalent lower form, exactly as used after Jensen:
`exp(-13/10) > 27/100`. -/
theorem real_exp_neg_thirteen_tenths_gt :
    (27 / 100 : ℝ) < Real.exp (-(13 / 10 : ℝ)) := by
  rw [Real.exp_neg]
  rw [lt_inv_comm₀ (by norm_num : (0 : ℝ) < 27 / 100) (Real.exp_pos _)]
  simpa using real_exp_thirteen_tenths_lt

/-- Real form of the exponential endpoint for the rational Gamma exponent
budget. -/
theorem real_exp_neg_gammaExponentBound_gt
    (a : Nat) (ha : 150 ≤ a) :
    (27 / 100 : ℝ) < Real.exp (-(gammaExponentBound a : ℝ)) := by
  have hboundQ := gammaExponentBound_lt a ha
  have hboundR : (gammaExponentBound a : ℝ) < 13 / 10 := by
    have hcast :
        ((gammaExponentBound a : ℚ) : ℝ) < ((13 / 10 : ℚ) : ℝ) :=
      (Rat.cast_lt (K := ℝ)).2 hboundQ
    simpa using hcast
  have hneg : -(13 / 10 : ℝ) < -(gammaExponentBound a : ℝ) := by
    linarith
  exact real_exp_neg_thirteen_tenths_gt.trans (Real.exp_strictMono hneg)

/-- Scalar inequality behind the truncation proof's pointwise estimate
`exp(-L) * (1 + J) <= 2` once `0 <= L` and `J <= 2L`. -/
theorem one_add_two_mul_mul_exp_neg_le_two {u : ℝ} (hu : 0 ≤ u) :
    (1 + 2 * u) * Real.exp (-u) ≤ 2 := by
  have h1 : 1 ≤ Real.exp u := Real.one_le_exp hu
  have h2 : 2 * u ≤ Real.exp u := Real.two_mul_le_exp
  have hsum : 1 + 2 * u ≤ 2 * Real.exp u := by
    nlinarith
  have hexp_neg_nonneg : 0 ≤ Real.exp (-u) := (Real.exp_pos _).le
  have hmul := mul_le_mul_of_nonneg_right hsum hexp_neg_nonneg
  calc
    (1 + 2 * u) * Real.exp (-u)
        ≤ (2 * Real.exp u) * Real.exp (-u) := hmul
    _ = 2 := by
      rw [mul_assoc, ← Real.exp_add]
      simp

/-- Jensen plus the scalar exponential endpoint, in the prefactored form used
by the printed Gamma-margin proof. -/
theorem gammaPrefactor_integral_exp_neg_lower_of_mean_le_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {a : Nat} (ha : 150 ≤ a) {f : α → ℝ}
    (hf : Integrable f μ)
    (hexp : Integrable (fun x => Real.exp (-f x)) μ)
    (hmean : ∫ x, f x ∂ μ ≤ (gammaExponentBound a : ℝ)) :
    9 / (40 * ((a : ℝ) - 2)) ≤
      (5 / (6 * ((a : ℝ) - 2))) *
        ∫ x, Real.exp (-f x) ∂ μ := by
  have hJ := real_exp_neg_le_integral_exp_neg_of_integral_le
    (μ := μ) (f := f) (C := (gammaExponentBound a : ℝ)) hf hexp hmean
  have h27 :
      (27 / 100 : ℝ) ≤ ∫ x, Real.exp (-f x) ∂ μ :=
    (real_exp_neg_gammaExponentBound_gt a ha).le.trans hJ
  exact gammaPrefactor_lower_of_expLower a ha h27

/-- Real form of the finite exponent-moment estimate. -/
theorem printedTailGammaExponentMoment_real_lt_thirteen_tenths
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    (printedTailGammaExponentMoment μ a : ℝ) < 13 / 10 := by
  have h := printedTailGammaExponentMoment_lt_thirteen_tenths
    (a := a) (μ := μ) ha hμ
  have hcast :
      ((printedTailGammaExponentMoment μ a : ℚ) : ℝ) < ((13 / 10 : ℚ) : ℝ) :=
    (Rat.cast_lt (K := ℝ)).2 h
  simpa using hcast

end Prop52
