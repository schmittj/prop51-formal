/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Differential identities for the Proposition 5.2 Gamma integration by parts

The Gamma margin uses the identity obtained by differentiating
`x^(a-1) exp(-x) exp(-L(1/(6x)))`.  This file records the local differential
and algebraic identities needed for that integration-by-parts step.
-/

import Prop52.GammaTruncation
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace Prop52

open Finset
open MeasureTheory
open Filter

/-- Real derivative polynomial of the low logarithm `L`. -/
noncomputable def printedTailLDerivReal
    (μ : List Nat) (a : Nat) (x : ℝ) : ℝ :=
  ∑ r ∈ Finset.Ico 1 (printedTailP a + 1),
    (r : ℝ) * (hCoeff μ r : ℝ) * x^(r - 1)

/-- Termwise derivative of the finite low logarithm `L`. -/
theorem hasDerivAt_printedTailLReal
    (μ : List Nat) (a : Nat) (x : ℝ) :
    HasDerivAt (fun z => printedTailLReal μ a z)
      (printedTailLDerivReal μ a x) x := by
  unfold printedTailLReal printedTailLDerivReal
  refine HasDerivAt.fun_sum fun r hr => ?_
  have hpow := hasDerivAt_pow r x
  convert hpow.const_mul (hCoeff μ r : ℝ) using 1
  ring

/-- The aligned Gamma bracket is exactly `M t + 6 t^2 L'(t) - J(t)`. -/
theorem gammaLowBracketAlignedReal_eq_deriv_form
    (μ : List Nat) {a : Nat} (ha : 150 ≤ a) (x : ℝ) :
    gammaLowBracketAlignedReal μ a x =
      (M a : ℝ) * x +
        6 * x^2 * printedTailLDerivReal μ a x -
        printedTailJReal μ a x := by
  let p : Nat := printedTailP a
  let F : Nat → ℝ := fun j =>
    6 * (j : ℝ) * (hCoeff μ j : ℝ) * x^(j + 1)
  let D : Nat → ℝ := fun j =>
    (j : ℝ) * (hCoeff μ j : ℝ) * x^(j - 1)
  let K : Nat → ℝ := fun j => (kCoeff μ j : ℝ) * x^j
  let G : Nat → ℝ := fun j => (kCoeff μ (j + 1) : ℝ) * x^(j + 1)
  have hp : 1 ≤ p := by
    dsimp [p, printedTailP]
    omega
  have hD :
      6 * x^2 * (∑ j ∈ Finset.Ico 1 (p + 1), D j) =
        ∑ j ∈ Finset.Ico 1 (p + 1), F j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjpos : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    dsimp [D, F]
    rw [show j + 1 = (j - 1) + 2 by omega, pow_add]
    ring
  have hKshift :
      (∑ j ∈ Finset.Ico 2 (p + 1), K j) =
        ∑ j ∈ Finset.Ico 1 p, G j := by
    have h := (Finset.sum_Ico_add' K 1 p 1).symm
    simpa [G, Nat.add_comm, Nat.add_assoc] using h
  have hKsplit :
      (∑ j ∈ Finset.Ico 1 (p + 1), K j) =
        K 1 + ∑ j ∈ Finset.Ico 1 p, G j := by
    have hsplit := Finset.sum_eq_sum_Ico_succ_bot
      (a := 1) (b := p + 1) (by omega : 1 < p + 1) K
    rw [hsplit, hKshift]
  unfold gammaLowBracketAlignedReal printedTailLDerivReal printedTailJReal
  change
    (((M a : ℝ) - (kCoeff μ 1 : ℝ)) * x +
        (∑ j ∈ Finset.Ico 1 (p + 1), F j) -
        ∑ j ∈ Finset.Ico 1 p, G j) =
      (M a : ℝ) * x +
        6 * x^2 * (∑ j ∈ Finset.Ico 1 (p + 1), D j) -
        ∑ j ∈ Finset.Ico 1 (p + 1), K j
  rw [hD, hKsplit]
  dsimp [K]
  ring

/-- Derivative of the Gamma substitution argument `L(1/(6x))` away from
`x=0`. -/
theorem hasDerivAt_printedTailLGammaArg
    (μ : List Nat) (a : Nat) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun z => printedTailLGammaArg μ a z)
      (-(printedTailLDerivReal μ a (1 / (6 * x))) / (6 * x^2)) x := by
  unfold printedTailLGammaArg
  have ht :
      HasDerivAt (fun z : ℝ => 1 / (6 * z))
        (-(1 : ℝ) / (6 * x^2)) x := by
    have hlin : HasDerivAt (fun z : ℝ => 6 * z) 6 x := by
      simpa using (hasDerivAt_id x).const_mul (6 : ℝ)
    have hlin_ne : 6 * x ≠ 0 := by
      exact mul_ne_zero (by norm_num) hx
    convert hlin.inv hlin_ne using 1
    · ext z
      change 1 / (6 * z) = (6 * z)⁻¹
      by_cases hz : z = 0
      · simp [hz]
      · field_simp [hz]
    · field_simp [hx]
  have hL := hasDerivAt_printedTailLReal μ a (1 / (6 * x))
  have hcomp := hL.comp x ht
  convert hcomp using 1
  field_simp [hx]

/-- Envelope whose derivative is integrated in the Gamma integration by
parts argument. -/
noncomputable def gammaIBPEnvelope
    (μ : List Nat) (a : Nat) (x : ℝ) : ℝ :=
  x^(a - 1) * Real.exp (-x) *
    Real.exp (-(printedTailLGammaArg μ a x))

/-- Raw product/chain-rule derivative of the Gamma integration-by-parts
envelope.  The following algebraic simplification is intentionally kept
separate from this local differentiability fact. -/
theorem hasDerivAt_gammaIBPEnvelope_raw
    (μ : List Nat) (a : Nat) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun z => gammaIBPEnvelope μ a z)
      ((((a - 1 : Nat) : ℝ) * x^(a - 1 - 1) * Real.exp (-x) +
          x^(a - 1) * (-Real.exp (-x))) *
          Real.exp (-(printedTailLGammaArg μ a x)) +
        (x^(a - 1) * Real.exp (-x)) *
          (Real.exp (-(printedTailLGammaArg μ a x)) *
            (printedTailLDerivReal μ a (1 / (6 * x)) / (6 * x^2)))) x := by
  unfold gammaIBPEnvelope
  have hpow : HasDerivAt (fun z : ℝ => z^(a - 1))
      (((a - 1 : Nat) : ℝ) * x^(a - 1 - 1)) x :=
    hasDerivAt_pow (a - 1) x
  have hexp_neg :
      HasDerivAt (fun z : ℝ => Real.exp (-z)) (-Real.exp (-x)) x := by
    have hneg : HasDerivAt (fun z : ℝ => -z) (-1) x :=
      (hasDerivAt_id x).neg
    convert hneg.exp using 1
    ring
  have hLG := hasDerivAt_printedTailLGammaArg μ a hx
  have hexp_L :
      HasDerivAt (fun z : ℝ => Real.exp (-(printedTailLGammaArg μ a z)))
        (Real.exp (-(printedTailLGammaArg μ a x)) *
          (printedTailLDerivReal μ a (1 / (6 * x)) / (6 * x^2))) x := by
    have hneg := hLG.neg
    convert hneg.exp using 1
    simp only [Pi.neg_apply]
    ring
  have hleft := hpow.mul hexp_neg
  have hall := hleft.mul hexp_L
  convert hall using 1

/-- Logarithmic-derivative form of the Gamma integration-by-parts envelope
derivative. -/
theorem hasDerivAt_gammaIBPEnvelope
    (μ : List Nat) {a : Nat} (ha : 150 ≤ a) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun z => gammaIBPEnvelope μ a z)
      (gammaIBPEnvelope μ a x *
        (((a - 1 : Nat) : ℝ) / x - 1 +
          printedTailLDerivReal μ a (1 / (6 * x)) / (6 * x^2))) x := by
  have hraw := hasDerivAt_gammaIBPEnvelope_raw μ a hx
  convert hraw using 1
  unfold gammaIBPEnvelope
  have hpow :
      x^(a - 1) = x^(a - 1 - 1) * x := by
    calc
      x^(a - 1) = x^((a - 1 - 1) + 1) := by
        exact congrArg (fun n : Nat => x^n)
          (by omega : a - 1 = (a - 1 - 1) + 1)
      _ = x^(a - 1 - 1) * x := by
        exact pow_succ x (a - 1 - 1)
  rw [hpow]
  field_simp [hx]
  ring

/-- Algebraic identification of the logarithmic derivative with the bracket
appearing in the Gamma integration-by-parts identity. -/
theorem gammaIBP_logDeriv_eq_bracket_add_J_sub_one
    (μ : List Nat) {a : Nat} (ha : 150 ≤ a) {x : ℝ} (hx : x ≠ 0) :
    (((a - 1 : Nat) : ℝ) / x - 1 +
        printedTailLDerivReal μ a (1 / (6 * x)) / (6 * x^2)) =
      gammaLowBracketAlignedReal μ a (1 / (6 * x)) +
        printedTailJReal μ a (1 / (6 * x)) - 1 := by
  have hbr := gammaLowBracketAlignedReal_eq_deriv_form
    (μ := μ) (a := a) ha (x := 1 / (6 * x))
  rw [hbr]
  unfold M
  rw [Nat.cast_sub (by omega : 6 ≤ 6 * a)]
  push_cast
  rw [Nat.cast_sub (by omega : 1 ≤ a)]
  field_simp [hx]
  ring_nf

/-- Bracket form of the Gamma integration-by-parts envelope derivative. -/
theorem hasDerivAt_gammaIBPEnvelope_bracket
    (μ : List Nat) {a : Nat} (ha : 150 ≤ a) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun z => gammaIBPEnvelope μ a z)
      (gammaIBPEnvelope μ a x *
        (gammaLowBracketAlignedReal μ a (1 / (6 * x)) +
          printedTailJReal μ a (1 / (6 * x)) - 1)) x := by
  have h := hasDerivAt_gammaIBPEnvelope μ ha hx
  convert h using 1
  rw [gammaIBP_logDeriv_eq_bracket_add_J_sub_one
    (μ := μ) (a := a) ha hx]

/-- Density form of the Gamma integration-by-parts envelope on the support of
the Gamma law. -/
theorem gammaPDF_toReal_mul_exp_neg_L_eq_invGamma_mul_envelope
    (μ : List Nat) {a : Nat} (ha : 150 ≤ a) {x : ℝ} (hx : 0 ≤ x) :
    (ProbabilityTheory.gammaPDF (a : ℝ) 1 x).toReal *
        Real.exp (-(printedTailLGammaArg μ a x)) =
      (Real.Gamma (a : ℝ))⁻¹ * gammaIBPEnvelope μ a x := by
  rw [ProbabilityTheory.gammaPDF_of_nonneg hx]
  rw [ENNReal.toReal_ofReal]
  · simp only [Real.one_rpow, one_mul]
    unfold gammaIBPEnvelope
    have hshape : (a : ℝ) - 1 = ((a - 1 : Nat) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ a)]
      ring
    rw [hshape]
    rw [Real.rpow_natCast]
    ring
  · positivity

noncomputable def gammaIBPBracketIntegrand
    (μ : List Nat) (a : Nat) (x : ℝ) : ℝ :=
  gammaIBPEnvelope μ a x *
    gammaLowBracketAlignedReal μ a (1 / (6 * x))

noncomputable def gammaIBPWIntegrand
    (μ : List Nat) (a : Nat) (x : ℝ) : ℝ :=
  gammaIBPEnvelope μ a x *
    (1 - printedTailJReal μ a (1 / (6 * x)))

noncomputable def gammaIBPDerivativeIntegrand
    (μ : List Nat) (a : Nat) (x : ℝ) : ℝ :=
  gammaIBPEnvelope μ a x *
    (gammaLowBracketAlignedReal μ a (1 / (6 * x)) +
      printedTailJReal μ a (1 / (6 * x)) - 1)

theorem gammaIBPDerivativeIntegrand_eq_bracket_sub_W
    (μ : List Nat) (a : Nat) (x : ℝ) :
    gammaIBPDerivativeIntegrand μ a x =
      gammaIBPBracketIntegrand μ a x - gammaIBPWIntegrand μ a x := by
  unfold gammaIBPDerivativeIntegrand gammaIBPBracketIntegrand
    gammaIBPWIntegrand
  ring

/-- Conditional integral form of the Gamma integration-by-parts identity.

The remaining analytic endpoint work is exactly the proof that the derivative
integral on `(0,∞)` vanishes, together with the two integrability facts. -/
theorem gammaIBP_integral_W_eq_bracket_of_derivative_integral_zero
    (μ : List Nat) (a : Nat)
    (hzero :
      (∫ x in Set.Ioi (0 : ℝ),
        gammaIBPDerivativeIntegrand μ a x) = 0)
    (hbracket :
      IntegrableOn (gammaIBPBracketIntegrand μ a) (Set.Ioi (0 : ℝ)))
    (hW :
      IntegrableOn (gammaIBPWIntegrand μ a) (Set.Ioi (0 : ℝ))) :
    (∫ x in Set.Ioi (0 : ℝ), gammaIBPWIntegrand μ a x) =
      ∫ x in Set.Ioi (0 : ℝ), gammaIBPBracketIntegrand μ a x := by
  have hderiv_sub :
      (∫ x in Set.Ioi (0 : ℝ),
        gammaIBPDerivativeIntegrand μ a x) =
      ∫ x in Set.Ioi (0 : ℝ),
        (gammaIBPBracketIntegrand μ a x - gammaIBPWIntegrand μ a x) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x _hx => ?_
    exact gammaIBPDerivativeIntegrand_eq_bracket_sub_W μ a x
  have hsub :
      (∫ x in Set.Ioi (0 : ℝ),
        (gammaIBPBracketIntegrand μ a x - gammaIBPWIntegrand μ a x)) =
        (∫ x in Set.Ioi (0 : ℝ), gammaIBPBracketIntegrand μ a x) -
          ∫ x in Set.Ioi (0 : ℝ), gammaIBPWIntegrand μ a x := by
    exact MeasureTheory.integral_sub hbracket hW
  rw [hderiv_sub, hsub] at hzero
  linarith

/-- The derivative integral vanishes once the two endpoint conditions for the
Gamma integration-by-parts envelope have been discharged.  This packages the
standard improper FTC step and leaves only the analytic endpoint estimates as
explicit hypotheses. -/
theorem gammaIBP_derivative_integral_zero_of_tendsto
    (μ : List Nat) {a : Nat} (ha : 150 ≤ a)
    (hcont :
      ContinuousWithinAt (gammaIBPEnvelope μ a) (Set.Ici (0 : ℝ)) 0)
    (hderivInt :
      IntegrableOn (gammaIBPDerivativeIntegrand μ a) (Set.Ioi (0 : ℝ)))
    (htop : Tendsto (gammaIBPEnvelope μ a) atTop (nhds 0)) :
    (∫ x in Set.Ioi (0 : ℝ),
      gammaIBPDerivativeIntegrand μ a x) = 0 := by
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z => gammaIBPEnvelope μ a z)
        (gammaIBPDerivativeIntegrand μ a x) x := by
    intro x hx
    unfold gammaIBPDerivativeIntegrand
    exact hasDerivAt_gammaIBPEnvelope_bracket μ ha
      (ne_of_gt (Set.mem_Ioi.mp hx))
  have hFTC := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (a := (0 : ℝ)) (f := fun x => gammaIBPEnvelope μ a x)
    (f' := gammaIBPDerivativeIntegrand μ a) (m := 0)
    hcont hderiv hderivInt htop
  have hzero : gammaIBPEnvelope μ a 0 = 0 := by
    unfold gammaIBPEnvelope
    have hpow : (0 : ℝ)^(a - 1) = 0 := by
      exact zero_pow (by omega : a - 1 ≠ 0)
    simp [hpow]
  simpa [hzero] using hFTC

end Prop52
