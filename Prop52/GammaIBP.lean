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

/-- The scalar Gamma density core `x^(a-1) exp(-x)` is integrable on
`(0,∞)` for the integer shapes used here. -/
private theorem integrableOn_gammaIBP_core
    {a : Nat} (ha : 150 ≤ a) :
    IntegrableOn (fun x : ℝ => x^(a - 1) * Real.exp (-x))
      (Set.Ioi (0 : ℝ)) := by
  have hgamma := Real.GammaIntegral_convergent
    (s := (a : ℝ)) (by exact_mod_cast (by omega : 0 < a))
  refine hgamma.congr_fun ?_ measurableSet_Ioi
  intro x hx
  have hshape : (a : ℝ) - 1 = ((a - 1 : Nat) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ a)]
    ring
  simp [hshape, mul_comm]

/-- Gamma-density core with one of the inverse-power factors appearing in the
bracket polynomial. -/
private theorem integrableOn_gammaIBP_core_invPow
    {a r : Nat} (ha : 150 ≤ a) (hr : r ≤ printedTailP a + 1) :
    IntegrableOn
      (fun x : ℝ => x^(a - 1) * Real.exp (-x) * (1 / (6 * x))^r)
      (Set.Ioi (0 : ℝ)) := by
  have hrle : r ≤ a - 1 := by
    unfold printedTailP at hr
    omega
  have hshape_pos : (0 : ℝ) < (a - r : Nat) := by
    exact_mod_cast (by omega : 0 < a - r)
  have hgamma := Real.GammaIntegral_convergent
    (s := ((a - r : Nat) : ℝ)) hshape_pos
  have hconst :
      IntegrableOn
        (fun x : ℝ =>
          (1 / (6 : ℝ)^r) *
            (Real.exp (-x) * x^(((a - r : Nat) : ℝ) - 1)))
        (Set.Ioi (0 : ℝ)) :=
    hgamma.const_mul (1 / (6 : ℝ)^r)
  refine hconst.congr_fun ?_ measurableSet_Ioi
  intro x hx
  have hxpos : 0 < x := Set.mem_Ioi.mp hx
  have hxne : x ≠ 0 := hxpos.ne'
  have hshape :
      ((a - r : Nat) : ℝ) - 1 = ((a - 1 - r : Nat) : ℝ) := by
    rw [← Nat.cast_one, ← Nat.cast_sub (by omega : 1 ≤ a - r)]
    congr 1
    omega
  rw [hshape]
  change
    (1 / (6 : ℝ)^r) *
        (Real.exp (-x) * x^(((a - 1 - r : Nat) : ℝ))) =
      x^(a - 1) * Real.exp (-x) * (1 / (6 * x))^r
  rw [Real.rpow_natCast]
  have hpow :
      x^(a - 1) = x^(a - 1 - r) * x^r := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow]
  field_simp [hxne, pow_ne_zero r (by norm_num : (6 : ℝ) ≠ 0)]
  rw [← mul_pow (6 : ℝ) x r]
  rw [← mul_pow (6 * x) (1 / (x * 6)) r]
  have hunit : (6 * x) * (1 / (x * 6)) = (1 : ℝ) := by
    field_simp [hxne]
  rw [hunit, one_pow]

/-- The inverse-power Gamma core remains integrable after multiplication by
`exp(-L(1/(6x)))`, since `L >= 0` on the positive ray. -/
private theorem integrableOn_gammaIBP_core_invPow_expNegL
    {a r : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a))
    (hr : r ≤ printedTailP a + 1) :
    IntegrableOn
      (fun x : ℝ =>
        x^(a - 1) * Real.exp (-x) *
          Real.exp (-(printedTailLGammaArg μ a x)) *
            (1 / (6 * x))^r)
      (Set.Ioi (0 : ℝ)) := by
  change Integrable
    (fun x : ℝ =>
      x^(a - 1) * Real.exp (-x) *
        Real.exp (-(printedTailLGammaArg μ a x)) *
          (1 / (6 * x))^r)
    (volume.restrict (Set.Ioi (0 : ℝ)))
  have hbase :
      Integrable
        (fun x : ℝ => x^(a - 1) * Real.exp (-x) * (1 / (6 * x))^r)
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (integrableOn_gammaIBP_core_invPow (a := a) (r := r) ha hr)
  refine hbase.mono' ?hmeas ?hbound
  · unfold printedTailLGammaArg printedTailLReal
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : 0 < x := Set.mem_Ioi.mp hx
    have hxnonneg : 0 ≤ x := hxpos.le
    have ht_nonneg : 0 ≤ 1 / (6 * x) := by positivity
    have hexp_le := real_exp_neg_printedTailLReal_le_one
      (a := a) (μ := μ) hμ ht_nonneg
    have hcore_nonneg :
        0 ≤ x^(a - 1) * Real.exp (-x) :=
      mul_nonneg (pow_nonneg hxnonneg _) (Real.exp_pos _).le
    have ht_pow_nonneg : 0 ≤ (1 / (6 * x))^r :=
      pow_nonneg ht_nonneg r
    have hbase_nonneg :
        0 ≤ x^(a - 1) * Real.exp (-x) * (1 / (6 * x))^r :=
      mul_nonneg hcore_nonneg ht_pow_nonneg
    calc
      |x^(a - 1) * Real.exp (-x) *
          Real.exp (-(printedTailLGammaArg μ a x)) *
            (1 / (6 * x))^r|
          =
        (x^(a - 1) * Real.exp (-x) * (1 / (6 * x))^r) *
          Real.exp (-(printedTailLGammaArg μ a x)) := by
            rw [abs_of_nonneg]
            · ring
            · positivity
      _ ≤ x^(a - 1) * Real.exp (-x) * (1 / (6 * x))^r :=
          mul_le_of_le_one_right hbase_nonneg
            (by simpa [printedTailLGammaArg] using hexp_le)

/-- The `W=exp(-L)(1-J)` side of the integration-by-parts identity is
Lebesgue-integrable on `(0,∞)`.  This uses the pointwise bound `|W| <= 2`
from the Gamma-measure file and domination by the Gamma density core. -/
theorem integrableOn_gammaIBPWIntegrand
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    IntegrableOn (gammaIBPWIntegrand μ a) (Set.Ioi (0 : ℝ)) := by
  change Integrable (gammaIBPWIntegrand μ a)
    (volume.restrict (Set.Ioi (0 : ℝ)))
  have hbase :
      Integrable (fun x : ℝ => x^(a - 1) * Real.exp (-x))
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (integrableOn_gammaIBP_core (a := a) ha)
  refine (hbase.const_mul (2 : ℝ)).mono' ?hmeas ?hbound
  · unfold gammaIBPWIntegrand gammaIBPEnvelope printedTailLGammaArg
      printedTailLReal printedTailJReal
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : 0 < x := Set.mem_Ioi.mp hx
    have hxnonneg : 0 ≤ x := hxpos.le
    have ht_nonneg : 0 ≤ 1 / (6 * x) := by positivity
    have hW := abs_exp_neg_L_mul_one_sub_JReal_le_two
      (a := a) (μ := μ) hμ ht_nonneg
    have hW' :
        |Real.exp (-(printedTailLGammaArg μ a x)) *
            (1 - printedTailJReal μ a (1 / (6 * x)))| ≤ 2 := by
      simpa [printedTailLGammaArg] using hW
    have hcore_nonneg :
        0 ≤ x^(a - 1) * Real.exp (-x) :=
      mul_nonneg (pow_nonneg hxnonneg _) (Real.exp_pos _).le
    unfold gammaIBPWIntegrand gammaIBPEnvelope
    calc
      |x^(a - 1) * Real.exp (-x) *
          Real.exp (-(printedTailLGammaArg μ a x)) *
            (1 - printedTailJReal μ a (1 / (6 * x)))|
          =
        (x^(a - 1) * Real.exp (-x)) *
          |Real.exp (-(printedTailLGammaArg μ a x)) *
            (1 - printedTailJReal μ a (1 / (6 * x)))| := by
            rw [show
              x^(a - 1) * Real.exp (-x) *
                    Real.exp (-(printedTailLGammaArg μ a x)) *
                  (1 - printedTailJReal μ a (1 / (6 * x))) =
                (x^(a - 1) * Real.exp (-x)) *
                  (Real.exp (-(printedTailLGammaArg μ a x)) *
                    (1 - printedTailJReal μ a (1 / (6 * x)))) by ring]
            rw [abs_mul, abs_of_nonneg hcore_nonneg]
      _ ≤ (x^(a - 1) * Real.exp (-x)) * 2 :=
            mul_le_mul_of_nonneg_left hW' hcore_nonneg
      _ = 2 * (x^(a - 1) * Real.exp (-x)) := by ring

/-- The bracket side of the integration-by-parts identity is
Lebesgue-integrable on `(0,∞)`. -/
theorem integrableOn_gammaIBPBracketIntegrand
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    IntegrableOn (gammaIBPBracketIntegrand μ a) (Set.Ioi (0 : ℝ)) := by
  let G : ℝ → ℝ := fun x =>
    x^(a - 1) * Real.exp (-x) *
      Real.exp (-(printedTailLGammaArg μ a x))
  have hlin :
      IntegrableOn
        (fun x : ℝ =>
          G x * (((M a : ℝ) - (kCoeff μ 1 : ℝ)) * (1 / (6 * x))))
        (Set.Ioi (0 : ℝ)) := by
    have hbase := integrableOn_gammaIBP_core_invPow_expNegL
      (a := a) (r := 1) (μ := μ) ha hμ (by
        unfold printedTailP
        omega)
    simpa [G, pow_one, mul_assoc, mul_comm, mul_left_comm] using
      hbase.const_mul ((M a : ℝ) - (kCoeff μ 1 : ℝ))
  have hsumF :
      IntegrableOn
        (fun x : ℝ =>
          G x *
            (∑ j ∈ Finset.Ico 1 (printedTailP a + 1),
              6 * (j : ℝ) * (hCoeff μ j : ℝ) *
                (1 / (6 * x))^(j + 1)))
        (Set.Ioi (0 : ℝ)) := by
    have hsum :
        IntegrableOn
          (fun x : ℝ =>
            ∑ j ∈ Finset.Ico 1 (printedTailP a + 1),
              G x * (6 * (j : ℝ) * (hCoeff μ j : ℝ) *
                (1 / (6 * x))^(j + 1)))
          (Set.Ioi (0 : ℝ)) := by
      change Integrable
        (fun x : ℝ =>
          ∑ j ∈ Finset.Ico 1 (printedTailP a + 1),
            G x * (6 * (j : ℝ) * (hCoeff μ j : ℝ) *
              (1 / (6 * x))^(j + 1)))
        (volume.restrict (Set.Ioi (0 : ℝ)))
      refine MeasureTheory.integrable_finset_sum _ ?_
      intro j hj
      have hr : j + 1 ≤ printedTailP a + 1 := (Finset.mem_Ico.mp hj).2
      have hbase := integrableOn_gammaIBP_core_invPow_expNegL
        (a := a) (r := j + 1) (μ := μ) ha hμ hr
      simpa [G, mul_assoc, mul_comm, mul_left_comm] using
        hbase.const_mul (6 * (j : ℝ) * (hCoeff μ j : ℝ))
    simpa [Finset.mul_sum, G, mul_assoc, mul_comm, mul_left_comm] using hsum
  have hsumG :
      IntegrableOn
        (fun x : ℝ =>
          G x *
            (∑ j ∈ Finset.Ico 1 (printedTailP a),
              (kCoeff μ (j + 1) : ℝ) * (1 / (6 * x))^(j + 1)))
        (Set.Ioi (0 : ℝ)) := by
    have hsum :
        IntegrableOn
          (fun x : ℝ =>
            ∑ j ∈ Finset.Ico 1 (printedTailP a),
              G x * ((kCoeff μ (j + 1) : ℝ) *
                (1 / (6 * x))^(j + 1)))
          (Set.Ioi (0 : ℝ)) := by
      change Integrable
        (fun x : ℝ =>
          ∑ j ∈ Finset.Ico 1 (printedTailP a),
            G x * ((kCoeff μ (j + 1) : ℝ) *
              (1 / (6 * x))^(j + 1)))
        (volume.restrict (Set.Ioi (0 : ℝ)))
      refine MeasureTheory.integrable_finset_sum _ ?_
      intro j hj
      have hr : j + 1 ≤ printedTailP a + 1 := by
        have hjlt : j < printedTailP a := (Finset.mem_Ico.mp hj).2
        omega
      have hbase := integrableOn_gammaIBP_core_invPow_expNegL
        (a := a) (r := j + 1) (μ := μ) ha hμ hr
      simpa [G, mul_assoc, mul_comm, mul_left_comm] using
        hbase.const_mul (kCoeff μ (j + 1) : ℝ)
    simpa [Finset.mul_sum, G, mul_assoc, mul_comm, mul_left_comm] using hsum
  unfold gammaIBPBracketIntegrand gammaIBPEnvelope gammaLowBracketAlignedReal
  change IntegrableOn
    (fun x : ℝ =>
      G x *
        ((((M a : ℝ) - (kCoeff μ 1 : ℝ)) * (1 / (6 * x)) +
          (∑ j ∈ Finset.Ico 1 (printedTailP a + 1),
            6 * (j : ℝ) * (hCoeff μ j : ℝ) *
              (1 / (6 * x))^(j + 1))) -
          ∑ j ∈ Finset.Ico 1 (printedTailP a),
            (kCoeff μ (j + 1) : ℝ) *
              (1 / (6 * x))^(j + 1)))
      (Set.Ioi (0 : ℝ))
  simpa [mul_add, mul_sub, Finset.mul_sum, mul_assoc, mul_comm,
    mul_left_comm] using (hlin.add hsumF).sub hsumG

theorem gammaIBPDerivativeIntegrand_eq_bracket_sub_W
    (μ : List Nat) (a : Nat) (x : ℝ) :
    gammaIBPDerivativeIntegrand μ a x =
      gammaIBPBracketIntegrand μ a x - gammaIBPWIntegrand μ a x := by
  unfold gammaIBPDerivativeIntegrand gammaIBPBracketIntegrand
    gammaIBPWIntegrand
  ring

/-- The derivative integrand is integrable once the two sides of the
integration-by-parts identity are integrable. -/
theorem integrableOn_gammaIBPDerivativeIntegrand
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    IntegrableOn (gammaIBPDerivativeIntegrand μ a) (Set.Ioi (0 : ℝ)) := by
  have hsub :
      IntegrableOn
        (fun x : ℝ =>
          gammaIBPBracketIntegrand μ a x - gammaIBPWIntegrand μ a x)
        (Set.Ioi (0 : ℝ)) :=
    (integrableOn_gammaIBPBracketIntegrand (a := a) (μ := μ) ha hμ).sub
      (integrableOn_gammaIBPWIntegrand (a := a) (μ := μ) ha hμ)
  refine hsub.congr_fun ?_ measurableSet_Ioi
  intro x _hx
  exact (gammaIBPDerivativeIntegrand_eq_bracket_sub_W μ a x).symm

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

/-- The Gamma-substitution low logarithm tends to zero at infinity, since it
is a finite sum of positive inverse powers of `x`. -/
theorem tendsto_printedTailLGammaArg_atTop_zero
    (μ : List Nat) (a : Nat) :
    Tendsto (printedTailLGammaArg μ a) atTop (nhds 0) := by
  unfold printedTailLGammaArg printedTailLReal
  have hbase : Tendsto (fun y : ℝ => 1 / (6 * y)) atTop (nhds 0) := by
    have hy : Tendsto (fun y : ℝ => y⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero
    simpa [div_eq_mul_inv, Ring.mul_inverse_rev] using
      hy.mul (tendsto_const_nhds (x := (6 : ℝ)⁻¹))
  have hsum :
      Tendsto
        (fun y : ℝ =>
          ∑ r ∈ Finset.Ico 1 (printedTailP a + 1),
            (hCoeff μ r : ℝ) * (1 / (6 * y))^r)
        atTop
        (nhds
          (∑ r ∈ Finset.Ico 1 (printedTailP a + 1), (0 : ℝ))) := by
    refine tendsto_finset_sum _ fun r hr => ?_
    have hrpos : r ≠ 0 := by
      have hle : 1 ≤ r := (Finset.mem_Ico.mp hr).1
      omega
    have hpow : Tendsto (fun y : ℝ => (1 / (6 * y))^r) atTop (nhds 0) := by
      simpa [zero_pow hrpos] using hbase.pow r
    simpa using hpow.const_mul (hCoeff μ r : ℝ)
  simpa using hsum

/-- The Gamma integration-by-parts envelope vanishes at infinity. -/
theorem tendsto_gammaIBPEnvelope_atTop_zero
    (μ : List Nat) (a : Nat) :
    Tendsto (gammaIBPEnvelope μ a) atTop (nhds 0) := by
  have hpoly_exp :
      Tendsto (fun x : ℝ => x^(a - 1) * Real.exp (-x))
        atTop (nhds 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (a - 1)
  have hL := tendsto_printedTailLGammaArg_atTop_zero μ a
  have hexpL :
      Tendsto (fun x : ℝ => Real.exp (-(printedTailLGammaArg μ a x)))
        atTop (nhds 1) := by
    have hneg : Tendsto (fun x : ℝ => -(printedTailLGammaArg μ a x))
        atTop (nhds 0) := by
      simpa using hL.neg
    simpa using (Real.continuous_exp.tendsto 0).comp hneg
  unfold gammaIBPEnvelope
  simpa using hpoly_exp.mul hexpL

/-- The Gamma integration-by-parts envelope is continuous from the right at
the origin.  This is the only singular endpoint: on the positive ray the
extra factor `exp(-L(1/(6x)))` is bounded by `1`, so the envelope is squeezed
by `x^(a-1) exp(-x)`, which vanishes at `0` for `a >= 150`. -/
theorem continuousWithinAt_gammaIBPEnvelope_zero
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    ContinuousWithinAt (gammaIBPEnvelope μ a) (Set.Ici (0 : ℝ)) 0 := by
  have hzero : gammaIBPEnvelope μ a 0 = 0 := by
    unfold gammaIBPEnvelope
    have hpow : (0 : ℝ)^(a - 1) = 0 := by
      exact zero_pow (by omega : a - 1 ≠ 0)
    simp [hpow]
  rw [ContinuousWithinAt, hzero]
  have hcore_tendsto :
      Tendsto (fun x : ℝ => x^(a - 1) * Real.exp (-x))
        (nhdsWithin (0 : ℝ) (Set.Ici (0 : ℝ))) (nhds 0) := by
    have hcont :
        ContinuousWithinAt
          (fun x : ℝ => x^(a - 1) * Real.exp (-x))
          (Set.Ici (0 : ℝ)) 0 := by
      fun_prop
    have hpow : (0 : ℝ)^(a - 1) = 0 := by
      exact zero_pow (by omega : a - 1 ≠ 0)
    simpa [ContinuousWithinAt, hpow] using hcont
  refine squeeze_zero' ?hnonneg ?hbound hcore_tendsto
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hxnonneg : 0 ≤ x := hx
    unfold gammaIBPEnvelope
    positivity
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hxnonneg : 0 ≤ x := hx
    have ht_nonneg : 0 ≤ 1 / (6 * x) :=
      div_nonneg zero_le_one (mul_nonneg (by norm_num) hxnonneg)
    have hexp_le := real_exp_neg_printedTailLReal_le_one
      (a := a) (μ := μ) hμ ht_nonneg
    have hcore_nonneg :
        0 ≤ x^(a - 1) * Real.exp (-x) :=
      mul_nonneg (pow_nonneg hxnonneg _) (Real.exp_pos _).le
    unfold gammaIBPEnvelope
    exact mul_le_of_le_one_right hcore_nonneg
      (by simpa [printedTailLGammaArg] using hexp_le)

/-- The derivative integral vanishes after the infinity endpoint has been
closed; the remaining hypotheses are the origin continuity and derivative
integrability required by the improper FTC. -/
theorem gammaIBP_derivative_integral_zero_of_origin
    (μ : List Nat) {a : Nat} (ha : 150 ≤ a)
    (hcont :
      ContinuousWithinAt (gammaIBPEnvelope μ a) (Set.Ici (0 : ℝ)) 0)
    (hderivInt :
      IntegrableOn (gammaIBPDerivativeIntegrand μ a) (Set.Ioi (0 : ℝ))) :
    (∫ x in Set.Ioi (0 : ℝ),
      gammaIBPDerivativeIntegrand μ a x) = 0 := by
  exact gammaIBP_derivative_integral_zero_of_tendsto
    μ ha hcont hderivInt (tendsto_gammaIBPEnvelope_atTop_zero μ a)

/-- Endpoint-and-integrability packaged version of the Gamma
integration-by-parts identity. -/
theorem gammaIBP_integral_W_eq_bracket_of_endpoints
    (μ : List Nat) {a : Nat} (ha : 150 ≤ a)
    (hcont :
      ContinuousWithinAt (gammaIBPEnvelope μ a) (Set.Ici (0 : ℝ)) 0)
    (hderivInt :
      IntegrableOn (gammaIBPDerivativeIntegrand μ a) (Set.Ioi (0 : ℝ)))
    (hbracket :
      IntegrableOn (gammaIBPBracketIntegrand μ a) (Set.Ioi (0 : ℝ)))
    (hW :
      IntegrableOn (gammaIBPWIntegrand μ a) (Set.Ioi (0 : ℝ))) :
    (∫ x in Set.Ioi (0 : ℝ), gammaIBPWIntegrand μ a x) =
      ∫ x in Set.Ioi (0 : ℝ), gammaIBPBracketIntegrand μ a x := by
  exact gammaIBP_integral_W_eq_bracket_of_derivative_integral_zero
    μ a
    (gammaIBP_derivative_integral_zero_of_origin
      μ ha hcont hderivInt)
    hbracket hW

/-- Closed integration-by-parts identity with only the origin-continuity
condition left explicit.  The infinity endpoint and integrability conditions
are discharged above. -/
theorem gammaIBP_integral_W_eq_bracket_of_origin
    (μ : List Nat) {a : Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a))
    (hcont :
      ContinuousWithinAt (gammaIBPEnvelope μ a) (Set.Ici (0 : ℝ)) 0) :
    (∫ x in Set.Ioi (0 : ℝ), gammaIBPWIntegrand μ a x) =
      ∫ x in Set.Ioi (0 : ℝ), gammaIBPBracketIntegrand μ a x := by
  exact gammaIBP_integral_W_eq_bracket_of_derivative_integral_zero
    μ a
    (gammaIBP_derivative_integral_zero_of_origin
      μ ha hcont (integrableOn_gammaIBPDerivativeIntegrand
        (a := a) (μ := μ) ha hμ))
    (integrableOn_gammaIBPBracketIntegrand (a := a) (μ := μ) ha hμ)
    (integrableOn_gammaIBPWIntegrand (a := a) (μ := μ) ha hμ)

/-- Closed Gamma integration-by-parts identity. -/
theorem gammaIBP_integral_W_eq_bracket
    (μ : List Nat) {a : Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    (∫ x in Set.Ioi (0 : ℝ), gammaIBPWIntegrand μ a x) =
      ∫ x in Set.Ioi (0 : ℝ), gammaIBPBracketIntegrand μ a x := by
  exact gammaIBP_integral_W_eq_bracket_of_origin μ ha hμ
    (continuousWithinAt_gammaIBPEnvelope_zero (a := a) (μ := μ) ha hμ)

/-- Convert the bracket Gamma expectation to the Lebesgue envelope integral
used by the integration-by-parts identity. -/
theorem gammaFull_bracketIntegral_eq_invGamma_mul_IBPBracketIntegral
    (μ : List Nat) {a : Nat} (ha : 150 ≤ a) :
    (∫ y, Real.exp (-(printedTailLGammaArg μ a y)) *
        gammaLowBracketAlignedReal μ a (1 / (6 * y)) ∂ gammaFullMeasure a) =
      (Real.Gamma (a : ℝ))⁻¹ *
        ∫ y in Set.Ioi (0 : ℝ), gammaIBPBracketIntegrand μ a y := by
  rw [integral_gammaFullMeasure_eq_integral_Ici_gammaPDF_toReal_smul]
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy_nonneg : 0 ≤ y := le_of_lt (Set.mem_Ioi.mp hy)
  have hpdf := gammaPDF_toReal_mul_exp_neg_L_eq_invGamma_mul_envelope
    (μ := μ) (a := a) ha (x := y) hy_nonneg
  simp only [smul_eq_mul]
  unfold gammaIBPBracketIntegrand
  calc
    (ProbabilityTheory.gammaPDF (a : ℝ) 1 y).toReal *
        (Real.exp (-(printedTailLGammaArg μ a y)) *
          gammaLowBracketAlignedReal μ a (1 / (6 * y)))
        =
      ((ProbabilityTheory.gammaPDF (a : ℝ) 1 y).toReal *
          Real.exp (-(printedTailLGammaArg μ a y))) *
        gammaLowBracketAlignedReal μ a (1 / (6 * y)) := by ring
    _ =
      ((Real.Gamma (a : ℝ))⁻¹ * gammaIBPEnvelope μ a y) *
        gammaLowBracketAlignedReal μ a (1 / (6 * y)) := by
          rw [hpdf]
    _ =
      (Real.Gamma (a : ℝ))⁻¹ *
        (gammaIBPEnvelope μ a y *
          gammaLowBracketAlignedReal μ a (1 / (6 * y))) := by ring

/-- Convert the `W=exp(-L)(1-J)` Gamma expectation to the Lebesgue envelope
integral used by the integration-by-parts identity. -/
theorem gammaFull_WIntegral_eq_invGamma_mul_IBPWIntegral
    (μ : List Nat) {a : Nat} (ha : 150 ≤ a) :
    (∫ y, Real.exp (-(printedTailLGammaArg μ a y)) *
        (1 - printedTailJReal μ a (1 / (6 * y))) ∂ gammaFullMeasure a) =
      (Real.Gamma (a : ℝ))⁻¹ *
        ∫ y in Set.Ioi (0 : ℝ), gammaIBPWIntegrand μ a y := by
  rw [integral_gammaFullMeasure_eq_integral_Ici_gammaPDF_toReal_smul]
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy_nonneg : 0 ≤ y := le_of_lt (Set.mem_Ioi.mp hy)
  have hpdf := gammaPDF_toReal_mul_exp_neg_L_eq_invGamma_mul_envelope
    (μ := μ) (a := a) ha (x := y) hy_nonneg
  simp only [smul_eq_mul]
  unfold gammaIBPWIntegrand
  calc
    (ProbabilityTheory.gammaPDF (a : ℝ) 1 y).toReal *
        (Real.exp (-(printedTailLGammaArg μ a y)) *
          (1 - printedTailJReal μ a (1 / (6 * y))))
        =
      ((ProbabilityTheory.gammaPDF (a : ℝ) 1 y).toReal *
          Real.exp (-(printedTailLGammaArg μ a y))) *
        (1 - printedTailJReal μ a (1 / (6 * y))) := by ring
    _ =
      ((Real.Gamma (a : ℝ))⁻¹ * gammaIBPEnvelope μ a y) *
        (1 - printedTailJReal μ a (1 / (6 * y))) := by
          rw [hpdf]
    _ =
      (Real.Gamma (a : ℝ))⁻¹ *
        (gammaIBPEnvelope μ a y *
          (1 - printedTailJReal μ a (1 / (6 * y)))) := by ring

/-- Conditional closed Gamma lower bound for the untruncated
`W=exp(-L)(1-J)` expectation.  The hypotheses record exactly the remaining
endpoint and integrability facts needed by the integration-by-parts step. -/
theorem gammaFull_WIntegral_lower_of_IBP_endpoints
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a))
    (hcont :
      ContinuousWithinAt (gammaIBPEnvelope μ a) (Set.Ici (0 : ℝ)) 0)
    (hderivInt :
      IntegrableOn (gammaIBPDerivativeIntegrand μ a) (Set.Ioi (0 : ℝ)))
    (hbracket :
      IntegrableOn (gammaIBPBracketIntegrand μ a) (Set.Ioi (0 : ℝ)))
    (hW :
      IntegrableOn (gammaIBPWIntegrand μ a) (Set.Ioi (0 : ℝ))) :
    9 / (40 * ((a : ℝ) - 2)) ≤
      ∫ y, Real.exp (-(printedTailLGammaArg μ a y)) *
        (1 - printedTailJReal μ a (1 / (6 * y))) ∂ gammaFullMeasure a := by
  have hlower := gammaLowBracketAlignedIntegral_lower
    (a := a) (μ := μ) ha hμ
  have hIBP := gammaIBP_integral_W_eq_bracket_of_endpoints
    μ ha hcont hderivInt hbracket hW
  calc
    9 / (40 * ((a : ℝ) - 2))
        ≤ ∫ y, Real.exp (-(printedTailLGammaArg μ a y)) *
          gammaLowBracketAlignedReal μ a (1 / (6 * y)) ∂
            gammaFullMeasure a := hlower
    _ =
      ∫ y, Real.exp (-(printedTailLGammaArg μ a y)) *
        (1 - printedTailJReal μ a (1 / (6 * y))) ∂ gammaFullMeasure a := by
          rw [gammaFull_bracketIntegral_eq_invGamma_mul_IBPBracketIntegral
            (μ := μ) (a := a) ha]
          rw [gammaFull_WIntegral_eq_invGamma_mul_IBPWIntegral
            (μ := μ) (a := a) ha]
          rw [hIBP]

/-- Gamma lower bound for the untruncated `W` expectation with only the
origin-continuity condition still explicit. -/
theorem gammaFull_WIntegral_lower_of_IBP_origin
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a))
    (hcont :
      ContinuousWithinAt (gammaIBPEnvelope μ a) (Set.Ici (0 : ℝ)) 0) :
    9 / (40 * ((a : ℝ) - 2)) ≤
      ∫ y, Real.exp (-(printedTailLGammaArg μ a y)) *
        (1 - printedTailJReal μ a (1 / (6 * y))) ∂ gammaFullMeasure a := by
  have hlower := gammaLowBracketAlignedIntegral_lower
    (a := a) (μ := μ) ha hμ
  have hIBP := gammaIBP_integral_W_eq_bracket_of_origin
    μ ha hμ hcont
  calc
    9 / (40 * ((a : ℝ) - 2))
        ≤ ∫ y, Real.exp (-(printedTailLGammaArg μ a y)) *
          gammaLowBracketAlignedReal μ a (1 / (6 * y)) ∂
            gammaFullMeasure a := hlower
    _ =
      ∫ y, Real.exp (-(printedTailLGammaArg μ a y)) *
        (1 - printedTailJReal μ a (1 / (6 * y))) ∂ gammaFullMeasure a := by
          rw [gammaFull_bracketIntegral_eq_invGamma_mul_IBPBracketIntegral
            (μ := μ) (a := a) ha]
          rw [gammaFull_WIntegral_eq_invGamma_mul_IBPWIntegral
            (μ := μ) (a := a) ha]
          rw [hIBP]

/-- Closed Gamma lower bound for the untruncated
`W=exp(-L)(1-J)` expectation. -/
theorem gammaFull_WIntegral_lower
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    9 / (40 * ((a : ℝ) - 2)) ≤
      ∫ y, Real.exp (-(printedTailLGammaArg μ a y)) *
        (1 - printedTailJReal μ a (1 / (6 * y))) ∂ gammaFullMeasure a := by
  exact gammaFull_WIntegral_lower_of_IBP_origin
    (a := a) (μ := μ) ha hμ
    (continuousWithinAt_gammaIBPEnvelope_zero (a := a) (μ := μ) ha hμ)

end Prop52
