/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Gamma integral bridge for the Proposition 5.2 tail

`Prop52.GammaMoment` proves the finite rational moment bound used in the
large-tail argument.  This file begins the analytic bridge back to the printed
Gamma-integral proof: the monomial Gamma integrals are evaluated and identified
with the factorial ratios `gammaWeight`.
-/

import Prop52.GammaReal
import Mathlib.Probability.Distributions.Gamma

namespace Prop52

open Finset
open MeasureTheory Set
open scoped ENNReal

private theorem gammaIntegral_nat_power_exp_eq_factorial (n : Nat) :
    ∫ y : ℝ in Set.Ioi 0, y ^ ((n : Nat) : ℝ) * Real.exp (-y) =
      (n.factorial : ℝ) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (n : ℝ) + 1) (r := (1 : ℝ)) (by positivity) (by norm_num)
  have hpow : ((n : ℝ) + 1 - 1) = (n : ℝ) := by ring
  simpa [hpow, Real.Gamma_nat_eq_factorial] using h

private theorem factorial_cast_real_ne (n : Nat) :
    ((n.factorial : Nat) : ℝ) ≠ 0 := by
  exact_mod_cast n.factorial_pos.ne'

/-- The normalized monomial contribution obtained from the integer-shape
Gamma density after substituting `t = 1/(6y)`.

The statement uses the same truncated Nat subtractions as `gammaWeight`; in all
applications below the caller is in the non-underflow range supplied by
`printedTailP`. -/
noncomputable def gammaMonomialMoment (shape s : Nat) : ℝ :=
  (1 / (6 : ℝ)^s) *
    (1 / ((Nat.factorial (shape - 1) : Nat) : ℝ)) *
      ∫ y : ℝ in Set.Ioi 0,
        y ^ (((shape - s - 1 : Nat) : ℝ)) * Real.exp (-y)

/-- Evaluation of the normalized integer-shape Gamma monomial integral as the
factorial ratio already used by the rational certificate layer. -/
theorem gammaMonomialMoment_eq_gammaWeight (shape s : Nat) :
    gammaMonomialMoment shape s = (gammaWeight shape s : ℝ) := by
  unfold gammaMonomialMoment
  rw [gammaIntegral_nat_power_exp_eq_factorial]
  unfold gammaWeight
  norm_num
  field_simp [pow_ne_zero s (by norm_num : (6 : ℝ) ≠ 0),
    factorial_cast_real_ne (shape - 1)]

/-- Integral form of the low-polynomial exponent mean
`E[L(1/(6Y))]`, expanded monomial-by-monomial. -/
noncomputable def printedTailGammaExponentIntegral (μ : List Nat) (a : Nat) : ℝ :=
  ∑ r ∈ Finset.Ico 1 (printedTailP a + 1),
    (hCoeff μ r : ℝ) * gammaMonomialMoment (a - 2) r

/-- The analytic Gamma-integral expansion is exactly the finite rational moment
already bounded in `Prop52.GammaMoment`. -/
theorem printedTailGammaExponentIntegral_eq_moment
    (μ : List Nat) (a : Nat) :
    printedTailGammaExponentIntegral μ a =
      (printedTailGammaExponentMoment μ a : ℝ) := by
  unfold printedTailGammaExponentIntegral printedTailGammaExponentMoment
  rw [Rat.cast_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Rat.cast_mul, gammaMonomialMoment_eq_gammaWeight]

/-- Analytic restatement of the rational Gamma exponent budget. -/
theorem printedTailGammaExponentIntegral_le_bound
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    printedTailGammaExponentIntegral μ a ≤ (gammaExponentBound a : ℝ) := by
  rw [printedTailGammaExponentIntegral_eq_moment]
  exact (Rat.cast_le (K := ℝ)).2
    (printedTailGammaExponentMoment_le_bound (a := a) (μ := μ) ha hμ)

/-- The low polynomial `L` from the printed Gamma proof, now as a real
function. -/
noncomputable def printedTailLReal (μ : List Nat) (a : Nat) (x : ℝ) : ℝ :=
  ∑ r ∈ Finset.Ico 1 (printedTailP a + 1), (hCoeff μ r : ℝ) * x^r

theorem printedTailLReal_nonneg
    {a : Nat} {μ : List Nat} (hμ : Prop51.IsPartitionOf μ (M a))
    {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ printedTailLReal μ a x := by
  unfold printedTailLReal
  refine Finset.sum_nonneg fun r _hr => ?_
  exact mul_nonneg
    ((Rat.cast_nonneg (K := ℝ)).2 (hCoeff_nonneg_of_partition hμ r))
    (pow_nonneg hx r)

theorem real_exp_neg_printedTailLReal_le_one
    {a : Nat} {μ : List Nat} (hμ : Prop51.IsPartitionOf μ (M a))
    {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-(printedTailLReal μ a x)) ≤ 1 := by
  have hL := printedTailLReal_nonneg (a := a) (μ := μ) hμ hx
  have hneg : -(printedTailLReal μ a x) ≤ 0 := by linarith
  simpa using (Real.exp_le_exp_of_le hneg)

/-- The Gamma law used in the large-tail argument, with integer shape
`a - 2` and rate `1`. -/
noncomputable def gammaTailMeasure (a : Nat) : Measure ℝ :=
  ProbabilityTheory.gammaMeasure (((a - 2 : Nat) : ℝ)) 1

theorem ae_nonneg_gammaTailMeasure (a : Nat) :
    ∀ᵐ y ∂ gammaTailMeasure a, 0 ≤ y := by
  rw [ae_iff]
  simpa [Set.compl_setOf, not_le] using
    (show gammaTailMeasure a (Set.Iio 0) = 0 from by
      unfold gammaTailMeasure ProbabilityTheory.gammaMeasure
      rw [withDensity_apply _ measurableSet_Iio]
      exact ProbabilityTheory.lintegral_gammaPDF_of_nonpos (x := 0)
        (a := ((a - 2 : Nat) : ℝ)) (r := 1) le_rfl)

/-- Unfold integrals against the Gamma-tail measure to integrals against
Lebesgue measure with the Gamma density. -/
theorem integral_gammaTailMeasure_eq_integral_gammaPDF_toReal_smul
    (a : Nat) (g : ℝ → ℝ) :
    (∫ y, g y ∂ gammaTailMeasure a) =
      ∫ y, (ProbabilityTheory.gammaPDF (((a - 2 : Nat) : ℝ)) 1 y).toReal •
        g y := by
  unfold gammaTailMeasure ProbabilityTheory.gammaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul]
  · unfold ProbabilityTheory.gammaPDF
    exact (ProbabilityTheory.measurable_gammaPDFReal (((a - 2 : Nat) : ℝ)) 1).ennreal_ofReal
  · filter_upwards with y
    simp [ProbabilityTheory.gammaPDF]

/-- Same density conversion, restricted to the support `[0,∞)` of the Gamma
law. -/
theorem integral_gammaTailMeasure_eq_integral_Ici_gammaPDF_toReal_smul
    (a : Nat) (g : ℝ → ℝ) :
    (∫ y, g y ∂ gammaTailMeasure a) =
      ∫ y in Set.Ici 0,
        (ProbabilityTheory.gammaPDF (((a - 2 : Nat) : ℝ)) 1 y).toReal •
          g y := by
  rw [integral_gammaTailMeasure_eq_integral_gammaPDF_toReal_smul]
  rw [← MeasureTheory.integral_indicator measurableSet_Ici]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with y
  by_cases hy : 0 ≤ y
  · have hymem : y ∈ Set.Ici (0 : ℝ) := hy
    simp [Set.indicator, hymem]
  · have hyneg : y < 0 := lt_of_not_ge hy
    have hynot : y ∉ Set.Ici (0 : ℝ) := hy
    rw [ProbabilityTheory.gammaPDF_of_neg hyneg]
    simp [Set.indicator, hynot]

private theorem gammaPDF_toReal_mul_invPow_eq_gammaMonomial_integrand
    {a r : Nat} (ha : 150 ≤ a) (hr : r ≤ printedTailP a)
    {y : ℝ} (hy : 0 < y) :
    (ProbabilityTheory.gammaPDF (((a - 2 : Nat) : ℝ)) 1 y).toReal *
        (1 / (6 * y))^r =
      (1 / (6 : ℝ)^r) *
        (1 / ((Nat.factorial (a - 3) : Nat) : ℝ)) *
          (y ^ (((a - r - 3 : Nat) : ℝ)) * Real.exp (-y)) := by
  rw [ProbabilityTheory.gammaPDF_of_nonneg hy.le]
  rw [ENNReal.toReal_ofReal]
  · simp only [Real.one_rpow, one_mul]
    have hshape : (((a - 2 : Nat) : ℝ)) = ((a - 3 : Nat) : ℝ) + 1 := by
      rw [show a - 2 = (a - 3) + 1 by omega]
      norm_num
    rw [hshape]
    rw [Real.Gamma_nat_eq_factorial (a - 3)]
    have hpowA : y ^ (((a - 3 : Nat) : ℝ) + 1 - 1) = y ^ (a - 3) := by
      rw [show (((a - 3 : Nat) : ℝ) + 1 - 1) =
        ((a - 3 : Nat) : ℝ) by ring]
      exact Real.rpow_natCast y (a - 3)
    rw [hpowA]
    have hsplit : a - 3 = (a - r - 3) + r := by
      unfold printedTailP at hr
      omega
    rw [hsplit]
    rw [pow_add]
    rw [show y ^ (((a - r - 3 : Nat) : ℝ)) = y ^ (a - r - 3) by
      exact Real.rpow_natCast y (a - r - 3)]
    field_simp [pow_ne_zero r hy.ne', pow_ne_zero (a - r - 3) hy.ne',
      pow_ne_zero (a - r - 3 + r) hy.ne', factorial_cast_real_ne (a - 3),
      pow_ne_zero r (by norm_num : (6 : ℝ) ≠ 0)]
    rw [← mul_pow y (1 / (y * 6)) r]
    have hy6 : y * (1 / (y * 6)) = (1 / 6 : ℝ) := by
      field_simp [hy.ne']
    rw [hy6]
    rw [show (1 / 6 : ℝ)^r * 6^r = ((1 / 6 : ℝ) * 6)^r by
      rw [mul_pow]]
    norm_num
  · positivity

/-- The actual Gamma-tail expectation of the inverse monomial `(1/(6Y))^r`
is the normalized monomial moment used in the algebraic certificate layer. -/
theorem integral_invPow_gammaTailMeasure_eq_gammaMonomialMoment
    {a r : Nat} (ha : 150 ≤ a) (hr : r ≤ printedTailP a) :
    (∫ y, (1 / (6 * y))^r ∂ gammaTailMeasure a) =
      gammaMonomialMoment (a - 2) r := by
  let C : ℝ := (1 / (6 : ℝ)^r) *
    (1 / ((Nat.factorial (a - 3) : Nat) : ℝ))
  calc
    (∫ y, (1 / (6 * y))^r ∂ gammaTailMeasure a)
        = ∫ y in Set.Ici 0,
            (ProbabilityTheory.gammaPDF (((a - 2 : Nat) : ℝ)) 1 y).toReal •
              (1 / (6 * y))^r := by
          rw [integral_gammaTailMeasure_eq_integral_Ici_gammaPDF_toReal_smul]
    _ = ∫ y in Set.Ioi 0,
            (ProbabilityTheory.gammaPDF (((a - 2 : Nat) : ℝ)) 1 y).toReal •
              (1 / (6 * y))^r := by
          rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    _ = ∫ y in Set.Ioi 0,
            C * (y ^ (((a - r - 3 : Nat) : ℝ)) * Real.exp (-y)) := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
          dsimp [C]
          simpa [smul_eq_mul, mul_assoc] using
            gammaPDF_toReal_mul_invPow_eq_gammaMonomial_integrand
              (a := a) (r := r) ha hr (Set.mem_Ioi.mp hy)
    _ = C * ∫ y in Set.Ioi 0,
            y ^ (((a - r - 3 : Nat) : ℝ)) * Real.exp (-y) := by
          rw [MeasureTheory.integral_const_mul]
    _ = gammaMonomialMoment (a - 2) r := by
          dsimp [C]
          unfold gammaMonomialMoment
          have hshape : a - 2 - r - 1 = a - r - 3 := by omega
          have hden : a - 2 - 1 = a - 3 := by omega
          rw [hshape, hden]

private theorem gammaMonomialMoment_pos (shape r : Nat) :
    0 < gammaMonomialMoment shape r := by
  rw [gammaMonomialMoment_eq_gammaWeight]
  unfold gammaWeight
  positivity

theorem integrable_invPow_gammaTailMeasure
    {a r : Nat} (ha : 150 ≤ a) (hr : r ≤ printedTailP a) :
    Integrable (fun y : ℝ => (1 / (6 * y))^r) (gammaTailMeasure a) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_invPow_gammaTailMeasure_eq_gammaMonomialMoment
    (a := a) (r := r) ha hr]
  exact ne_of_gt (gammaMonomialMoment_pos (a - 2) r)

theorem isProbabilityMeasure_gammaTailMeasure
    {a : Nat} (ha : 150 ≤ a) :
    IsProbabilityMeasure (gammaTailMeasure a) := by
  unfold gammaTailMeasure
  exact ProbabilityTheory.isProbabilityMeasure_gammaMeasure
    (by exact_mod_cast (by omega : 0 < a - 2)) (by norm_num)

/-- The random variable `L(1/(6Y))` used in the Gamma/Jensen margin, where
`Y` has the integer-shape Gamma law `gammaTailMeasure a`. -/
noncomputable def printedTailLGammaArg (μ : List Nat) (a : Nat) (y : ℝ) : ℝ :=
  printedTailLReal μ a (1 / (6 * y))

theorem integrable_printedTailLGammaArg
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a) :
    Integrable (printedTailLGammaArg μ a) (gammaTailMeasure a) := by
  unfold printedTailLGammaArg printedTailLReal
  refine MeasureTheory.integrable_finset_sum _ ?_
  intro r hr
  have hrle : r ≤ printedTailP a :=
    Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hr).2
  exact (integrable_invPow_gammaTailMeasure (a := a) (r := r) ha hrle).const_mul _

/-- The actual Gamma-tail mean of `L(1/(6Y))` is the finite monomial expansion
`printedTailGammaExponentIntegral`. -/
theorem integral_printedTailLGammaArg_eq_exponentIntegral
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a) :
    (∫ y, printedTailLGammaArg μ a y ∂ gammaTailMeasure a) =
      printedTailGammaExponentIntegral μ a := by
  unfold printedTailLGammaArg printedTailLReal printedTailGammaExponentIntegral
  rw [MeasureTheory.integral_finset_sum]
  · refine Finset.sum_congr rfl fun r hr => ?_
    have hrle : r ≤ printedTailP a :=
      Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hr).2
    rw [MeasureTheory.integral_const_mul]
    rw [integral_invPow_gammaTailMeasure_eq_gammaMonomialMoment
      (a := a) (r := r) ha hrle]
  · intro r hr
    have hrle : r ≤ printedTailP a :=
      Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hr).2
    exact (integrable_invPow_gammaTailMeasure
      (a := a) (r := r) ha hrle).const_mul _

theorem integral_printedTailLGammaArg_le_bound
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    (∫ y, printedTailLGammaArg μ a y ∂ gammaTailMeasure a) ≤
      (gammaExponentBound a : ℝ) := by
  rw [integral_printedTailLGammaArg_eq_exponentIntegral (a := a) (μ := μ) ha]
  exact printedTailGammaExponentIntegral_le_bound (a := a) (μ := μ) ha hμ

/-- The negative exponential in the Jensen lower bound is integrable under the
Gamma-tail probability measure.  The proof uses only the almost-everywhere
support `Y >= 0` and the coefficientwise nonnegativity of `L`. -/
theorem integrable_exp_neg_printedTailLGammaArg
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    Integrable (fun y => Real.exp (-(printedTailLGammaArg μ a y)))
      (gammaTailMeasure a) := by
  haveI := isProbabilityMeasure_gammaTailMeasure ha
  refine Integrable.of_mem_Icc (μ := gammaTailMeasure a) 0 1 ?hmeas ?hbounds
  · unfold printedTailLGammaArg printedTailLReal
    fun_prop
  · filter_upwards [ae_nonneg_gammaTailMeasure a] with y hy
    have hx : 0 ≤ 1 / (6 * y) := by positivity
    have hle := real_exp_neg_printedTailLReal_le_one
      (a := a) (μ := μ) hμ hx
    constructor
    · positivity
    · simpa [printedTailLGammaArg] using hle

/-- Jensen and the scalar endpoint specialized to the Gamma law with shape
`a - 2`. -/
theorem gammaTailPrefactor_integral_exp_neg_lower_of_mean_le_bound
    {a : Nat} (ha : 150 ≤ a) {f : ℝ → ℝ}
    (hf : Integrable f (gammaTailMeasure a))
    (hexp : Integrable (fun y => Real.exp (-f y)) (gammaTailMeasure a))
    (hmean : ∫ y, f y ∂ gammaTailMeasure a ≤ (gammaExponentBound a : ℝ)) :
    9 / (40 * ((a : ℝ) - 2)) ≤
      (5 / (6 * ((a : ℝ) - 2))) *
        ∫ y, Real.exp (-f y) ∂ gammaTailMeasure a := by
  haveI := isProbabilityMeasure_gammaTailMeasure ha
  exact gammaPrefactor_integral_exp_neg_lower_of_mean_le_bound
    (μ := gammaTailMeasure a) (a := a) ha hf hexp hmean

/-- The Jensen/Gamma lower bound for the concrete low polynomial
`L(1/(6Y))` attached to a partition. -/
theorem gammaTailPrefactor_integral_exp_neg_printedTailLGammaArg_lower
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    9 / (40 * ((a : ℝ) - 2)) ≤
      (5 / (6 * ((a : ℝ) - 2))) *
        ∫ y, Real.exp (-(printedTailLGammaArg μ a y)) ∂ gammaTailMeasure a := by
  exact gammaTailPrefactor_integral_exp_neg_lower_of_mean_le_bound
    (a := a) ha
    (integrable_printedTailLGammaArg (a := a) (μ := μ) ha)
    (integrable_exp_neg_printedTailLGammaArg (a := a) (μ := μ) ha hμ)
    (integral_printedTailLGammaArg_le_bound (a := a) (μ := μ) ha hμ)

end Prop52
