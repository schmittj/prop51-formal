/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Gamma integral bridge for the Proposition 5.2 tail

`Prop52.GammaMoment` proves the finite rational moment bound used in the
large-tail argument.  This file begins the analytic bridge back to the printed
Gamma-integral proof: the monomial Gamma integrals are evaluated and identified
with the factorial ratios `gammaWeight`.
-/

import Prop52.GammaReal
import Prop52.GammaRetain
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

noncomputable def printedTailJReal (μ : List Nat) (a : Nat) (x : ℝ) : ℝ :=
  ∑ r ∈ Finset.Ico 1 (printedTailP a + 1), (kCoeff μ r : ℝ) * x^r

theorem printedTailLReal_nonneg
    {a : Nat} {μ : List Nat} (hμ : Prop51.IsPartitionOf μ (M a))
    {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ printedTailLReal μ a x := by
  unfold printedTailLReal
  refine Finset.sum_nonneg fun r _hr => ?_
  exact mul_nonneg
    ((Rat.cast_nonneg (K := ℝ)).2 (hCoeff_nonneg_of_partition hμ r))
    (pow_nonneg hx r)

theorem printedTailJReal_nonneg
    (μ : List Nat) (a : Nat) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ printedTailJReal μ a x := by
  unfold printedTailJReal
  refine Finset.sum_nonneg fun r _hr => ?_
  exact mul_nonneg
    ((Rat.cast_nonneg (K := ℝ)).2 (kCoeff_nonneg μ r))
    (pow_nonneg hx r)

theorem printedTailJReal_le_two_LReal
    {a : Nat} {μ : List Nat} (hμ : Prop51.IsPartitionOf μ (M a))
    {x : ℝ} (hx : 0 ≤ x) :
    printedTailJReal μ a x ≤ 2 * printedTailLReal μ a x := by
  unfold printedTailJReal printedTailLReal
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun r _hr => ?_
  have hkQ := kCoeff_le_two_hCoeff_of_partition
    (a := a) (μ := μ) hμ r
  have hkR : (kCoeff μ r : ℝ) ≤ 2 * (hCoeff μ r : ℝ) := by
    have hcast := (Rat.cast_le (K := ℝ)).2 hkQ
    simpa using hcast
  calc
    (kCoeff μ r : ℝ) * x^r ≤ (2 * (hCoeff μ r : ℝ)) * x^r :=
      mul_le_mul_of_nonneg_right hkR (pow_nonneg hx r)
    _ = 2 * ((hCoeff μ r : ℝ) * x^r) := by ring

theorem real_exp_neg_printedTailLReal_le_one
    {a : Nat} {μ : List Nat} (hμ : Prop51.IsPartitionOf μ (M a))
    {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-(printedTailLReal μ a x)) ≤ 1 := by
  have hL := printedTailLReal_nonneg (a := a) (μ := μ) hμ hx
  have hneg : -(printedTailLReal μ a x) ≤ 0 := by linarith
  simpa using (Real.exp_le_exp_of_le hneg)

/-- Pointwise truncation estimate from the paper:
`|W(t)| = |exp(-L(t)) (1-J(t))| <= 2` for `t >= 0`. -/
theorem abs_exp_neg_L_mul_one_sub_JReal_le_two
    {a : Nat} {μ : List Nat} (hμ : Prop51.IsPartitionOf μ (M a))
    {x : ℝ} (hx : 0 ≤ x) :
    |Real.exp (-(printedTailLReal μ a x)) *
        (1 - printedTailJReal μ a x)| ≤ 2 := by
  have hLnonneg := printedTailLReal_nonneg (a := a) (μ := μ) hμ hx
  have hJnonneg := printedTailJReal_nonneg μ a hx
  have hJle := printedTailJReal_le_two_LReal
    (a := a) (μ := μ) hμ hx
  have habsJ :
      |1 - printedTailJReal μ a x| ≤
        1 + printedTailJReal μ a x := by
    refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
  have hexp_nonneg :
      0 ≤ Real.exp (-(printedTailLReal μ a x)) := (Real.exp_pos _).le
  calc
    |Real.exp (-(printedTailLReal μ a x)) *
        (1 - printedTailJReal μ a x)|
        =
      Real.exp (-(printedTailLReal μ a x)) *
        |1 - printedTailJReal μ a x| := by
        rw [abs_mul, abs_of_nonneg hexp_nonneg]
    _ ≤
      Real.exp (-(printedTailLReal μ a x)) *
        (1 + printedTailJReal μ a x) :=
        mul_le_mul_of_nonneg_left habsJ hexp_nonneg
    _ ≤
      Real.exp (-(printedTailLReal μ a x)) *
        (1 + 2 * printedTailLReal μ a x) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hexp_nonneg
    _ =
      (1 + 2 * printedTailLReal μ a x) *
        Real.exp (-(printedTailLReal μ a x)) := by ring
    _ ≤ 2 :=
      one_add_two_mul_mul_exp_neg_le_two hLnonneg

/-- Real version of the retained Gamma bracket lower polynomial. -/
noncomputable def gammaRetainBracketLowerReal
    (μ : List Nat) (a : Nat) (x : ℝ) : ℝ :=
  ((M a : ℝ) - (kCoeff μ 1 : ℝ)) * x +
    ∑ j ∈ Finset.Ico 1 (printedTailP a + 1),
      (gammaRetainBracketCoeff μ j : ℝ) * x^(j + 1)

/-- Real version of the coefficient-aligned low Gamma bracket
`M x + 6 x^2 L'(x) - J(x)`. -/
noncomputable def gammaLowBracketAlignedReal
    (μ : List Nat) (a : Nat) (x : ℝ) : ℝ :=
  ((M a : ℝ) - (kCoeff μ 1 : ℝ)) * x +
    (∑ j ∈ Finset.Ico 1 (printedTailP a + 1),
      6 * (j : ℝ) * (hCoeff μ j : ℝ) * x^(j + 1)) -
    ∑ j ∈ Finset.Ico 1 (printedTailP a),
      (kCoeff μ (j + 1) : ℝ) * x^(j + 1)

theorem gammaRetainBracketLowerReal_add_final_eq_lowBracketAlignedReal
    (μ : List Nat) (a : Nat) (x : ℝ) (ha : 150 ≤ a) :
    gammaRetainBracketLowerReal μ a x +
        (kCoeff μ (printedTailP a + 1) : ℝ) * x^(printedTailP a + 1) =
      gammaLowBracketAlignedReal μ a x := by
  let p : Nat := printedTailP a
  let F : Nat → ℝ := fun j => 6 * (j : ℝ) * (hCoeff μ j : ℝ) * x^(j + 1)
  let G : Nat → ℝ := fun j => (kCoeff μ (j + 1) : ℝ) * x^(j + 1)
  have hp : 1 ≤ p := by
    dsimp [p, printedTailP]
    have : 2 ≤ a := by omega
    omega
  have hretain_sum :
      (∑ j ∈ Finset.Ico 1 (p + 1),
          (gammaRetainBracketCoeff μ j : ℝ) * x^(j + 1)) =
        ∑ j ∈ Finset.Ico 1 (p + 1), (F j - G j) := by
    refine Finset.sum_congr rfl fun j _hj => ?_
    dsimp [F, G, gammaRetainBracketCoeff]
    norm_num
    ring
  have hGsplit :
      (∑ j ∈ Finset.Ico 1 (p + 1), G j) =
        (∑ j ∈ Finset.Ico 1 p, G j) + G p := by
    simpa using Finset.sum_Ico_succ_top hp G
  have hretain_sum' :
      (∑ j ∈ Finset.Ico 1 (printedTailP a + 1),
          (gammaRetainBracketCoeff μ j : ℝ) * x^(j + 1)) =
        ∑ j ∈ Finset.Ico 1 (printedTailP a + 1), (F j - G j) := by
    simpa [p] using hretain_sum
  have hGsplit' :
      (∑ j ∈ Finset.Ico 1 (printedTailP a + 1), G j) =
        (∑ j ∈ Finset.Ico 1 (printedTailP a), G j) +
          G (printedTailP a) := by
    simpa [p] using hGsplit
  unfold gammaRetainBracketLowerReal gammaLowBracketAlignedReal
  rw [hretain_sum', Finset.sum_sub_distrib, hGsplit']
  dsimp [F, G]
  ring

theorem gammaRetainBracketLowerReal_le_lowBracketAlignedReal
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a) {x : ℝ} (hx : 0 ≤ x) :
    gammaRetainBracketLowerReal μ a x ≤ gammaLowBracketAlignedReal μ a x := by
  have hk_nonneg :
      0 ≤ (kCoeff μ (printedTailP a + 1) : ℝ) :=
    (Rat.cast_nonneg (K := ℝ)).2 (kCoeff_nonneg μ (printedTailP a + 1))
  have hfinal :
      0 ≤ (kCoeff μ (printedTailP a + 1) : ℝ) *
          x^(printedTailP a + 1) :=
    mul_nonneg hk_nonneg (pow_nonneg hx (printedTailP a + 1))
  have h_eq :=
    gammaRetainBracketLowerReal_add_final_eq_lowBracketAlignedReal μ a x ha
  nlinarith

/-- Real pointwise retained-bracket lower bound. -/
theorem fiveM_x2_le_gammaRetainBracketLowerReal
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) {x : ℝ} (hx : 0 ≤ x) :
    5 * (M a : ℝ) * x^2 ≤ gammaRetainBracketLowerReal μ a x := by
  unfold gammaRetainBracketLowerReal
  have hlinear_nonneg :
      0 ≤ ((M a : ℝ) - (kCoeff μ 1 : ℝ)) * x := by
    have hq := gammaRetainBracketLinearCoeff_nonneg
      (a := a) (μ := μ) hμ
    have hr :
        0 ≤ ((M a : ℝ) - (kCoeff μ 1 : ℝ)) := by
      have hcast : (0 : ℝ) ≤ (((M a : ℚ) - kCoeff μ 1 : ℚ) : ℝ) :=
        (Rat.cast_nonneg (K := ℝ)).2 hq
      simpa using hcast
    exact mul_nonneg hr hx
  have hterms_nonneg :
      ∀ j ∈ Finset.Ico 1 (printedTailP a + 1),
        0 ≤ (gammaRetainBracketCoeff μ j : ℝ) * x^(j + 1) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have hcoeff :
        0 ≤ (gammaRetainBracketCoeff μ j : ℝ) :=
      (Rat.cast_nonneg (K := ℝ)).2
        (gammaRetainBracketCoeff_nonneg (a := a) (μ := μ) hμ hj1)
    exact mul_nonneg hcoeff (pow_nonneg hx (j + 1))
  have hmem1 : 1 ∈ Finset.Ico 1 (printedTailP a + 1) := by
    simp [printedTailP]
    omega
  have hsingle := Finset.single_le_sum hterms_nonneg hmem1
  have hterm1 :
      5 * (M a : ℝ) * x^2 ≤
        (gammaRetainBracketCoeff μ 1 : ℝ) * x^(1 + 1) := by
    have hcoeffQ := fiveM_le_gammaRetainBracketCoeff_one
      (a := a) (μ := μ) hμ
    have hcoeffR :
        5 * (M a : ℝ) ≤ (gammaRetainBracketCoeff μ 1 : ℝ) := by
      have hcast :
          (((5 : ℚ) * (M a : ℚ) : ℚ) : ℝ) ≤
            (gammaRetainBracketCoeff μ 1 : ℝ) :=
        (Rat.cast_le (K := ℝ)).2 hcoeffQ
      simpa using hcast
    have hx2 : 0 ≤ x^2 := pow_nonneg hx 2
    calc
      5 * (M a : ℝ) * x^2
          ≤ (gammaRetainBracketCoeff μ 1 : ℝ) * x^2 :=
            mul_le_mul_of_nonneg_right hcoeffR hx2
      _ = (gammaRetainBracketCoeff μ 1 : ℝ) * x^(1 + 1) := by norm_num
  calc
    5 * (M a : ℝ) * x^2
        ≤ (gammaRetainBracketCoeff μ 1 : ℝ) * x^(1 + 1) := hterm1
    _ ≤ ∑ j ∈ Finset.Ico 1 (printedTailP a + 1),
          (gammaRetainBracketCoeff μ j : ℝ) * x^(j + 1) := hsingle
    _ ≤ ((M a : ℝ) - (kCoeff μ 1 : ℝ)) * x +
          ∑ j ∈ Finset.Ico 1 (printedTailP a + 1),
            (gammaRetainBracketCoeff μ j : ℝ) * x^(j + 1) := by
          nlinarith

/-- Real pointwise low-bracket lower bound in the exact form needed under the
Gamma integral. -/
theorem fiveM_x2_le_gammaLowBracketAlignedReal
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) {x : ℝ} (hx : 0 ≤ x) :
    5 * (M a : ℝ) * x^2 ≤ gammaLowBracketAlignedReal μ a x := by
  exact (fiveM_x2_le_gammaRetainBracketLowerReal
    (a := a) (μ := μ) ha hμ hx).trans
      (gammaRetainBracketLowerReal_le_lowBracketAlignedReal
        (a := a) (μ := μ) ha (x := x) hx)

/-- The Gamma law used in the large-tail argument, with integer shape
`a - 2` and rate `1`. -/
noncomputable def gammaTailMeasure (a : Nat) : Measure ℝ :=
  ProbabilityTheory.gammaMeasure (((a - 2 : Nat) : ℝ)) 1

/-- The integer-shape Gamma law with shape `a`, used for the
integration-by-parts side before shifting two powers of `1/(6Y)`. -/
noncomputable def gammaFullMeasure (a : Nat) : Measure ℝ :=
  ProbabilityTheory.gammaMeasure ((a : ℝ)) 1

theorem gammaFullMeasure_eq_gammaTailMeasure_add_two (a : Nat) :
    gammaFullMeasure a = gammaTailMeasure (a + 2) := by
  unfold gammaFullMeasure gammaTailMeasure
  rw [show a + 2 - 2 = a by omega]

theorem ae_nonneg_gammaTailMeasure (a : Nat) :
    ∀ᵐ y ∂ gammaTailMeasure a, 0 ≤ y := by
  rw [ae_iff]
  simpa [Set.compl_setOf, not_le] using
    (show gammaTailMeasure a (Set.Iio 0) = 0 from by
      unfold gammaTailMeasure ProbabilityTheory.gammaMeasure
      rw [withDensity_apply _ measurableSet_Iio]
      exact ProbabilityTheory.lintegral_gammaPDF_of_nonpos (x := 0)
        (a := ((a - 2 : Nat) : ℝ)) (r := 1) le_rfl)

theorem ae_nonneg_gammaFullMeasure (a : Nat) :
    ∀ᵐ y ∂ gammaFullMeasure a, 0 ≤ y := by
  rw [ae_iff]
  simpa [Set.compl_setOf, not_le] using
    (show gammaFullMeasure a (Set.Iio 0) = 0 from by
      unfold gammaFullMeasure ProbabilityTheory.gammaMeasure
      rw [withDensity_apply _ measurableSet_Iio]
      exact ProbabilityTheory.lintegral_gammaPDF_of_nonpos (x := 0)
        (a := (a : ℝ)) (r := 1) le_rfl)

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

/-- Unfold integrals against the full shape-`a` Gamma measure to integrals
against Lebesgue measure with the Gamma density. -/
theorem integral_gammaFullMeasure_eq_integral_gammaPDF_toReal_smul
    (a : Nat) (g : ℝ → ℝ) :
    (∫ y, g y ∂ gammaFullMeasure a) =
      ∫ y, (ProbabilityTheory.gammaPDF (a : ℝ) 1 y).toReal • g y := by
  unfold gammaFullMeasure ProbabilityTheory.gammaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul]
  · unfold ProbabilityTheory.gammaPDF
    exact (ProbabilityTheory.measurable_gammaPDFReal (a : ℝ) 1).ennreal_ofReal
  · filter_upwards with y
    simp [ProbabilityTheory.gammaPDF]

/-- Same density conversion for the full shape-`a` Gamma law, restricted to
its support `[0,∞)`. -/
theorem integral_gammaFullMeasure_eq_integral_Ici_gammaPDF_toReal_smul
    (a : Nat) (g : ℝ → ℝ) :
    (∫ y, g y ∂ gammaFullMeasure a) =
      ∫ y in Set.Ici 0,
        (ProbabilityTheory.gammaPDF (a : ℝ) 1 y).toReal • g y := by
  rw [integral_gammaFullMeasure_eq_integral_gammaPDF_toReal_smul]
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

private theorem fiveM_gammaPDF_full_mul_invSq_eq_tail_prefactor
    {a : Nat} (ha : 150 ≤ a) {y : ℝ} (hy : 0 < y) :
    (5 * (M a : ℝ)) *
        ((ProbabilityTheory.gammaPDF (a : ℝ) 1 y).toReal *
          (1 / (6 * y))^2) =
      (5 / (6 * ((a : ℝ) - 2))) *
        (ProbabilityTheory.gammaPDF (((a - 2 : Nat) : ℝ)) 1 y).toReal := by
  rw [ProbabilityTheory.gammaPDF_of_nonneg hy.le]
  rw [ProbabilityTheory.gammaPDF_of_nonneg hy.le]
  rw [ENNReal.toReal_ofReal, ENNReal.toReal_ofReal]
  · simp only [Real.one_rpow, one_mul]
    have hMcast : (M a : ℝ) = 6 * ((a : ℝ) - 1) := by
      unfold M
      rw [Nat.cast_sub (by omega : 6 ≤ 6 * a)]
      push_cast
      ring
    have hshapeFull : (a : ℝ) = ((a - 1 : Nat) : ℝ) + 1 := by
      rw [show a = (a - 1) + 1 by omega]
      norm_num
    have hshapeTail : (((a - 2 : Nat) : ℝ)) = ((a - 3 : Nat) : ℝ) + 1 := by
      rw [show a - 2 = (a - 3) + 1 by omega]
      norm_num
    rw [hMcast, hshapeFull, hshapeTail]
    rw [Real.Gamma_nat_eq_factorial (a - 1),
      Real.Gamma_nat_eq_factorial (a - 3)]
    have hpowFull :
        y ^ (((a - 1 : Nat) : ℝ) + 1 - 1) = y^(a - 1) := by
      rw [show (((a - 1 : Nat) : ℝ) + 1 - 1) =
        ((a - 1 : Nat) : ℝ) by ring]
      exact Real.rpow_natCast y (a - 1)
    have hpowTail :
        y ^ (((a - 3 : Nat) : ℝ) + 1 - 1) = y^(a - 3) := by
      rw [show (((a - 3 : Nat) : ℝ) + 1 - 1) =
        ((a - 3 : Nat) : ℝ) by ring]
      exact Real.rpow_natCast y (a - 3)
    rw [hpowFull, hpowTail]
    have hfac1 :
        (((a - 1).factorial : Nat) : ℝ) =
          ((a : ℝ) - 1) * (((a - 2).factorial : Nat) : ℝ) := by
      rw [show a - 1 = (a - 2) + 1 by omega, Nat.factorial_succ]
      rw [Nat.cast_mul]
      rw [show (((a - 2 + 1 : Nat) : ℝ)) = (a : ℝ) - 1 by
        rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub (by omega : 2 ≤ a)]
        ring]
    have hfac2 :
        (((a - 2).factorial : Nat) : ℝ) =
          ((a : ℝ) - 2) * (((a - 3).factorial : Nat) : ℝ) := by
      rw [show a - 2 = (a - 3) + 1 by omega, Nat.factorial_succ]
      rw [Nat.cast_mul]
      rw [show (((a - 3 + 1 : Nat) : ℝ)) = (a : ℝ) - 2 by
        rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub (by omega : 3 ≤ a)]
        ring]
    rw [hfac1, hfac2]
    have hy_ne : y ≠ 0 := hy.ne'
    have ha1 : (a : ℝ) - 1 ≠ 0 := by
      have haR : (150 : ℝ) ≤ a := by exact_mod_cast ha
      nlinarith
    have ha2 : (a : ℝ) - 2 ≠ 0 := by
      have haR : (150 : ℝ) ≤ a := by exact_mod_cast ha
      nlinarith
    field_simp [hy_ne, ha1, ha2, factorial_cast_real_ne (a - 3)]
    rw [show a - 1 = (a - 3) + 2 by omega, pow_add]
    field_simp [hy_ne]
    rw [show a - 3 + 2 = a - 1 by omega]
    rw [Nat.cast_sub (by omega : 1 ≤ a)]
    ring_nf
  · positivity
  · positivity

/-- Integral form of the Gamma shape shift
`5M * E_a[(1/(6Y))^2 g(Y)] =
  5/(6(a-2)) * E_{a-2}[g(Y)]`.

This is the formal version of the scalar change of Gamma shape used between
the integration-by-parts bracket and Jensen's inequality. -/
theorem fiveM_integral_invSq_mul_gammaFull_eq_tail_prefactor
    {a : Nat} (ha : 150 ≤ a) (g : ℝ → ℝ) :
    (5 * (M a : ℝ)) *
        ∫ y, (1 / (6 * y))^2 * g y ∂ gammaFullMeasure a =
      (5 / (6 * ((a : ℝ) - 2))) *
        ∫ y, g y ∂ gammaTailMeasure a := by
  rw [integral_gammaFullMeasure_eq_integral_Ici_gammaPDF_toReal_smul]
  rw [integral_gammaTailMeasure_eq_integral_Ici_gammaPDF_toReal_smul]
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  rw [← MeasureTheory.integral_const_mul]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hshift := fiveM_gammaPDF_full_mul_invSq_eq_tail_prefactor
    (a := a) ha (Set.mem_Ioi.mp hy)
  simp only [smul_eq_mul]
  calc
    (5 * (M a : ℝ)) *
        ((ProbabilityTheory.gammaPDF (a : ℝ) 1 y).toReal *
          ((1 / (6 * y))^2 * g y))
        =
      ((5 * (M a : ℝ)) *
        ((ProbabilityTheory.gammaPDF (a : ℝ) 1 y).toReal *
          (1 / (6 * y))^2)) * g y := by ring
    _ =
      ((5 / (6 * ((a : ℝ) - 2))) *
        (ProbabilityTheory.gammaPDF (((a - 2 : Nat) : ℝ)) 1 y).toReal) *
          g y := by rw [hshift]
    _ =
      (5 / (6 * ((a : ℝ) - 2))) *
        ((ProbabilityTheory.gammaPDF (((a - 2 : Nat) : ℝ)) 1 y).toReal *
          g y) := by ring

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

theorem integral_invPow_gammaFullMeasure_eq_gammaMonomialMoment
    {a r : Nat} (ha : 150 ≤ a) (hr : r ≤ printedTailP a + 1) :
    (∫ y, (1 / (6 * y))^r ∂ gammaFullMeasure a) =
      gammaMonomialMoment a r := by
  rw [gammaFullMeasure_eq_gammaTailMeasure_add_two]
  have hA : 150 ≤ a + 2 := by omega
  have hrA : r ≤ printedTailP (a + 2) := by
    unfold printedTailP at hr ⊢
    omega
  have h := integral_invPow_gammaTailMeasure_eq_gammaMonomialMoment
    (a := a + 2) (r := r) hA hrA
  simpa [show a + 2 - 2 = a by omega] using h

theorem integrable_invPow_gammaFullMeasure
    {a r : Nat} (ha : 150 ≤ a) (hr : r ≤ printedTailP a + 1) :
    Integrable (fun y : ℝ => (1 / (6 * y))^r) (gammaFullMeasure a) := by
  rw [gammaFullMeasure_eq_gammaTailMeasure_add_two]
  have hA : 150 ≤ a + 2 := by omega
  have hrA : r ≤ printedTailP (a + 2) := by
    unfold printedTailP at hr ⊢
    omega
  exact integrable_invPow_gammaTailMeasure (a := a + 2) (r := r) hA hrA

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

theorem fiveM_integral_invSq_exp_neg_printedTailLGammaArg_gammaFull_eq_tail_prefactor
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a) :
    (5 * (M a : ℝ)) *
        ∫ y, (1 / (6 * y))^2 *
          Real.exp (-(printedTailLGammaArg μ a y)) ∂ gammaFullMeasure a =
      (5 / (6 * ((a : ℝ) - 2))) *
        ∫ y, Real.exp (-(printedTailLGammaArg μ a y)) ∂ gammaTailMeasure a := by
  simpa using
    fiveM_integral_invSq_mul_gammaFull_eq_tail_prefactor
      (a := a) ha
      (fun y => Real.exp (-(printedTailLGammaArg μ a y)))

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

theorem integrable_invPow_mul_exp_neg_printedTailLGammaArg_gammaFull
    {a r : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a))
    (hr : r ≤ printedTailP a + 1) :
    Integrable
      (fun y => (1 / (6 * y))^r *
        Real.exp (-(printedTailLGammaArg μ a y))) (gammaFullMeasure a) := by
  refine (integrable_invPow_gammaFullMeasure
    (a := a) (r := r) ha hr).mono' ?hmeas ?hbound
  · unfold printedTailLGammaArg printedTailLReal
    fun_prop
  · filter_upwards [ae_nonneg_gammaFullMeasure a] with y hy
    have hx : 0 ≤ 1 / (6 * y) := by positivity
    have hpow : 0 ≤ (1 / (6 * y))^r := pow_nonneg hx r
    have hexp_le := real_exp_neg_printedTailLReal_le_one
      (a := a) (μ := μ) hμ hx
    have hprod_nonneg :
        0 ≤ (1 / (6 * y))^r *
          Real.exp (-(printedTailLGammaArg μ a y)) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hprod_nonneg]
    exact mul_le_of_le_one_right hpow hexp_le

theorem integrable_fiveM_invSq_exp_neg_printedTailLGammaArg_gammaFull
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    Integrable
      (fun y => (5 * (M a : ℝ)) *
        ((1 / (6 * y))^2 *
          Real.exp (-(printedTailLGammaArg μ a y)))) (gammaFullMeasure a) := by
  exact (integrable_invPow_mul_exp_neg_printedTailLGammaArg_gammaFull
    (a := a) (r := 2) (μ := μ) ha hμ (by
      unfold printedTailP
      omega)).const_mul _

theorem integrable_exp_neg_mul_gammaLowBracketAlignedReal_gammaFull
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    Integrable
      (fun y => Real.exp (-(printedTailLGammaArg μ a y)) *
        gammaLowBracketAlignedReal μ a (1 / (6 * y))) (gammaFullMeasure a) := by
  let E : ℝ → ℝ := fun y => Real.exp (-(printedTailLGammaArg μ a y))
  have hlin :
      Integrable
        (fun y => E y *
          (((M a : ℝ) - (kCoeff μ 1 : ℝ)) * (1 / (6 * y))))
        (gammaFullMeasure a) := by
    have hbase := integrable_invPow_mul_exp_neg_printedTailLGammaArg_gammaFull
      (a := a) (r := 1) (μ := μ) ha hμ (by
        unfold printedTailP
        omega)
    simpa [E, pow_one, mul_assoc, mul_comm, mul_left_comm] using
      hbase.const_mul ((M a : ℝ) - (kCoeff μ 1 : ℝ))
  have hsumF :
      Integrable
        (fun y => E y *
          (∑ j ∈ Finset.Ico 1 (printedTailP a + 1),
            6 * (j : ℝ) * (hCoeff μ j : ℝ) * (1 / (6 * y))^(j + 1)))
        (gammaFullMeasure a) := by
    have hsum :
        Integrable
          (fun y => ∑ j ∈ Finset.Ico 1 (printedTailP a + 1),
            E y * (6 * (j : ℝ) * (hCoeff μ j : ℝ) *
              (1 / (6 * y))^(j + 1))) (gammaFullMeasure a) := by
      refine MeasureTheory.integrable_finset_sum _ ?_
      intro j hj
      have hr : j + 1 ≤ printedTailP a + 1 := (Finset.mem_Ico.mp hj).2
      have hbase := integrable_invPow_mul_exp_neg_printedTailLGammaArg_gammaFull
        (a := a) (r := j + 1) (μ := μ) ha hμ hr
      simpa [E, mul_assoc, mul_comm, mul_left_comm] using
        hbase.const_mul (6 * (j : ℝ) * (hCoeff μ j : ℝ))
    simpa [Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using hsum
  have hsumG :
      Integrable
        (fun y => E y *
          (∑ j ∈ Finset.Ico 1 (printedTailP a),
            (kCoeff μ (j + 1) : ℝ) * (1 / (6 * y))^(j + 1)))
        (gammaFullMeasure a) := by
    have hsum :
        Integrable
          (fun y => ∑ j ∈ Finset.Ico 1 (printedTailP a),
            E y * ((kCoeff μ (j + 1) : ℝ) *
              (1 / (6 * y))^(j + 1))) (gammaFullMeasure a) := by
      refine MeasureTheory.integrable_finset_sum _ ?_
      intro j hj
      have hr : j + 1 ≤ printedTailP a + 1 := by
        have hjlt : j < printedTailP a := (Finset.mem_Ico.mp hj).2
        omega
      have hbase := integrable_invPow_mul_exp_neg_printedTailLGammaArg_gammaFull
        (a := a) (r := j + 1) (μ := μ) ha hμ hr
      simpa [E, mul_assoc, mul_comm, mul_left_comm] using
        hbase.const_mul (kCoeff μ (j + 1) : ℝ)
    simpa [Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using hsum
  simpa [gammaLowBracketAlignedReal, E, mul_add, mul_sub, Finset.mul_sum,
    mul_assoc, mul_comm, mul_left_comm] using (hlin.add hsumF).sub hsumG

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

/-- Jensen lower bound transported back to the shape-`a` Gamma expectation
with the two retained powers of `1/(6Y)`. -/
theorem fiveM_integral_invSq_exp_neg_printedTailLGammaArg_gammaFull_lower
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    9 / (40 * ((a : ℝ) - 2)) ≤
      (5 * (M a : ℝ)) *
        ∫ y, (1 / (6 * y))^2 *
          Real.exp (-(printedTailLGammaArg μ a y)) ∂ gammaFullMeasure a := by
  rw [fiveM_integral_invSq_exp_neg_printedTailLGammaArg_gammaFull_eq_tail_prefactor
    (a := a) (μ := μ) ha]
  exact gammaTailPrefactor_integral_exp_neg_printedTailLGammaArg_lower
    (a := a) (μ := μ) ha hμ

/-- Integrated retained-bracket lower bound, with integrability kept explicit.
The remaining analytic work is to identify the integral of this bracket with
the Gamma expectation of `W` and then compare that expectation to the finite
coefficient sum. -/
theorem gammaLowBracketAlignedIntegral_lower_of_integrable
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a))
    (hleft : Integrable
      (fun y => (5 * (M a : ℝ)) *
        ((1 / (6 * y))^2 *
          Real.exp (-(printedTailLGammaArg μ a y)))) (gammaFullMeasure a))
    (hright : Integrable
      (fun y => Real.exp (-(printedTailLGammaArg μ a y)) *
        gammaLowBracketAlignedReal μ a (1 / (6 * y))) (gammaFullMeasure a)) :
    9 / (40 * ((a : ℝ) - 2)) ≤
      ∫ y, Real.exp (-(printedTailLGammaArg μ a y)) *
        gammaLowBracketAlignedReal μ a (1 / (6 * y)) ∂ gammaFullMeasure a := by
  have hJ :=
    fiveM_integral_invSq_exp_neg_printedTailLGammaArg_gammaFull_lower
      (a := a) (μ := μ) ha hμ
  have hleft_int :
      (∫ y, (5 * (M a : ℝ)) *
        ((1 / (6 * y))^2 *
          Real.exp (-(printedTailLGammaArg μ a y))) ∂ gammaFullMeasure a) =
        (5 * (M a : ℝ)) *
          ∫ y, (1 / (6 * y))^2 *
            Real.exp (-(printedTailLGammaArg μ a y)) ∂ gammaFullMeasure a := by
    rw [MeasureTheory.integral_const_mul]
  rw [← hleft_int] at hJ
  have hmono :
      (∫ y, (5 * (M a : ℝ)) *
        ((1 / (6 * y))^2 *
          Real.exp (-(printedTailLGammaArg μ a y))) ∂ gammaFullMeasure a) ≤
      ∫ y, Real.exp (-(printedTailLGammaArg μ a y)) *
        gammaLowBracketAlignedReal μ a (1 / (6 * y)) ∂ gammaFullMeasure a := by
    refine MeasureTheory.integral_mono_ae hleft hright ?_
    filter_upwards [ae_nonneg_gammaFullMeasure a] with y hy
    have hx : 0 ≤ 1 / (6 * y) := by positivity
    have hb := fiveM_x2_le_gammaLowBracketAlignedReal
      (a := a) (μ := μ) ha hμ hx
    have hexp_nonneg :
        0 ≤ Real.exp (-(printedTailLGammaArg μ a y)) := by positivity
    calc
      (5 * (M a : ℝ)) *
          ((1 / (6 * y))^2 *
            Real.exp (-(printedTailLGammaArg μ a y)))
          =
        Real.exp (-(printedTailLGammaArg μ a y)) *
          (5 * (M a : ℝ) * (1 / (6 * y))^2) := by ring
      _ ≤ Real.exp (-(printedTailLGammaArg μ a y)) *
            gammaLowBracketAlignedReal μ a (1 / (6 * y)) :=
          mul_le_mul_of_nonneg_left hb hexp_nonneg
  exact hJ.trans hmono

/-- Closed integrated retained-bracket lower bound. -/
theorem gammaLowBracketAlignedIntegral_lower
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    9 / (40 * ((a : ℝ) - 2)) ≤
      ∫ y, Real.exp (-(printedTailLGammaArg μ a y)) *
        gammaLowBracketAlignedReal μ a (1 / (6 * y)) ∂ gammaFullMeasure a :=
  gammaLowBracketAlignedIntegral_lower_of_integrable
    (a := a) (μ := μ) ha hμ
    (integrable_fiveM_invSq_exp_neg_printedTailLGammaArg_gammaFull
      (a := a) (μ := μ) ha hμ)
    (integrable_exp_neg_mul_gammaLowBracketAlignedReal_gammaFull
      (a := a) (μ := μ) ha hμ)

end Prop52
