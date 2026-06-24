/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Gamma lower-tail estimates for the Proposition 5.2 truncation

This file records the small Chernoff/Markov estimates used in the
Taylor--Gamma truncation comparison.  They are kept separate from
`GammaMeasure.lean` so the existing Gamma-integral bridge remains stable.
-/

import Prop52.GammaMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace Prop52

open MeasureTheory Set
open scoped ENNReal

/-- The exponential tilt used in the Chernoff estimates is integrable under
the integer-shape Gamma law. -/
theorem integrable_exp_neg_mul_gammaFullMeasure
    {b : Nat} (hb : 1 ≤ b) {u : ℝ} (hu : 0 < u) :
    Integrable (fun y : ℝ => Real.exp (-(u * y))) (gammaFullMeasure b) := by
  have hb_pos : (0 : ℝ) < b := by exact_mod_cast hb
  haveI : IsProbabilityMeasure (gammaFullMeasure b) := by
    unfold gammaFullMeasure
    exact ProbabilityTheory.isProbabilityMeasure_gammaMeasure hb_pos (by norm_num)
  refine Integrable.of_mem_Icc (μ := gammaFullMeasure b) 0 1 ?hmeas ?hbounds
  · fun_prop
  · filter_upwards [ae_nonneg_gammaFullMeasure b] with y hy
    constructor
    · exact (Real.exp_pos _).le
    · exact Real.exp_le_one_iff.mpr (by nlinarith)

/-- Laplace transform of the integer-shape Gamma law used by the truncation
tail estimates. -/
theorem integral_exp_neg_mul_gammaFullMeasure_eq
    {b : Nat} (hb : 1 ≤ b) {u : ℝ} (hu : 0 < u) :
    (∫ y : ℝ, Real.exp (-(u * y)) ∂ gammaFullMeasure b) =
      (1 / (1 + u))^b := by
  have hb_pos : (0 : ℝ) < b := by exact_mod_cast hb
  have hu1_pos : (0 : ℝ) < 1 + u := by linarith
  have hGamma_ne : Real.Gamma (b : ℝ) ≠ 0 :=
    (Real.Gamma_pos_of_pos hb_pos).ne'
  have hGamma_eq :
      Real.Gamma (b : ℝ) = (((b - 1).factorial : Nat) : ℝ) := by
    rw [show (b : ℝ) = ((b - 1 : Nat) : ℝ) + 1 by
      rw [show b = (b - 1) + 1 by omega]
      norm_num]
    exact Real.Gamma_nat_eq_factorial (b - 1)
  calc
    (∫ y : ℝ, Real.exp (-(u * y)) ∂ gammaFullMeasure b)
        =
      ∫ y : ℝ in Set.Ioi 0,
        (ProbabilityTheory.gammaPDF (b : ℝ) 1 y).toReal *
          Real.exp (-(u * y)) := by
        rw [integral_gammaFullMeasure_eq_integral_Ici_gammaPDF_toReal_smul]
        rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
        rfl
    _ =
      ∫ y : ℝ in Set.Ioi 0,
        (1 / Real.Gamma (b : ℝ)) *
          (y ^ ((b : ℝ) - 1) * Real.exp (-((1 + u) * y))) := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
        have hy_nonneg : 0 ≤ y := (Set.mem_Ioi.mp hy).le
        rw [ProbabilityTheory.gammaPDF_of_nonneg hy_nonneg]
        rw [ENNReal.toReal_ofReal]
        · simp only [Real.one_rpow, one_div, one_mul]
          have hexp :
              Real.exp (-y) * Real.exp (-(u * y)) =
                Real.exp (-((1 + u) * y)) := by
            rw [← Real.exp_add]
            congr 1
            ring
          calc
            (Real.Gamma (b : ℝ))⁻¹ * y ^ ((b : ℝ) - 1) *
                Real.exp (-y) * Real.exp (-(u * y))
                =
              (Real.Gamma (b : ℝ))⁻¹ * y ^ ((b : ℝ) - 1) *
                (Real.exp (-y) * Real.exp (-(u * y))) := by ring
            _ =
              (Real.Gamma (b : ℝ))⁻¹ *
                (y ^ ((b : ℝ) - 1) * Real.exp (-((1 + u) * y))) := by
              rw [hexp]
              ring
        · positivity
    _ =
      (1 / Real.Gamma (b : ℝ)) *
        ∫ y : ℝ in Set.Ioi 0,
          y ^ ((b : ℝ) - 1) * Real.exp (-((1 + u) * y)) := by
        rw [MeasureTheory.integral_const_mul]
    _ =
      (1 / Real.Gamma (b : ℝ)) *
        ((1 / (1 + u))^(b : ℝ) * Real.Gamma (b : ℝ)) := by
        rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hb_pos hu1_pos]
    _ = (1 / (1 + u))^b := by
        rw [Real.rpow_natCast]
        field_simp [hGamma_ne]

/-- `lintegral` form of the same Laplace transform, convenient for Markov's
inequality. -/
theorem lintegral_exp_neg_mul_gammaFullMeasure_eq
    {b : Nat} (hb : 1 ≤ b) {u : ℝ} (hu : 0 < u) :
    (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-(u * y))) ∂ gammaFullMeasure b) =
      ENNReal.ofReal ((1 / (1 + u))^b) := by
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (integrable_exp_neg_mul_gammaFullMeasure (b := b) hb hu)
    (ae_of_all _ fun y => (Real.exp_pos (-(u * y))).le)]
  rw [integral_exp_neg_mul_gammaFullMeasure_eq (b := b) hb hu]

/-- Chernoff/Markov lower-tail estimate for an integer-shape Gamma law. -/
theorem gammaFullMeasure_Iic_le_chernoff
    {b : Nat} (hb : 1 ≤ b) {u c : ℝ} (hu : 0 < u) :
    gammaFullMeasure b (Set.Iic c) ≤
      ENNReal.ofReal (Real.exp (u * c) * (1 / (1 + u))^b) := by
  let f : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (-(u * y)))
  let eps : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(u * c)))
  have hf : AEMeasurable f (gammaFullMeasure b) := by
    dsimp [f]
    fun_prop
  have heps_ne_zero : eps ≠ 0 := by
    dsimp [eps]
    simp [Real.exp_pos]
  have heps_ne_top : eps ≠ ∞ := by
    dsimp [eps]
    simp
  have hmarkov :=
    MeasureTheory.meas_ge_le_lintegral_div (μ := gammaFullMeasure b)
      (f := f) hf heps_ne_zero heps_ne_top
  have hset : {y : ℝ | eps ≤ f y} = Set.Iic c := by
    ext y
    dsimp [eps, f]
    rw [ENNReal.ofReal_le_ofReal_iff (Real.exp_pos (-(u * y))).le]
    rw [Real.exp_le_exp]
    constructor <;> intro h
    · change y ≤ c
      nlinarith
    · change y ≤ c at h
      nlinarith
  have hdiv :
      ENNReal.ofReal ((1 / (1 + u))^b) / eps =
        ENNReal.ofReal (Real.exp (u * c) * (1 / (1 + u))^b) := by
    dsimp [eps]
    rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos (-(u * c)))]
    congr 1
    rw [Real.exp_neg]
    field_simp [ne_of_gt (Real.exp_pos (u * c))]
  calc
    gammaFullMeasure b (Set.Iic c)
        ≤ (∫⁻ y : ℝ, f y ∂ gammaFullMeasure b) / eps := by
          simpa [hset] using hmarkov
    _ = ENNReal.ofReal ((1 / (1 + u))^b) / eps := by
          rw [lintegral_exp_neg_mul_gammaFullMeasure_eq (b := b) hb hu]
    _ = ENNReal.ofReal
          (Real.exp (u * c) * (1 / (1 + u))^b) := hdiv

/-- The lower-tail estimate used for the `W` term in the truncation split:
`P(X < a/2) <= (5/6)^a` for `X ~ Gamma(a,1)`. -/
theorem gammaFullMeasure_Iio_half_le_five_six_pow
    {a : Nat} (ha : 1 ≤ a) :
    gammaFullMeasure a (Set.Iio ((a : ℝ) / 2)) ≤
      ENNReal.ofReal ((5 / 6 : ℝ)^a) := by
  have hsubset :
      Set.Iio ((a : ℝ) / 2) ⊆ Set.Iic ((a : ℝ) / 2) := by
    intro y hy
    exact le_of_lt (Set.mem_Iio.mp hy)
  have hchernoff :=
    gammaFullMeasure_Iic_le_chernoff
      (b := a) ha (u := (1 : ℝ)) (c := (a : ℝ) / 2) (by norm_num)
  have hbase :
      Real.exp (1 / 2 : ℝ) * (1 / 2 : ℝ) ≤ 5 / 6 := by
    nlinarith [real_exp_one_half_lt_five_thirds]
  have hreal :
      Real.exp ((1 : ℝ) * ((a : ℝ) / 2)) *
          (1 / (1 + (1 : ℝ)))^a ≤
        (5 / 6 : ℝ)^a := by
    rw [one_mul]
    rw [show (a : ℝ) / 2 = (a : ℝ) * (1 / 2 : ℝ) by ring]
    rw [Real.exp_nat_mul]
    norm_num
    calc
      Real.exp (1 / 2 : ℝ)^a * (1 / 2 : ℝ)^a
          = (Real.exp (1 / 2 : ℝ) * (1 / 2 : ℝ))^a := by
            rw [mul_pow]
      _ ≤ (5 / 6 : ℝ)^a :=
            pow_le_pow_left₀ (by positivity) hbase a
  exact (measure_mono hsubset).trans
    (hchernoff.trans (ENNReal.ofReal_le_ofReal hreal))

/-- Standard lambda-form Chernoff lower-tail bound for an integer-shape Gamma
law, obtained from the general Markov estimate with
`u = 1 / lambda - 1`. -/
theorem gammaFullMeasure_Iic_lambda_mul_shape_le
    {b : Nat} (hb : 1 ≤ b) {lambda : ℝ}
    (hlambda_pos : 0 < lambda) (hlambda_lt_one : lambda < 1) :
    gammaFullMeasure b (Set.Iic (lambda * (b : ℝ))) ≤
      ENNReal.ofReal ((lambda * Real.exp (1 - lambda))^b) := by
  let u : ℝ := 1 / lambda - 1
  have hu : 0 < u := by
    dsimp [u]
    have hlt : 1 < 1 / lambda := by
      rw [lt_div_iff₀ hlambda_pos]
      nlinarith
    linarith
  have hchernoff :=
    gammaFullMeasure_Iic_le_chernoff
      (b := b) hb (u := u) (c := lambda * (b : ℝ)) hu
  have hlambda_ne : lambda ≠ 0 := ne_of_gt hlambda_pos
  have hreal :
      Real.exp (u * (lambda * (b : ℝ))) *
          (1 / (1 + u))^b =
        (lambda * Real.exp (1 - lambda))^b := by
    have h1u : 1 + u = 1 / lambda := by
      dsimp [u]
      ring
    rw [h1u]
    have hbase : 1 / (1 / lambda) = lambda := by
      field_simp [hlambda_ne]
    rw [hbase]
    have huc :
        u * (lambda * (b : ℝ)) = (b : ℝ) * (1 - lambda) := by
      dsimp [u]
      field_simp [hlambda_ne]
    rw [huc]
    rw [Real.exp_nat_mul]
    rw [mul_pow]
    ring
  calc
    gammaFullMeasure b (Set.Iic (lambda * (b : ℝ)))
        ≤ ENNReal.ofReal
            (Real.exp (u * (lambda * (b : ℝ))) *
              (1 / (1 + u))^b) := hchernoff
    _ = ENNReal.ofReal ((lambda * Real.exp (1 - lambda))^b) := by
          rw [hreal]

end Prop52
