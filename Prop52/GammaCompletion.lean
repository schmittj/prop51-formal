/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Completion bridge for the Proposition 5.2 Gamma tail

This file isolates the remaining Taylor--Gamma truncation theorem.  The
Gamma integration-by-parts lower bound is closed in `GammaIBP.lean`, and the
finite residue arithmetic is closed in `GammaTruncation.lean`.  What remains
is the analytic comparison between the untruncated Gamma expectation and the
finite Taylor-Gamma sum.  We keep that comparison as one explicit interface
so the public theorem surface does not obscure the only open analytic point.
-/

import Prop52.GammaIBP

namespace Prop52

open MeasureTheory
open scoped ENNReal

/-- The untruncated Gamma integrand
`W(t_Y)=exp(-L(t_Y))(1-J(t_Y))`, with `t_Y=1/(6Y)`. -/
noncomputable def printedTailWGammaIntegrand
    (μ : List Nat) (a : Nat) (y : ℝ) : ℝ :=
  Real.exp (-(printedTailLGammaArg μ a y)) *
    (1 - printedTailJReal μ a (1 / (6 * y)))

/-- The untruncated Gamma expectation
`E[exp(-L(t_X)) (1 - J(t_X))]` used in the integration-by-parts margin. -/
noncomputable def printedTailWGammaIntegral (μ : List Nat) (a : Nat) : ℝ :=
  ∫ y, printedTailWGammaIntegrand μ a y ∂ gammaFullMeasure a

/-- The finite Taylor-Gamma sum, written as the corresponding Gamma
expectation before applying `integral_printedTailWTruncReal_R0_eq_mainSum`. -/
noncomputable def printedTailWTruncGammaIntegral
    (μ : List Nat) (a : Nat) : ℝ :=
  ∫ y, printedTailWTruncReal μ a (printedTailR0 a) y ∂ gammaFullMeasure a

/-- Remaining Taylor--Gamma truncation estimate.

This is the formal version of the absolute-error statement
`|E W(t_X) - sum_{s<=r0} gamma_s omega_s| <= residue pieces`.  The existing
Lean code already proves that these residue pieces fit under the displayed
`truncationResidueRhs`; the missing work is the analytic event split proving
this inequality itself.
-/
def PrintedTailGammaTruncationErrorBound : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      |printedTailWGammaIntegral μ a -
          printedTailWTruncGammaIntegral μ a| ≤
        (truncationResiduePiecesLhs μ a : ℝ)

/-- Paper-shaped Taylor--Gamma truncation estimate.

This is weaker than `PrintedTailGammaTruncationErrorBound`: the finite residue
pieces have already been absorbed into the displayed closed budget
`truncationResidueRhs`.  It matches the final form of the printed
Taylor--Gamma truncation lemma and is the cleaner public interface for the
remaining analytic tail theorem. -/
def PrintedTailGammaTruncationResidueBound : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      |printedTailWGammaIntegral μ a -
          printedTailWTruncGammaIntegral μ a| ≤
        (truncationResidueRhs a : ℝ)

/-- Sharper remaining analytic target for the Taylor--Gamma truncation.

The lower event and finite Gamma moment pieces are now proved in Lean.  The
remaining issue is the upper-event analytic Taylor control of the full function
`W`, bounded by the first residue piece.  This formulation intentionally does
not replace the printed proof by a different estimate: it isolates exactly the
coefficient-tail bound which still needs the full analytic `\widehat W`
argument rather than only the finite-prefix certificates. -/
def PrintedTailUpperEventTruncationBound : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      (∫ y in Set.Ici ((a : ℝ) / 2),
          |printedTailWGammaIntegrand μ a y -
            printedTailWTruncReal μ a (printedTailR0 a) y|
            ∂ gammaFullMeasure a) ≤
        ((∑ s ∈ (Finset.range (a + 1)).filter
            (fun s : Nat => printedTailR0 a + 1 ≤ s),
            printedTailWAbsCoeff μ a s * (printedTailX1 a)^s : ℚ) : ℝ)

/-- Paper-shaped upper-event Taylor bound.

On the event `Y >= a/2`, the paper uses `t_Y <= x₁ = x₂/2` and the full
analytic majorant `\widehat W(x₂) <= 920` to bound the whole Taylor tail by
`920 / 2^(r0+1)`.  The finite-window version above is a useful internal
auxiliary, but this is the statement matching the printed truncation lemma. -/
def PrintedTailUpperEventResidueBound : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      (∫ y in Set.Ici ((a : ℝ) / 2),
          |printedTailWGammaIntegrand μ a y -
            printedTailWTruncReal μ a (printedTailR0 a) y|
            ∂ gammaFullMeasure a) ≤
        ((920 / (2 : ℚ)^(printedTailR0 a + 1) : ℚ) : ℝ)

/-- Pointwise form of the paper-shaped upper-event Taylor bound.

This is the real analytic estimate left by the printed proof: on the upper
event `Y >= a/2`, equivalently `t_Y <= x₁`, the full Taylor tail of
`W(t)=exp(-L(t))(1-J(t))` after `r0` is bounded by
`920 / 2^(r0+1)`.  The following theorem turns this pointwise statement into
the integrated upper-event interface using only that `gammaFullMeasure` is a
probability measure. -/
def PrintedTailUpperEventPointwiseResidueBound : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      ∀ y : ℝ, (a : ℝ) / 2 ≤ y →
        |printedTailWGammaIntegrand μ a y -
          printedTailWTruncReal μ a (printedTailR0 a) y| ≤
        ((920 / (2 : ℚ)^(printedTailR0 a + 1) : ℚ) : ℝ)

/-- Pure real-variable form of the remaining Taylor tail.

This is the analytic core with all Gamma-measure bookkeeping removed.  It
states that the Taylor tail of
`t ↦ exp(-L(t)) * (1 - J(t))` after `r0` is bounded on the interval
`0 <= t <= x1`. -/
def PrintedTailWRealTailResidueBound : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      ∀ t : ℝ, 0 ≤ t → t ≤ (printedTailX1 a : ℝ) →
        |Real.exp (-(printedTailLReal μ a t)) *
            (1 - printedTailJReal μ a t) -
          (∑ s ∈ Finset.range (printedTailR0 a + 1),
            (printedTailOmegaCoeff μ a s : ℝ) * t^s)| ≤
        ((920 / (2 : ℚ)^(printedTailR0 a + 1) : ℚ) : ℝ)

theorem printedTailUpperEventPointwiseResidueBound_of_realTail
    (htail : PrintedTailWRealTailResidueBound) :
    PrintedTailUpperEventPointwiseResidueBound := by
  intro a ha μ hμ y hy
  have ha_pos : (0 : ℝ) < a := by
    exact_mod_cast (by omega : 0 < a)
  have hy_pos : 0 < y := by nlinarith
  have ht_nonneg : 0 ≤ 1 / (6 * y) := by positivity
  have ht_le : 1 / (6 * y) ≤ (printedTailX1 a : ℝ) := by
    have hden_pos : 0 < 3 * (a : ℝ) := by nlinarith
    have hden_le : 3 * (a : ℝ) ≤ 6 * y := by nlinarith
    have hx1_cast : (printedTailX1 a : ℝ) = 1 / (3 * (a : ℝ)) := by
      unfold printedTailX1
      norm_num
    rw [hx1_cast]
    exact one_div_le_one_div_of_le hden_pos hden_le
  simpa [printedTailWGammaIntegrand, printedTailLGammaArg,
    printedTailWTruncReal] using
    htail a ha μ hμ (1 / (6 * y)) ht_nonneg ht_le

theorem printedTailUpperEventResidueBound_of_pointwise
    (hpoint : PrintedTailUpperEventPointwiseResidueBound) :
    PrintedTailUpperEventResidueBound := by
  intro a ha μ hμ
  let S : Set ℝ := Set.Ici ((a : ℝ) / 2)
  let W : ℝ → ℝ := printedTailWGammaIntegrand μ a
  let P : ℝ → ℝ := printedTailWTruncReal μ a (printedTailR0 a)
  let C : ℝ := ((920 / (2 : ℚ)^(printedTailR0 a + 1) : ℚ) : ℝ)
  haveI : IsProbabilityMeasure (gammaFullMeasure a) := by
    unfold gammaFullMeasure
    exact ProbabilityTheory.isProbabilityMeasure_gammaMeasure
      (by exact_mod_cast (by omega : 0 < a)) (by norm_num)
  have hfinite : gammaFullMeasure a S ≠ ⊤ := measure_ne_top _ _
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hW_bound :
      ∀ᵐ y ∂ gammaFullMeasure a, ‖W y‖ ≤ (2 : ℝ) := by
    filter_upwards [ae_nonneg_gammaFullMeasure a] with y hy_nonneg
    have hx : 0 ≤ 1 / (6 * y) := by positivity
    simpa [W, printedTailWGammaIntegrand, printedTailLGammaArg, Real.norm_eq_abs]
      using abs_exp_neg_L_mul_one_sub_JReal_le_two
        (a := a) (μ := μ) hμ (x := 1 / (6 * y)) hx
  have hW_int : Integrable W (gammaFullMeasure a) := by
    refine Integrable.of_bound ?_ 2 hW_bound
    dsimp [W]
    unfold printedTailWGammaIntegrand printedTailLGammaArg
      printedTailLReal printedTailJReal
    fun_prop
  have hRle : printedTailR0 a ≤ printedTailP a + 1 := by
    unfold printedTailR0 printedTailP
    omega
  have hP_int : Integrable P (gammaFullMeasure a) := by
    dsimp [P]
    exact integrable_printedTailWTruncReal
      (a := a) (R := printedTailR0 a) (μ := μ) ha hRle
  have hleft_int :
      IntegrableOn (fun y => |W y - P y|) S (gammaFullMeasure a) :=
    (hW_int.sub hP_int).abs.integrableOn
  have hright_int :
      IntegrableOn (fun _ : ℝ => C) S (gammaFullMeasure a) :=
    integrableOn_const hfinite
  have hmono_restrict :
      (fun y => |W y - P y|) ≤ᵐ[(gammaFullMeasure a).restrict S]
        fun _ : ℝ => C := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy
    simpa [S, W, P, C] using hpoint a ha μ hμ y hy
  have hmeasure_le_one :
      (gammaFullMeasure a S).toReal ≤ (1 : ℝ) := by
    have hle : gammaFullMeasure a S ≤ (1 : ℝ≥0∞) := by
      calc
        gammaFullMeasure a S ≤ gammaFullMeasure a Set.univ :=
          measure_mono (Set.subset_univ S)
        _ = 1 := by simp
    simpa using ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ∞) hle
  calc
    (∫ y in Set.Ici ((a : ℝ) / 2),
        |printedTailWGammaIntegrand μ a y -
          printedTailWTruncReal μ a (printedTailR0 a) y|
          ∂ gammaFullMeasure a)
        =
      ∫ y in S, |W y - P y| ∂ gammaFullMeasure a := rfl
    _ ≤ ∫ y in S, C ∂ gammaFullMeasure a :=
      MeasureTheory.setIntegral_mono_ae_restrict
        hleft_int hright_int hmono_restrict
    _ = (gammaFullMeasure a S).toReal * C := by
      rw [MeasureTheory.setIntegral_const (μ := gammaFullMeasure a)
        (s := S) (c := C)]
      simp [MeasureTheory.measureReal_def, smul_eq_mul]
    _ ≤ 1 * C := by
      exact mul_le_mul_of_nonneg_right hmeasure_le_one hC_nonneg
    _ = ((920 / (2 : ℚ)^(printedTailR0 a + 1) : ℚ) : ℝ) := by
      simp [C]

theorem printedTailUpperEventResidueBound_of_realTail
    (htail : PrintedTailWRealTailResidueBound) :
    PrintedTailUpperEventResidueBound :=
  printedTailUpperEventResidueBound_of_pointwise
    (printedTailUpperEventPointwiseResidueBound_of_realTail htail)

theorem printedTailGammaTruncationErrorBound_of_upperEvent
    (hupper : PrintedTailUpperEventTruncationBound) :
    PrintedTailGammaTruncationErrorBound := by
  intro a ha μ hμ
  let Slo : Set ℝ := Set.Iio ((a : ℝ) / 2)
  let Shi : Set ℝ := Set.Ici ((a : ℝ) / 2)
  let W : ℝ → ℝ := printedTailWGammaIntegrand μ a
  let P : ℝ → ℝ := printedTailWTruncReal μ a (printedTailR0 a)
  haveI : IsProbabilityMeasure (gammaFullMeasure a) := by
    unfold gammaFullMeasure
    exact ProbabilityTheory.isProbabilityMeasure_gammaMeasure
      (by exact_mod_cast (by omega : 0 < a)) (by norm_num)
  have hW_bound :
      ∀ᵐ y ∂ gammaFullMeasure a, ‖W y‖ ≤ (2 : ℝ) := by
    filter_upwards [ae_nonneg_gammaFullMeasure a] with y hy_nonneg
    have hx : 0 ≤ 1 / (6 * y) := by positivity
    simpa [W, printedTailWGammaIntegrand, printedTailLGammaArg, Real.norm_eq_abs]
      using abs_exp_neg_L_mul_one_sub_JReal_le_two
        (a := a) (μ := μ) hμ (x := 1 / (6 * y)) hx
  have hW_int : Integrable W (gammaFullMeasure a) := by
    refine Integrable.of_bound ?_ 2 hW_bound
    dsimp [W]
    unfold printedTailWGammaIntegrand printedTailLGammaArg
      printedTailLReal printedTailJReal
    fun_prop
  have hRle : printedTailR0 a ≤ printedTailP a + 1 := by
    unfold printedTailR0 printedTailP
    omega
  have hP_int : Integrable P (gammaFullMeasure a) := by
    dsimp [P]
    exact integrable_printedTailWTruncReal
      (a := a) (R := printedTailR0 a) (μ := μ) ha hRle
  have hdiff_int : Integrable (fun y => W y - P y) (gammaFullMeasure a) :=
    hW_int.sub hP_int
  have hdiff_abs_int :
      Integrable (fun y => |W y - P y|) (gammaFullMeasure a) :=
    hdiff_int.abs
  have hdiff_eq :
      printedTailWGammaIntegral μ a -
          printedTailWTruncGammaIntegral μ a =
        ∫ y, W y - P y ∂ gammaFullMeasure a := by
    calc
      printedTailWGammaIntegral μ a -
          printedTailWTruncGammaIntegral μ a
          =
        (∫ y, W y ∂ gammaFullMeasure a) -
          ∫ y, P y ∂ gammaFullMeasure a := by
            rfl
      _ = ∫ y, W y - P y ∂ gammaFullMeasure a := by
            rw [MeasureTheory.integral_sub hW_int hP_int]
  have habs_global :
      |printedTailWGammaIntegral μ a -
          printedTailWTruncGammaIntegral μ a| ≤
        ∫ y, |W y - P y| ∂ gammaFullMeasure a := by
    rw [hdiff_eq]
    exact MeasureTheory.abs_integral_le_integral_abs
  have hsplit :
      (∫ y, |W y - P y| ∂ gammaFullMeasure a) =
        (∫ y in Slo, |W y - P y| ∂ gammaFullMeasure a) +
          ∫ y in Shi, |W y - P y| ∂ gammaFullMeasure a := by
    have h :=
      MeasureTheory.integral_add_compl
        (μ := gammaFullMeasure a) (s := Slo)
        (f := fun y => |W y - P y|) measurableSet_Iio hdiff_abs_int
    rw [Set.compl_Iio] at h
    exact h.symm
  have hlower :
      (∫ y in Slo, |W y - P y| ∂ gammaFullMeasure a) ≤
        ((2 * (5 / 6 : ℚ)^a +
          ((∑ s ∈ (Finset.range (printedTailR0 a + 1)).filter
            (fun s : Nat => s ≤ a / 8),
            gammaWeight a s * |printedTailOmegaCoeff μ a s|) *
            (9 / 10 : ℚ)^(a - a / 8) +
          (∑ s ∈ (Finset.range (printedTailR0 a + 1)).filter
            (fun s : Nat => a / 8 + 1 ≤ s),
            gammaWeight a s * |printedTailOmegaCoeff μ a s|)) : ℚ) : ℝ) := by
    simpa [Slo, W, P, printedTailWGammaIntegrand] using
      integral_abs_printedTailWGammaIntegrand_sub_WTruncReal_R0_lower_event_le_residue_terms
        (a := a) ha (μ := μ) hμ
  have hupper' :
      (∫ y in Shi, |W y - P y| ∂ gammaFullMeasure a) ≤
        ((∑ s ∈ (Finset.range (a + 1)).filter
            (fun s : Nat => printedTailR0 a + 1 ≤ s),
            printedTailWAbsCoeff μ a s * (printedTailX1 a)^s : ℚ) : ℝ) := by
    simpa [Shi, W, P] using hupper a ha μ hμ
  calc
    |printedTailWGammaIntegral μ a -
        printedTailWTruncGammaIntegral μ a|
        ≤ ∫ y, |W y - P y| ∂ gammaFullMeasure a := habs_global
    _ =
        (∫ y in Slo, |W y - P y| ∂ gammaFullMeasure a) +
          ∫ y in Shi, |W y - P y| ∂ gammaFullMeasure a := hsplit
    _ ≤
        ((2 * (5 / 6 : ℚ)^a +
          ((∑ s ∈ (Finset.range (printedTailR0 a + 1)).filter
            (fun s : Nat => s ≤ a / 8),
            gammaWeight a s * |printedTailOmegaCoeff μ a s|) *
            (9 / 10 : ℚ)^(a - a / 8) +
          (∑ s ∈ (Finset.range (printedTailR0 a + 1)).filter
            (fun s : Nat => a / 8 + 1 ≤ s),
            gammaWeight a s * |printedTailOmegaCoeff μ a s|)) : ℚ) : ℝ) +
        ((∑ s ∈ (Finset.range (a + 1)).filter
            (fun s : Nat => printedTailR0 a + 1 ≤ s),
            printedTailWAbsCoeff μ a s * (printedTailX1 a)^s : ℚ) : ℝ) :=
          add_le_add hlower hupper'
    _ = (truncationResiduePiecesLhs μ a : ℝ) := by
          unfold truncationResiduePiecesLhs
          norm_num
          ring

/-- The exact finite-piece truncation estimate also implies the paper-shaped
residue estimate after the closed rational residue budget is applied. -/
theorem printedTailGammaTruncationResidueBound_of_truncationError
    (htrunc : PrintedTailGammaTruncationErrorBound) :
    PrintedTailGammaTruncationResidueBound := by
  intro a ha μ hμ
  have herr := htrunc a ha μ hμ
  have hresQ := truncationResiduePiecesLhs_le_truncationResidueRhs
    printedTailWPointBoundX2_closed
    (printedTailAbsoluteMomentBounds_of_majorant
      (printedTailMajorantMomentBounds_of_wPointMomentBounds
        printedTailWPointMomentBounds_closed))
    (a := a) ha (μ := μ) hμ
  have hresR :
      (truncationResiduePiecesLhs μ a : ℝ) ≤
        (truncationResidueRhs a : ℝ) := by
    exact_mod_cast hresQ
  exact herr.trans hresR

/-- The paper-shaped upper-event estimate implies the paper-shaped
Taylor--Gamma truncation estimate.  The lower-event integral and the two
finite Gamma-moment residue estimates are already closed in Lean; the only
input here is the full analytic Taylor tail on `Y >= a/2`. -/
theorem printedTailGammaTruncationResidueBound_of_upperEvent
    (hupper : PrintedTailUpperEventResidueBound) :
    PrintedTailGammaTruncationResidueBound := by
  intro a ha μ hμ
  let Slo : Set ℝ := Set.Iio ((a : ℝ) / 2)
  let Shi : Set ℝ := Set.Ici ((a : ℝ) / 2)
  let W : ℝ → ℝ := printedTailWGammaIntegrand μ a
  let P : ℝ → ℝ := printedTailWTruncReal μ a (printedTailR0 a)
  haveI : IsProbabilityMeasure (gammaFullMeasure a) := by
    unfold gammaFullMeasure
    exact ProbabilityTheory.isProbabilityMeasure_gammaMeasure
      (by exact_mod_cast (by omega : 0 < a)) (by norm_num)
  have hW_bound :
      ∀ᵐ y ∂ gammaFullMeasure a, ‖W y‖ ≤ (2 : ℝ) := by
    filter_upwards [ae_nonneg_gammaFullMeasure a] with y hy_nonneg
    have hx : 0 ≤ 1 / (6 * y) := by positivity
    simpa [W, printedTailWGammaIntegrand, printedTailLGammaArg, Real.norm_eq_abs]
      using abs_exp_neg_L_mul_one_sub_JReal_le_two
        (a := a) (μ := μ) hμ (x := 1 / (6 * y)) hx
  have hW_int : Integrable W (gammaFullMeasure a) := by
    refine Integrable.of_bound ?_ 2 hW_bound
    dsimp [W]
    unfold printedTailWGammaIntegrand printedTailLGammaArg
      printedTailLReal printedTailJReal
    fun_prop
  have hRle : printedTailR0 a ≤ printedTailP a + 1 := by
    unfold printedTailR0 printedTailP
    omega
  have hP_int : Integrable P (gammaFullMeasure a) := by
    dsimp [P]
    exact integrable_printedTailWTruncReal
      (a := a) (R := printedTailR0 a) (μ := μ) ha hRle
  have hdiff_int : Integrable (fun y => W y - P y) (gammaFullMeasure a) :=
    hW_int.sub hP_int
  have hdiff_abs_int :
      Integrable (fun y => |W y - P y|) (gammaFullMeasure a) :=
    hdiff_int.abs
  have hdiff_eq :
      printedTailWGammaIntegral μ a -
          printedTailWTruncGammaIntegral μ a =
        ∫ y, W y - P y ∂ gammaFullMeasure a := by
    calc
      printedTailWGammaIntegral μ a -
          printedTailWTruncGammaIntegral μ a
          =
        (∫ y, W y ∂ gammaFullMeasure a) -
          ∫ y, P y ∂ gammaFullMeasure a := by
            rfl
      _ = ∫ y, W y - P y ∂ gammaFullMeasure a := by
            rw [MeasureTheory.integral_sub hW_int hP_int]
  have habs_global :
      |printedTailWGammaIntegral μ a -
          printedTailWTruncGammaIntegral μ a| ≤
        ∫ y, |W y - P y| ∂ gammaFullMeasure a := by
    rw [hdiff_eq]
    exact MeasureTheory.abs_integral_le_integral_abs
  have hsplit :
      (∫ y, |W y - P y| ∂ gammaFullMeasure a) =
        (∫ y in Slo, |W y - P y| ∂ gammaFullMeasure a) +
          ∫ y in Shi, |W y - P y| ∂ gammaFullMeasure a := by
    have h :=
      MeasureTheory.integral_add_compl
        (μ := gammaFullMeasure a) (s := Slo)
        (f := fun y => |W y - P y|) measurableSet_Iio hdiff_abs_int
    rw [Set.compl_Iio] at h
    exact h.symm
  let Low : ℚ :=
    (∑ s ∈ (Finset.range (printedTailR0 a + 1)).filter
        (fun s : Nat => s ≤ a / 8),
        gammaWeight a s * |printedTailOmegaCoeff μ a s|)
      * (9 / 10 : ℚ)^(a - a / 8)
  let High : ℚ :=
    ∑ s ∈ (Finset.range (printedTailR0 a + 1)).filter
        (fun s : Nat => a / 8 + 1 ≤ s),
        gammaWeight a s * |printedTailOmegaCoeff μ a s|
  have hlower :
      (∫ y in Slo, |W y - P y| ∂ gammaFullMeasure a) ≤
        ((2 * (5 / 6 : ℚ)^a + (Low + High) : ℚ) : ℝ) := by
    simpa [Slo, W, P, Low, High, printedTailWGammaIntegrand] using
      integral_abs_printedTailWGammaIntegrand_sub_WTruncReal_R0_lower_event_le_residue_terms
        (a := a) ha (μ := μ) hμ
  have hupper' :
      (∫ y in Shi, |W y - P y| ∂ gammaFullMeasure a) ≤
        ((920 / (2 : ℚ)^(printedTailR0 a + 1) : ℚ) : ℝ) := by
    simpa [Shi, W, P] using hupper a ha μ hμ
  have hlowQ :
      Low ≤ 9 * (9 / 10 : ℚ)^(a - a / 8) := by
    simpa [Low] using
      gammaWeight_absOmega_low_tail_le_residue_term
        (printedTailAbsoluteMomentBounds_of_majorant
          (printedTailMajorantMomentBounds_of_wPointMomentBounds
            printedTailWPointMomentBounds_closed))
        (a := a) ha (μ := μ) hμ
  have hhighQ :
      High ≤ 920 * (a : ℚ) * (3 / 10 : ℚ)^(a / 8 + 1) := by
    simpa [High] using
      gammaWeight_absOmega_high_tail_le_residue_term
        printedTailWPointBoundX2_closed (a := a) ha (μ := μ) hμ
  have hbudgetQ :
      2 * (5 / 6 : ℚ)^a + (Low + High) +
          920 / (2 : ℚ)^(printedTailR0 a + 1)
        ≤ truncationResidueRhs a := by
    unfold truncationResidueRhs printedTailR0 printedTailP
    nlinarith [hlowQ, hhighQ]
  calc
    |printedTailWGammaIntegral μ a -
        printedTailWTruncGammaIntegral μ a|
        ≤ ∫ y, |W y - P y| ∂ gammaFullMeasure a := habs_global
    _ =
        (∫ y in Slo, |W y - P y| ∂ gammaFullMeasure a) +
          ∫ y in Shi, |W y - P y| ∂ gammaFullMeasure a := hsplit
    _ ≤
        ((2 * (5 / 6 : ℚ)^a + (Low + High) : ℚ) : ℝ) +
          ((920 / (2 : ℚ)^(printedTailR0 a + 1) : ℚ) : ℝ) :=
          add_le_add hlower hupper'
    _ =
        ((2 * (5 / 6 : ℚ)^a + (Low + High) +
          920 / (2 : ℚ)^(printedTailR0 a + 1) : ℚ) : ℝ) := by
          norm_num
    _ ≤ (truncationResidueRhs a : ℝ) := by
          exact_mod_cast hbudgetQ

/-- The closed point/moment certificates imply the rational residue budget
needed after the analytic truncation comparison. -/
theorem truncationResiduePiecesLhs_le_truncationResidueRhs_closed
    {a : Nat} (ha : 150 ≤ a) {μ : List Nat}
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    truncationResiduePiecesLhs μ a ≤ truncationResidueRhs a := by
  exact truncationResiduePiecesLhs_le_truncationResidueRhs
    printedTailWPointBoundX2_closed
    (printedTailAbsoluteMomentBounds_of_majorant
      (printedTailMajorantMomentBounds_of_wPointMomentBounds
        printedTailWPointMomentBounds_closed))
    (a := a) ha (μ := μ) hμ

/-- Once the Taylor--Gamma truncation error is proved, the printed
Gamma/integral lower bound follows from the closed integration-by-parts margin
and the finite residue arithmetic. -/
theorem printedTailGammaIntegralLowerBound_of_truncationError
    (htrunc : PrintedTailGammaTruncationErrorBound) :
    PrintedTailGammaIntegralLowerBound := by
  intro a ha μ hμ
  have hlow :
      9 / (40 * ((a : ℝ) - 2)) ≤ printedTailWGammaIntegral μ a := by
    simpa [printedTailWGammaIntegral, printedTailWGammaIntegrand,
      one_div, mul_assoc, mul_comm, mul_left_comm] using
      gammaFull_WIntegral_lower (a := a) (μ := μ) ha hμ
  have herr := htrunc a ha μ hμ
  have hresQ := truncationResiduePiecesLhs_le_truncationResidueRhs_closed
    (a := a) ha (μ := μ) hμ
  have hresR :
      (truncationResiduePiecesLhs μ a : ℝ) ≤
        (truncationResidueRhs a : ℝ) := by
    exact_mod_cast hresQ
  have hmain :
      printedTailWTruncGammaIntegral μ a =
        (printedTailMainSum μ a : ℝ) := by
    simpa [printedTailWTruncGammaIntegral] using
      integral_printedTailWTruncReal_R0_eq_mainSum
        (μ := μ) (a := a) ha
  have hupper :
      printedTailWGammaIntegral μ a ≤
        (printedTailMainSum μ a : ℝ) +
          (truncationResidueRhs a : ℝ) := by
    have hdiff :
        printedTailWGammaIntegral μ a -
            printedTailWTruncGammaIntegral μ a ≤
          (truncationResiduePiecesLhs μ a : ℝ) :=
      (le_abs_self _).trans herr
    calc
      printedTailWGammaIntegral μ a
          ≤ printedTailWTruncGammaIntegral μ a +
              (truncationResiduePiecesLhs μ a : ℝ) := by
            linarith
      _ = (printedTailMainSum μ a : ℝ) +
              (truncationResiduePiecesLhs μ a : ℝ) := by
            rw [hmain]
      _ ≤ (printedTailMainSum μ a : ℝ) +
              (truncationResidueRhs a : ℝ) := by
            linarith
  have hreal :
      ((9 / (40 * ((a : ℚ) - 2)) : ℚ) : ℝ) ≤
        ((printedTailMainSum μ a + truncationResidueRhs a : ℚ) : ℝ) := by
    calc
      ((9 / (40 * ((a : ℚ) - 2)) : ℚ) : ℝ)
          = 9 / (40 * ((a : ℝ) - 2)) := by norm_num
      _ ≤ printedTailWGammaIntegral μ a := hlow
      _ ≤ (printedTailMainSum μ a : ℝ) +
            (truncationResidueRhs a : ℝ) := hupper
      _ = ((printedTailMainSum μ a + truncationResidueRhs a : ℚ) : ℝ) := by
            norm_num
  exact (Rat.cast_le (K := ℝ)).mp hreal

/-- Variant of `printedTailGammaIntegralLowerBound_of_truncationError` using
the paper-shaped truncation estimate directly against `truncationResidueRhs`.
This avoids exposing the internal finite residue decomposition at the public
theorem surface. -/
theorem printedTailGammaIntegralLowerBound_of_truncationResidue
    (htrunc : PrintedTailGammaTruncationResidueBound) :
    PrintedTailGammaIntegralLowerBound := by
  intro a ha μ hμ
  have hlow :
      9 / (40 * ((a : ℝ) - 2)) ≤ printedTailWGammaIntegral μ a := by
    simpa [printedTailWGammaIntegral, printedTailWGammaIntegrand,
      one_div, mul_assoc, mul_comm, mul_left_comm] using
      gammaFull_WIntegral_lower (a := a) (μ := μ) ha hμ
  have herr := htrunc a ha μ hμ
  have hmain :
      printedTailWTruncGammaIntegral μ a =
        (printedTailMainSum μ a : ℝ) := by
    simpa [printedTailWTruncGammaIntegral] using
      integral_printedTailWTruncReal_R0_eq_mainSum
        (μ := μ) (a := a) ha
  have hupper :
      printedTailWGammaIntegral μ a ≤
        (printedTailMainSum μ a : ℝ) +
          (truncationResidueRhs a : ℝ) := by
    have hdiff :
        printedTailWGammaIntegral μ a -
            printedTailWTruncGammaIntegral μ a ≤
          (truncationResidueRhs a : ℝ) :=
      (le_abs_self _).trans herr
    calc
      printedTailWGammaIntegral μ a
          ≤ printedTailWTruncGammaIntegral μ a +
              (truncationResidueRhs a : ℝ) := by
            linarith
      _ = (printedTailMainSum μ a : ℝ) +
              (truncationResidueRhs a : ℝ) := by
            rw [hmain]
  have hreal :
      ((9 / (40 * ((a : ℚ) - 2)) : ℚ) : ℝ) ≤
        ((printedTailMainSum μ a + truncationResidueRhs a : ℚ) : ℝ) := by
    calc
      ((9 / (40 * ((a : ℚ) - 2)) : ℚ) : ℝ)
          = 9 / (40 * ((a : ℝ) - 2)) := by norm_num
      _ ≤ printedTailWGammaIntegral μ a := hlow
      _ ≤ (printedTailMainSum μ a : ℝ) +
            (truncationResidueRhs a : ℝ) := hupper
      _ = ((printedTailMainSum μ a + truncationResidueRhs a : ℚ) : ℝ) := by
            norm_num
  exact (Rat.cast_le (K := ℝ)).mp hreal

end Prop52
