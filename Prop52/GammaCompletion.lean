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
open PowerSeries
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

/-- Real power-series representation for the low exponential factor
`E(t)=exp(-L(t))`.

This isolates the only genuinely exponential analytic identity.  The theorem
`printedTailWRealSeriesHasSum_of_eSeries` below shows that the finite marked
polynomial `J` then assembles the full `W=E(1-J)` series using only the formal
coefficient convolution already proved in `Printed.lean`. -/
def PrintedTailERealSeriesHasSum : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      ∀ t : ℝ, 0 ≤ t → t ≤ (printedTailX1 a : ℝ) →
        HasSum
          (fun s : Nat => (printedTailECoeff μ a s : ℝ) * t^s)
          (Real.exp (-(printedTailLReal μ a t)))

theorem printedTailLowExpInput_zero (μ : List Nat) (a : Nat) :
    printedTailLowExpInput μ a 0 = 0 := by
  unfold printedTailLowExpInput hCoeff
  simp

/-- The formal low-exponential input evaluates to the real polynomial
`-L(t)` used in the printed Gamma-tail argument. -/
theorem printedTailLowExpInput_eval_eq_neg_printedTailLReal
    (μ : List Nat) (a : Nat) (t : ℝ) :
    (∑ r ∈ Finset.range (printedTailP a + 1),
        (printedTailLowExpInput μ a r : ℝ) * t^r)
      = -(printedTailLReal μ a t) := by
  unfold printedTailLowExpInput printedTailLReal
  have hsubset :
      Finset.Ico 1 (printedTailP a + 1) ⊆
        Finset.range (printedTailP a + 1) := by
    intro r hr
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hr).2
  have hzero :
      ∀ r ∈ Finset.range (printedTailP a + 1),
        r ∉ Finset.Ico 1 (printedTailP a + 1) →
          ((if r ≤ printedTailP a then -hCoeff μ r else 0 : ℚ) : ℝ) *
              t^r = 0 := by
    intro r hr hnot
    have hrlt : r < printedTailP a + 1 := Finset.mem_range.mp hr
    have hr0 : r = 0 := by
      by_contra hne
      have hr1 : 1 ≤ r := by omega
      exact hnot (Finset.mem_Ico.mpr ⟨hr1, hrlt⟩)
    subst r
    simp [hCoeff]
  calc
    ∑ r ∈ Finset.range (printedTailP a + 1),
        ((if r ≤ printedTailP a then -hCoeff μ r else 0 : ℚ) : ℝ) * t^r
        = ∑ r ∈ Finset.Ico 1 (printedTailP a + 1),
            ((if r ≤ printedTailP a then -hCoeff μ r else 0 : ℚ) : ℝ) *
              t^r := by
          exact (Finset.sum_subset hsubset hzero).symm
    _ = ∑ r ∈ Finset.Ico 1 (printedTailP a + 1),
          -((hCoeff μ r : ℝ) * t^r) := by
          refine Finset.sum_congr rfl fun r hr => ?_
          have hrle : r ≤ printedTailP a :=
            Nat.le_of_lt_succ (Finset.mem_Ico.mp hr).2
          simp [hrle]
    _ = -∑ r ∈ Finset.Ico 1 (printedTailP a + 1),
          (hCoeff μ r : ℝ) * t^r := by
          rw [Finset.sum_neg_distrib]

theorem printedTailX1_lt_one_real {a : Nat} (ha : 150 ≤ a) :
    (printedTailX1 a : ℝ) < 1 := by
  have haR : (150 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hx1_cast : (printedTailX1 a : ℝ) = 1 / (3 * (a : ℝ)) := by
    unfold printedTailX1
    norm_num
  rw [hx1_cast]
  have hden_pos : (0 : ℝ) < 3 * (a : ℝ) := by nlinarith
  rw [div_lt_one hden_pos]
  nlinarith

private theorem hasSum_nat_shift_mul_left
    {f : Nat → ℝ} {A c : ℝ} (hf : HasSum f A) (r : Nat) :
    HasSum (fun s : Nat => if r ≤ s then c * f (s - r) else 0) (c * A) := by
  let H : Nat → ℝ := fun s => if r ≤ s then c * f (s - r) else 0
  have hshift : HasSum (fun n : Nat => H (n + r)) (c * A) := by
    simpa [H] using HasSum.mul_left c hf
  have hfull := (hasSum_nat_add_iff r).mp hshift
  have hprefix : ∑ i ∈ Finset.range r, H i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hlt : i < r := Finset.mem_range.mp hi
    simp [H, not_le_of_gt hlt]
  simpa [H, hprefix] using hfull

private theorem hasSum_finset_sum_nat
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    {f : ι → Nat → ℝ} {A : ι → ℝ}
    (h : ∀ i ∈ S, HasSum (f i) (A i)) :
    HasSum (fun n : Nat => ∑ i ∈ S, f i n) (∑ i ∈ S, A i) := by
  classical
  revert h
  refine Finset.induction_on S ?base ?step
  · intro _h
    simpa using (hasSum_zero : HasSum (fun _ : Nat => (0 : ℝ)) 0)
  · intro i S hi ih h
    have hi_sum : HasSum (f i) (A i) := h i (by simp [hi])
    have hS_sum :
        HasSum (fun n : Nat => ∑ j ∈ S, f j n) (∑ j ∈ S, A j) :=
      ih fun j hj => h j (by simp [hj])
    simpa [Finset.sum_insert hi, add_comm, add_left_comm, add_assoc] using
      hi_sum.add hS_sum

/-- Real power-series representation for the full upper-event function.

This is the remaining analytic identity behind the Taylor tail: on the
interval used by the Gamma upper event, the formal `omega` coefficients really
sum to `exp(-L(t)) * (1 - J(t))`.  The theorem below shows that the already
closed coefficient majorant then supplies the printed `920 / 2^(r0+1)` tail
budget. -/
def PrintedTailWRealSeriesHasSum : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      ∀ t : ℝ, 0 ≤ t → t ≤ (printedTailX1 a : ℝ) →
        HasSum
          (fun s : Nat => (printedTailOmegaCoeff μ a s : ℝ) * t^s)
          (Real.exp (-(printedTailLReal μ a t)) *
            (1 - printedTailJReal μ a t))

theorem printedTailWRealSeriesHasSum_of_eSeries
    (hEseries : PrintedTailERealSeriesHasSum) :
    PrintedTailWRealSeriesHasSum := by
  intro a ha μ hμ t ht0 ht1
  let Efun : Nat → ℝ := fun s =>
    (printedTailECoeff μ a s : ℝ) * t^s
  let Eval : ℝ := Real.exp (-(printedTailLReal μ a t))
  let S : Finset Nat := Finset.Ico 1 (printedTailP a + 1)
  let Cfun : Nat → ℝ := fun s =>
    ∑ r ∈ S,
      if r ≤ s then ((kCoeff μ r : ℝ) * t^r) * Efun (s - r) else 0
  have hE : HasSum Efun Eval := by
    simpa [Efun, Eval] using hEseries a ha μ hμ t ht0 ht1
  have hconv_terms :
      ∀ r ∈ S,
        HasSum
          (fun s : Nat =>
            if r ≤ s then ((kCoeff μ r : ℝ) * t^r) * Efun (s - r) else 0)
          (((kCoeff μ r : ℝ) * t^r) * Eval) := by
    intro r _hr
    exact hasSum_nat_shift_mul_left hE r
  have hconv_raw :
      HasSum Cfun
        (∑ r ∈ S, ((kCoeff μ r : ℝ) * t^r) * Eval) := by
    simpa [Cfun] using
      hasSum_finset_sum_nat (S := S) hconv_terms
  have hconv_target :
      (∑ r ∈ S, ((kCoeff μ r : ℝ) * t^r) * Eval) =
        printedTailJReal μ a t * Eval := by
    unfold printedTailJReal
    dsimp [S]
    rw [Finset.sum_mul]
  have hconv :
      HasSum Cfun (printedTailJReal μ a t * Eval) := by
    simpa [hconv_target] using hconv_raw
  have hC_coeff :
      ∀ s : Nat,
        ((coeff s (printedTailESeries μ a * printedTailLowJSeries μ a) : ℚ) : ℝ) *
            t^s = Cfun s := by
    intro s
    have hcoeff := coeff_printedTailESeries_mul_lowJSeries_Ico μ a s
    rw [hcoeff]
    rw [Rat.cast_sum]
    rw [Finset.sum_mul]
    dsimp [Cfun, S]
    refine Finset.sum_congr rfl fun r hr => ?_
    by_cases hrs : r ≤ s
    · rw [if_pos hrs, if_pos hrs, Rat.cast_mul]
      have hpow : t^s = t^r * t^(s - r) := by
        have hs_eq : r + (s - r) = s := Nat.add_sub_of_le hrs
        calc
          t^s = t^(r + (s - r)) := by rw [hs_eq]
          _ = t^r * t^(s - r) := by rw [pow_add]
      rw [hpow]
      ring
    · rw [if_neg hrs, if_neg hrs]
      simp
  have hconv_coeff :
      HasSum
        (fun s : Nat =>
          ((coeff s (printedTailESeries μ a * printedTailLowJSeries μ a) : ℚ) : ℝ) *
            t^s)
        (printedTailJReal μ a t * Eval) :=
    HasSum.congr_fun hconv hC_coeff
  have homega_point :
      ∀ s : Nat,
        (printedTailOmegaCoeff μ a s : ℝ) * t^s =
          Efun s -
            ((coeff s (printedTailESeries μ a * printedTailLowJSeries μ a) : ℚ) : ℝ) *
              t^s := by
    intro s
    have hcoeff :
        printedTailOmegaCoeff μ a s =
          printedTailECoeff μ a s -
            coeff s (printedTailESeries μ a * printedTailLowJSeries μ a) := by
      rw [← coeff_printedTailWSeries μ a s]
      unfold printedTailWSeries
      rw [mul_sub, mul_one, map_sub, coeff_printedTailESeries]
    rw [hcoeff, Rat.cast_sub, sub_mul]
  have hWsum :
      HasSum
        (fun s : Nat => (printedTailOmegaCoeff μ a s : ℝ) * t^s)
        (Eval - printedTailJReal μ a t * Eval) :=
    HasSum.congr_fun (hE.sub hconv_coeff) homega_point
  convert hWsum using 1
  ring

theorem printedTailWRealTailResidueBound_of_hasSum
    (hseries : PrintedTailWRealSeriesHasSum) :
    PrintedTailWRealTailResidueBound := by
  intro a ha μ hμ t ht0 ht1
  let R : Nat := printedTailR0 a + 1
  let f : Nat → ℝ := fun s =>
    (printedTailOmegaCoeff μ a s : ℝ) * t^s
  let G : Nat → ℝ := fun s =>
    if R ≤ s then
      ((printedTailWAbsCoeff μ a s * (printedTailX1 a)^s : ℚ) : ℝ)
    else 0
  let W : ℝ :=
    Real.exp (-(printedTailLReal μ a t)) *
      (1 - printedTailJReal μ a t)
  have hsum : HasSum f W := by
    simpa [f, W] using hseries a ha μ hμ t ht0 ht1
  have hf : Summable f := hsum.summable
  have hsplit :
      (∑ i ∈ Finset.range R, f i) +
          (∑' i : Nat, f (i + R)) = W := by
    have h := hf.sum_add_tsum_nat_add R
    simpa [hsum.tsum_eq] using h
  have hdiff :
      W - (∑ s ∈ Finset.range R, f s) =
        ∑' i : Nat, f (i + R) := by
    linarith
  have hG_nonneg : ∀ s : Nat, 0 ≤ G s := by
    intro s
    dsimp [G]
    by_cases hs : R ≤ s
    · rw [if_pos hs]
      exact_mod_cast
        mul_nonneg (printedTailWAbsCoeff_nonneg μ a s)
          (pow_nonneg (by unfold printedTailX1; positivity) s)
    · rw [if_neg hs]
  have hG : Summable G := by
    simpa [G, R] using
      summable_printedTailWAbsCoeff_x1_tail_closed
        (a := a) ha (μ := μ) hμ
  have hG_shift : Summable (fun i : Nat => G (i + R)) := by
    exact (summable_nat_add_iff R).mpr hG
  have hnorm_le_G : ∀ i : Nat, ‖f (i + R)‖ ≤ G (i + R) := by
    intro i
    have hsR : R ≤ i + R := by omega
    have homega :
        |(printedTailOmegaCoeff μ a (i + R) : ℝ)| ≤
          (printedTailWAbsCoeff μ a (i + R) : ℝ) := by
      exact_mod_cast abs_printedTailOmegaCoeff_le_WAbsCoeff μ a (i + R)
    have hpow_nonneg : 0 ≤ t^(i + R) := pow_nonneg ht0 _
    have hpow :
        |t^(i + R)| ≤ (printedTailX1 a : ℝ)^(i + R) := by
      rw [abs_of_nonneg hpow_nonneg]
      exact pow_le_pow_left₀ ht0 ht1 _
    have hW_nonneg :
        0 ≤ (printedTailWAbsCoeff μ a (i + R) : ℝ) := by
      exact_mod_cast printedTailWAbsCoeff_nonneg μ a (i + R)
    calc
      ‖f (i + R)‖
          = |(printedTailOmegaCoeff μ a (i + R) : ℝ) * t^(i + R)| := by
            change ‖(printedTailOmegaCoeff μ a (i + R) : ℝ) *
                t^(i + R)‖ =
              |(printedTailOmegaCoeff μ a (i + R) : ℝ) * t^(i + R)|
            rw [Real.norm_eq_abs]
      _ = |(printedTailOmegaCoeff μ a (i + R) : ℝ)| * |t^(i + R)| := by
            rw [abs_mul]
      _ ≤ (printedTailWAbsCoeff μ a (i + R) : ℝ) *
            (printedTailX1 a : ℝ)^(i + R) :=
            mul_le_mul homega hpow (abs_nonneg _) hW_nonneg
      _ = ((printedTailWAbsCoeff μ a (i + R) *
              (printedTailX1 a)^(i + R) : ℚ) : ℝ) := by
            rw [Rat.cast_mul, Rat.cast_pow]
      _ = G (i + R) := by
            dsimp [G]
            rw [if_pos hsR]
  have hnorm_summable : Summable (fun i : Nat => ‖f (i + R)‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg (f (i + R)))
      hnorm_le_G hG_shift
  have htail_norm_le :
      ‖∑' i : Nat, f (i + R)‖ ≤
        ∑' i : Nat, G (i + R) := by
    calc
      ‖∑' i : Nat, f (i + R)‖ ≤
          ∑' i : Nat, ‖f (i + R)‖ :=
            norm_tsum_le_tsum_norm hnorm_summable
      _ ≤ ∑' i : Nat, G (i + R) :=
            Summable.tsum_le_tsum hnorm_le_G hnorm_summable hG_shift
  have hprefix_nonneg : 0 ≤ ∑ i ∈ Finset.range R, G i :=
    Finset.sum_nonneg fun i _hi => hG_nonneg i
  have hG_shift_le_total :
      (∑' i : Nat, G (i + R)) ≤ ∑' s : Nat, G s := by
    have h := hG.sum_add_tsum_nat_add R
    nlinarith
  have hG_total_le :
      (∑' s : Nat, G s) ≤
        ((920 / (2 : ℚ)^(printedTailR0 a + 1) : ℚ) : ℝ) := by
    simpa [G, R] using
      tsum_printedTailWAbsCoeff_x1_tail_le_residue_term_closed
        (a := a) ha (μ := μ) hμ
  calc
    |Real.exp (-(printedTailLReal μ a t)) *
        (1 - printedTailJReal μ a t) -
      (∑ s ∈ Finset.range (printedTailR0 a + 1),
        (printedTailOmegaCoeff μ a s : ℝ) * t^s)|
        =
      |W - ∑ s ∈ Finset.range R, f s| := by
        simp [W, f, R]
    _ = |∑' i : Nat, f (i + R)| := by
        rw [hdiff]
    _ = ‖∑' i : Nat, f (i + R)‖ := by
        rw [Real.norm_eq_abs]
    _ ≤ ∑' i : Nat, G (i + R) := htail_norm_le
    _ ≤ ∑' s : Nat, G s := hG_shift_le_total
    _ ≤ ((920 / (2 : ℚ)^(printedTailR0 a + 1) : ℚ) : ℝ) := hG_total_le

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
