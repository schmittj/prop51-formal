/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Large-range arithmetic for the printed Proposition 5.2 coefficient

This module records exact rational arithmetic from the printed-series
large-range argument.  The analytic estimates proving the lower bound are not
yet formalized here; the final rational margin used to close the proof is.
-/

import Prop52.Statement
import Prop52.Recurrence
import Prop51.Majorant
import Prop51.DNorm
import Mathlib.Tactic

namespace Prop52

open PowerSeries

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

/-! ## The printed coefficient as a power-series coefficient -/

noncomputable def printedFullFSeries (μ : List Nat) : ℚ⟦X⟧ :=
  Prop51.expSeries (fun r => -hCoeff μ r)

noncomputable def printedFullKSeries (μ : List Nat) : ℚ⟦X⟧ :=
  mk (kCoeff μ)

theorem coeff_printedFullFSeries (μ : List Nat) (a : Nat) :
    coeff a (printedFullFSeries μ) = fCoeff μ a := by
  simp [printedFullFSeries, fCoeff]

theorem coeff_printedFullKSeries (μ : List Nat) (r : Nat) :
    coeff r (printedFullKSeries μ) = kCoeff μ r := by
  simp [printedFullKSeries]

theorem coeff_printedFullFSeries_mul_KSeries (μ : List Nat) (a : Nat) :
    coeff a (printedFullFSeries μ * printedFullKSeries μ) =
      ((List.range a).map fun j : Nat =>
        kCoeff μ (j + 1) * fCoeff μ (a - (j + 1))).sum := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_printedFullFSeries, coeff_printedFullKSeries]
  rw [Finset.sum_range_succ]
  rw [Nat.sub_self]
  change (∑ x ∈ Finset.range a, fCoeff μ x * kCoeff μ (a - x)) +
      fCoeff μ a * kCoeff μ 0 =
    ∑ i ∈ Finset.range a, kCoeff μ (i + 1) * fCoeff μ (a - (i + 1))
  rw [show kCoeff μ 0 = 0 by rfl, mul_zero, add_zero]
  rw [← Finset.sum_range_reflect (fun x : Nat =>
    fCoeff μ x * kCoeff μ (a - x)) a]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjlt : j < a := Finset.mem_range.mp hj
  have hsub : a - (a - 1 - j) = j + 1 := by omega
  have hsub' : a - (j + 1) = a - 1 - j := by omega
  rw [hsub, hsub']
  ring

theorem coeff_printedFullSeries_eq_printedCoeff (μ : List Nat) (a : Nat) :
    coeff a (printedFullFSeries μ * (1 - printedFullKSeries μ)) =
      printedCoeff μ a := by
  unfold printedCoeff markedConvolution
  rw [mul_sub, mul_one, map_sub, coeff_printedFullFSeries,
    coeff_printedFullFSeries_mul_KSeries]
  rw [← bCoeff_eq_fCoeff μ a]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun k _hk => ?_)
  rw [kCoeff_eq_markedCoeff, ← bCoeff_eq_fCoeff μ (a - (k + 1))]

/-! ## Low/high split interface for the printed large tail

The human proof expands the printed coefficient using
`p = floor(a/2)`, keeps the low polynomials

`L(t) = sum_{r<=p} h_r t^r` and `J(t) = sum_{r<=p} k_r t^r`,

and writes `E = exp(-L)` and `W = E*(1-J)`.  The hard remaining work is to
prove the exact split and the estimates below from the coefficient
recurrences.  This section records the precise Lean objects and proves the
final normalized-error assembly.
-/

def printedTailP (a : Nat) : Nat :=
  a / 2

def printedTailR0 (a : Nat) : Nat :=
  a - printedTailP a - 1

/-- Coefficients of the low polynomial `-L(t)` used to define
`E(t)=exp(-L(t))`. -/
def printedTailLowExpInput (μ : List Nat) (a r : Nat) : ℚ :=
  if r ≤ printedTailP a then -hCoeff μ r else 0

def printedTailHighExpInput (μ : List Nat) (a r : Nat) : ℚ :=
  if printedTailP a < r then -hCoeff μ r else 0

/-- The coefficient `e_s` of `E(t)=exp(-L(t))`. -/
def printedTailECoeff (μ : List Nat) (a s : Nat) : ℚ :=
  Prop51.expCoeff (printedTailLowExpInput μ a) s

noncomputable def printedTailESeries (μ : List Nat) (a : Nat) : ℚ⟦X⟧ :=
  Prop51.expSeries (printedTailLowExpInput μ a)

noncomputable def printedTailHighESeries (μ : List Nat) (a : Nat) : ℚ⟦X⟧ :=
  Prop51.expSeries (printedTailHighExpInput μ a)

noncomputable def printedTailLowJSeries (μ : List Nat) (a : Nat) : ℚ⟦X⟧ :=
  mk fun r => if 1 ≤ r ∧ r ≤ printedTailP a then kCoeff μ r else 0

noncomputable def printedTailHighKSeries (μ : List Nat) (a : Nat) : ℚ⟦X⟧ :=
  mk fun r => if printedTailP a < r then kCoeff μ r else 0

noncomputable def printedTailWSeries (μ : List Nat) (a : Nat) : ℚ⟦X⟧ :=
  printedTailESeries μ a * (1 - printedTailLowJSeries μ a)

/-- The coefficient `omega_s` of `W(t)=E(t)(1-J(t))`, written as a finite
convolution with the low marked numerator `J`. -/
def printedTailOmegaCoeff (μ : List Nat) (a s : Nat) : ℚ :=
  printedTailECoeff μ a s -
    ((List.range s).map fun j : Nat =>
      let r := j + 1
      if r ≤ printedTailP a then
        kCoeff μ r * printedTailECoeff μ a (s - r)
      else 0).sum

theorem coeff_printedTailESeries (μ : List Nat) (a s : Nat) :
    coeff s (printedTailESeries μ a) = printedTailECoeff μ a s := by
  simp [printedTailESeries, printedTailECoeff]

private theorem expCoeff_eq_zero_of_input_eq_zero_le (L : Nat → ℚ) :
    ∀ n : Nat, 1 ≤ n → (∀ r : Nat, 1 ≤ r → r ≤ n → L r = 0) →
      Prop51.expCoeff L n = 0
  | 0, hn, _ => by omega
  | n + 1, _hn, hzero => by
      have hrec := Prop51.expCoeff_succ_mul L n
      have hsum :
          (∑ t ∈ Finset.range (n + 1),
              ((t + 1 : Nat) : ℚ) * L (t + 1) * Prop51.expCoeff L (n - t)) =
            0 := by
        refine Finset.sum_eq_zero fun t ht => ?_
        have htlt : t < n + 1 := Finset.mem_range.mp ht
        have hz : L (t + 1) = 0 := hzero (t + 1) (by omega) (by omega)
        simp [hz]
      have hne : (((n + 1 : Nat) : ℚ) ≠ 0) := by
        exact_mod_cast Nat.succ_ne_zero n
      rw [hsum] at hrec
      exact (mul_eq_zero.mp hrec).resolve_left hne

private theorem expCoeff_eq_input_of_gap (L : Nat → ℚ) (p n : Nat)
    (hpn : p < n) (hnp : n ≤ 2 * p + 1)
    (hzero : ∀ r : Nat, 1 ≤ r → r ≤ p → L r = 0) :
    Prop51.expCoeff L n = L n := by
  rcases n with _ | n
  · omega
  have hrec := Prop51.expCoeff_succ_mul L n
  have hsum :
      (∑ t ∈ Finset.range (n + 1),
          ((t + 1 : Nat) : ℚ) * L (t + 1) * Prop51.expCoeff L (n - t)) =
        ((n + 1 : Nat) : ℚ) * L (n + 1) := by
    rw [Finset.sum_range_succ]
    have hprefix :
        (∑ t ∈ Finset.range n,
            ((t + 1 : Nat) : ℚ) * L (t + 1) * Prop51.expCoeff L (n - t)) =
          0 := by
      refine Finset.sum_eq_zero fun t ht => ?_
      have htlt : t < n := Finset.mem_range.mp ht
      by_cases htp : t + 1 ≤ p
      · have hz : L (t + 1) = 0 := hzero (t + 1) (by omega) htp
        simp [hz]
      · have hdeg_pos : 1 ≤ n - t := by omega
        have hdeg_le_p : n - t ≤ p := by omega
        have hE :
            Prop51.expCoeff L (n - t) = 0 :=
          expCoeff_eq_zero_of_input_eq_zero_le L (n - t) hdeg_pos
            (fun r hr1 hrle => hzero r hr1 (by omega))
        simp [hE]
    rw [hprefix]
    simp
  rw [hsum] at hrec
  have hne : (((n + 1 : Nat) : ℚ) ≠ 0) := by
    exact_mod_cast Nat.succ_ne_zero n
  exact mul_left_cancel₀ hne hrec

theorem coeff_printedTailHighESeries_eq_zero_of_le_p
    (μ : List Nat) (a s : Nat) (hs : 1 ≤ s) (hsp : s ≤ printedTailP a) :
    coeff s (printedTailHighESeries μ a) = 0 := by
  rw [printedTailHighESeries, Prop51.coeff_expSeries]
  refine expCoeff_eq_zero_of_input_eq_zero_le (printedTailHighExpInput μ a)
    s hs ?_
  intro r hr1 hrs
  unfold printedTailHighExpInput
  rw [if_neg (by omega)]

theorem coeff_printedTailHighESeries_eq_neg_hCoeff_of_gt_p_le_a
    (μ : List Nat) (a s : Nat) (hsp : printedTailP a < s) (hsa : s ≤ a) :
    coeff s (printedTailHighESeries μ a) = -hCoeff μ s := by
  rw [printedTailHighESeries, Prop51.coeff_expSeries]
  rw [expCoeff_eq_input_of_gap (printedTailHighExpInput μ a) (printedTailP a) s
    hsp (by unfold printedTailP at *; omega) ?_]
  · unfold printedTailHighExpInput
    rw [if_pos hsp]
  · intro r _hr1 hrp
    unfold printedTailHighExpInput
    rw [if_neg (by omega)]

theorem coeff_printedTailHighESeries_piecewise
    (μ : List Nat) (a s : Nat) (hsa : s ≤ a) :
    coeff s (printedTailHighESeries μ a) =
      if s = 0 then 1 else if printedTailP a < s then -hCoeff μ s else 0 := by
  by_cases hs0 : s = 0
  · subst hs0
    simp [printedTailHighESeries]
  · rw [if_neg hs0]
    by_cases hsp : printedTailP a < s
    · rw [if_pos hsp,
        coeff_printedTailHighESeries_eq_neg_hCoeff_of_gt_p_le_a μ a s hsp hsa]
    · have hspos : 1 ≤ s := by omega
      have hsle : s ≤ printedTailP a := by omega
      rw [if_neg hsp,
        coeff_printedTailHighESeries_eq_zero_of_le_p μ a s hspos hsle]

theorem coeff_printedTailLowJSeries (μ : List Nat) (a r : Nat) :
    coeff r (printedTailLowJSeries μ a) =
      if 1 ≤ r ∧ r ≤ printedTailP a then kCoeff μ r else 0 := by
  simp [printedTailLowJSeries]

theorem coeff_printedTailHighKSeries_eq_zero_of_le_p
    (μ : List Nat) (a s : Nat) (hs : s ≤ printedTailP a) :
    coeff s (printedTailHighKSeries μ a) = 0 := by
  simp [printedTailHighKSeries, hs]

theorem printedFullFSeries_eq_low_mul_high (μ : List Nat) (a : Nat) :
    printedFullFSeries μ = printedTailESeries μ a * printedTailHighESeries μ a := by
  rw [printedFullFSeries, printedTailESeries, printedTailHighESeries,
    Prop51.expSeries_mul]
  congr 1
  funext r
  unfold printedTailLowExpInput printedTailHighExpInput
  by_cases hr : r ≤ printedTailP a
  · rw [if_pos hr, if_neg (by omega)]
    ring
  · rw [if_neg hr, if_pos (by omega)]
    ring

theorem printedFullKSeries_eq_low_add_high (μ : List Nat) (a : Nat) :
    printedFullKSeries μ = printedTailLowJSeries μ a + printedTailHighKSeries μ a := by
  ext r
  simp only [printedFullKSeries, printedTailLowJSeries, printedTailHighKSeries,
    coeff_mk, map_add]
  rcases r with _ | r
  · simp [kCoeff]
  · by_cases hr : r + 1 ≤ printedTailP a
    · rw [if_pos ⟨by omega, hr⟩, if_neg (by omega)]
      ring
    · rw [if_neg (fun h => hr h.2), if_pos (by omega)]
      ring

theorem coeff_printedTail_series_split_eq_printedCoeff
    (μ : List Nat) (a : Nat) :
    coeff a
        (printedTailHighESeries μ a * printedTailWSeries μ a -
          printedTailESeries μ a * printedTailHighESeries μ a *
            printedTailHighKSeries μ a) =
      printedCoeff μ a := by
  rw [← coeff_printedFullSeries_eq_printedCoeff μ a]
  congr 1
  rw [printedFullFSeries_eq_low_mul_high,
    printedFullKSeries_eq_low_add_high]
  unfold printedTailWSeries
  ring

theorem coeff_printedTailESeries_mul_lowJSeries
    (μ : List Nat) (a s : Nat) :
    coeff s (printedTailESeries μ a * printedTailLowJSeries μ a) =
      ((List.range s).map fun j : Nat =>
        let r := j + 1
        if r ≤ printedTailP a then
          kCoeff μ r * printedTailECoeff μ a (s - r)
        else 0).sum := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_printedTailESeries, coeff_printedTailLowJSeries]
  rw [Finset.sum_range_succ]
  simp
  rw [Prop51.list_range_map_sum]
  rw [← Finset.sum_range_reflect (fun x : Nat =>
    if 1 ≤ s - x ∧ s ≤ printedTailP a + x then
      printedTailECoeff μ a x * kCoeff μ (s - x)
    else 0) s]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjlt : j < s := Finset.mem_range.mp hj
  have hs_sub : s - (s - 1 - j) = j + 1 := by omega
  have hs_sub' : s - (j + 1) = s - 1 - j := by omega
  have hcond :
      (1 ≤ s - (s - 1 - j) ∧ s ≤ printedTailP a + (s - 1 - j)) ↔
        j < printedTailP a := by
    constructor <;> intro h
    · omega
    · constructor <;> omega
  rw [hs_sub']
  by_cases hp : j < printedTailP a
  · have hc : 1 ≤ s - (s - 1 - j) ∧ s ≤ printedTailP a + (s - 1 - j) :=
      hcond.mpr hp
    rw [if_pos hc, if_pos hp, hs_sub]
    ring
  · have hc : ¬(1 ≤ s - (s - 1 - j) ∧ s ≤ printedTailP a + (s - 1 - j)) :=
      fun hc => hp (hcond.mp hc)
    rw [if_neg hc, if_neg hp]

theorem coeff_printedTailWSeries (μ : List Nat) (a s : Nat) :
    coeff s (printedTailWSeries μ a) = printedTailOmegaCoeff μ a s := by
  unfold printedTailWSeries printedTailOmegaCoeff
  rw [mul_sub, mul_one, map_sub, coeff_printedTailESeries,
    coeff_printedTailESeries_mul_lowJSeries]

theorem coeff_printedTailHighESeries_mul_W_eq_piecewiseSum
    (μ : List Nat) (a : Nat) :
    coeff a (printedTailHighESeries μ a * printedTailWSeries μ a) =
      ∑ x ∈ Finset.range (a + 1),
        (if x = 0 then printedTailOmegaCoeff μ a a
         else if printedTailP a < x then
           -hCoeff μ x * printedTailOmegaCoeff μ a (a - x)
         else 0) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_printedTailWSeries]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxle : x ≤ a := by
    have := Finset.mem_range.mp hx
    omega
  rw [coeff_printedTailHighESeries_piecewise μ a x hxle]
  by_cases hx0 : x = 0
  · subst hx0
    simp
  · rw [if_neg hx0]
    by_cases hpx : printedTailP a < x
    · rw [if_pos hpx]
      simp [hx0, hpx]
    · rw [if_neg hpx]
      simp [hx0, hpx]

theorem coeff_printedTailHighESeries_mul_highKSeries_eq_piecewise
    (μ : List Nat) (a s : Nat) (hsa : s ≤ a) :
    coeff s (printedTailHighESeries μ a * printedTailHighKSeries μ a) =
      if printedTailP a < s then kCoeff μ s else 0 := by
  have hale : a ≤ 2 * printedTailP a + 1 := by
    unfold printedTailP
    omega
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_range_succ']
  have htail :
      (∑ x ∈ Finset.range s,
          coeff (x + 1) (printedTailHighESeries μ a) *
            coeff (s - (x + 1)) (printedTailHighKSeries μ a)) = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    have hxlt : x < s := Finset.mem_range.mp hx
    by_cases hxlep : x + 1 ≤ printedTailP a
    · rw [coeff_printedTailHighESeries_eq_zero_of_le_p μ a (x + 1)
        (by omega) hxlep]
      simp
    · have hdeg_le_p : s - (x + 1) ≤ printedTailP a := by omega
      rw [coeff_printedTailHighKSeries_eq_zero_of_le_p μ a (s - (x + 1))
        hdeg_le_p]
      simp
  rw [htail]
  simp [printedTailHighESeries, printedTailHighKSeries]

theorem coeff_printedTailE_mul_highE_mul_highK_eq_piecewiseSum
    (μ : List Nat) (a : Nat) :
    coeff a
        (printedTailESeries μ a * printedTailHighESeries μ a *
          printedTailHighKSeries μ a) =
      ∑ s ∈ Finset.range (a + 1),
        (if printedTailP a < a - s then
          printedTailECoeff μ a s * kCoeff μ (a - s)
        else 0) := by
  rw [mul_assoc, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_printedTailESeries]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hsle : s ≤ a := by
    have := Finset.mem_range.mp hs
    omega
  rw [coeff_printedTailHighESeries_mul_highKSeries_eq_piecewise μ a (a - s)
    (by omega)]
  by_cases hsp : printedTailP a < a - s
  · simp [hsp]
  · simp [hsp]

/-- Integer-shape Gamma moment `Gamma(a-s)/(6^s Gamma(a))`, expressed as a
rational factorial ratio.  The large-tail proofs only use this for
`s <= printedTailR0 a`, where the subtractions do not underflow. -/
def gammaWeight (a s : Nat) : ℚ :=
  ((Nat.factorial (a - s - 1) : Nat) : ℚ) /
    ((6 : ℚ)^s * ((Nat.factorial (a - 1) : Nat) : ℚ))

def printedTailHRawSum (μ : List Nat) (a : Nat) : ℚ :=
  ((List.range (printedTailR0 a + 1)).map fun s : Nat =>
    hCoeff μ (a - s) * printedTailOmegaCoeff μ a s).sum

def printedTailKRawSum (μ : List Nat) (a : Nat) : ℚ :=
  ((List.range (printedTailR0 a + 1)).map fun s : Nat =>
    kCoeff μ (a - s) * printedTailECoeff μ a s).sum

private theorem sum_Ico_eq_sum_range_reverse_rat
    (F : Nat → ℚ) {lo hi : Nat} (hlohi : lo ≤ hi) :
    ∑ x ∈ Finset.Ico lo (hi + 1), F x =
      ∑ s ∈ Finset.range (hi + 1 - lo), F (hi - s) := by
  rw [Finset.sum_Ico_eq_sum_range]
  let K := hi + 1 - lo
  rw [← Finset.sum_range_reflect (fun j => F (lo + j)) K]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjK : j < K := Finset.mem_range.mp hj
  change F (lo + (K - 1 - j)) = F (hi - j)
  congr 1
  unfold K
  omega

theorem coeff_printedTailHighESeries_mul_W_eq_omega_sub_HRaw
    (μ : List Nat) (a : Nat) (ha : 1 ≤ a) :
    coeff a (printedTailHighESeries μ a * printedTailWSeries μ a) =
      printedTailOmegaCoeff μ a a - printedTailHRawSum μ a := by
  rw [coeff_printedTailHighESeries_mul_W_eq_piecewiseSum]
  unfold printedTailHRawSum
  rw [Prop51.list_range_map_sum]
  have hp_lt_a : printedTailP a < a := by
    unfold printedTailP
    omega
  have hlen : printedTailR0 a + 1 = a - printedTailP a := by
    unfold printedTailR0
    omega
  rw [hlen]
  let F : Nat → ℚ := fun x =>
    if x = 0 then printedTailOmegaCoeff μ a a
    else if printedTailP a < x then
      -hCoeff μ x * printedTailOmegaCoeff μ a (a - x)
    else 0
  change (∑ x ∈ Finset.range (a + 1), F x) =
    printedTailOmegaCoeff μ a a -
      ∑ s ∈ Finset.range (a - printedTailP a),
        hCoeff μ (a - s) * printedTailOmegaCoeff μ a s
  rw [Finset.range_eq_Ico]
  rw [← Finset.sum_Ico_consecutive F (by omega : 0 ≤ printedTailP a + 1)
    (by omega : printedTailP a + 1 ≤ a + 1)]
  rw [Nat.Ico_zero_eq_range]
  have hlow :
      (∑ x ∈ Finset.range (printedTailP a + 1), F x) =
        printedTailOmegaCoeff μ a a := by
    rw [Finset.sum_range_succ']
    have htail :
        (∑ x ∈ Finset.range (printedTailP a), F (x + 1)) = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      have hxlt : x < printedTailP a := Finset.mem_range.mp hx
      have hx0 : x + 1 ≠ 0 := by omega
      have hnot : ¬ printedTailP a < x + 1 := by omega
      simp [F, hnot]
    rw [htail]
    simp [F]
  have hhi :
      (∑ x ∈ Finset.Ico (printedTailP a + 1) (a + 1), F x) =
        -∑ s ∈ Finset.range (a - printedTailP a),
          hCoeff μ (a - s) * printedTailOmegaCoeff μ a s := by
    rw [sum_Ico_eq_sum_range_reverse_rat F (by omega : printedTailP a + 1 ≤ a)]
    have hlen' : a + 1 - (printedTailP a + 1) = a - printedTailP a := by omega
    rw [hlen']
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hslt : s < a - printedTailP a := Finset.mem_range.mp hs
    have hs_gt : printedTailP a < a - s := by omega
    have hs_ne : a - s ≠ 0 := by omega
    have hsub : a - (a - s) = s := by omega
    simp [F, hs_ne, hs_gt, hsub]
  rw [hlow, hhi]
  ring

theorem coeff_printedTailE_mul_highE_mul_highK_eq_KRaw
    (μ : List Nat) (a : Nat) (ha : 1 ≤ a) :
    coeff a
        (printedTailESeries μ a * printedTailHighESeries μ a *
          printedTailHighKSeries μ a) =
      printedTailKRawSum μ a := by
  rw [coeff_printedTailE_mul_highE_mul_highK_eq_piecewiseSum]
  unfold printedTailKRawSum
  rw [Prop51.list_range_map_sum]
  have hp_lt_a : printedTailP a < a := by
    unfold printedTailP
    omega
  have hlen : printedTailR0 a + 1 = a - printedTailP a := by
    unfold printedTailR0
    omega
  rw [hlen]
  let G : Nat → ℚ := fun s =>
    if printedTailP a < a - s then
      printedTailECoeff μ a s * kCoeff μ (a - s)
    else 0
  change (∑ s ∈ Finset.range (a + 1), G s) =
    ∑ s ∈ Finset.range (a - printedTailP a),
      kCoeff μ (a - s) * printedTailECoeff μ a s
  rw [Finset.range_eq_Ico]
  rw [← Finset.sum_Ico_consecutive G (by omega : 0 ≤ a - printedTailP a)
    (by omega : a - printedTailP a ≤ a + 1)]
  rw [Nat.Ico_zero_eq_range]
  have hlow :
      (∑ s ∈ Finset.range (a - printedTailP a), G s) =
        ∑ s ∈ Finset.range (a - printedTailP a),
          kCoeff μ (a - s) * printedTailECoeff μ a s := by
    refine Finset.sum_congr rfl fun s hs => ?_
    have hslt : s < a - printedTailP a := Finset.mem_range.mp hs
    have hactive : printedTailP a < a - s := by omega
    simp [G, hactive]
    ring
  have hhi :
      (∑ s ∈ Finset.Ico (a - printedTailP a) (a + 1), G s) = 0 := by
    refine Finset.sum_eq_zero fun s hs => ?_
    have hslo : a - printedTailP a ≤ s := (Finset.mem_Ico.mp hs).1
    have hnot : ¬ printedTailP a < a - s := by omega
    simp [G, hnot]
  rw [hlow, hhi, add_zero]

theorem printedCoeff_eq_tail_raw_split
    (μ : List Nat) (a : Nat) (ha : 1 ≤ a) :
    printedCoeff μ a =
      printedTailOmegaCoeff μ a a - printedTailHRawSum μ a -
        printedTailKRawSum μ a := by
  have hseries := coeff_printedTail_series_split_eq_printedCoeff μ a
  rw [map_sub, coeff_printedTailHighESeries_mul_W_eq_omega_sub_HRaw μ a ha,
    coeff_printedTailE_mul_highE_mul_highK_eq_KRaw μ a ha] at hseries
  exact hseries.symm

def printedTailMainSum (μ : List Nat) (a : Nat) : ℚ :=
  ((List.range (printedTailR0 a + 1)).map fun s : Nat =>
    gammaWeight a s * printedTailOmegaCoeff μ a s).sum

def printedTailDen (μ : List Nat) (a : Nat) : ℚ :=
  ((N μ : Nat) : ℚ) * Prop51.c a

def printedTailHNormSum (μ : List Nat) (a : Nat) : ℚ :=
  ((List.range (printedTailR0 a + 1)).map fun s : Nat =>
    hCoeff μ (a - s) * printedTailOmegaCoeff μ a s / printedTailDen μ a).sum

def printedTailKNormSum (μ : List Nat) (a : Nat) : ℚ :=
  ((List.range (printedTailR0 a + 1)).map fun s : Nat =>
    kCoeff μ (a - s) * printedTailECoeff μ a s).sum / printedTailDen μ a

def printedTailOmegaNorm (μ : List Nat) (a : Nat) : ℚ :=
  printedTailOmegaCoeff μ a a / printedTailDen μ a

def printedTailSplitRhs (μ : List Nat) (a : Nat) : ℚ :=
  printedTailHNormSum μ a + printedTailKNormSum μ a - printedTailOmegaNorm μ a

/-- Exact normalized split target corresponding to equation `(exact-split)` in
the printed proof. -/
def PrintedTailExactSplit : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      (-printedCoeff μ a) / printedTailDen μ a = printedTailSplitRhs μ a

theorem printedTailExactSplit_closed : PrintedTailExactSplit := by
  intro a ha μ _hμ
  have hraw := printedCoeff_eq_tail_raw_split μ a (by omega)
  have hHnorm :
      printedTailHNormSum μ a =
        printedTailHRawSum μ a / printedTailDen μ a := by
    unfold printedTailHNormSum printedTailHRawSum
    rw [Prop51.list_range_map_sum, Prop51.list_range_map_sum]
    rw [← Finset.sum_div]
  have hKnorm :
      printedTailKNormSum μ a =
        printedTailKRawSum μ a / printedTailDen μ a := by
    rfl
  unfold printedTailSplitRhs printedTailOmegaNorm
  rw [hHnorm, hKnorm]
  rw [hraw]
  ring

/-- The Gamma-margin plus truncation step, stated directly for the finite main
sum `sum gamma_s omega_s`. -/
def PrintedTailMainLowerBound : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      9 / (40 * ((a : ℚ) - 2)) - 1 / (a : ℚ)^2 ≤
        printedTailMainSum μ a

def printedTailHErrorBudget (a : Nat) : ℚ :=
  (86069 / 3125 : ℚ) / (a : ℚ)^2

/-- The `h_{a-s}` replacement error:
`86069/3125 = 36*(2304/3125)+1`. -/
def PrintedTailHErrorBound : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      |printedTailHNormSum μ a - printedTailMainSum μ a| ≤
        printedTailHErrorBudget a

/-- Positive coefficientwise majorant for the low exponential
`E(t)=exp(-L(t))`, using absolute logarithmic coefficients. -/
def printedTailEAbsCoeff (μ : List Nat) (a s : Nat) : ℚ :=
  Prop51.expCoeff (fun r => |printedTailLowExpInput μ a r|) s

/-- Positive coefficientwise majorant for
`W(t)=E(t)(1-J(t))`, namely `exp(|L|) * (1 + |J|)` at coefficient level. -/
def printedTailWAbsCoeff (μ : List Nat) (a s : Nat) : ℚ :=
  printedTailEAbsCoeff μ a s +
    ((List.range s).map fun j : Nat =>
      let r := j + 1
      |if r ≤ printedTailP a then
        kCoeff μ r * printedTailEAbsCoeff μ a (s - r)
      else 0|).sum

private theorem printedTailEAbsCoeff_nonneg (μ : List Nat) (a s : Nat) :
    0 ≤ printedTailEAbsCoeff μ a s := by
  unfold printedTailEAbsCoeff
  exact Prop51.expCoeff_nonneg (fun r => abs_nonneg _) s

theorem abs_printedTailECoeff_le_EAbsCoeff (μ : List Nat) (a s : Nat) :
    |printedTailECoeff μ a s| ≤ printedTailEAbsCoeff μ a s := by
  unfold printedTailECoeff printedTailEAbsCoeff
  exact Prop51.abs_expCoeff_le_of_abs_le (fun r => abs_nonneg _)
    (fun r => le_rfl) s

theorem abs_printedTailOmegaCoeff_le_WAbsCoeff
    (μ : List Nat) (a s : Nat) :
    |printedTailOmegaCoeff μ a s| ≤ printedTailWAbsCoeff μ a s := by
  unfold printedTailOmegaCoeff printedTailWAbsCoeff
  have hconv :
      |((List.range s).map fun j : Nat =>
          let r := j + 1
          if r ≤ printedTailP a then
            kCoeff μ r * printedTailECoeff μ a (s - r)
          else 0).sum|
        ≤
      ((List.range s).map fun j : Nat =>
          |let r := j + 1
          if r ≤ printedTailP a then
            kCoeff μ r * printedTailEAbsCoeff μ a (s - r)
          else 0|).sum := by
    rw [Prop51.list_range_map_sum, Prop51.list_range_map_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun j hj => ?_
    dsimp only
    by_cases hr : j + 1 ≤ printedTailP a
    · simp [hr]
      rw [abs_of_nonneg (printedTailEAbsCoeff_nonneg μ a (s - (j + 1)))]
      exact mul_le_mul_of_nonneg_left
        (abs_printedTailECoeff_le_EAbsCoeff μ a (s - (j + 1)))
        (abs_nonneg _)
    · simp [hr]
  calc
    |printedTailECoeff μ a s -
        ((List.range s).map fun j : Nat =>
          let r := j + 1
          if r ≤ printedTailP a then
            kCoeff μ r * printedTailECoeff μ a (s - r)
          else 0).sum|
        ≤
      |printedTailECoeff μ a s| +
        |((List.range s).map fun j : Nat =>
          let r := j + 1
          if r ≤ printedTailP a then
            kCoeff μ r * printedTailECoeff μ a (s - r)
          else 0).sum| := by
          calc
            |printedTailECoeff μ a s -
                ((List.range s).map fun j : Nat =>
                  let r := j + 1
                  if r ≤ printedTailP a then
                    kCoeff μ r * printedTailECoeff μ a (s - r)
                  else 0).sum|
                =
              |printedTailECoeff μ a s +
                -((List.range s).map fun j : Nat =>
                  let r := j + 1
                  if r ≤ printedTailP a then
                    kCoeff μ r * printedTailECoeff μ a (s - r)
                  else 0).sum| := by ring_nf
            _ ≤
              |printedTailECoeff μ a s| +
                |-((List.range s).map fun j : Nat =>
                  let r := j + 1
                  if r ≤ printedTailP a then
                    kCoeff μ r * printedTailECoeff μ a (s - r)
                  else 0).sum| := abs_add_le _ _
            _ =
              |printedTailECoeff μ a s| +
                |((List.range s).map fun j : Nat =>
                  let r := j + 1
                  if r ≤ printedTailP a then
                    kCoeff μ r * printedTailECoeff μ a (s - r)
                  else 0).sum| := by rw [abs_neg]
    _ ≤
      printedTailEAbsCoeff μ a s +
        ((List.range s).map fun j : Nat =>
          |let r := j + 1
          if r ≤ printedTailP a then
            kCoeff μ r * printedTailEAbsCoeff μ a (s - r)
          else 0|).sum := by
        exact add_le_add
          (abs_printedTailECoeff_le_EAbsCoeff μ a s) hconv

/-- Majorant moment estimates for `exp(|L|)*(1+|J|)` and `exp(|L|)`.
These are the coefficientwise-positive moment bounds that correspond most
directly to `\widehat W` and `\widehat E` in the printed proof. -/
def PrintedTailMajorantMomentBounds : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      (∑ s ∈ Finset.range (printedTailR0 a + 1),
          gammaWeight a s * printedTailWAbsCoeff μ a s ≤ 9) ∧
      (∑ s ∈ Finset.range (printedTailR0 a + 1),
          (s : ℚ) * gammaWeight a s * printedTailWAbsCoeff μ a s ≤ 18) ∧
      (∑ s ∈ Finset.range (printedTailR0 a + 1),
          gammaWeight a s * printedTailEAbsCoeff μ a s ≤ 9)

/-- The two absolute-moment estimates from the printed proof:
`sum gamma_s |omega_s| <= 9` and
`sum s gamma_s |omega_s| <= 18`.

This is intentionally stated in the same finite `s <= r_0` language as the
tail split above.  The following theorem proves that these two moments imply
the displayed `h`-replacement error, using only the already-formalized
`d`-ratio estimate and elementary partition bounds. -/
def PrintedTailAbsoluteMomentBounds : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      (∑ s ∈ Finset.range (printedTailR0 a + 1),
          gammaWeight a s * |printedTailOmegaCoeff μ a s| ≤ 9) ∧
      (∑ s ∈ Finset.range (printedTailR0 a + 1),
          (s : ℚ) * gammaWeight a s * |printedTailOmegaCoeff μ a s| ≤ 18)

private theorem gammaWeight_nonneg {a s : Nat} (_hs : s < a) :
    0 ≤ gammaWeight a s := by
  unfold gammaWeight
  positivity

private theorem gammaWeight_pos {a s : Nat} (_hs : s < a) :
    0 < gammaWeight a s := by
  unfold gammaWeight
  positivity

private theorem printedTail_range_lt_a {a s : Nat} (ha : 150 ≤ a)
    (hs : s ∈ Finset.range (printedTailR0 a + 1)) : s < a := by
  have hsle : s ≤ printedTailR0 a := by
    have := Finset.mem_range.mp hs
    omega
  unfold printedTailR0 printedTailP at hsle
  omega

private theorem printedTail_range_p_succ_le {a s : Nat} (ha : 150 ≤ a)
    (hs : s ∈ Finset.range (printedTailR0 a + 1)) :
    printedTailP a + 1 ≤ a - s := by
  have hp_lt_a : printedTailP a < a := by
    unfold printedTailP
    omega
  have hlen : printedTailR0 a + 1 = a - printedTailP a := by
    unfold printedTailR0
    omega
  have hslt : s < a - printedTailP a := by
    simpa [hlen] using Finset.mem_range.mp hs
  omega

private theorem printedTail_two_mul_sub_ge {a s : Nat} (ha : 150 ≤ a)
    (hs : s ∈ Finset.range (printedTailR0 a + 1)) :
    a ≤ 2 * (a - s) := by
  have hp := printedTail_range_p_succ_le (a := a) (s := s) ha hs
  unfold printedTailP at hp
  omega

theorem printedTailAbsoluteMomentBounds_of_majorant
    (hmaj : PrintedTailMajorantMomentBounds) :
    PrintedTailAbsoluteMomentBounds := by
  intro a ha μ hμ
  have hmajW0 := (hmaj a ha μ hμ).1
  have hmajW1 := (hmaj a ha μ hμ).2.1
  constructor
  · calc
      ∑ s ∈ Finset.range (printedTailR0 a + 1),
          gammaWeight a s * |printedTailOmegaCoeff μ a s|
          ≤
        ∑ s ∈ Finset.range (printedTailR0 a + 1),
          gammaWeight a s * printedTailWAbsCoeff μ a s := by
          refine Finset.sum_le_sum fun s hs => ?_
          have hslt := printedTail_range_lt_a (a := a) (s := s) ha hs
          exact mul_le_mul_of_nonneg_left
            (abs_printedTailOmegaCoeff_le_WAbsCoeff μ a s)
            (gammaWeight_nonneg hslt)
      _ ≤ 9 := hmajW0
  · calc
      ∑ s ∈ Finset.range (printedTailR0 a + 1),
          (s : ℚ) * gammaWeight a s * |printedTailOmegaCoeff μ a s|
          ≤
        ∑ s ∈ Finset.range (printedTailR0 a + 1),
          (s : ℚ) * gammaWeight a s * printedTailWAbsCoeff μ a s := by
          refine Finset.sum_le_sum fun s hs => ?_
          have hslt := printedTail_range_lt_a (a := a) (s := s) ha hs
          exact mul_le_mul_of_nonneg_left
            (abs_printedTailOmegaCoeff_le_WAbsCoeff μ a s)
            (mul_nonneg (by positivity) (gammaWeight_nonneg hslt))
      _ ≤ 18 := hmajW1

private theorem inv_q_pow_le_q_over_two_pow_succ {mi r : Nat}
    (hmi : 1 ≤ mi) :
    1 / (((mi + 1 : Nat) : ℚ)^r) ≤
      (((mi + 1 : Nat) : ℚ)) / (2 : ℚ)^(r + 1) := by
  let q : ℚ := ((mi + 1 : Nat) : ℚ)
  have hq2 : (2 : ℚ) ≤ q := by
    dsimp [q]
    exact_mod_cast (by omega : 2 ≤ mi + 1)
  have hqpos : 0 < q := by
    dsimp [q]
    exact_mod_cast Nat.succ_pos mi
  have hden1 : 0 < q^r := pow_pos hqpos r
  have hden2 : 0 < (2 : ℚ)^(r + 1) := by positivity
  have hpow : (2 : ℚ)^(r + 1) ≤ q^(r + 1) :=
    pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 2) hq2 (r + 1)
  rw [div_le_div_iff₀ hden1 hden2]
  calc
    (1 : ℚ) * (2 : ℚ)^(r + 1) ≤ q^(r + 1) := by simpa using hpow
    _ = q * q^r := by rw [pow_succ']

private theorem sum_q_div_const (μ : List Nat) {D : ℚ} :
    (μ.map fun mi : Nat => (((mi + 1 : Nat) : ℚ)) / D).sum =
      (((μ.map (· + 1)).sum : Nat) : ℚ) / D := by
  induction μ with
  | nil => simp
  | cons mi μ ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      push_cast
      ring

private theorem sPower_nonneg (μ : List Nat) (r : Nat) :
    0 ≤ sPower μ r := by
  unfold sPower
  refine List.sum_nonneg fun x hx => ?_
  simp only [List.mem_map] at hx
  obtain ⟨mi, _hmi, rfl⟩ := hx
  positivity

private theorem sPower_le_N_over_two_pow_succ
    {μ : List Nat} (hpos : ∀ m ∈ μ, 1 ≤ m) (r : Nat) :
    sPower μ r ≤ (N μ : ℚ) / (2 : ℚ)^(r + 1) := by
  unfold sPower N
  calc
    (μ.map fun mi : Nat => 1 / (((mi + 1 : Nat) : ℚ)^r)).sum
        ≤ (μ.map fun mi : Nat =>
            (((mi + 1 : Nat) : ℚ)) / (2 : ℚ)^(r + 1)).sum := by
          refine List.sum_le_sum fun mi hmi => ?_
          exact inv_q_pow_le_q_over_two_pow_succ (hpos mi hmi)
    _ = (((μ.map (· + 1)).sum : Nat) : ℚ) / (2 : ℚ)^(r + 1) :=
          sum_q_div_const μ

private theorem sPower_div_N_le_two_pow_succ
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) (r : Nat) :
    sPower μ r / (N μ : ℚ) ≤ 1 / (2 : ℚ)^(r + 1) := by
  have hμ_copy := hμ
  obtain ⟨_hsum, hpos⟩ := hμ
  have hNpos : (0 : ℚ) < (N μ : ℚ) := by
    have hNnat : 0 < N μ := printedTail_N_pos (a := a) (μ := μ) ha hμ_copy
    exact_mod_cast hNnat
  have hmain := sPower_le_N_over_two_pow_succ (μ := μ) hpos r
  rw [div_le_iff₀ hNpos]
  calc
    sPower μ r ≤ (N μ : ℚ) / (2 : ℚ)^(r + 1) := hmain
    _ = (1 / (2 : ℚ)^(r + 1)) * (N μ : ℚ) := by ring

private theorem one_div_two_pow_mono {u v : Nat} (hvu : v ≤ u) :
    1 / (2 : ℚ)^u ≤ 1 / (2 : ℚ)^v := by
  have hpow : (2 : ℚ)^v ≤ (2 : ℚ)^u :=
    pow_le_pow_right₀ (by norm_num : (0 : ℚ) ≤ 2) hvu
  exact one_div_le_one_div_of_le (by positivity) hpow

def printedTailPowBudgetRhs (a : Nat) : ℚ :=
  9 / (2 : ℚ)^(printedTailP a + 2)

def printedTailPowBudgetScaled (a : Nat) : ℚ :=
  (a : ℚ)^2 * printedTailPowBudgetRhs a

private theorem printedTailPowBudgetScaled_step8 (a : Nat) (ha : 150 ≤ a) :
    printedTailPowBudgetScaled (a + 8) ≤ printedTailPowBudgetScaled a := by
  unfold printedTailPowBudgetScaled printedTailPowBudgetRhs printedTailP
  have hdiv : (a + 8) / 2 = a / 2 + 4 := by
    simpa [show 8 = 4 * 2 by norm_num] using
      Nat.add_mul_div_right a 4 (by decide : 0 < 2)
  rw [hdiv]
  rw [show a / 2 + 4 + 2 = a / 2 + 2 + 4 by omega, pow_add]
  norm_num
  have hpoly : (((a + 8 : Nat) : ℚ)^2 / 16 ≤ (a : ℚ)^2) := by
    push_cast
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  have hnonneg : 0 ≤ 9 / (2 : ℚ) ^ (a / 2 + 2) := by positivity
  calc
    ((a : ℚ) + 8) ^ 2 *
        (9 / ((2 : ℚ) ^ (a / 2 + 2) * 16))
        = (((a + 8 : Nat) : ℚ)^2 / 16) *
            (9 / (2 : ℚ) ^ (a / 2 + 2)) := by
            push_cast
            ring
    _ ≤ (a : ℚ)^2 * (9 / (2 : ℚ) ^ (a / 2 + 2)) :=
        mul_le_mul_of_nonneg_right hpoly hnonneg

private theorem printedTailPowBudgetScaled_150 :
    printedTailPowBudgetScaled 150 < 1 := by native_decide
private theorem printedTailPowBudgetScaled_151 :
    printedTailPowBudgetScaled 151 < 1 := by native_decide
private theorem printedTailPowBudgetScaled_152 :
    printedTailPowBudgetScaled 152 < 1 := by native_decide
private theorem printedTailPowBudgetScaled_153 :
    printedTailPowBudgetScaled 153 < 1 := by native_decide
private theorem printedTailPowBudgetScaled_154 :
    printedTailPowBudgetScaled 154 < 1 := by native_decide
private theorem printedTailPowBudgetScaled_155 :
    printedTailPowBudgetScaled 155 < 1 := by native_decide
private theorem printedTailPowBudgetScaled_156 :
    printedTailPowBudgetScaled 156 < 1 := by native_decide
private theorem printedTailPowBudgetScaled_157 :
    printedTailPowBudgetScaled 157 < 1 := by native_decide

theorem printedTailPowBudget_bound (a : Nat) (ha : 150 ≤ a) :
    printedTailPowBudgetRhs a ≤ 1 / (a : ℚ)^2 := by
  have hscaled : printedTailPowBudgetScaled a < 1 := by
    refine Nat.strong_induction_on a ?_ ha
    intro a ih ha
    by_cases hle : a ≤ 157
    · interval_cases a <;> first
        | exact printedTailPowBudgetScaled_150
        | exact printedTailPowBudgetScaled_151
        | exact printedTailPowBudgetScaled_152
        | exact printedTailPowBudgetScaled_153
        | exact printedTailPowBudgetScaled_154
        | exact printedTailPowBudgetScaled_155
        | exact printedTailPowBudgetScaled_156
        | exact printedTailPowBudgetScaled_157
    · have hprev_ge : 150 ≤ a - 8 := by omega
      have hprev_lt : a - 8 < a := by omega
      have hprev : printedTailPowBudgetScaled (a - 8) < 1 :=
        ih (a - 8) hprev_lt hprev_ge
      have hstep :
          printedTailPowBudgetScaled ((a - 8) + 8) ≤
            printedTailPowBudgetScaled (a - 8) :=
        printedTailPowBudgetScaled_step8 (a - 8) hprev_ge
      have hadd : (a - 8) + 8 = a := by omega
      rw [hadd] at hstep
      exact lt_of_le_of_lt hstep hprev
  unfold printedTailPowBudgetScaled at hscaled
  have ha_sq_pos : (0 : ℚ) < (a : ℚ)^2 := by
    have ha_pos : (0 : ℚ) < (a : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 150) ha)
    positivity
  rw [le_div_iff₀ ha_sq_pos]
  nlinarith

private theorem hCoeff_div_den_eq_gammaWeight_mul
    {a s : Nat} {μ : List Nat} (hs : s < a) (hN : N μ ≠ 0) :
    hCoeff μ (a - s) / printedTailDen μ a =
      gammaWeight a s * (Prop51.d (a - s) / Prop51.d a) *
        (1 - sPower μ (a - s) / (N μ : ℚ)) := by
  have ha1 : 1 ≤ a := by omega
  have has1 : 1 ≤ a - s := by omega
  have hNq : ((N μ : Nat) : ℚ) ≠ 0 := by exact_mod_cast hN
  have hda : Prop51.d a ≠ 0 := (Prop51.d_pos a ha1).ne'
  have hdas : Prop51.d (a - s) ≠ 0 := (Prop51.d_pos (a - s) has1).ne'
  have hfac_a : (((a - 1).factorial : Nat) : ℚ) ≠ 0 := by positivity
  have hfac_as : ((((a - s - 1).factorial : Nat) : ℚ)) ≠ 0 := by positivity
  have hpow6 : (6 : ℚ)^a = (6 : ℚ)^(a - s) * (6 : ℚ)^s := by
    nth_rewrite 1 [show a = (a - s) + s by omega]
    rw [pow_add]
  unfold hCoeff printedTailDen gammaWeight
  rw [Prop51.c_eq_d (a - s), Prop51.c_eq_d a, hpow6]
  field_simp [hNq, hda, hdas, hfac_a, hfac_as]

private theorem hCoeff_div_den_sub_gammaWeight_abs_le
    {a s : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a))
    (hs : s ∈ Finset.range (printedTailR0 a + 1)) :
    |hCoeff μ (a - s) / printedTailDen μ a - gammaWeight a s| ≤
      (2 * (2304 / 3125 : ℚ) / (a : ℚ)^2) *
          ((s : ℚ) * gammaWeight a s) +
        (1 / (2 : ℚ)^(printedTailP a + 2)) * gammaWeight a s := by
  have hslt : s < a := printedTail_range_lt_a (a := a) (s := s) ha hs
  have hNpos_nat : 0 < N μ := printedTail_N_pos (a := a) (μ := μ) ha hμ
  have hNqpos : (0 : ℚ) < (N μ : ℚ) := by exact_mod_cast hNpos_nat
  have hgamma_nonneg : 0 ≤ gammaWeight a s := gammaWeight_nonneg hslt
  have hdpos_a : 0 < Prop51.d a := Prop51.d_pos a (by omega)
  have hdpos_as : 0 < Prop51.d (a - s) := Prop51.d_pos (a - s) (by omega)
  set R : ℚ := Prop51.d (a - s) / Prop51.d a with hR
  set x : ℚ := sPower μ (a - s) / (N μ : ℚ) with hx
  have hR_nonneg : 0 ≤ R := by
    rw [hR]
    exact div_nonneg hdpos_as.le hdpos_a.le
  have hR_le_one : R ≤ 1 := by
    rw [hR]
    rw [div_le_one₀ hdpos_a]
    exact Prop51.d_mono (Nat.sub_le a s)
  have hx_nonneg : 0 ≤ x := by
    rw [hx]
    exact div_nonneg (sPower_nonneg μ (a - s)) hNqpos.le
  have hrepr := hCoeff_div_den_eq_gammaWeight_mul
    (a := a) (s := s) (μ := μ) hslt (ne_of_gt hNpos_nat)
  rw [hrepr]
  change |gammaWeight a s * R * (1 - x) - gammaWeight a s| ≤
      (2 * (2304 / 3125 : ℚ) / (a : ℚ)^2) *
          ((s : ℚ) * gammaWeight a s) +
        (1 / (2 : ℚ)^(printedTailP a + 2)) * gammaWeight a s
  rw [show gammaWeight a s * R * (1 - x) - gammaWeight a s =
        gammaWeight a s * (R * (1 - x) - 1) by ring]
  rw [abs_mul, abs_of_nonneg hgamma_nonneg]
  have hmain_nonpos :
      R * (1 - x) - 1 ≤ 0 := by
    have : R * (1 - x) ≤ 1 := by
      calc
        R * (1 - x) ≤ R * 1 := by
          exact mul_le_mul_of_nonneg_left (by linarith : 1 - x ≤ 1) hR_nonneg
        _ ≤ 1 := by simpa using hR_le_one
    exact sub_nonpos.mpr this
  rw [abs_of_nonpos hmain_nonpos]
  have hdiff_decomp :
      -(R * (1 - x) - 1) = (1 - R) + R * x := by
    ring
  rw [hdiff_decomp]
  have hratio := Prop51.d_ratio_lb a s hslt
  have hR_drift :
      1 - R ≤
        (2304 / 3125 : ℚ) *
          ((s : ℚ) / ((a : ℚ) * ((a - s : Nat) : ℚ))) := by
    rw [hR]
    linarith
  have hsub_cast : ((a - s : Nat) : ℚ) = (a : ℚ) - (s : ℚ) := by
    rw [Nat.cast_sub hslt.le]
  have hfrac :
      (s : ℚ) / ((a : ℚ) * ((a - s : Nat) : ℚ))
        ≤ 2 * (s : ℚ) / (a : ℚ)^2 := by
    rw [hsub_cast]
    have haQ : (0 : ℚ) < a := by exact_mod_cast (by omega : 0 < a)
    have hsubQ : (0 : ℚ) < (a : ℚ) - (s : ℚ) := by
      rw [← hsub_cast]
      exact_mod_cast (by omega : 0 < a - s)
    have hs_nonneg : (0 : ℚ) ≤ s := by positivity
    have htwice : (a : ℚ) ≤ 2 * ((a : ℚ) - (s : ℚ)) := by
      have hnat := printedTail_two_mul_sub_ge (a := a) (s := s) ha hs
      rw [← hsub_cast]
      exact_mod_cast hnat
    have hrecip :
        1 / ((a : ℚ) * ((a : ℚ) - (s : ℚ)))
          ≤ 2 / (a : ℚ)^2 := by
      field_simp [haQ.ne', hsubQ.ne']
      nlinarith
    calc
      (s : ℚ) / ((a : ℚ) * ((a : ℚ) - (s : ℚ)))
          = (s : ℚ) * (1 / ((a : ℚ) * ((a : ℚ) - (s : ℚ)))) := by ring
      _ ≤ (s : ℚ) * (2 / (a : ℚ)^2) :=
          mul_le_mul_of_nonneg_left hrecip hs_nonneg
      _ = 2 * (s : ℚ) / (a : ℚ)^2 := by ring
  have hpow_succ :
      1 / (2 : ℚ)^(a - s + 1) ≤
        1 / (2 : ℚ)^(printedTailP a + 2) := by
    have hp := printedTail_range_p_succ_le (a := a) (s := s) ha hs
    exact one_div_two_pow_mono (by omega : printedTailP a + 2 ≤ a - s + 1)
  have hx_le :
      x ≤ 1 / (2 : ℚ)^(printedTailP a + 2) := by
    rw [hx]
    exact (sPower_div_N_le_two_pow_succ
      (a := a) (μ := μ) ha hμ (a - s)).trans hpow_succ
  calc
    gammaWeight a s * ((1 - R) + R * x)
        ≤ gammaWeight a s *
            (((2304 / 3125 : ℚ) *
                ((s : ℚ) / ((a : ℚ) * ((a - s : Nat) : ℚ)))) + x) := by
          have hRx_le_x : R * x ≤ x := by
            nlinarith [hR_nonneg, hR_le_one, hx_nonneg]
          have hsum :
              (1 - R) + R * x ≤
                ((2304 / 3125 : ℚ) *
                  ((s : ℚ) / ((a : ℚ) * ((a - s : Nat) : ℚ)))) + x := by
            nlinarith [hR_drift, hRx_le_x]
          exact mul_le_mul_of_nonneg_left hsum hgamma_nonneg
    _ ≤ gammaWeight a s *
            (((2304 / 3125 : ℚ) * (2 * (s : ℚ) / (a : ℚ)^2)) +
              1 / (2 : ℚ)^(printedTailP a + 2)) := by
          have hdrift :
              (2304 / 3125 : ℚ) *
                  ((s : ℚ) / ((a : ℚ) * ((a - s : Nat) : ℚ))) ≤
                (2304 / 3125 : ℚ) * (2 * (s : ℚ) / (a : ℚ)^2) :=
            mul_le_mul_of_nonneg_left hfrac (by norm_num)
          have hsum :
              ((2304 / 3125 : ℚ) *
                  ((s : ℚ) / ((a : ℚ) * ((a - s : Nat) : ℚ)))) + x ≤
                ((2304 / 3125 : ℚ) * (2 * (s : ℚ) / (a : ℚ)^2)) +
                  1 / (2 : ℚ)^(printedTailP a + 2) := by
            linarith
          exact mul_le_mul_of_nonneg_left hsum hgamma_nonneg
    _ =
      (2 * (2304 / 3125 : ℚ) / (a : ℚ)^2) *
          ((s : ℚ) * gammaWeight a s) +
        (1 / (2 : ℚ)^(printedTailP a + 2)) * gammaWeight a s := by ring

theorem printedTailHErrorBound_of_absoluteMoments
    (hmom : PrintedTailAbsoluteMomentBounds) :
    PrintedTailHErrorBound := by
  intro a ha μ hμ
  have hmom0 := (hmom a ha μ hμ).1
  have hmom1 := (hmom a ha μ hμ).2
  have hpowBudget := printedTailPowBudget_bound a ha
  unfold printedTailHNormSum printedTailMainSum
  rw [Prop51.list_range_map_sum, Prop51.list_range_map_sum]
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm :
      ∑ x ∈ Finset.range (printedTailR0 a + 1),
          |hCoeff μ (a - x) * printedTailOmegaCoeff μ a x /
              printedTailDen μ a -
            gammaWeight a x * printedTailOmegaCoeff μ a x|
        ≤
      (2 * (2304 / 3125 : ℚ) / (a : ℚ)^2) *
          (∑ x ∈ Finset.range (printedTailR0 a + 1),
            (x : ℚ) * gammaWeight a x * |printedTailOmegaCoeff μ a x|) +
        (1 / (2 : ℚ)^(printedTailP a + 2)) *
          (∑ x ∈ Finset.range (printedTailR0 a + 1),
            gammaWeight a x * |printedTailOmegaCoeff μ a x|) := by
    calc
      ∑ x ∈ Finset.range (printedTailR0 a + 1),
          |hCoeff μ (a - x) * printedTailOmegaCoeff μ a x /
              printedTailDen μ a -
            gammaWeight a x * printedTailOmegaCoeff μ a x|
          =
        ∑ x ∈ Finset.range (printedTailR0 a + 1),
          |(hCoeff μ (a - x) / printedTailDen μ a -
              gammaWeight a x) * printedTailOmegaCoeff μ a x| := by
            refine Finset.sum_congr rfl fun x hx => ?_
            congr 1
            ring
      _ ≤
        ∑ x ∈ Finset.range (printedTailR0 a + 1),
          ((2 * (2304 / 3125 : ℚ) / (a : ℚ)^2) *
              ((x : ℚ) * gammaWeight a x) +
            (1 / (2 : ℚ)^(printedTailP a + 2)) * gammaWeight a x) *
              |printedTailOmegaCoeff μ a x| := by
            refine Finset.sum_le_sum fun x hx => ?_
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right
              (hCoeff_div_den_sub_gammaWeight_abs_le
                (a := a) (s := x) (μ := μ) ha hμ hx)
              (abs_nonneg _)
      _ =
        (2 * (2304 / 3125 : ℚ) / (a : ℚ)^2) *
            (∑ x ∈ Finset.range (printedTailR0 a + 1),
              (x : ℚ) * gammaWeight a x * |printedTailOmegaCoeff μ a x|) +
          (1 / (2 : ℚ)^(printedTailP a + 2)) *
            (∑ x ∈ Finset.range (printedTailR0 a + 1),
              gammaWeight a x * |printedTailOmegaCoeff μ a x|) := by
            calc
              ∑ x ∈ Finset.range (printedTailR0 a + 1),
                  ((2 * (2304 / 3125 : ℚ) / (a : ℚ)^2) *
                      ((x : ℚ) * gammaWeight a x) +
                    (1 / (2 : ℚ)^(printedTailP a + 2)) * gammaWeight a x) *
                    |printedTailOmegaCoeff μ a x|
                  =
                ∑ x ∈ Finset.range (printedTailR0 a + 1),
                  ((2 * (2304 / 3125 : ℚ) / (a : ℚ)^2) *
                      ((x : ℚ) * gammaWeight a x *
                        |printedTailOmegaCoeff μ a x|) +
                    (1 / (2 : ℚ)^(printedTailP a + 2)) *
                      (gammaWeight a x *
                        |printedTailOmegaCoeff μ a x|)) := by
                    refine Finset.sum_congr rfl fun x hx => ?_
                    ring
              _ = _ := by
                    rw [Finset.sum_add_distrib, ← Finset.mul_sum,
                      ← Finset.mul_sum]
  calc
    ∑ x ∈ Finset.range (printedTailR0 a + 1),
        |hCoeff μ (a - x) * printedTailOmegaCoeff μ a x /
            printedTailDen μ a -
          gammaWeight a x * printedTailOmegaCoeff μ a x|
        ≤
      (2 * (2304 / 3125 : ℚ) / (a : ℚ)^2) *
          (∑ x ∈ Finset.range (printedTailR0 a + 1),
            (x : ℚ) * gammaWeight a x * |printedTailOmegaCoeff μ a x|) +
        (1 / (2 : ℚ)^(printedTailP a + 2)) *
          (∑ x ∈ Finset.range (printedTailR0 a + 1),
            gammaWeight a x * |printedTailOmegaCoeff μ a x|) := hterm
    _ ≤
      (2 * (2304 / 3125 : ℚ) / (a : ℚ)^2) * 18 +
        (1 / (2 : ℚ)^(printedTailP a + 2)) * 9 := by
          gcongr
    _ ≤
      (2 * (2304 / 3125 : ℚ) / (a : ℚ)^2) * 18 +
        1 / (a : ℚ)^2 := by
          have hpow9 :
              (1 / (2 : ℚ)^(printedTailP a + 2)) * 9
                ≤ 1 / (a : ℚ)^2 := by
            unfold printedTailPowBudgetRhs at hpowBudget
            convert hpowBudget using 1
            ring
          linarith
    _ = printedTailHErrorBudget a := by
          unfold printedTailHErrorBudget
          ring

def PrintedTailKErrorBound : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      |printedTailKNormSum μ a| ≤ 1 / (a : ℚ)^2

/-- The absolute moment needed for the `k`-error:
`sum gamma_s |e_s| <= 9`.  In the printed proof this is obtained from the
same coefficientwise majorant used for the `omega` absolute moments, since
`E` is dominated by the positive exponential majorant for `W`. -/
def PrintedTailEAbsoluteMomentBound : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      ∑ s ∈ Finset.range (printedTailR0 a + 1),
          gammaWeight a s * |printedTailECoeff μ a s| ≤ 9

theorem printedTailEAbsoluteMomentBound_of_majorant
    (hmaj : PrintedTailMajorantMomentBounds) :
    PrintedTailEAbsoluteMomentBound := by
  intro a ha μ hμ
  have hmajE := (hmaj a ha μ hμ).2.2
  calc
    ∑ s ∈ Finset.range (printedTailR0 a + 1),
        gammaWeight a s * |printedTailECoeff μ a s|
        ≤
      ∑ s ∈ Finset.range (printedTailR0 a + 1),
        gammaWeight a s * printedTailEAbsCoeff μ a s := by
        refine Finset.sum_le_sum fun s hs => ?_
        have hslt := printedTail_range_lt_a (a := a) (s := s) ha hs
        exact mul_le_mul_of_nonneg_left
          (abs_printedTailECoeff_le_EAbsCoeff μ a s)
          (gammaWeight_nonneg hslt)
    _ ≤ 9 := hmajE

def printedTailKPowBudgetRhs (a : Nat) : ℚ :=
  9 / (2 : ℚ)^(printedTailP a)

def printedTailKPowBudgetScaled (a : Nat) : ℚ :=
  (a : ℚ)^2 * printedTailKPowBudgetRhs a

private theorem printedTailKPowBudgetScaled_step8 (a : Nat) (ha : 150 ≤ a) :
    printedTailKPowBudgetScaled (a + 8) ≤ printedTailKPowBudgetScaled a := by
  unfold printedTailKPowBudgetScaled printedTailKPowBudgetRhs printedTailP
  have hdiv : (a + 8) / 2 = a / 2 + 4 := by
    simpa [show 8 = 4 * 2 by norm_num] using
      Nat.add_mul_div_right a 4 (by decide : 0 < 2)
  rw [hdiv, pow_add]
  norm_num
  have hpoly : (((a + 8 : Nat) : ℚ)^2 / 16 ≤ (a : ℚ)^2) := by
    push_cast
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  have hnonneg : 0 ≤ 9 / (2 : ℚ) ^ (a / 2) := by positivity
  calc
    ((a : ℚ) + 8) ^ 2 *
        (9 / ((2 : ℚ) ^ (a / 2) * 16))
        = (((a + 8 : Nat) : ℚ)^2 / 16) *
            (9 / (2 : ℚ) ^ (a / 2)) := by
            push_cast
            ring
    _ ≤ (a : ℚ)^2 * (9 / (2 : ℚ) ^ (a / 2)) :=
        mul_le_mul_of_nonneg_right hpoly hnonneg

private theorem printedTailKPowBudgetScaled_150 :
    printedTailKPowBudgetScaled 150 < 1 := by native_decide
private theorem printedTailKPowBudgetScaled_151 :
    printedTailKPowBudgetScaled 151 < 1 := by native_decide
private theorem printedTailKPowBudgetScaled_152 :
    printedTailKPowBudgetScaled 152 < 1 := by native_decide
private theorem printedTailKPowBudgetScaled_153 :
    printedTailKPowBudgetScaled 153 < 1 := by native_decide
private theorem printedTailKPowBudgetScaled_154 :
    printedTailKPowBudgetScaled 154 < 1 := by native_decide
private theorem printedTailKPowBudgetScaled_155 :
    printedTailKPowBudgetScaled 155 < 1 := by native_decide
private theorem printedTailKPowBudgetScaled_156 :
    printedTailKPowBudgetScaled 156 < 1 := by native_decide
private theorem printedTailKPowBudgetScaled_157 :
    printedTailKPowBudgetScaled 157 < 1 := by native_decide

theorem printedTailKPowBudget_bound (a : Nat) (ha : 150 ≤ a) :
    printedTailKPowBudgetRhs a ≤ 1 / (a : ℚ)^2 := by
  have hscaled : printedTailKPowBudgetScaled a < 1 := by
    refine Nat.strong_induction_on a ?_ ha
    intro a ih ha
    by_cases hle : a ≤ 157
    · interval_cases a <;> first
        | exact printedTailKPowBudgetScaled_150
        | exact printedTailKPowBudgetScaled_151
        | exact printedTailKPowBudgetScaled_152
        | exact printedTailKPowBudgetScaled_153
        | exact printedTailKPowBudgetScaled_154
        | exact printedTailKPowBudgetScaled_155
        | exact printedTailKPowBudgetScaled_156
        | exact printedTailKPowBudgetScaled_157
    · have hprev_ge : 150 ≤ a - 8 := by omega
      have hprev_lt : a - 8 < a := by omega
      have hprev : printedTailKPowBudgetScaled (a - 8) < 1 :=
        ih (a - 8) hprev_lt hprev_ge
      have hstep :
          printedTailKPowBudgetScaled ((a - 8) + 8) ≤
            printedTailKPowBudgetScaled (a - 8) :=
        printedTailKPowBudgetScaled_step8 (a - 8) hprev_ge
      have hadd : (a - 8) + 8 = a := by omega
      rw [hadd] at hstep
      exact lt_of_le_of_lt hstep hprev
  unfold printedTailKPowBudgetScaled at hscaled
  have ha_sq_pos : (0 : ℚ) < (a : ℚ)^2 := by
    have ha_pos : (0 : ℚ) < (a : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 150) ha)
    positivity
  rw [le_div_iff₀ ha_sq_pos]
  nlinarith

private theorem marked_summand_le_q_over_two_pow {mi r : Nat} (hmi : 1 ≤ mi) :
    (mi : ℚ) / (((mi + 1 : Nat) : ℚ)^r) ≤
      (((mi + 1 : Nat) : ℚ)) / (2 : ℚ)^r := by
  let q : ℚ := ((mi + 1 : Nat) : ℚ)
  have hmiq : (mi : ℚ) ≤ q := by
    dsimp [q]
    exact_mod_cast (by omega : mi ≤ mi + 1)
  have hq2 : (2 : ℚ) ≤ q := by
    dsimp [q]
    exact_mod_cast (by omega : 2 ≤ mi + 1)
  have hqpos : 0 < q := by
    dsimp [q]
    exact_mod_cast Nat.succ_pos mi
  have hden1 : 0 < q^r := pow_pos hqpos r
  have hden2 : 0 < (2 : ℚ)^r := by positivity
  have hpow : (2 : ℚ)^r ≤ q^r :=
    pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 2) hq2 r
  rw [div_le_div_iff₀ hden1 hden2]
  exact mul_le_mul hmiq hpow hden2.le (by positivity)

private theorem markedWeight_le_N_over_two_pow
    (μ : List Nat) (hpos : ∀ m ∈ μ, 1 ≤ m) (r : Nat) :
    markedWeight μ r ≤ (N μ : ℚ) / (2 : ℚ)^r := by
  unfold markedWeight N
  calc
    (μ.map fun mi : Nat => (mi : ℚ) / (((mi + 1 : Nat) : ℚ)^r)).sum
        ≤ (μ.map fun mi : Nat =>
            (((mi + 1 : Nat) : ℚ)) / (2 : ℚ)^r).sum := by
          refine List.sum_le_sum fun mi hmi => ?_
          exact marked_summand_le_q_over_two_pow (hpos mi hmi)
    _ = (((μ.map (· + 1)).sum : Nat) : ℚ) / (2 : ℚ)^r :=
          sum_q_div_const μ

private theorem markedWeight_nonneg (μ : List Nat) (r : Nat) :
    0 ≤ markedWeight μ r := by
  unfold markedWeight
  refine List.sum_nonneg fun x hx => ?_
  simp only [List.mem_map] at hx
  obtain ⟨mi, _hmi, rfl⟩ := hx
  positivity

private theorem kCoeff_eq_of_two_le (μ : List Nat) {r : Nat} (hr : 2 ≤ r) :
    kCoeff μ r =
      12 * (((r - 1 : Nat) : ℚ)) * Prop51.c (r - 1) * markedWeight μ r := by
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 2 := ⟨r - 2, by omega⟩
  simp [kCoeff]

private theorem kCoeff_core_ratio_le_gamma {a s : Nat}
    (hs2 : 2 ≤ a - s) :
    12 * (((a - s - 1 : Nat) : ℚ)) * Prop51.c (a - s - 1) /
        Prop51.c a ≤
      2 * gammaWeight a s := by
  let t : Nat := a - s - 1
  have ht1 : 1 ≤ t := by
    dsimp [t]
    omega
  have hta : t ≤ a := by
    dsimp [t]
    omega
  have ha1 : 1 ≤ a := by omega
  have hca : Prop51.c a ≠ 0 := (Prop51.c_pos a ha1).ne'
  have hda : Prop51.d a ≠ 0 := (Prop51.d_pos a ha1).ne'
  have hdt : Prop51.d t ≠ 0 := (Prop51.d_pos t ht1).ne'
  have ht_fac : ((t : ℚ) * (((t - 1).factorial : Nat) : ℚ)) =
      ((t.factorial : Nat) : ℚ) := by
    exact_mod_cast Nat.mul_factorial_pred (by omega : t ≠ 0)
  have ht_eq : t = a - s - 1 := rfl
  have hpow6 : (6 : ℚ)^a = (6 : ℚ)^t * (6 : ℚ)^(s + 1) := by
    nth_rewrite 1 [show a = t + (s + 1) by dsimp [t]; omega]
    rw [pow_add]
  have hgamma_t :
      gammaWeight a s =
        ((t.factorial : Nat) : ℚ) /
          ((6 : ℚ)^s * ((Nat.factorial (a - 1) : Nat) : ℚ)) := by
    unfold gammaWeight
    rw [← ht_eq]
  have heq :
      12 * (((a - s - 1 : Nat) : ℚ)) * Prop51.c (a - s - 1) /
          Prop51.c a =
        2 * gammaWeight a s * (Prop51.d t / Prop51.d a) := by
    rw [← ht_eq, Prop51.c_eq_d t, Prop51.c_eq_d a, hpow6, hgamma_t]
    field_simp [hca, hda, hdt]
    rw [show (6 : ℚ)^(s + 1) = (6 : ℚ)^s * 6 by rw [pow_succ]]
    rw [← ht_fac]
    ring
  rw [heq]
  have hratio : Prop51.d t / Prop51.d a ≤ 1 := by
    rw [div_le_one₀ (Prop51.d_pos a ha1)]
    exact Prop51.d_mono hta
  have hgamma_nonneg : 0 ≤ gammaWeight a s := gammaWeight_nonneg (by omega : s < a)
  nlinarith

private theorem kCoeff_div_den_le_gamma_pow
    {a s : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a))
    (hs : s ∈ Finset.range (printedTailR0 a + 1)) :
    kCoeff μ (a - s) / printedTailDen μ a ≤
      (2 / (2 : ℚ)^(a - s)) * gammaWeight a s := by
  have hr_ge : printedTailP a + 1 ≤ a - s :=
    printedTail_range_p_succ_le (a := a) (s := s) ha hs
  have hr2 : 2 ≤ a - s := by
    unfold printedTailP at hr_ge
    omega
  have hNpos_nat : 0 < N μ := printedTail_N_pos (a := a) (μ := μ) ha hμ
  have hNpos : (0 : ℚ) < (N μ : ℚ) := by exact_mod_cast hNpos_nat
  have hcpos : 0 < Prop51.c a := Prop51.c_pos a (by omega)
  have hdenpos : 0 < printedTailDen μ a := by
    unfold printedTailDen
    exact mul_pos hNpos hcpos
  have hmw := markedWeight_le_N_over_two_pow μ hμ.2 (a - s)
  have hmw_nonneg := markedWeight_nonneg μ (a - s)
  have hk_eq := kCoeff_eq_of_two_le μ (r := a - s) hr2
  rw [hk_eq]
  have hcore := kCoeff_core_ratio_le_gamma (a := a) (s := s) hr2
  unfold printedTailDen
  calc
    (12 * (((a - s - 1 : Nat) : ℚ)) * Prop51.c (a - s - 1) *
          markedWeight μ (a - s)) /
        ((N μ : ℚ) * Prop51.c a)
        =
      (12 * (((a - s - 1 : Nat) : ℚ)) * Prop51.c (a - s - 1) /
          Prop51.c a) * (markedWeight μ (a - s) / (N μ : ℚ)) := by
        field_simp [hNpos.ne', hcpos.ne']
    _ ≤
      (2 * gammaWeight a s) * (1 / (2 : ℚ)^(a - s)) := by
        have hmw_div :
            markedWeight μ (a - s) / (N μ : ℚ) ≤
              1 / (2 : ℚ)^(a - s) := by
          rw [div_le_iff₀ hNpos]
          calc
            markedWeight μ (a - s) ≤
                (N μ : ℚ) / (2 : ℚ)^(a - s) := hmw
            _ = (1 / (2 : ℚ)^(a - s)) * (N μ : ℚ) := by ring
        have hmw_div_nonneg :
            0 ≤ markedWeight μ (a - s) / (N μ : ℚ) :=
          div_nonneg hmw_nonneg hNpos.le
        have hcore_rhs_nonneg : 0 ≤ 2 * gammaWeight a s :=
          mul_nonneg (by norm_num) (gammaWeight_nonneg
            (printedTail_range_lt_a (a := a) (s := s) ha hs))
        exact mul_le_mul hcore hmw_div hmw_div_nonneg hcore_rhs_nonneg
    _ = (2 / (2 : ℚ)^(a - s)) * gammaWeight a s := by ring

private theorem kCoeff_div_den_le_gamma_uniform
    {a s : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a))
    (hs : s ∈ Finset.range (printedTailR0 a + 1)) :
    kCoeff μ (a - s) / printedTailDen μ a ≤
      (1 / (2 : ℚ)^(printedTailP a)) * gammaWeight a s := by
  have hpoint := kCoeff_div_den_le_gamma_pow (a := a) (s := s) (μ := μ) ha hμ hs
  have hr_ge : printedTailP a + 1 ≤ a - s :=
    printedTail_range_p_succ_le (a := a) (s := s) ha hs
  have hpow :
      2 / (2 : ℚ)^(a - s) ≤ 1 / (2 : ℚ)^(printedTailP a) := by
    have hr1 : 1 ≤ a - s := by omega
    have hrewrite :
        2 / (2 : ℚ)^(a - s) = 1 / (2 : ℚ)^((a - s) - 1) := by
      have hsplit : (2 : ℚ)^(a - s) =
          (2 : ℚ)^((a - s) - 1) * 2 := by
        nth_rewrite 1 [show a - s = (a - s - 1) + 1 by omega]
        rw [pow_add]
        norm_num
      rw [hsplit]
      field_simp
    rw [hrewrite]
    exact one_div_two_pow_mono (by omega : printedTailP a ≤ (a - s) - 1)
  exact hpoint.trans (mul_le_mul_of_nonneg_right hpow (gammaWeight_nonneg
    (printedTail_range_lt_a (a := a) (s := s) ha hs)))

theorem printedTailKErrorBound_of_eAbsoluteMoment
    (he : PrintedTailEAbsoluteMomentBound) :
    PrintedTailKErrorBound := by
  intro a ha μ hμ
  have heMom := he a ha μ hμ
  have hbudget := printedTailKPowBudget_bound a ha
  have hdenpos : 0 < printedTailDen μ a := by
    unfold printedTailDen
    have hNpos : (0 : ℚ) < (N μ : ℚ) := by
      exact_mod_cast printedTail_N_pos (a := a) (μ := μ) ha hμ
    exact mul_pos hNpos (Prop51.c_pos a (by omega))
  unfold printedTailKNormSum
  rw [Prop51.list_range_map_sum]
  rw [abs_div]
  rw [abs_of_pos hdenpos]
  calc
    |∑ x ∈ Finset.range (printedTailR0 a + 1),
        kCoeff μ (a - x) * printedTailECoeff μ a x| / printedTailDen μ a
        ≤
      ∑ x ∈ Finset.range (printedTailR0 a + 1),
        |kCoeff μ (a - x) * printedTailECoeff μ a x / printedTailDen μ a|
        := by
          calc
            |∑ x ∈ Finset.range (printedTailR0 a + 1),
                kCoeff μ (a - x) * printedTailECoeff μ a x| /
                printedTailDen μ a
                ≤
              (∑ x ∈ Finset.range (printedTailR0 a + 1),
                |kCoeff μ (a - x) * printedTailECoeff μ a x|) /
                printedTailDen μ a :=
                  div_le_div_of_nonneg_right
                    (Finset.abs_sum_le_sum_abs _ _) hdenpos.le
            _ =
              ∑ x ∈ Finset.range (printedTailR0 a + 1),
                |kCoeff μ (a - x) * printedTailECoeff μ a x /
                  printedTailDen μ a| := by
                  rw [Finset.sum_div]
                  refine Finset.sum_congr rfl fun x hx => ?_
                  rw [abs_div, abs_of_pos hdenpos]
    _ ≤
      ∑ x ∈ Finset.range (printedTailR0 a + 1),
        (1 / (2 : ℚ)^(printedTailP a)) *
          (gammaWeight a x * |printedTailECoeff μ a x|) := by
        refine Finset.sum_le_sum fun x hx => ?_
        have hkgamma :=
          kCoeff_div_den_le_gamma_uniform (a := a) (s := x) (μ := μ) ha hμ hx
        have hk_nonneg :
            0 ≤ kCoeff μ (a - x) / printedTailDen μ a := by
          have hr_ge := printedTail_range_p_succ_le (a := a) (s := x) ha hx
          have hr2 : 2 ≤ a - x := by unfold printedTailP at hr_ge; omega
          rw [kCoeff_eq_of_two_le μ (r := a - x) hr2]
          exact div_nonneg
            (mul_nonneg
              (mul_nonneg (mul_nonneg (by norm_num) (by positivity))
                (Prop51.c_pos (a - x - 1) (by omega)).le)
              (markedWeight_nonneg μ (a - x)))
            hdenpos.le
        rw [abs_div, abs_mul, abs_of_pos hdenpos]
        have hrewrite :
            |kCoeff μ (a - x)| / printedTailDen μ a =
              kCoeff μ (a - x) / printedTailDen μ a := by
          have hk_num_nonneg : 0 ≤ kCoeff μ (a - x) := by
            have hmul := mul_nonneg hk_nonneg hdenpos.le
            rwa [div_mul_cancel₀ _ hdenpos.ne'] at hmul
          rw [abs_of_nonneg hk_num_nonneg]
        calc
          |kCoeff μ (a - x)| * |printedTailECoeff μ a x| /
              printedTailDen μ a
              =
            (|kCoeff μ (a - x)| / printedTailDen μ a) *
              |printedTailECoeff μ a x| := by ring
          _ = kCoeff μ (a - x) / printedTailDen μ a *
              |printedTailECoeff μ a x| := by rw [hrewrite]
          _ ≤
            ((1 / (2 : ℚ)^(printedTailP a)) * gammaWeight a x) *
              |printedTailECoeff μ a x|
              := mul_le_mul_of_nonneg_right hkgamma (abs_nonneg _)
          _ = (1 / (2 : ℚ)^(printedTailP a)) *
              (gammaWeight a x * |printedTailECoeff μ a x|) := by ring
    _ =
      (1 / (2 : ℚ)^(printedTailP a)) *
        (∑ x ∈ Finset.range (printedTailR0 a + 1),
          gammaWeight a x * |printedTailECoeff μ a x|) := by
        rw [Finset.mul_sum]
    _ ≤ (1 / (2 : ℚ)^(printedTailP a)) * 9 := by
        exact mul_le_mul_of_nonneg_left heMom (by positivity)
    _ = printedTailKPowBudgetRhs a := by
        unfold printedTailKPowBudgetRhs
        ring
    _ ≤ 1 / (a : ℚ)^2 := hbudget

def PrintedTailOmegaErrorBound : Prop :=
  ∀ a : Nat, 150 ≤ a →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      |printedTailOmegaNorm μ a| ≤ 1 / (a : ℚ)^2

/-- Final normalized large-tail assembly from the exact split and the three
finite error estimates. -/
theorem printedTailNormalizedLowerBound_of_split_errorBounds
    (hsplit : PrintedTailExactSplit)
    (hmain : PrintedTailMainLowerBound)
    (hh : PrintedTailHErrorBound)
    (hk : PrintedTailKErrorBound)
    (homega : PrintedTailOmegaErrorBound) :
    PrintedTailNormalizedLowerBound := by
  intro a ha μ hμ
  change printedLargeMargin a ≤ (-printedCoeff μ a) / printedTailDen μ a
  rw [hsplit a ha μ hμ]
  have hmain_lb := hmain a ha μ hμ
  have hh_abs := abs_le.mp (hh a ha μ hμ)
  have hk_abs := abs_le.mp (hk a ha μ hμ)
  have homega_abs := abs_le.mp (homega a ha μ hμ)
  have hmargin_decomp :
      printedLargeMargin a =
        9 / (40 * ((a : ℚ) - 2)) - 1 / (a : ℚ)^2 -
          printedTailHErrorBudget a - 1 / (a : ℚ)^2 -
          1 / (a : ℚ)^2 := by
    unfold printedLargeMargin printedTailHErrorBudget
    ring
  unfold printedTailSplitRhs
  rw [hmargin_decomp]
  nlinarith [hh_abs.1, hk_abs.1, homega_abs.2]

theorem printedCoeffNegativityTail_of_split_errorBounds
    (hsplit : PrintedTailExactSplit)
    (hmain : PrintedTailMainLowerBound)
    (hh : PrintedTailHErrorBound)
    (hk : PrintedTailKErrorBound)
    (homega : PrintedTailOmegaErrorBound) :
    PrintedCoeffNegativityTail :=
  printedCoeffNegativityTail_of_normalizedLowerBound
    (printedTailNormalizedLowerBound_of_split_errorBounds
      hsplit hmain hh hk homega)

theorem printedTailNormalizedLowerBound_of_errorBounds
    (hmain : PrintedTailMainLowerBound)
    (hh : PrintedTailHErrorBound)
    (hk : PrintedTailKErrorBound)
    (homega : PrintedTailOmegaErrorBound) :
    PrintedTailNormalizedLowerBound :=
  printedTailNormalizedLowerBound_of_split_errorBounds
    printedTailExactSplit_closed hmain hh hk homega

theorem printedCoeffNegativityTail_of_errorBounds
    (hmain : PrintedTailMainLowerBound)
    (hh : PrintedTailHErrorBound)
    (hk : PrintedTailKErrorBound)
    (homega : PrintedTailOmegaErrorBound) :
    PrintedCoeffNegativityTail :=
  printedCoeffNegativityTail_of_split_errorBounds
    printedTailExactSplit_closed hmain hh hk homega

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
