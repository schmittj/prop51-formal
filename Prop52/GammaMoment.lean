/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Algebraic Gamma-moment bounds for Proposition 5.2

This file develops the rational part of the Gamma-margin argument for the
large printed Proposition 5.2 tail.  It deliberately stays in finite sums and
factorial ratios: the probabilistic language in the paper is represented here
by the weights `gammaWeight`.
-/

import Prop52.GammaRetain

namespace Prop52

/-- The finite exponent moment corresponding to
`E[L(1/(6Y))]` for an integer-shape Gamma variable `Y` of shape `a-2`.
It is written directly as a rational finite sum. -/
def printedTailGammaExponentMoment (μ : List Nat) (a : Nat) : ℚ :=
  ∑ r ∈ Finset.Ico 1 (printedTailP a + 1),
    hCoeff μ r * gammaWeight (a - 2) r

private theorem factorial_cast_ne (n : Nat) :
    (((n.factorial : Nat) : ℚ)) ≠ 0 := by
  exact_mod_cast n.factorial_pos.ne'

private theorem choose_cast_ne {n r : Nat} (hr : r ≤ n) :
    (((n.choose r : Nat) : ℚ)) ≠ 0 := by
  exact_mod_cast (Nat.choose_pos hr).ne'

private theorem factorial_succ_cast (n : Nat) :
    (((n + 1).factorial : Nat) : ℚ) =
      ((n + 1 : Nat) : ℚ) * ((n.factorial : Nat) : ℚ) := by
  exact_mod_cast Nat.factorial_succ n

/-- Shifting two powers of `t = 1/(6Y)` from a Gamma law of shape `a` to one
of shape `a-2` produces exactly the scalar prefactor used in the Jensen
margin. -/
theorem M_mul_gammaWeight_shift_two_eq
    {a r : Nat} (ha : 150 ≤ a) :
    (M a : ℚ) * gammaWeight a (r + 2) =
      (1 / (6 * ((a : ℚ) - 2))) * gammaWeight (a - 2) r := by
  have hMcast : (M a : ℚ) = 6 * ((a : ℚ) - 1) := by
    unfold M
    rw [Nat.cast_sub (by omega : 6 ≤ 6 * a)]
    push_cast
    ring
  rw [hMcast]
  unfold gammaWeight
  have hpow6 : (6 : ℚ)^r ≠ 0 := by positivity
  have hpow6s : (6 : ℚ)^(r + 2) ≠ 0 := by positivity
  have hfac_num_ne :
      (((Nat.factorial (a - r - 3) : Nat) : ℚ)) ≠ 0 :=
    factorial_cast_ne _
  have hfac_den_ne :
      (((Nat.factorial (a - 3) : Nat) : ℚ)) ≠ 0 :=
    factorial_cast_ne _
  have ha2Q : (a : ℚ) - 2 ≠ 0 := by
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  have ha1Q : (a : ℚ) - 1 ≠ 0 := by
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  rw [show a - (r + 2) - 1 = a - r - 3 by omega]
  rw [show a - 2 - r - 1 = a - r - 3 by omega]
  rw [show a - 2 - 1 = a - 3 by omega]
  rw [show a - 1 = (a - 2) + 1 by omega, factorial_succ_cast]
  rw [show (((a - 2 + 1 : Nat) : ℚ)) = (a : ℚ) - 1 by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub (by omega : 2 ≤ a)]
    ring]
  rw [show a - 2 = (a - 3) + 1 by omega, factorial_succ_cast]
  rw [show (((a - 3 + 1 : Nat) : ℚ)) = (a : ℚ) - 2 by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub (by omega : 3 ≤ a)]
    ring]
  field_simp [hpow6, hpow6s, hfac_num_ne, hfac_den_ne, ha2Q, ha1Q]
  ring

/-- Adjacent recurrence for the integer-shape Gamma weights:
`6(a-s) γ_s = γ_{s-1}`. -/
theorem gammaWeight_mul_six_sub_eq_pred
    {a s : Nat} (hspos : 1 ≤ s) (hslt : s < a) :
    gammaWeight a s * (6 * ((a : ℚ) - s)) =
      gammaWeight a (s - 1) := by
  unfold gammaWeight
  have hpow6 : (6 : ℚ)^(s - 1) ≠ 0 := by positivity
  have hpow6s : (6 : ℚ)^s ≠ 0 := by positivity
  have hfac_den_ne :
      (((Nat.factorial (a - 1) : Nat) : ℚ)) ≠ 0 :=
    factorial_cast_ne _
  have hasubQ : (a : ℚ) - s ≠ 0 := by
    have hsQ : (s : ℚ) < a := by exact_mod_cast hslt
    nlinarith
  have hpow_s : (6 : ℚ)^s = 6 * (6 : ℚ)^(s - 1) := by
    rw [show s = 1 + (s - 1) by omega, pow_add]
    norm_num
  have hfac :
      (((Nat.factorial (a - (s - 1) - 1) : Nat) : ℚ)) =
        ((a : ℚ) - s) *
          (((Nat.factorial (a - s - 1) : Nat) : ℚ)) := by
    rw [show a - (s - 1) - 1 = (a - s - 1) + 1 by omega]
    rw [Nat.factorial_succ]
    rw [Nat.cast_mul]
    rw [show (((a - s - 1 + 1 : Nat) : ℚ)) = (a : ℚ) - s by
      rw [show a - s - 1 + 1 = a - s by omega]
      rw [Nat.cast_sub (by omega : s ≤ a)]]
  rw [hfac, hpow_s]
  field_simp [hpow6, hpow6s, hfac_den_ne, hasubQ]

theorem gammaWeight_zero (a : Nat) :
    gammaWeight a 0 = 1 := by
  unfold gammaWeight
  rw [show a - 0 - 1 = a - 1 by omega]
  field_simp [factorial_cast_ne (a - 1)]

theorem gammaWeight_succ_eq_mul_inv_six_sub
    {a s : Nat} (hslt : s + 1 < a) :
    gammaWeight a (s + 1) =
      gammaWeight a s * (1 / (6 * ((a : ℚ) - (s + 1 : Nat)))) := by
  have hrec := gammaWeight_mul_six_sub_eq_pred
    (a := a) (s := s + 1) (by omega : 1 ≤ s + 1) hslt
  rw [show s + 1 - 1 = s by omega] at hrec
  have hden : 6 * ((a : ℚ) - (s + 1 : Nat)) ≠ 0 := by
    have hsQ : ((s + 1 : Nat) : ℚ) < a := by exact_mod_cast hslt
    nlinarith
  have hden' : (a : ℚ) - (s + 1 : Nat) ≠ 0 := by
    have hsQ : ((s + 1 : Nat) : ℚ) < a := by exact_mod_cast hslt
    nlinarith
  calc
    gammaWeight a (s + 1)
        = (gammaWeight a (s + 1) *
            (6 * ((a : ℚ) - (s + 1 : Nat)))) /
            (6 * ((a : ℚ) - (s + 1 : Nat))) := by
            field_simp [hden, hden']
    _ = gammaWeight a s /
            (6 * ((a : ℚ) - (s + 1 : Nat))) := by
            rw [hrec]
    _ = gammaWeight a s *
            (1 / (6 * ((a : ℚ) - (s + 1 : Nat)))) := by
            ring

private theorem gammaWeight_small_step_le_scaled_x2
    {a s : Nat} (ha : 150 ≤ a) (hs : s ≤ a / 8) :
    1 / (6 * ((a : ℚ) - (s + 1 : Nat))) ≤
      (3 / 10 : ℚ) * printedTailX2 a := by
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hs8 : 8 * s ≤ a := by omega
  have hs8Q : (8 * s : ℚ) ≤ a := by exact_mod_cast hs8
  have hden1 : 0 < 6 * ((a : ℚ) - (s + 1 : Nat)) := by
    push_cast
    nlinarith
  have hden2 : 0 < 5 * (a : ℚ) := by nlinarith
  have hden_le :
      5 * (a : ℚ) ≤ 6 * ((a : ℚ) - (s + 1 : Nat)) := by
    push_cast
    nlinarith
  unfold printedTailX2
  rw [show (3 / 10 : ℚ) * (2 / (3 * (a : ℚ))) =
      1 / (5 * (a : ℚ)) by
        field_simp [(by nlinarith : (3 * (a : ℚ)) ≠ 0),
          (by nlinarith : (5 * (a : ℚ)) ≠ 0)]
        ring]
  exact one_div_le_one_div_of_le hden2 hden_le

private theorem gammaWeight_large_step_le_x2
    {a s : Nat} (ha : 150 ≤ a) (hsR : s + 1 ≤ printedTailR0 a) :
    1 / (6 * ((a : ℚ) - (s + 1 : Nat))) ≤
      printedTailX2 a := by
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have hnat : a ≤ 4 * (a - (s + 1)) := by
    unfold printedTailR0 printedTailP at hsR
    omega
  have hq : (a : ℚ) ≤ 4 * ((a - (s + 1) : Nat) : ℚ) := by
    exact_mod_cast hnat
  have hsub_cast :
      ((a - (s + 1) : Nat) : ℚ) = (a : ℚ) - (s + 1 : Nat) := by
    rw [Nat.cast_sub (by omega : s + 1 ≤ a)]
  have hden1 : 0 < 6 * ((a : ℚ) - (s + 1 : Nat)) := by
    rw [← hsub_cast]
    have hsub_pos : 0 < a - (s + 1) := by
      unfold printedTailR0 printedTailP at hsR
      omega
    positivity
  have hden2 : 0 < 3 * (a : ℚ) := by nlinarith
  unfold printedTailX2
  rw [div_le_iff₀ hden1]
  field_simp [hden2.ne']
  rw [← hsub_cast]
  nlinarith

private theorem gammaWeight_le_x2_minPow
    {a : Nat} (ha : 150 ≤ a) :
    ∀ s : Nat, s ≤ printedTailR0 a →
      gammaWeight a s ≤
        (3 / 10 : ℚ)^(min s (a / 8 + 1)) *
          (printedTailX2 a)^s
  | 0, _hs => by
      simp [gammaWeight_zero]
  | s + 1, hsR => by
      have hsRpred : s ≤ printedTailR0 a := by omega
      have hslt : s + 1 < a := by
        unfold printedTailR0 printedTailP at hsR
        omega
      have ih := gammaWeight_le_x2_minPow ha s hsRpred
      have hstep_eq := gammaWeight_succ_eq_mul_inv_six_sub
        (a := a) (s := s) hslt
      have hx2_nonneg : 0 ≤ printedTailX2 a := by
        unfold printedTailX2
        positivity
      have hpow_nonneg :
          0 ≤ (printedTailX2 a)^s := pow_nonneg hx2_nonneg s
      rw [hstep_eq]
      by_cases hsmall : s ≤ a / 8
      · have hstep := gammaWeight_small_step_le_scaled_x2
          (a := a) (s := s) ha hsmall
        have hstep_nonneg :
            0 ≤ 1 / (6 * ((a : ℚ) - (s + 1 : Nat))) := by
          have hsQ : ((s + 1 : Nat) : ℚ) < a := by exact_mod_cast hslt
          have hdenpos : 0 < 6 * ((a : ℚ) - (s + 1 : Nat)) := by
            nlinarith
          exact (one_div_nonneg.mpr hdenpos.le)
        have hA_nonneg :
            0 ≤ (3 / 10 : ℚ)^(min s (a / 8 + 1)) *
              (printedTailX2 a)^s := by
          exact mul_nonneg (by positivity) hpow_nonneg
        have hmul :
            gammaWeight a s *
                (1 / (6 * ((a : ℚ) - (s + 1 : Nat)))) ≤
              ((3 / 10 : ℚ)^(min s (a / 8 + 1)) *
                  (printedTailX2 a)^s) *
                ((3 / 10 : ℚ) * printedTailX2 a) := by
          exact mul_le_mul ih hstep hstep_nonneg hA_nonneg
        have hmin_s : min s (a / 8 + 1) = s := by omega
        have hmin_succ : min (s + 1) (a / 8 + 1) = s + 1 := by omega
        calc
          gammaWeight a s *
              (1 / (6 * ((a : ℚ) - (s + 1 : Nat))))
              ≤
            ((3 / 10 : ℚ)^(min s (a / 8 + 1)) *
                (printedTailX2 a)^s) *
              ((3 / 10 : ℚ) * printedTailX2 a) := hmul
          _ =
            (3 / 10 : ℚ)^(min (s + 1) (a / 8 + 1)) *
              (printedTailX2 a)^(s + 1) := by
              rw [hmin_s, hmin_succ, pow_succ, pow_succ]
              ring
      · have hstep := gammaWeight_large_step_le_x2
          (a := a) (s := s) ha hsR
        have hstep_nonneg :
            0 ≤ 1 / (6 * ((a : ℚ) - (s + 1 : Nat))) := by
          have hsQ : ((s + 1 : Nat) : ℚ) < a := by exact_mod_cast hslt
          have hdenpos : 0 < 6 * ((a : ℚ) - (s + 1 : Nat)) := by
            nlinarith
          exact (one_div_nonneg.mpr hdenpos.le)
        have hA_nonneg :
            0 ≤ (3 / 10 : ℚ)^(min s (a / 8 + 1)) *
              (printedTailX2 a)^s := by
          exact mul_nonneg (by positivity) hpow_nonneg
        have hmul :
            gammaWeight a s *
                (1 / (6 * ((a : ℚ) - (s + 1 : Nat)))) ≤
              ((3 / 10 : ℚ)^(min s (a / 8 + 1)) *
                  (printedTailX2 a)^s) *
                printedTailX2 a := by
          exact mul_le_mul ih hstep hstep_nonneg hA_nonneg
        have hmin_s : min s (a / 8 + 1) = a / 8 + 1 := by omega
        have hmin_succ : min (s + 1) (a / 8 + 1) = a / 8 + 1 := by omega
        calc
          gammaWeight a s *
              (1 / (6 * ((a : ℚ) - (s + 1 : Nat))))
              ≤
            ((3 / 10 : ℚ)^(min s (a / 8 + 1)) *
                (printedTailX2 a)^s) *
              printedTailX2 a := hmul
          _ =
            (3 / 10 : ℚ)^(min (s + 1) (a / 8 + 1)) *
              (printedTailX2 a)^(s + 1) := by
              rw [hmin_s, hmin_succ, pow_succ]
              ring

/-- Tail-side gamma-weight comparison used in the final term of
`truncationResidueRhs`: after `S=floor(a/8)`, the Gamma weight is smaller than
the `x₂` coefficient weight by a factor `(3/10)^(S+1)`. -/
theorem gammaWeight_le_x2_tailFactor
    {a s : Nat} (ha : 150 ≤ a)
    (hsR : s ≤ printedTailR0 a) (hsS : a / 8 + 1 ≤ s) :
    gammaWeight a s ≤
      (3 / 10 : ℚ)^(a / 8 + 1) * (printedTailX2 a)^s := by
  have h := gammaWeight_le_x2_minPow (a := a) ha s hsR
  rwa [show min s (a / 8 + 1) = a / 8 + 1 by omega] at h

/-- Coefficient recurrence for the low exponential `E=exp(-L)`, with the
minus sign exposed in the form used by the discrete integration-by-parts
calculation. -/
theorem printedTailECoeff_succ_mul_eq_neg_lowDerivConv
    (μ : List Nat) (a n : Nat) :
    ((n + 1 : Nat) : ℚ) * printedTailECoeff μ a (n + 1) =
      -∑ t ∈ Finset.range (n + 1),
        if t + 1 ≤ printedTailP a then
          ((t + 1 : Nat) : ℚ) * hCoeff μ (t + 1) *
            printedTailECoeff μ a (n - t)
        else 0 := by
  have hrec := Prop51.expCoeff_succ_mul (printedTailLowExpInput μ a) n
  unfold printedTailECoeff at hrec ⊢
  rw [hrec]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun t _ht => ?_
  unfold printedTailLowExpInput
  by_cases htp : t + 1 ≤ printedTailP a
  · rw [if_pos htp, if_pos htp]
    ring
  · rw [if_neg htp, if_neg htp]
    ring

/-- The low-derivative convolution form for the coefficient of
`t L'(t) E(t)`. -/
theorem printedTailLowDerivConv_eq_neg
    (μ : List Nat) (a n : Nat) :
    (∑ t ∈ Finset.range n,
      if t + 1 ≤ printedTailP a then
        ((t + 1 : Nat) : ℚ) * hCoeff μ (t + 1) *
          printedTailECoeff μ a (n - 1 - t)
      else 0) =
      -(n : ℚ) * printedTailECoeff μ a n := by
  cases n with
  | zero =>
      simp
  | succ n =>
      have h := printedTailECoeff_succ_mul_eq_neg_lowDerivConv μ a n
      have hneg := congrArg Neg.neg h
      calc
        (∑ t ∈ Finset.range (n + 1),
          if t + 1 ≤ printedTailP a then
            ((t + 1 : Nat) : ℚ) * hCoeff μ (t + 1) *
              printedTailECoeff μ a (n + 1 - 1 - t)
          else 0)
            =
          -(((n + 1 : Nat) : ℚ) *
            printedTailECoeff μ a (n + 1)) := by
            simpa [show n + 1 - 1 = n by omega] using hneg.symm
        _ = -((n + 1 : Nat) : ℚ) * printedTailECoeff μ a (n + 1) := by
            ring

/-- The same low-derivative convolution with the bracket's factor `6`. -/
theorem printedTailLowDerivConv_six_eq_neg
    (μ : List Nat) (a n : Nat) :
    (∑ t ∈ Finset.range n,
      if t + 1 ≤ printedTailP a then
        6 * ((t + 1 : Nat) : ℚ) * hCoeff μ (t + 1) *
          printedTailECoeff μ a (n - 1 - t)
      else 0) =
      -6 * (n : ℚ) * printedTailECoeff μ a n := by
  have h := printedTailLowDerivConv_eq_neg μ a n
  calc
    (∑ t ∈ Finset.range n,
      if t + 1 ≤ printedTailP a then
        6 * ((t + 1 : Nat) : ℚ) * hCoeff μ (t + 1) *
          printedTailECoeff μ a (n - 1 - t)
      else 0)
        =
      6 * (∑ t ∈ Finset.range n,
        if t + 1 ≤ printedTailP a then
          ((t + 1 : Nat) : ℚ) * hCoeff μ (t + 1) *
            printedTailECoeff μ a (n - 1 - t)
        else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ht => ?_
          by_cases ht : t + 1 ≤ printedTailP a
          · simp [ht]
            ring
          · simp [ht]
    _ = 6 * (-(n : ℚ) * printedTailECoeff μ a n) := by rw [h]
    _ = -6 * (n : ℚ) * printedTailECoeff μ a n := by ring

/-- Split the marked numerator convolution in `ω_{n+1}` into the head
`k₁ e_n` and the shifted remaining terms. -/
theorem printedTailOmegaCoeff_succ_sub_E_eq_neg_split
    (μ : List Nat) {a n : Nat} (ha : 150 ≤ a) :
    printedTailOmegaCoeff μ a (n + 1) - printedTailECoeff μ a (n + 1) =
      -(kCoeff μ 1 * printedTailECoeff μ a n +
        ∑ t ∈ Finset.range n,
          if t + 1 < printedTailP a then
            kCoeff μ (t + 2) * printedTailECoeff μ a (n - 1 - t)
          else 0) := by
  let F : Nat → ℚ := fun j =>
    if j + 1 ≤ printedTailP a then
      kCoeff μ (j + 1) * printedTailECoeff μ a (n + 1 - (j + 1))
    else 0
  have hp1 : 1 ≤ printedTailP a := by
    unfold printedTailP
    omega
  have hconv :
      ((List.range (n + 1)).map fun j : Nat =>
        let r := j + 1
        if r ≤ printedTailP a then
          kCoeff μ r * printedTailECoeff μ a (n + 1 - r)
        else 0).sum =
        ∑ j ∈ Finset.range (n + 1), F j := by
    rw [Prop51.list_range_map_sum]
  have hsplit :
      (∑ j ∈ Finset.range (n + 1), F j) =
        kCoeff μ 1 * printedTailECoeff μ a n +
          ∑ t ∈ Finset.range n,
            if t + 1 < printedTailP a then
              kCoeff μ (t + 2) * printedTailECoeff μ a (n - 1 - t)
            else 0 := by
    rw [Finset.sum_range_succ']
    have htail :
        (∑ x ∈ Finset.range n, F (x + 1)) =
          ∑ t ∈ Finset.range n,
            if t + 1 < printedTailP a then
              kCoeff μ (t + 2) * printedTailECoeff μ a (n - 1 - t)
            else 0 := by
      refine Finset.sum_congr rfl fun t ht => ?_
      have htlt : t < n := Finset.mem_range.mp ht
      dsimp [F]
      by_cases htp : t + 1 < printedTailP a
      · have htp' : t + 1 + 1 ≤ printedTailP a := by omega
        rw [if_pos htp', if_pos htp]
        congr 2
        omega
      · have htp' : ¬ t + 1 + 1 ≤ printedTailP a := by omega
        rw [if_neg htp', if_neg htp]
    rw [htail]
    dsimp [F]
    rw [if_pos hp1]
    ring
  unfold printedTailOmegaCoeff
  rw [hconv, hsplit]
  ring

/-- Coefficient of `t^s` in the product of the low exponential `E(t)` and
the aligned rational bracket `M t + 6 t^2 L'(t) - J(t)`.

This is written directly as a coefficient convolution instead of introducing a
new formal-power-series wrapper for `gammaLowBracketAligned`; the three terms
are exactly the linear, derivative, and marked-numerator pieces of that
bracket. -/
def printedTailLowBracketProductCoeff (μ : List Nat) (a s : Nat) : ℚ :=
  if s = 0 then 0 else
    let n := s - 1;
      ((M a : ℚ) - kCoeff μ 1) * printedTailECoeff μ a n +
        (∑ t ∈ Finset.range n,
          if t + 1 ≤ printedTailP a then
            6 * ((t + 1 : Nat) : ℚ) * hCoeff μ (t + 1) *
              printedTailECoeff μ a (n - 1 - t)
          else 0) -
        (∑ t ∈ Finset.range n,
          if t + 1 < printedTailP a then
            kCoeff μ (t + 2) * printedTailECoeff μ a (n - 1 - t)
          else 0)

/-- The aligned bracket product coefficient is the exact telescoping core:
one shifted low-exponential term plus the omega-minus-exponential correction. -/
theorem printedTailLowBracketProductCoeff_succ_eq_telescopeCore
    (μ : List Nat) {a n : Nat} (ha : 150 ≤ a) :
    printedTailLowBracketProductCoeff μ a (n + 1) =
      ((M a : ℚ) - 6 * (n : ℚ)) * printedTailECoeff μ a n +
        printedTailOmegaCoeff μ a (n + 1) -
        printedTailECoeff μ a (n + 1) := by
  unfold printedTailLowBracketProductCoeff
  rw [if_neg (by omega : n + 1 ≠ 0)]
  rw [show n + 1 - 1 = n by omega]
  change
    (((M a : ℚ) - kCoeff μ 1) * printedTailECoeff μ a n +
        (∑ t ∈ Finset.range n,
          if t + 1 ≤ printedTailP a then
            6 * ((t + 1 : Nat) : ℚ) * hCoeff μ (t + 1) *
              printedTailECoeff μ a (n - 1 - t)
          else 0) -
        (∑ t ∈ Finset.range n,
          if t + 1 < printedTailP a then
            kCoeff μ (t + 2) * printedTailECoeff μ a (n - 1 - t)
          else 0)) =
      ((M a : ℚ) - 6 * (n : ℚ)) * printedTailECoeff μ a n +
        printedTailOmegaCoeff μ a (n + 1) -
        printedTailECoeff μ a (n + 1)
  have hderiv := printedTailLowDerivConv_six_eq_neg μ a n
  have homega := printedTailOmegaCoeff_succ_sub_E_eq_neg_split
    (μ := μ) (a := a) (n := n) ha
  rw [hderiv]
  rw [show
      ((M a : ℚ) - 6 * (n : ℚ)) * printedTailECoeff μ a n +
          printedTailOmegaCoeff μ a (n + 1) -
          printedTailECoeff μ a (n + 1) =
        ((M a : ℚ) - 6 * (n : ℚ)) * printedTailECoeff μ a n +
          (printedTailOmegaCoeff μ a (n + 1) -
            printedTailECoeff μ a (n + 1)) by ring]
  rw [homega]
  ring

/-- Weighted form of the coefficient telescope.  After multiplication by the
Gamma moment weight, the factor `M-6n = 6(a-(n+1))` shifts the weight down by
one index. -/
theorem gammaWeight_mul_printedTailLowBracketProductCoeff_succ_eq
    (μ : List Nat) {a n : Nat} (ha : 150 ≤ a) (hnlt : n + 1 < a) :
    gammaWeight a (n + 1) *
        printedTailLowBracketProductCoeff μ a (n + 1) =
      gammaWeight a n * printedTailECoeff μ a n +
        gammaWeight a (n + 1) * printedTailOmegaCoeff μ a (n + 1) -
        gammaWeight a (n + 1) * printedTailECoeff μ a (n + 1) := by
  rw [printedTailLowBracketProductCoeff_succ_eq_telescopeCore
    (μ := μ) (a := a) (n := n) ha]
  have hMcast : (M a : ℚ) = 6 * ((a : ℚ) - 1) := by
    unfold M
    rw [Nat.cast_sub (by omega : 6 ≤ 6 * a)]
    push_cast
    ring
  have hshiftCoeff :
      (M a : ℚ) - 6 * (n : ℚ) =
        6 * ((a : ℚ) - (n + 1 : Nat)) := by
    rw [hMcast]
    push_cast
    ring
  have hgamma := gammaWeight_mul_six_sub_eq_pred
    (a := a) (s := n + 1) (by omega : 1 ≤ n + 1) hnlt
  rw [hshiftCoeff]
  calc
    gammaWeight a (n + 1) *
        (6 * ((a : ℚ) - ↑(n + 1)) *
            printedTailECoeff μ a n +
          printedTailOmegaCoeff μ a (n + 1) -
          printedTailECoeff μ a (n + 1))
        =
      (gammaWeight a (n + 1) *
          (6 * ((a : ℚ) - ↑(n + 1)))) *
          printedTailECoeff μ a n +
        gammaWeight a (n + 1) * printedTailOmegaCoeff μ a (n + 1) -
        gammaWeight a (n + 1) * printedTailECoeff μ a (n + 1) := by
        ring
    _ =
      gammaWeight a n * printedTailECoeff μ a n +
        gammaWeight a (n + 1) * printedTailOmegaCoeff μ a (n + 1) -
        gammaWeight a (n + 1) * printedTailECoeff μ a (n + 1) := by
        rw [hgamma]
        rw [show n + 1 - 1 = n by omega]

/-- Elementary finite telescoping identity used by the weighted bracket
coefficients. -/
private theorem sum_range_sub_shift_eq_boundary (F : Nat → ℚ) (R : Nat) :
    (∑ n ∈ Finset.range R, F n) -
        (∑ n ∈ Finset.range R, F (n + 1)) =
      F 0 - F R := by
  induction R with
  | zero =>
      simp
  | succ R ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      calc
        ((∑ n ∈ Finset.range R, F n) + F R) -
            ((∑ n ∈ Finset.range R, F (n + 1)) + F (R + 1))
            =
          ((∑ n ∈ Finset.range R, F n) -
              (∑ n ∈ Finset.range R, F (n + 1))) +
            F R - F (R + 1) := by
            ring
        _ = F 0 - F R + F R - F (R + 1) := by rw [ih]
        _ = F 0 - F (R + 1) := by ring

/-- At degree zero, the omega coefficient is the exponential coefficient; the
marked numerator has no constant term. -/
theorem printedTailOmegaCoeff_zero_eq_ECoeff_zero (μ : List Nat) (a : Nat) :
    printedTailOmegaCoeff μ a 0 = printedTailECoeff μ a 0 := by
  unfold printedTailOmegaCoeff
  simp

/-- Summed weighted bracket identity before collapsing the shifted
low-exponential sums. -/
theorem sum_gammaWeight_mul_printedTailLowBracketProductCoeff_succ_eq
    (μ : List Nat) {a R : Nat} (ha : 150 ≤ a) (hRlt : R < a) :
    (∑ n ∈ Finset.range R,
      gammaWeight a (n + 1) *
        printedTailLowBracketProductCoeff μ a (n + 1)) =
      (∑ n ∈ Finset.range R,
        gammaWeight a n * printedTailECoeff μ a n) +
      (∑ n ∈ Finset.range R,
        gammaWeight a (n + 1) * printedTailOmegaCoeff μ a (n + 1)) -
      (∑ n ∈ Finset.range R,
        gammaWeight a (n + 1) * printedTailECoeff μ a (n + 1)) := by
  calc
    (∑ n ∈ Finset.range R,
      gammaWeight a (n + 1) *
        printedTailLowBracketProductCoeff μ a (n + 1))
        =
      ∑ n ∈ Finset.range R,
        (gammaWeight a n * printedTailECoeff μ a n +
          gammaWeight a (n + 1) * printedTailOmegaCoeff μ a (n + 1) -
          gammaWeight a (n + 1) * printedTailECoeff μ a (n + 1)) := by
        refine Finset.sum_congr rfl fun n hn => ?_
        have hnlt : n + 1 < a := by
          have hnR : n < R := Finset.mem_range.mp hn
          omega
        exact gammaWeight_mul_printedTailLowBracketProductCoeff_succ_eq
          (μ := μ) (a := a) (n := n) ha hnlt
    _ =
      (∑ n ∈ Finset.range R,
        gammaWeight a n * printedTailECoeff μ a n) +
      (∑ n ∈ Finset.range R,
        gammaWeight a (n + 1) * printedTailOmegaCoeff μ a (n + 1)) -
      (∑ n ∈ Finset.range R,
        gammaWeight a (n + 1) * printedTailECoeff μ a (n + 1)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- Summed weighted bracket identity in telescoped form. -/
theorem sum_gammaWeight_mul_printedTailLowBracketProductCoeff_succ_eq_telescope
    (μ : List Nat) {a R : Nat} (ha : 150 ≤ a) (hRlt : R < a) :
    (∑ n ∈ Finset.range R,
      gammaWeight a (n + 1) *
        printedTailLowBracketProductCoeff μ a (n + 1)) =
      gammaWeight a 0 * printedTailECoeff μ a 0 -
        gammaWeight a R * printedTailECoeff μ a R +
      (∑ n ∈ Finset.range R,
        gammaWeight a (n + 1) * printedTailOmegaCoeff μ a (n + 1)) := by
  rw [sum_gammaWeight_mul_printedTailLowBracketProductCoeff_succ_eq
    (μ := μ) (a := a) (R := R) ha hRlt]
  have htelescope := sum_range_sub_shift_eq_boundary
    (fun n => gammaWeight a n * printedTailECoeff μ a n) R
  rw [show
      (∑ n ∈ Finset.range R, gammaWeight a n * printedTailECoeff μ a n) +
          (∑ n ∈ Finset.range R,
            gammaWeight a (n + 1) * printedTailOmegaCoeff μ a (n + 1)) -
          (∑ n ∈ Finset.range R,
            gammaWeight a (n + 1) * printedTailECoeff μ a (n + 1)) =
        ((∑ n ∈ Finset.range R, gammaWeight a n * printedTailECoeff μ a n) -
          (∑ n ∈ Finset.range R,
            gammaWeight a (n + 1) * printedTailECoeff μ a (n + 1))) +
          (∑ n ∈ Finset.range R,
            gammaWeight a (n + 1) * printedTailOmegaCoeff μ a (n + 1)) by ring]
  rw [htelescope]

/-- Summed weighted bracket identity as an omega prefix minus the terminal
low-exponential boundary. -/
theorem sum_gammaWeight_mul_printedTailLowBracketProductCoeff_succ_eq_omegaPrefix
    (μ : List Nat) {a R : Nat} (ha : 150 ≤ a) (hRlt : R < a) :
    (∑ n ∈ Finset.range R,
      gammaWeight a (n + 1) *
        printedTailLowBracketProductCoeff μ a (n + 1)) =
      (∑ s ∈ Finset.range (R + 1),
        gammaWeight a s * printedTailOmegaCoeff μ a s) -
        gammaWeight a R * printedTailECoeff μ a R := by
  rw [sum_gammaWeight_mul_printedTailLowBracketProductCoeff_succ_eq_telescope
    (μ := μ) (a := a) (R := R) ha hRlt]
  have hshift :
      (∑ s ∈ Finset.range (R + 1),
        gammaWeight a s * printedTailOmegaCoeff μ a s) =
        (∑ n ∈ Finset.range R,
          gammaWeight a (n + 1) * printedTailOmegaCoeff μ a (n + 1)) +
          gammaWeight a 0 * printedTailOmegaCoeff μ a 0 := by
    rw [Finset.sum_range_succ']
  rw [hshift, printedTailOmegaCoeff_zero_eq_ECoeff_zero]
  ring

/-- Specialization of the bracket-coefficient telescope to the finite
`printedTailMainSum` prefix used by the large-tail assembly. -/
theorem sum_gammaWeight_mul_printedTailLowBracketProductCoeff_eq_mainSum_sub_boundary
    (μ : List Nat) {a : Nat} (ha : 150 ≤ a) :
    (∑ n ∈ Finset.range (printedTailR0 a),
      gammaWeight a (n + 1) *
        printedTailLowBracketProductCoeff μ a (n + 1)) =
      printedTailMainSum μ a -
        gammaWeight a (printedTailR0 a) *
          printedTailECoeff μ a (printedTailR0 a) := by
  have hRlt : printedTailR0 a < a := by
    unfold printedTailR0 printedTailP
    omega
  rw [sum_gammaWeight_mul_printedTailLowBracketProductCoeff_succ_eq_omegaPrefix
    (μ := μ) (a := a) (R := printedTailR0 a) ha hRlt]
  unfold printedTailMainSum
  rw [Prop51.list_range_map_sum]

/-- The basic factorial-ratio identity behind the paper's Gamma-moment
calculation:

`c_r * Gamma(a-2-r)/(6^r Gamma(a-2)) =
  d_r / (r * binom(a-3,r))`.

The statement is used only when `1 <= r <= a-3`. -/
theorem c_mul_gammaWeight_sub_two_eq_d_div_choose
    {a r : Nat} (hrpos : 1 ≤ r) (hr : r ≤ a - 3) :
    Prop51.c r * gammaWeight (a - 2) r =
      Prop51.d r / ((r : ℚ) * (((a - 3).choose r : Nat) : ℚ)) := by
  have hpow6 : (6 : ℚ)^r ≠ 0 := by positivity
  have hrfac_ne : (((r - 1).factorial : Nat) : ℚ) ≠ 0 :=
    factorial_cast_ne (r - 1)
  have harfac_ne : ((((a - 3 - r).factorial : Nat) : ℚ)) ≠ 0 :=
    factorial_cast_ne (a - 3 - r)
  have hr_ne : (r : ℚ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  have hchoose_ne : (((a - 3).choose r : Nat) : ℚ) ≠ 0 :=
    choose_cast_ne hr
  have hchoose_nat :=
    Nat.choose_mul_factorial_mul_factorial (n := a - 3) (k := r) hr
  have hchoose :
      (((a - 3).choose r : Nat) : ℚ) *
          ((r.factorial : Nat) : ℚ) *
          (((a - 3 - r).factorial : Nat) : ℚ) =
        (((a - 3).factorial : Nat) : ℚ) := by
    exact_mod_cast hchoose_nat
  have hrfac :
      ((r.factorial : Nat) : ℚ) =
        (r : ℚ) * (((r - 1).factorial : Nat) : ℚ) := by
    rw [show r = (r - 1) + 1 by omega, factorial_succ_cast]
    congr 1
  have hden :
      (((a - 3).factorial : Nat) : ℚ) =
        (((a - 3).choose r : Nat) : ℚ) * (r : ℚ) *
          (((r - 1).factorial : Nat) : ℚ) *
          (((a - 3 - r).factorial : Nat) : ℚ) := by
    rw [← hchoose, hrfac]
    ring
  rw [Prop51.c_eq_d, gammaWeight]
  rw [show a - 2 - r - 1 = a - 3 - r by omega]
  rw [show a - 2 - 1 = a - 3 by omega]
  rw [hden]
  field_simp [hpow6, hrfac_ne, harfac_ne, hr_ne, hchoose_ne]

private theorem gammaWeight_nonneg_of_lt {a s : Nat} (_hs : s < a) :
    0 ≤ gammaWeight a s := by
  unfold gammaWeight
  positivity

/-- The `r=1` contribution to the Gamma exponent moment. -/
theorem printedTailGammaExponent_head_le
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    hCoeff μ 1 * gammaWeight (a - 2) 1 ≤
      5 * (M a : ℚ) / (24 * ((a : ℚ) - 3)) := by
  have hcoeff := hCoeff_le_M_two_sub_twopow_c_of_partition
    (a := a) (μ := μ) hμ 1
  have hgamma : 0 ≤ gammaWeight (a - 2) 1 :=
    gammaWeight_nonneg_of_lt (by omega : 1 < a - 2)
  have hcg := c_mul_gammaWeight_sub_two_eq_d_div_choose
    (a := a) (r := 1) (by norm_num) (by omega : 1 ≤ a - 3)
  rw [Prop51.d_one] at hcg
  have hchoose1 : ((((a - 3).choose 1 : Nat) : ℚ)) = (a : ℚ) - 3 := by
    rw [Nat.choose_one_right]
    rw [Nat.cast_sub (by omega : 3 ≤ a)]
    norm_num
  rw [hchoose1] at hcg
  have hbound :
      hCoeff μ 1 * gammaWeight (a - 2) 1 ≤
        ((M a : ℚ) * (2 - 1 / (2 : ℚ)^1)) *
          Prop51.c 1 * gammaWeight (a - 2) 1 :=
    mul_le_mul_of_nonneg_right hcoeff hgamma
  calc
    hCoeff μ 1 * gammaWeight (a - 2) 1
        ≤ ((M a : ℚ) * (2 - 1 / (2 : ℚ)^1)) *
            Prop51.c 1 * gammaWeight (a - 2) 1 := hbound
    _ = 5 * (M a : ℚ) / (24 * ((a : ℚ) - 3)) := by
      rw [show ((M a : ℚ) * (2 - 1 / (2 : ℚ)^1)) *
            Prop51.c 1 * gammaWeight (a - 2) 1 =
          (M a : ℚ) * (2 - 1 / (2 : ℚ)^1) *
            (Prop51.c 1 * gammaWeight (a - 2) 1) by ring]
      rw [hcg]
      norm_num
      have ha3 : (a : ℚ) - 3 ≠ 0 := by
        have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
        nlinarith
      field_simp [ha3]
      ring

/-- The uniform `r >= 2` contribution bound used in the Gamma exponent
moment estimate. -/
theorem printedTailGammaExponent_tail_term_le
    {a r : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a))
    (hr2 : 2 ≤ r) (hrp : r ≤ printedTailP a) :
    hCoeff μ r * gammaWeight (a - 2) r ≤
      8 * (M a : ℚ) /
        (25 * ((r : ℚ) * (((a - 3).choose r : Nat) : ℚ))) := by
  have hr_le_a3 : r ≤ a - 3 := by
    unfold printedTailP at hrp
    omega
  have hcoeff := hCoeff_le_M_two_sub_twopow_c_of_partition
    (a := a) (μ := μ) hμ r
  have hgamma : 0 ≤ gammaWeight (a - 2) r :=
    gammaWeight_nonneg_of_lt (by omega : r < a - 2)
  have hcg := c_mul_gammaWeight_sub_two_eq_d_div_choose
    (a := a) (r := r) (by omega : 1 ≤ r) hr_le_a3
  have hDpos :
      0 < (r : ℚ) * (((a - 3).choose r : Nat) : ℚ) := by
    exact mul_pos (by exact_mod_cast (by omega : 0 < r))
      (by exact_mod_cast Nat.choose_pos hr_le_a3)
  have htwo_sub_le : 2 - 1 / (2 : ℚ)^r ≤ 2 := by
    have hnonneg : 0 ≤ 1 / (2 : ℚ)^r := by positivity
    linarith
  have hprod :
      (2 - 1 / (2 : ℚ)^r) * Prop51.d r ≤ 8 / 25 := by
    calc
      (2 - 1 / (2 : ℚ)^r) * Prop51.d r
          ≤ 2 * Prop51.d r :=
            mul_le_mul_of_nonneg_right htwo_sub_le (Prop51.d_nonneg r)
      _ ≤ 2 * (4 / 25 : ℚ) :=
            mul_le_mul_of_nonneg_left (Prop51.d_ub r (by omega : 1 ≤ r))
              (by norm_num)
      _ = 8 / 25 := by norm_num
  have hbound :
      hCoeff μ r * gammaWeight (a - 2) r ≤
        ((M a : ℚ) * (2 - 1 / (2 : ℚ)^r)) *
          Prop51.c r * gammaWeight (a - 2) r :=
    mul_le_mul_of_nonneg_right hcoeff hgamma
  calc
    hCoeff μ r * gammaWeight (a - 2) r
        ≤ ((M a : ℚ) * (2 - 1 / (2 : ℚ)^r)) *
            Prop51.c r * gammaWeight (a - 2) r := hbound
    _ = (M a : ℚ) *
          (((2 - 1 / (2 : ℚ)^r) * Prop51.d r) /
            ((r : ℚ) * (((a - 3).choose r : Nat) : ℚ))) := by
          rw [show ((M a : ℚ) * (2 - 1 / (2 : ℚ)^r)) *
              Prop51.c r * gammaWeight (a - 2) r =
            (M a : ℚ) * (2 - 1 / (2 : ℚ)^r) *
              (Prop51.c r * gammaWeight (a - 2) r) by ring]
          rw [hcg]
          ring
    _ ≤ (M a : ℚ) * ((8 / 25 : ℚ) /
          ((r : ℚ) * (((a - 3).choose r : Nat) : ℚ))) :=
          mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hprod hDpos.le)
            (by positivity)
    _ = 8 * (M a : ℚ) /
          (25 * ((r : ℚ) * (((a - 3).choose r : Nat) : ℚ))) := by
          field_simp [hDpos.ne']

/-- The `r=2` denominator in the Gamma exponent estimate is
`(a-3)(a-4)`. -/
theorem gammaExponent_den_two_eq (a : Nat) (ha : 150 ≤ a) :
    (2 : ℚ) * (((a - 3).choose 2 : Nat) : ℚ) =
      ((a : ℚ) - 3) * ((a : ℚ) - 4) := by
  rw [Nat.cast_choose_two]
  rw [Nat.cast_sub (by omega : 3 ≤ a)]
  norm_num
  ring

/-- For all higher terms in the exponent moment, the denominator
`r * C(a-3,r)` is at least the `r=3` denominator. -/
theorem gammaExponent_recip_tail_le_three
    {a r : Nat} (ha : 150 ≤ a) (hr3 : 3 ≤ r)
    (hrp : r ≤ printedTailP a) :
    1 / ((r : ℚ) * (((a - 3).choose r : Nat) : ℚ)) ≤
      1 / ((3 : ℚ) * (((a - 3).choose 3 : Nat) : ℚ)) := by
  have hr_le_a3 : r ≤ a - 3 := by
    unfold printedTailP at hrp
    omega
  have hchoose3_le : (a - 3).choose 3 ≤ (a - 3).choose r :=
    Prop51.choose_three_le hr3 (by
      unfold printedTailP at hrp
      omega)
  have hden_le_nat :
      3 * ((a - 3).choose 3) ≤ r * ((a - 3).choose r) := by
    calc
      3 * ((a - 3).choose 3)
          ≤ r * ((a - 3).choose 3) :=
            Nat.mul_le_mul_right _ hr3
      _ ≤ r * ((a - 3).choose r) :=
            Nat.mul_le_mul_left _ hchoose3_le
  have hden_le :
      (3 : ℚ) * (((a - 3).choose 3 : Nat) : ℚ) ≤
        (r : ℚ) * (((a - 3).choose r : Nat) : ℚ) := by
    exact_mod_cast hden_le_nat
  have hden3_pos :
      0 < (3 : ℚ) * (((a - 3).choose 3 : Nat) : ℚ) := by
    exact mul_pos (by norm_num)
      (by exact_mod_cast Nat.choose_pos (by omega : 3 ≤ a - 3))
  exact one_div_le_one_div_of_le hden3_pos hden_le

/-- Sum of the `r >= 2` contributions to the Gamma exponent moment. -/
theorem printedTailGammaExponent_tail_sum_le
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    (∑ r ∈ Finset.Ico 2 (printedTailP a + 1),
      hCoeff μ r * gammaWeight (a - 2) r) ≤
      (8 * (M a : ℚ) / 25) *
        (1 / (((a : ℚ) - 3) * ((a : ℚ) - 4)) +
          (((printedTailP a : Nat) : ℚ) - 2) /
            ((3 : ℚ) * (((a - 3).choose 3 : Nat) : ℚ))) := by
  let p := printedTailP a
  let F : Nat → ℚ := fun r => hCoeff μ r * gammaWeight (a - 2) r
  have hp2 : 2 ≤ p := by
    dsimp [p, printedTailP]
    omega
  have hD2pos :
      0 < ((a : ℚ) - 3) * ((a : ℚ) - 4) := by
    have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
    nlinarith
  have hD3pos :
      0 < (3 : ℚ) * (((a - 3).choose 3 : Nat) : ℚ) := by
    exact mul_pos (by norm_num)
      (by exact_mod_cast Nat.choose_pos (by omega : 3 ≤ a - 3))
  have hsplit :
      (∑ r ∈ Finset.Ico 2 (p + 1), F r) =
        (∑ r ∈ Finset.Ico 2 3, F r) +
          ∑ r ∈ Finset.Ico 3 (p + 1), F r := by
    have h := Finset.sum_Ico_consecutive F
      (by norm_num : 2 ≤ 3) (by omega : 3 ≤ p + 1)
    exact h.symm
  have hhead :
      (∑ r ∈ Finset.Ico 2 3, F r) ≤
        (8 * (M a : ℚ) / 25) *
          (1 / (((a : ℚ) - 3) * ((a : ℚ) - 4))) := by
    have hterm := printedTailGammaExponent_tail_term_le
      (a := a) (r := 2) (μ := μ) ha hμ
      (by norm_num) (by dsimp [p, printedTailP] at hp2 ⊢; omega)
    rw [show Finset.Ico 2 3 = ({2} : Finset Nat) by decide,
      Finset.sum_singleton]
    dsimp [F]
    calc
      hCoeff μ 2 * gammaWeight (a - 2) 2
          ≤ 8 * (M a : ℚ) /
              (25 * ((2 : ℚ) * (((a - 3).choose 2 : Nat) : ℚ))) := hterm
      _ = (8 * (M a : ℚ) / 25) *
            (1 / (((a : ℚ) - 3) * ((a : ℚ) - 4))) := by
            rw [gammaExponent_den_two_eq a ha]
            field_simp [hD2pos.ne']
  have htail :
      (∑ r ∈ Finset.Ico 3 (p + 1), F r) ≤
        (8 * (M a : ℚ) / 25) *
          ((((p : Nat) : ℚ) - 2) /
            ((3 : ℚ) * (((a - 3).choose 3 : Nat) : ℚ))) := by
    have hterm :
        ∀ r ∈ Finset.Ico 3 (p + 1), F r ≤
          (8 * (M a : ℚ) / 25) *
            (1 / ((3 : ℚ) * (((a - 3).choose 3 : Nat) : ℚ))) := by
      intro r hr
      have hrmem := Finset.mem_Ico.mp hr
      have hrp : r ≤ printedTailP a := by
        dsimp [p] at hrmem
        omega
      have hraw := printedTailGammaExponent_tail_term_le
        (a := a) (r := r) (μ := μ) ha hμ (by omega : 2 ≤ r) hrp
      have hrecip := gammaExponent_recip_tail_le_three
        (a := a) (r := r) ha (by omega : 3 ≤ r) hrp
      have hDrpos :
          0 < (r : ℚ) * (((a - 3).choose r : Nat) : ℚ) := by
        exact mul_pos (by exact_mod_cast (by omega : 0 < r))
          (by exact_mod_cast Nat.choose_pos (by
            unfold printedTailP at hrp
            omega))
      calc
        F r
            ≤ 8 * (M a : ℚ) /
                (25 * ((r : ℚ) * (((a - 3).choose r : Nat) : ℚ))) := hraw
        _ = (8 * (M a : ℚ) / 25) *
              (1 / ((r : ℚ) * (((a - 3).choose r : Nat) : ℚ))) := by
              field_simp [hDrpos.ne']
        _ ≤ (8 * (M a : ℚ) / 25) *
              (1 / ((3 : ℚ) * (((a - 3).choose 3 : Nat) : ℚ))) :=
              mul_le_mul_of_nonneg_left hrecip (by positivity)
    calc
      (∑ r ∈ Finset.Ico 3 (p + 1), F r)
          ≤ ∑ r ∈ Finset.Ico 3 (p + 1),
              (8 * (M a : ℚ) / 25) *
                (1 / ((3 : ℚ) * (((a - 3).choose 3 : Nat) : ℚ))) :=
            Finset.sum_le_sum hterm
      _ = (8 * (M a : ℚ) / 25) *
            ((((p : Nat) : ℚ) - 2) /
              ((3 : ℚ) * (((a - 3).choose 3 : Nat) : ℚ))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            rw [Nat.card_Ico]
            have hcard : p + 1 - 3 = p - 2 := by omega
            rw [hcard]
            rw [Nat.cast_sub hp2]
            field_simp [hD3pos.ne']
            ring
  change (∑ r ∈ Finset.Ico 2 (p + 1), F r) ≤ _
  rw [hsplit]
  calc
    (∑ r ∈ Finset.Ico 2 3, F r) + ∑ r ∈ Finset.Ico 3 (p + 1), F r
        ≤ (8 * (M a : ℚ) / 25) *
            (1 / (((a : ℚ) - 3) * ((a : ℚ) - 4))) +
          (8 * (M a : ℚ) / 25) *
            ((((p : Nat) : ℚ) - 2) /
              ((3 : ℚ) * (((a - 3).choose 3 : Nat) : ℚ))) :=
          add_le_add hhead htail
    _ = (8 * (M a : ℚ) / 25) *
        (1 / (((a : ℚ) - 3) * ((a : ℚ) - 4)) +
          (((printedTailP a : Nat) : ℚ) - 2) /
            ((3 : ℚ) * (((a - 3).choose 3 : Nat) : ℚ))) := by
          dsimp [p]
          ring

private theorem choose_three_cast {n : Nat} (hn : 3 ≤ n) :
    ((n.choose 3 : Nat) : ℚ) =
      (n : ℚ) * (n - 1 : Nat) * (n - 2 : Nat) / 6 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 3 + m - 1 = m + 2 by omega,
    show 3 + m - 2 = m + 1 by omega]
  have h := Nat.choose_mul_factorial_mul_factorial
    (n := 3 + m) (k := 3) (by omega : 3 ≤ 3 + m)
  norm_num at h
  have hq :
      (((3 + m).choose 3 * 6 * m.factorial : Nat) : ℚ) =
        (((3 + m).factorial : Nat) : ℚ) := by
    exact_mod_cast h
  have hfac :
      (((3 + m).factorial : Nat) : ℚ) =
        ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) *
          ((m.factorial : Nat) : ℚ) := by
    rw [show 3 + m = (m + 2) + 1 by omega, Nat.factorial_succ]
    rw [show m + 2 = (m + 1) + 1 by omega, Nat.factorial_succ]
    rw [show m + 1 = m + 1 by rfl, Nat.factorial_succ]
    norm_num
    ring
  rw [Nat.cast_mul, Nat.cast_mul, hfac] at hq
  have hfac_ne : (((m.factorial : Nat) : ℚ)) ≠ 0 := by positivity
  field_simp [hfac_ne] at hq ⊢
  push_cast
  ring_nf at hq ⊢
  exact hq

theorem printedTailGammaExponent_budget_le_bound
    (a : Nat) (ha : 150 ≤ a) :
    5 * (M a : ℚ) / (24 * ((a : ℚ) - 3)) +
      (8 * (M a : ℚ) / 25) *
        (1 / (((a : ℚ) - 3) * ((a : ℚ) - 4)) +
          (((printedTailP a : Nat) : ℚ) - 2) /
            ((3 : ℚ) * (((a - 3).choose 3 : Nat) : ℚ))) ≤
      gammaExponentBound a := by
  have haQ : (150 : ℚ) ≤ a := by exact_mod_cast ha
  have ha3pos : (0 : ℚ) < (a : ℚ) - 3 := by nlinarith
  have ha4pos : (0 : ℚ) < (a : ℚ) - 4 := by nlinarith
  have ha5pos : (0 : ℚ) < (a : ℚ) - 5 := by nlinarith
  have hchoose3 :
      ((((a - 3).choose 3 : Nat) : ℚ)) =
        ((a : ℚ) - 3) * ((a : ℚ) - 4) * ((a : ℚ) - 5) / 6 := by
    rw [choose_three_cast (by omega : 3 ≤ a - 3)]
    rw [show a - 3 - 1 = a - 4 by omega]
    rw [show a - 3 - 2 = a - 5 by omega]
    rw [Nat.cast_sub (by omega : 3 ≤ a)]
    rw [Nat.cast_sub (by omega : 4 ≤ a)]
    rw [Nat.cast_sub (by omega : 5 ≤ a)]
    norm_num
  have hMcast : ((M a : Nat) : ℚ) = 6 * (a : ℚ) - 6 := by
    unfold M
    rw [Nat.cast_sub (by omega : 6 ≤ 6 * a)]
    norm_num
  have hp2a_nat : 2 * printedTailP a ≤ a := by
    unfold printedTailP
    exact Nat.mul_div_le a 2
  have hp_le : (((printedTailP a : Nat) : ℚ) - 2) ≤ (a : ℚ) / 2 := by
    have hp2a : (2 : ℚ) * ((printedTailP a : Nat) : ℚ) ≤ (a : ℚ) := by
      exact_mod_cast hp2a_nat
    nlinarith
  rw [gammaExponentBound, hchoose3]
  rw [hMcast]
  field_simp [ha3pos.ne', ha4pos.ne', ha5pos.ne']
  ring_nf
  nlinarith

/-- Closed rational version of the paper's estimate
`E[L(1/(6Y))] <= gammaExponentBound a < 13/10`. -/
theorem printedTailGammaExponentMoment_le_bound
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    printedTailGammaExponentMoment μ a ≤ gammaExponentBound a := by
  let p := printedTailP a
  let F : Nat → ℚ := fun r => hCoeff μ r * gammaWeight (a - 2) r
  have hp2 : 2 ≤ p := by
    dsimp [p, printedTailP]
    omega
  have hsplit :
      (∑ r ∈ Finset.Ico 1 (p + 1), F r) =
        (∑ r ∈ Finset.Ico 1 2, F r) +
          ∑ r ∈ Finset.Ico 2 (p + 1), F r := by
    have h := Finset.sum_Ico_consecutive F
      (by norm_num : 1 ≤ 2) (by omega : 2 ≤ p + 1)
    exact h.symm
  have hhead :
      (∑ r ∈ Finset.Ico 1 2, F r) ≤
        5 * (M a : ℚ) / (24 * ((a : ℚ) - 3)) := by
    rw [show Finset.Ico 1 2 = ({1} : Finset Nat) by decide,
      Finset.sum_singleton]
    dsimp [F]
    exact printedTailGammaExponent_head_le (a := a) (μ := μ) ha hμ
  have htail :
      (∑ r ∈ Finset.Ico 2 (p + 1), F r) ≤
        (8 * (M a : ℚ) / 25) *
          (1 / (((a : ℚ) - 3) * ((a : ℚ) - 4)) +
            (((p : Nat) : ℚ) - 2) /
              ((3 : ℚ) * (((a - 3).choose 3 : Nat) : ℚ))) := by
    dsimp [F, p]
    exact printedTailGammaExponent_tail_sum_le (a := a) (μ := μ) ha hμ
  have hbudget := printedTailGammaExponent_budget_le_bound a ha
  unfold printedTailGammaExponentMoment
  change (∑ r ∈ Finset.Ico 1 (p + 1), F r) ≤ gammaExponentBound a
  rw [hsplit]
  calc
    (∑ r ∈ Finset.Ico 1 2, F r) + ∑ r ∈ Finset.Ico 2 (p + 1), F r
        ≤ 5 * (M a : ℚ) / (24 * ((a : ℚ) - 3)) +
          (8 * (M a : ℚ) / 25) *
            (1 / (((a : ℚ) - 3) * ((a : ℚ) - 4)) +
              (((p : Nat) : ℚ) - 2) /
                ((3 : ℚ) * (((a - 3).choose 3 : Nat) : ℚ))) :=
          add_le_add hhead htail
    _ ≤ gammaExponentBound a := by
          dsimp [p] at hbudget ⊢
          exact hbudget

/-- The closed rational moment estimate in the scalar form used by Jensen. -/
theorem printedTailGammaExponentMoment_lt_thirteen_tenths
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    printedTailGammaExponentMoment μ a < 13 / 10 :=
  (printedTailGammaExponentMoment_le_bound (a := a) (μ := μ) ha hμ).trans_lt
    (gammaExponentBound_lt a ha)

end Prop52
