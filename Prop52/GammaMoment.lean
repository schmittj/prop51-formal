/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Algebraic Gamma-moment bounds for Proposition 5.2

This file develops the rational part of the Gamma-margin argument for the
large printed Proposition 5.2 tail.  It deliberately stays in finite sums and
factorial ratios: the probabilistic language in the paper is represented here
by the weights `gammaWeight`.
-/

import Prop52.Printed

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

end Prop52
