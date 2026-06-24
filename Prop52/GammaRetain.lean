/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Rational retained-term algebra for the Prop52 Gamma margin

This file formalizes the coefficient inequalities in the Gamma
integration-by-parts bracket.  It does not prove the analytic integration
identity; it proves the rational facts used after that identity:
all bracket coefficients are nonnegative, and the `j = 1` coefficient is at
least `5M`.
-/

import Prop52.Printed

namespace Prop52

/-- The coefficient of `t^(j+1)` in the bracket
`M t + 6 t^2 L'(t) - J(t)`. -/
def gammaRetainBracketCoeff (μ : List Nat) (j : Nat) : ℚ :=
  6 * (j : ℚ) * hCoeff μ j - kCoeff μ (j + 1)

private theorem two_marked_term_succ_le_one_sub_inv_pow
    {mi j : Nat} (hmi : 1 ≤ mi) (hj : 1 ≤ j) :
    2 * ((mi : ℚ) / (((mi + 1 : Nat) : ℚ)^(j + 1))) ≤
      1 - 1 / (((mi + 1 : Nat) : ℚ)^j) := by
  let q : ℚ := ((mi + 1 : Nat) : ℚ)
  have hqpos : 0 < q := by
    dsimp [q]
    exact_mod_cast Nat.succ_pos mi
  have hq2 : (2 : ℚ) ≤ q := by
    dsimp [q]
    exact_mod_cast Nat.succ_le_succ hmi
  have hq1 : (1 : ℚ) ≤ q := by linarith
  have hpow_ge_sq : q^2 ≤ q^(j + 1) :=
    pow_le_pow_right₀ hq1 (by omega : 2 ≤ j + 1)
  have hmain : 2 * (q - 1) ≤ q^(j + 1) - q := by
    nlinarith
  have hmi_eq : (mi : ℚ) = q - 1 := by
    dsimp [q]
    push_cast
    ring
  rw [show 2 * ((mi : ℚ) / q^(j + 1)) =
      (2 * (mi : ℚ)) / q^(j + 1) by ring]
  rw [div_le_iff₀ (pow_pos hqpos (j + 1))]
  rw [hmi_eq]
  have hrhs :
      (1 - 1 / q^j) * q^(j + 1) = q^(j + 1) - q := by
    rw [show j + 1 = j + 1 by rfl, pow_succ]
    field_simp [pow_ne_zero j hqpos.ne']
  rw [hrhs]
  exact hmain

/-- Termwise sum form of `u_j >= 2 w_{j+1}` for positive parts, where
`u_j = length(μ) - s_j`. -/
theorem two_markedWeight_succ_le_length_sub_sPower_of_pos
    {μ : List Nat} (hpos : ∀ m ∈ μ, 1 ≤ m) {j : Nat} (hj : 1 ≤ j) :
    2 * markedWeight μ (j + 1) ≤ (μ.length : ℚ) - sPower μ j := by
  induction μ with
  | nil =>
      simp [markedWeight, sPower]
  | cons mi μ ih =>
      have hmi : 1 ≤ mi := hpos mi (by simp)
      have htail : ∀ m ∈ μ, 1 ≤ m := by
        intro m hm
        exact hpos m (by simp [hm])
      have hterm := two_marked_term_succ_le_one_sub_inv_pow
        (mi := mi) (j := j) hmi hj
      have hterm' :
          2 * ((mi : ℚ) / (((mi : ℚ) + 1)^(j + 1))) ≤
            1 - 1 / (((mi : ℚ) + 1)^j) := by
        simpa [Nat.cast_add, Nat.cast_one] using hterm
      have ih' := ih htail
      unfold markedWeight sPower at ih' ⊢
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
        Nat.cast_one]
      have ih_norm :
          2 * (List.map (fun mi : Nat => (mi : ℚ) /
              (((mi : ℚ) + 1) ^ (j + 1))) μ).sum ≤
            (μ.length : ℚ) -
              (List.map (fun mi : Nat => 1 / (((mi : ℚ) + 1)^j)) μ).sum := by
        simpa [Nat.cast_add, Nat.cast_one] using ih'
      calc
        2 * ((mi : ℚ) / ((mi : ℚ) + 1) ^ (j + 1) +
            (List.map (fun mi : Nat => (mi : ℚ) /
              (((mi : ℚ) + 1) ^ (j + 1))) μ).sum)
            =
          2 * ((mi : ℚ) / ((mi : ℚ) + 1) ^ (j + 1)) +
            2 * (List.map (fun mi : Nat => (mi : ℚ) /
              (((mi : ℚ) + 1) ^ (j + 1))) μ).sum := by
          ring
        _ ≤
          (1 - 1 / (((mi : ℚ) + 1)^j)) +
            ((μ.length : ℚ) -
              (List.map (fun mi : Nat => 1 /
                (((mi : ℚ) + 1)^j)) μ).sum) :=
          add_le_add hterm' ih_norm
        _ =
          (↑μ.length + 1) -
            (1 / (((mi : ℚ) + 1)^j) +
              (List.map (fun mi : Nat => 1 /
                (((mi : ℚ) + 1)^j)) μ).sum) := by
          ring

private theorem N_sub_sPower_eq_M_add_length_sub_sPower
    {a : Nat} {μ : List Nat} (hμ : Prop51.IsPartitionOf μ (M a)) (j : Nat) :
    (N μ : ℚ) - sPower μ j =
      (M a : ℚ) + ((μ.length : ℚ) - sPower μ j) := by
  obtain ⟨hsum, _hpos⟩ := hμ
  have hN : N μ = M a + μ.length := by
    unfold N
    rw [Prop51.sum_map_add_one, hsum]
  rw [hN]
  push_cast
  ring

private theorem kCoeff_succ_eq
    (μ : List Nat) {j : Nat} (hj : 1 ≤ j) :
    kCoeff μ (j + 1) =
      12 * (j : ℚ) * Prop51.c j * markedWeight μ (j + 1) := by
  cases j with
  | zero => omega
  | succ n =>
      simp [kCoeff, Nat.cast_add, Nat.cast_one]

/-- Every coefficient in the Gamma integration-by-parts bracket after the
linear term is nonnegative. -/
theorem gammaRetainBracketCoeff_nonneg
    {a j : Nat} {μ : List Nat}
    (hμ : Prop51.IsPartitionOf μ (M a)) (hj : 1 ≤ j) :
    0 ≤ gammaRetainBracketCoeff μ j := by
  have hgap := two_markedWeight_succ_le_length_sub_sPower_of_pos
    (μ := μ) hμ.2 (j := j) hj
  have hN := N_sub_sPower_eq_M_add_length_sub_sPower
    (a := a) (μ := μ) hμ j
  have hk := kCoeff_succ_eq μ (j := j) hj
  have hinside :
      0 ≤ (M a : ℚ) + ((μ.length : ℚ) - sPower μ j) -
        2 * markedWeight μ (j + 1) := by
    have hM : 0 ≤ (M a : ℚ) := by positivity
    nlinarith
  unfold gammaRetainBracketCoeff hCoeff
  rw [hk, hN]
  calc
    0 ≤ 6 * (j : ℚ) * Prop51.c j *
        ((M a : ℚ) + ((μ.length : ℚ) - sPower μ j) -
          2 * markedWeight μ (j + 1)) := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (by positivity))
          (Prop51.c_nonneg j))
        hinside
    _ = 6 * (j : ℚ) *
          (Prop51.c j * ((M a : ℚ) +
            ((μ.length : ℚ) - sPower μ j))) -
        12 * (j : ℚ) * Prop51.c j * markedWeight μ (j + 1) := by
      ring

/-- The retained `j = 1` bracket coefficient is at least `5M`, which is the
positive term retained in the printed Gamma-margin proof. -/
theorem fiveM_le_gammaRetainBracketCoeff_one
    {a : Nat} {μ : List Nat} (hμ : Prop51.IsPartitionOf μ (M a)) :
    5 * (M a : ℚ) ≤ gammaRetainBracketCoeff μ 1 := by
  have hgap := two_markedWeight_succ_le_length_sub_sPower_of_pos
    (μ := μ) hμ.2 (j := 1) (by norm_num)
  have hN := N_sub_sPower_eq_M_add_length_sub_sPower
    (a := a) (μ := μ) hμ 1
  unfold gammaRetainBracketCoeff hCoeff
  rw [kCoeff_succ_eq μ (j := 1) (by norm_num), hN, Prop51.c_one]
  nlinarith

/-- A lower polynomial for the integration-by-parts bracket
`M t + 6t^2 L'(t) - J(t)`.

The final coefficient in this lower polynomial subtracts `k_{p+1}` even
though the low `J` polynomial only reaches degree `p`; this makes the
polynomial no larger than the actual low bracket and keeps every coefficient in
the uniform `gammaRetainBracketCoeff` form. -/
def gammaRetainBracketLower (μ : List Nat) (a : Nat) (x : ℚ) : ℚ :=
  ((M a : ℚ) - kCoeff μ 1) * x +
    ∑ j ∈ Finset.Ico 1 (printedTailP a + 1),
      gammaRetainBracketCoeff μ j * x^(j + 1)

/-- The linear coefficient of the retained Gamma bracket is nonnegative. -/
theorem gammaRetainBracketLinearCoeff_nonneg
    {a : Nat} {μ : List Nat} (hμ : Prop51.IsPartitionOf μ (M a)) :
    0 ≤ (M a : ℚ) - kCoeff μ 1 := by
  have hmw := markedWeight_le_M_div_two_pow_of_partition
    (a := a) (μ := μ) hμ 1
  simp [kCoeff] at hmw ⊢
  nlinarith

/-- Pointwise retained-bracket lower bound used by the Gamma-margin proof:
for nonnegative `x`, all retained bracket coefficients are nonnegative and the
`x^2` coefficient alone contributes at least `5M`. -/
theorem fiveM_x2_le_gammaRetainBracketLower
    {a : Nat} {μ : List Nat} (ha : 150 ≤ a)
    (hμ : Prop51.IsPartitionOf μ (M a)) {x : ℚ} (hx : 0 ≤ x) :
    5 * (M a : ℚ) * x^2 ≤ gammaRetainBracketLower μ a x := by
  unfold gammaRetainBracketLower
  have hlinear_nonneg : 0 ≤ ((M a : ℚ) - kCoeff μ 1) * x := by
    exact mul_nonneg (gammaRetainBracketLinearCoeff_nonneg
      (a := a) (μ := μ) hμ) hx
  have hterms_nonneg :
      ∀ j ∈ Finset.Ico 1 (printedTailP a + 1),
        0 ≤ gammaRetainBracketCoeff μ j * x^(j + 1) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    exact mul_nonneg
      (gammaRetainBracketCoeff_nonneg (a := a) (μ := μ) hμ hj1)
      (pow_nonneg hx (j + 1))
  have hmem1 : 1 ∈ Finset.Ico 1 (printedTailP a + 1) := by
    simp [printedTailP]
    omega
  have hsingle := Finset.single_le_sum hterms_nonneg hmem1
  have hterm1 :
      5 * (M a : ℚ) * x^2 ≤ gammaRetainBracketCoeff μ 1 * x^(1 + 1) := by
    have hcoeff := fiveM_le_gammaRetainBracketCoeff_one
      (a := a) (μ := μ) hμ
    have hx2 : 0 ≤ x^2 := pow_nonneg hx 2
    calc
      5 * (M a : ℚ) * x^2
          ≤ gammaRetainBracketCoeff μ 1 * x^2 :=
            mul_le_mul_of_nonneg_right hcoeff hx2
      _ = gammaRetainBracketCoeff μ 1 * x^(1 + 1) := by norm_num
  calc
    5 * (M a : ℚ) * x^2
        ≤ gammaRetainBracketCoeff μ 1 * x^(1 + 1) := hterm1
    _ ≤ ∑ j ∈ Finset.Ico 1 (printedTailP a + 1),
          gammaRetainBracketCoeff μ j * x^(j + 1) := hsingle
    _ ≤ ((M a : ℚ) - kCoeff μ 1) * x +
          ∑ j ∈ Finset.Ico 1 (printedTailP a + 1),
            gammaRetainBracketCoeff μ j * x^(j + 1) := by
          nlinarith

end Prop52
