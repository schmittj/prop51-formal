/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Bridge from the Prop52 mid upper bound to printed negativity

The finite certificate in `Prop52.MidCertificateAll` proves negativity of the
one-parameter upper bound `midUNormFast a (N μ)` for `14 <= a <= 149`.
This file isolates the remaining analytic/formal bridge: the coefficientwise
upper bound from the printed coefficient to that one-parameter expression.
-/

import Prop52.Printed
import Prop52.MidCertificateAll

namespace Prop52

open PowerSeries

/-! ## Exact `B_N * A_μ` decomposition -/

/-- The auxiliary series `A_μ(t)=P_μ(t)(1-K_μ(t))` used in the mid proof. -/
noncomputable def printedMidASeries (μ : List Nat) : ℚ⟦X⟧ :=
  Prop51.prodSeries μ * (1 - printedFullKSeries μ)

/-- Coefficients of `A_μ(t)=P_μ(t)(1-K_μ(t))`. -/
noncomputable def printedMidACoeff (μ : List Nat) (r : Nat) : ℚ :=
  coeff r (printedMidASeries μ)

theorem coeff_printedMidASeries (μ : List Nat) (r : Nat) :
    coeff r (printedMidASeries μ) = printedMidACoeff μ r := by
  rfl

theorem printedFullFSeries_eq_bSeries (μ : List Nat) :
    printedFullFSeries μ = Prop51.bSeries μ := by
  ext r
  rw [coeff_printedFullFSeries]
  rw [← bCoeff_eq_fCoeff μ r]
  rw [Prop51.bSeries, coeff_mk]

theorem printedFullFSeries_eq_B_mul_prod (μ : List Nat) :
    printedFullFSeries μ = Prop51.BSeriesQ (N μ) * Prop51.prodSeries μ := by
  rw [printedFullFSeries_eq_bSeries, Prop51.bSeries_eq_B_mul_prod]
  rfl

theorem coeff_printedMidASeries_zero (μ : List Nat) :
    printedMidACoeff μ 0 = 1 := by
  unfold printedMidACoeff printedMidASeries
  rw [coeff_zero_eq_constantCoeff, map_mul, Prop51.constantCoeff_prodSeries]
  have hK0 : constantCoeff (printedFullKSeries μ) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_printedFullKSeries]
    rfl
  rw [map_sub, map_one, hK0]
  ring

/--
Exact convolution form of the printed coefficient after the `A_μ` rewrite.

This is the formal target behind the mid-range upper bound: the remaining
coefficientwise work is to prove that positive-degree coefficients of
`A_μ` are nonpositive and bounded in size by the one-parameter `midS` sequence.
-/
theorem printedCoeff_eq_B_mul_A_coeff (μ : List Nat) (a : Nat) :
    printedCoeff μ a =
      ∑ k ∈ Finset.range (a + 1),
        Prop51.Bq (N μ) k * printedMidACoeff μ (a - k) := by
  rw [← coeff_printedFullSeries_eq_printedCoeff μ a]
  rw [printedFullFSeries_eq_B_mul_prod]
  have hseries :
      Prop51.BSeriesQ (N μ) * Prop51.prodSeries μ * (1 - printedFullKSeries μ) =
        Prop51.BSeriesQ (N μ) * printedMidASeries μ := by
    unfold printedMidASeries
    ring
  rw [hseries]
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Prop51.coeff_BSeriesQ, coeff_printedMidASeries]

/--
Remaining mid-range bridge target.

For every partition in the mid range, the printed coefficient is bounded above
by the certified one-parameter quantity, after undoing the normalization by
`N c_a`.
-/
def PrintedMidUpperBound : Prop :=
  ∀ a : Nat, 14 ≤ a → a ≤ 149 →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      printedCoeff μ a ≤ (((N μ : Nat) : ℚ) * Prop51.c a) *
        midUNormFast a (N μ)

private theorem mid_N_pos_of_partition {a : Nat} {μ : List Nat}
    (ha : 14 ≤ a) (hμ : Prop51.IsPartitionOf μ (M a)) :
    0 < N μ := by
  obtain ⟨hsum, _hpos⟩ := hμ
  unfold N
  rw [Prop51.sum_map_add_one]
  unfold M at hsum
  omega

private theorem mid_den_pos_of_partition {a : Nat} {μ : List Nat}
    (ha : 14 ≤ a) (hμ : Prop51.IsPartitionOf μ (M a)) :
    0 < (((N μ : Nat) : ℚ) * Prop51.c a) := by
  have hN : (0 : ℚ) < ((N μ : Nat) : ℚ) := by
    exact_mod_cast mid_N_pos_of_partition (a := a) (μ := μ) ha hμ
  have hc : 0 < Prop51.c a := Prop51.c_pos a (by omega)
  exact mul_pos hN hc

/--
Closing the printed mid-range sign from the coefficientwise bridge and the
native interval certificates.
-/
theorem printedCoeffNegativityMid_of_upperBound
    (hbound : PrintedMidUpperBound) :
    PrintedCoeffNegativityMid := by
  intro a ha_lo ha_hi μ hμ
  have hU : midUNormFast a (N μ) < 0 :=
    midUNormFast_neg_rows_14_149_of_partition a μ ha_lo ha_hi hμ
  have hden : 0 < (((N μ : Nat) : ℚ) * Prop51.c a) :=
    mid_den_pos_of_partition (a := a) (μ := μ) ha_lo hμ
  have hscaled :
      (((N μ : Nat) : ℚ) * Prop51.c a) * midUNormFast a (N μ) < 0 :=
    mul_neg_of_pos_of_neg hden hU
  exact lt_of_le_of_lt (hbound a ha_lo ha_hi μ hμ) hscaled

end Prop52
