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
