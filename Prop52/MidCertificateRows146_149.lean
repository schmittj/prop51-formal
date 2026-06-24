/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Prop52 mid-range certificate shard: rows 146--149

Native interval certificates for the printed Proposition 5.2 mid-range
checker, converted through `Prop52.MidInterval` into exact rational
`midUNormFast` negativity.
-/

import Prop52.MidInterval

namespace Prop52

theorem checkPrintedMidRowInterval_146 :
    checkPrintedMidRowInterval 146 = true := by
  native_decide

theorem checkPrintedMidRowInterval_147 :
    checkPrintedMidRowInterval 147 = true := by
  native_decide

theorem checkPrintedMidRowInterval_148 :
    checkPrintedMidRowInterval 148 = true := by
  native_decide

theorem checkPrintedMidRowInterval_149 :
    checkPrintedMidRowInterval 149 = true := by
  native_decide

/-- Exact normalized negativity certified for rows `146 <= a <= 149`. -/
theorem midUNormFast_neg_rows_146_149 (a i : Nat)
    (ha_lo : 146 ≤ a) (ha_hi : a ≤ 149) (hi : i < M a) :
    midUNormFast a (M a + 1 + i) < 0 := by
  interval_cases a
  · exact midUNormFast_neg_of_rowInterval 146 i checkPrintedMidRowInterval_146 hi
  · exact midUNormFast_neg_of_rowInterval 147 i checkPrintedMidRowInterval_147 hi
  · exact midUNormFast_neg_of_rowInterval 148 i checkPrintedMidRowInterval_148 hi
  · exact midUNormFast_neg_of_rowInterval 149 i checkPrintedMidRowInterval_149 hi

theorem midUNormFast_neg_rows_146_149_of_partition (a : Nat) (μ : List Nat)
    (ha_lo : 146 ≤ a) (ha_hi : a ≤ 149)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    midUNormFast a (N μ) < 0 := by
  have hlen_pos : 1 ≤ μ.length := by
    obtain ⟨hsum, _hpos⟩ := hμ
    cases μ with
    | nil =>
        simp [M] at hsum
        omega
    | cons m μ =>
        simp
  obtain ⟨hsum, hpos⟩ := hμ
  have hlen_le := Prop51.length_le_sum μ hpos
  let i := μ.length - 1
  have hi : i < M a := by
    dsimp [i]
    rw [hsum] at hlen_le
    omega
  have hN : N μ = M a + 1 + i := by
    unfold N
    rw [Prop51.sum_map_add_one, hsum]
    dsimp [i]
    omega
  rw [hN]
  exact midUNormFast_neg_rows_146_149 a i ha_lo ha_hi hi

end Prop52
