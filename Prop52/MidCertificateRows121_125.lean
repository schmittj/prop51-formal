/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Prop52 mid-range certificate shard: rows 121--125

Native interval certificates for the printed Proposition 5.2 mid-range
checker, converted through `Prop52.MidInterval` into exact rational
`midUNormFast` negativity.
-/

import Prop52.MidInterval

namespace Prop52

theorem checkPrintedMidRowInterval_121 :
    checkPrintedMidRowInterval 121 = true := by
  native_decide

theorem checkPrintedMidRowInterval_122 :
    checkPrintedMidRowInterval 122 = true := by
  native_decide

theorem checkPrintedMidRowInterval_123 :
    checkPrintedMidRowInterval 123 = true := by
  native_decide

theorem checkPrintedMidRowInterval_124 :
    checkPrintedMidRowInterval 124 = true := by
  native_decide

theorem checkPrintedMidRowInterval_125 :
    checkPrintedMidRowInterval 125 = true := by
  native_decide

/-- Exact normalized negativity certified for rows `121 <= a <= 125`. -/
theorem midUNormFast_neg_rows_121_125 (a i : Nat)
    (ha_lo : 121 ≤ a) (ha_hi : a ≤ 125) (hi : i < M a) :
    midUNormFast a (M a + 1 + i) < 0 := by
  interval_cases a
  · exact midUNormFast_neg_of_rowInterval 121 i checkPrintedMidRowInterval_121 hi
  · exact midUNormFast_neg_of_rowInterval 122 i checkPrintedMidRowInterval_122 hi
  · exact midUNormFast_neg_of_rowInterval 123 i checkPrintedMidRowInterval_123 hi
  · exact midUNormFast_neg_of_rowInterval 124 i checkPrintedMidRowInterval_124 hi
  · exact midUNormFast_neg_of_rowInterval 125 i checkPrintedMidRowInterval_125 hi

theorem midUNormFast_neg_rows_121_125_of_partition (a : Nat) (μ : List Nat)
    (ha_lo : 121 ≤ a) (ha_hi : a ≤ 125)
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
  exact midUNormFast_neg_rows_121_125 a i ha_lo ha_hi hi

end Prop52
