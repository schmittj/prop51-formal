/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Prop52 mid-range certificate shard: rows 116--120

Native interval certificates for the printed Proposition 5.2 mid-range
checker, converted through `Prop52.MidInterval` into exact rational
`midUNormFast` negativity.
-/

import Prop52.MidInterval

namespace Prop52

theorem checkPrintedMidRowInterval_116 :
    checkPrintedMidRowInterval 116 = true := by
  native_decide

theorem checkPrintedMidRowInterval_117 :
    checkPrintedMidRowInterval 117 = true := by
  native_decide

theorem checkPrintedMidRowInterval_118 :
    checkPrintedMidRowInterval 118 = true := by
  native_decide

theorem checkPrintedMidRowInterval_119 :
    checkPrintedMidRowInterval 119 = true := by
  native_decide

theorem checkPrintedMidRowInterval_120 :
    checkPrintedMidRowInterval 120 = true := by
  native_decide

/-- Exact normalized negativity certified for rows `116 <= a <= 120`. -/
theorem midUNormFast_neg_rows_116_120 (a i : Nat)
    (ha_lo : 116 ≤ a) (ha_hi : a ≤ 120) (hi : i < M a) :
    midUNormFast a (M a + 1 + i) < 0 := by
  interval_cases a
  · exact midUNormFast_neg_of_rowInterval 116 i checkPrintedMidRowInterval_116 hi
  · exact midUNormFast_neg_of_rowInterval 117 i checkPrintedMidRowInterval_117 hi
  · exact midUNormFast_neg_of_rowInterval 118 i checkPrintedMidRowInterval_118 hi
  · exact midUNormFast_neg_of_rowInterval 119 i checkPrintedMidRowInterval_119 hi
  · exact midUNormFast_neg_of_rowInterval 120 i checkPrintedMidRowInterval_120 hi

theorem midUNormFast_neg_rows_116_120_of_partition (a : Nat) (μ : List Nat)
    (ha_lo : 116 ≤ a) (ha_hi : a ≤ 120)
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
  exact midUNormFast_neg_rows_116_120 a i ha_lo ha_hi hi

end Prop52
