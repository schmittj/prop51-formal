/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Prop52 mid-range certificate shard: rows 81--90

Native interval certificates for the printed Proposition 5.2 mid-range
checker, converted through `Prop52.MidInterval` into exact rational
`midUNormFast` negativity.
-/

import Prop52.MidInterval

namespace Prop52

theorem checkPrintedMidRowInterval_81 :
    checkPrintedMidRowInterval 81 = true := by
  native_decide

theorem checkPrintedMidRowInterval_82 :
    checkPrintedMidRowInterval 82 = true := by
  native_decide

theorem checkPrintedMidRowInterval_83 :
    checkPrintedMidRowInterval 83 = true := by
  native_decide

theorem checkPrintedMidRowInterval_84 :
    checkPrintedMidRowInterval 84 = true := by
  native_decide

theorem checkPrintedMidRowInterval_85 :
    checkPrintedMidRowInterval 85 = true := by
  native_decide

theorem checkPrintedMidRowInterval_86 :
    checkPrintedMidRowInterval 86 = true := by
  native_decide

theorem checkPrintedMidRowInterval_87 :
    checkPrintedMidRowInterval 87 = true := by
  native_decide

theorem checkPrintedMidRowInterval_88 :
    checkPrintedMidRowInterval 88 = true := by
  native_decide

theorem checkPrintedMidRowInterval_89 :
    checkPrintedMidRowInterval 89 = true := by
  native_decide

theorem checkPrintedMidRowInterval_90 :
    checkPrintedMidRowInterval 90 = true := by
  native_decide

/-- Exact normalized negativity certified for rows `81 <= a <= 90`. -/
theorem midUNormFast_neg_rows_81_90 (a i : Nat)
    (ha_lo : 81 ≤ a) (ha_hi : a ≤ 90) (hi : i < M a) :
    midUNormFast a (M a + 1 + i) < 0 := by
  interval_cases a
  · exact midUNormFast_neg_of_rowInterval 81 i checkPrintedMidRowInterval_81 hi
  · exact midUNormFast_neg_of_rowInterval 82 i checkPrintedMidRowInterval_82 hi
  · exact midUNormFast_neg_of_rowInterval 83 i checkPrintedMidRowInterval_83 hi
  · exact midUNormFast_neg_of_rowInterval 84 i checkPrintedMidRowInterval_84 hi
  · exact midUNormFast_neg_of_rowInterval 85 i checkPrintedMidRowInterval_85 hi
  · exact midUNormFast_neg_of_rowInterval 86 i checkPrintedMidRowInterval_86 hi
  · exact midUNormFast_neg_of_rowInterval 87 i checkPrintedMidRowInterval_87 hi
  · exact midUNormFast_neg_of_rowInterval 88 i checkPrintedMidRowInterval_88 hi
  · exact midUNormFast_neg_of_rowInterval 89 i checkPrintedMidRowInterval_89 hi
  · exact midUNormFast_neg_of_rowInterval 90 i checkPrintedMidRowInterval_90 hi

theorem midUNormFast_neg_rows_81_90_of_partition (a : Nat) (μ : List Nat)
    (ha_lo : 81 ≤ a) (ha_hi : a ≤ 90)
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
  exact midUNormFast_neg_rows_81_90 a i ha_lo ha_hi hi

end Prop52
