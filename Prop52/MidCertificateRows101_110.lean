/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Prop52 mid-range certificate shard: rows 101--110

Native interval certificates for the printed Proposition 5.2 mid-range
checker, converted through `Prop52.MidInterval` into exact rational
`midUNormFast` negativity.
-/

import Prop52.MidInterval

namespace Prop52

theorem checkPrintedMidRowInterval_101 :
    checkPrintedMidRowInterval 101 = true := by
  native_decide

theorem checkPrintedMidRowInterval_102 :
    checkPrintedMidRowInterval 102 = true := by
  native_decide

theorem checkPrintedMidRowInterval_103 :
    checkPrintedMidRowInterval 103 = true := by
  native_decide

theorem checkPrintedMidRowInterval_104 :
    checkPrintedMidRowInterval 104 = true := by
  native_decide

theorem checkPrintedMidRowInterval_105 :
    checkPrintedMidRowInterval 105 = true := by
  native_decide

theorem checkPrintedMidRowInterval_106 :
    checkPrintedMidRowInterval 106 = true := by
  native_decide

theorem checkPrintedMidRowInterval_107 :
    checkPrintedMidRowInterval 107 = true := by
  native_decide

theorem checkPrintedMidRowInterval_108 :
    checkPrintedMidRowInterval 108 = true := by
  native_decide

theorem checkPrintedMidRowInterval_109 :
    checkPrintedMidRowInterval 109 = true := by
  native_decide

theorem checkPrintedMidRowInterval_110 :
    checkPrintedMidRowInterval 110 = true := by
  native_decide

/-- Exact normalized negativity certified for rows `101 <= a <= 110`. -/
theorem midUNormFast_neg_rows_101_110 (a i : Nat)
    (ha_lo : 101 ≤ a) (ha_hi : a ≤ 110) (hi : i < M a) :
    midUNormFast a (M a + 1 + i) < 0 := by
  interval_cases a
  · exact midUNormFast_neg_of_rowInterval 101 i checkPrintedMidRowInterval_101 hi
  · exact midUNormFast_neg_of_rowInterval 102 i checkPrintedMidRowInterval_102 hi
  · exact midUNormFast_neg_of_rowInterval 103 i checkPrintedMidRowInterval_103 hi
  · exact midUNormFast_neg_of_rowInterval 104 i checkPrintedMidRowInterval_104 hi
  · exact midUNormFast_neg_of_rowInterval 105 i checkPrintedMidRowInterval_105 hi
  · exact midUNormFast_neg_of_rowInterval 106 i checkPrintedMidRowInterval_106 hi
  · exact midUNormFast_neg_of_rowInterval 107 i checkPrintedMidRowInterval_107 hi
  · exact midUNormFast_neg_of_rowInterval 108 i checkPrintedMidRowInterval_108 hi
  · exact midUNormFast_neg_of_rowInterval 109 i checkPrintedMidRowInterval_109 hi
  · exact midUNormFast_neg_of_rowInterval 110 i checkPrintedMidRowInterval_110 hi

theorem midUNormFast_neg_rows_101_110_of_partition (a : Nat) (μ : List Nat)
    (ha_lo : 101 ≤ a) (ha_hi : a ≤ 110)
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
  exact midUNormFast_neg_rows_101_110 a i ha_lo ha_hi hi

end Prop52
