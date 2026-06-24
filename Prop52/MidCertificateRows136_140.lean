/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Prop52 mid-range certificate shard: rows 136--140

Native interval certificates for the printed Proposition 5.2 mid-range
checker, converted through `Prop52.MidInterval` into exact rational
`midUNormFast` negativity.
-/

import Prop52.MidInterval

namespace Prop52

theorem checkPrintedMidRowInterval_136 :
    checkPrintedMidRowInterval 136 = true := by
  native_decide

theorem checkPrintedMidRowInterval_137 :
    checkPrintedMidRowInterval 137 = true := by
  native_decide

theorem checkPrintedMidRowInterval_138 :
    checkPrintedMidRowInterval 138 = true := by
  native_decide

theorem checkPrintedMidRowInterval_139 :
    checkPrintedMidRowInterval 139 = true := by
  native_decide

theorem checkPrintedMidRowInterval_140 :
    checkPrintedMidRowInterval 140 = true := by
  native_decide

/-- Exact normalized negativity certified for rows `136 <= a <= 140`. -/
theorem midUNormFast_neg_rows_136_140 (a i : Nat)
    (ha_lo : 136 ≤ a) (ha_hi : a ≤ 140) (hi : i < M a) :
    midUNormFast a (M a + 1 + i) < 0 := by
  interval_cases a
  · exact midUNormFast_neg_of_rowInterval 136 i checkPrintedMidRowInterval_136 hi
  · exact midUNormFast_neg_of_rowInterval 137 i checkPrintedMidRowInterval_137 hi
  · exact midUNormFast_neg_of_rowInterval 138 i checkPrintedMidRowInterval_138 hi
  · exact midUNormFast_neg_of_rowInterval 139 i checkPrintedMidRowInterval_139 hi
  · exact midUNormFast_neg_of_rowInterval 140 i checkPrintedMidRowInterval_140 hi

theorem midUNormFast_neg_rows_136_140_of_partition (a : Nat) (μ : List Nat)
    (ha_lo : 136 ≤ a) (ha_hi : a ≤ 140)
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
  exact midUNormFast_neg_rows_136_140 a i ha_lo ha_hi hi

end Prop52
