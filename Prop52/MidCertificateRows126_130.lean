/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Prop52 mid-range certificate shard: rows 126--130

Native interval certificates for the printed Proposition 5.2 mid-range
checker, converted through `Prop52.MidInterval` into exact rational
`midUNormFast` negativity.
-/

import Prop52.MidInterval

namespace Prop52

theorem checkPrintedMidRowInterval_126 :
    checkPrintedMidRowInterval 126 = true := by
  native_decide

theorem checkPrintedMidRowInterval_127 :
    checkPrintedMidRowInterval 127 = true := by
  native_decide

theorem checkPrintedMidRowInterval_128 :
    checkPrintedMidRowInterval 128 = true := by
  native_decide

theorem checkPrintedMidRowInterval_129 :
    checkPrintedMidRowInterval 129 = true := by
  native_decide

theorem checkPrintedMidRowInterval_130 :
    checkPrintedMidRowInterval 130 = true := by
  native_decide

/-- Exact normalized negativity certified for rows `126 <= a <= 130`. -/
theorem midUNormFast_neg_rows_126_130 (a i : Nat)
    (ha_lo : 126 ≤ a) (ha_hi : a ≤ 130) (hi : i < M a) :
    midUNormFast a (M a + 1 + i) < 0 := by
  interval_cases a
  · exact midUNormFast_neg_of_rowInterval 126 i checkPrintedMidRowInterval_126 hi
  · exact midUNormFast_neg_of_rowInterval 127 i checkPrintedMidRowInterval_127 hi
  · exact midUNormFast_neg_of_rowInterval 128 i checkPrintedMidRowInterval_128 hi
  · exact midUNormFast_neg_of_rowInterval 129 i checkPrintedMidRowInterval_129 hi
  · exact midUNormFast_neg_of_rowInterval 130 i checkPrintedMidRowInterval_130 hi

theorem midUNormFast_neg_rows_126_130_of_partition (a : Nat) (μ : List Nat)
    (ha_lo : 126 ≤ a) (ha_hi : a ≤ 130)
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
  exact midUNormFast_neg_rows_126_130 a i ha_lo ha_hi hi

end Prop52
