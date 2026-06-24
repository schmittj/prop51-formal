/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Prop52 mid-range certificate shard: rows 131--135

Native interval certificates for the printed Proposition 5.2 mid-range
checker, converted through `Prop52.MidInterval` into exact rational
`midUNormFast` negativity.
-/

import Prop52.MidInterval

namespace Prop52

theorem checkPrintedMidRowInterval_131 :
    checkPrintedMidRowInterval 131 = true := by
  native_decide

theorem checkPrintedMidRowInterval_132 :
    checkPrintedMidRowInterval 132 = true := by
  native_decide

theorem checkPrintedMidRowInterval_133 :
    checkPrintedMidRowInterval 133 = true := by
  native_decide

theorem checkPrintedMidRowInterval_134 :
    checkPrintedMidRowInterval 134 = true := by
  native_decide

theorem checkPrintedMidRowInterval_135 :
    checkPrintedMidRowInterval 135 = true := by
  native_decide

/-- Exact normalized negativity certified for rows `131 <= a <= 135`. -/
theorem midUNormFast_neg_rows_131_135 (a i : Nat)
    (ha_lo : 131 ≤ a) (ha_hi : a ≤ 135) (hi : i < M a) :
    midUNormFast a (M a + 1 + i) < 0 := by
  interval_cases a
  · exact midUNormFast_neg_of_rowInterval 131 i checkPrintedMidRowInterval_131 hi
  · exact midUNormFast_neg_of_rowInterval 132 i checkPrintedMidRowInterval_132 hi
  · exact midUNormFast_neg_of_rowInterval 133 i checkPrintedMidRowInterval_133 hi
  · exact midUNormFast_neg_of_rowInterval 134 i checkPrintedMidRowInterval_134 hi
  · exact midUNormFast_neg_of_rowInterval 135 i checkPrintedMidRowInterval_135 hi

theorem midUNormFast_neg_rows_131_135_of_partition (a : Nat) (μ : List Nat)
    (ha_lo : 131 ≤ a) (ha_hi : a ≤ 135)
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
  exact midUNormFast_neg_rows_131_135 a i ha_lo ha_hi hi

end Prop52
