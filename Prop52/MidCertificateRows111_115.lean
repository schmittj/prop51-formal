/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Prop52 mid-range certificate shard: rows 111--115

Native interval certificates for the printed Proposition 5.2 mid-range
checker, converted through `Prop52.MidInterval` into exact rational
`midUNormFast` negativity.
-/

import Prop52.MidInterval

namespace Prop52

theorem checkPrintedMidRowInterval_111 :
    checkPrintedMidRowInterval 111 = true := by
  native_decide

theorem checkPrintedMidRowInterval_112 :
    checkPrintedMidRowInterval 112 = true := by
  native_decide

theorem checkPrintedMidRowInterval_113 :
    checkPrintedMidRowInterval 113 = true := by
  native_decide

theorem checkPrintedMidRowInterval_114 :
    checkPrintedMidRowInterval 114 = true := by
  native_decide

theorem checkPrintedMidRowInterval_115 :
    checkPrintedMidRowInterval 115 = true := by
  native_decide

/-- Exact normalized negativity certified for rows `111 <= a <= 115`. -/
theorem midUNormFast_neg_rows_111_115 (a i : Nat)
    (ha_lo : 111 ≤ a) (ha_hi : a ≤ 115) (hi : i < M a) :
    midUNormFast a (M a + 1 + i) < 0 := by
  interval_cases a
  · exact midUNormFast_neg_of_rowInterval 111 i checkPrintedMidRowInterval_111 hi
  · exact midUNormFast_neg_of_rowInterval 112 i checkPrintedMidRowInterval_112 hi
  · exact midUNormFast_neg_of_rowInterval 113 i checkPrintedMidRowInterval_113 hi
  · exact midUNormFast_neg_of_rowInterval 114 i checkPrintedMidRowInterval_114 hi
  · exact midUNormFast_neg_of_rowInterval 115 i checkPrintedMidRowInterval_115 hi

theorem midUNormFast_neg_rows_111_115_of_partition (a : Nat) (μ : List Nat)
    (ha_lo : 111 ≤ a) (ha_hi : a ≤ 115)
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
  exact midUNormFast_neg_rows_111_115 a i ha_lo ha_hi hi

end Prop52
