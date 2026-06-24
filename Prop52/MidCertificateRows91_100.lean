/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Prop52 mid-range certificate shard: rows 91--100

Native interval certificates for the printed Proposition 5.2 mid-range
checker, converted through `Prop52.MidInterval` into exact rational
`midUNormFast` negativity.
-/

import Prop52.MidInterval

namespace Prop52

theorem checkPrintedMidRowInterval_91 :
    checkPrintedMidRowInterval 91 = true := by
  native_decide

theorem checkPrintedMidRowInterval_92 :
    checkPrintedMidRowInterval 92 = true := by
  native_decide

theorem checkPrintedMidRowInterval_93 :
    checkPrintedMidRowInterval 93 = true := by
  native_decide

theorem checkPrintedMidRowInterval_94 :
    checkPrintedMidRowInterval 94 = true := by
  native_decide

theorem checkPrintedMidRowInterval_95 :
    checkPrintedMidRowInterval 95 = true := by
  native_decide

theorem checkPrintedMidRowInterval_96 :
    checkPrintedMidRowInterval 96 = true := by
  native_decide

theorem checkPrintedMidRowInterval_97 :
    checkPrintedMidRowInterval 97 = true := by
  native_decide

theorem checkPrintedMidRowInterval_98 :
    checkPrintedMidRowInterval 98 = true := by
  native_decide

theorem checkPrintedMidRowInterval_99 :
    checkPrintedMidRowInterval 99 = true := by
  native_decide

theorem checkPrintedMidRowInterval_100 :
    checkPrintedMidRowInterval 100 = true := by
  native_decide

/-- Exact normalized negativity certified for rows `91 <= a <= 100`. -/
theorem midUNormFast_neg_rows_91_100 (a i : Nat)
    (ha_lo : 91 ≤ a) (ha_hi : a ≤ 100) (hi : i < M a) :
    midUNormFast a (M a + 1 + i) < 0 := by
  interval_cases a
  · exact midUNormFast_neg_of_rowInterval 91 i checkPrintedMidRowInterval_91 hi
  · exact midUNormFast_neg_of_rowInterval 92 i checkPrintedMidRowInterval_92 hi
  · exact midUNormFast_neg_of_rowInterval 93 i checkPrintedMidRowInterval_93 hi
  · exact midUNormFast_neg_of_rowInterval 94 i checkPrintedMidRowInterval_94 hi
  · exact midUNormFast_neg_of_rowInterval 95 i checkPrintedMidRowInterval_95 hi
  · exact midUNormFast_neg_of_rowInterval 96 i checkPrintedMidRowInterval_96 hi
  · exact midUNormFast_neg_of_rowInterval 97 i checkPrintedMidRowInterval_97 hi
  · exact midUNormFast_neg_of_rowInterval 98 i checkPrintedMidRowInterval_98 hi
  · exact midUNormFast_neg_of_rowInterval 99 i checkPrintedMidRowInterval_99 hi
  · exact midUNormFast_neg_of_rowInterval 100 i checkPrintedMidRowInterval_100 hi

theorem midUNormFast_neg_rows_91_100_of_partition (a : Nat) (μ : List Nat)
    (ha_lo : 91 ≤ a) (ha_hi : a ≤ 100)
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
  exact midUNormFast_neg_rows_91_100 a i ha_lo ha_hi hi

end Prop52
