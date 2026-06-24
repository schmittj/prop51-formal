/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Prop52 mid-range certificate shard: rows 141--145

Native interval certificates for the printed Proposition 5.2 mid-range
checker, converted through `Prop52.MidInterval` into exact rational
`midUNormFast` negativity.
-/

import Prop52.MidInterval

namespace Prop52

theorem checkPrintedMidRowInterval_141 :
    checkPrintedMidRowInterval 141 = true := by
  native_decide

theorem checkPrintedMidRowInterval_142 :
    checkPrintedMidRowInterval 142 = true := by
  native_decide

theorem checkPrintedMidRowInterval_143 :
    checkPrintedMidRowInterval 143 = true := by
  native_decide

theorem checkPrintedMidRowInterval_144 :
    checkPrintedMidRowInterval 144 = true := by
  native_decide

theorem checkPrintedMidRowInterval_145 :
    checkPrintedMidRowInterval 145 = true := by
  native_decide

/-- Exact normalized negativity certified for rows `141 <= a <= 145`. -/
theorem midUNormFast_neg_rows_141_145 (a i : Nat)
    (ha_lo : 141 ≤ a) (ha_hi : a ≤ 145) (hi : i < M a) :
    midUNormFast a (M a + 1 + i) < 0 := by
  interval_cases a
  · exact midUNormFast_neg_of_rowInterval 141 i checkPrintedMidRowInterval_141 hi
  · exact midUNormFast_neg_of_rowInterval 142 i checkPrintedMidRowInterval_142 hi
  · exact midUNormFast_neg_of_rowInterval 143 i checkPrintedMidRowInterval_143 hi
  · exact midUNormFast_neg_of_rowInterval 144 i checkPrintedMidRowInterval_144 hi
  · exact midUNormFast_neg_of_rowInterval 145 i checkPrintedMidRowInterval_145 hi

theorem midUNormFast_neg_rows_141_145_of_partition (a : Nat) (μ : List Nat)
    (ha_lo : 141 ≤ a) (ha_hi : a ≤ 145)
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
  exact midUNormFast_neg_rows_141_145 a i ha_lo ha_hi hi

end Prop52
