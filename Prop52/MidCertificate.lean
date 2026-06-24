/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Native certificate shards for the Prop52 mid-range interval checker

This file records native-evaluated interval certificates for the printed
Proposition 5.2 mid-range checker.  The soundness bridge is in
`Prop52.MidInterval`; each Boolean theorem below is immediately converted to
an exact rational negativity statement for `midUNormFast`.

The first shard covers `14 <= a <= 58`.  Later shards will extend the same
pattern through `a = 149`.
-/

import Prop52.MidInterval

namespace Prop52

theorem checkPrintedMidRowsInterval_14_10 :
    checkPrintedMidRowsInterval 14 10 = true := by
  native_decide

theorem checkPrintedMidRowsInterval_24_10 :
    checkPrintedMidRowsInterval 24 10 = true := by
  native_decide

theorem checkPrintedMidRowsInterval_34_10 :
    checkPrintedMidRowsInterval 34 10 = true := by
  native_decide

theorem checkPrintedMidRowsInterval_44_5 :
    checkPrintedMidRowsInterval 44 5 = true := by
  native_decide

theorem checkPrintedMidRowsInterval_49_5 :
    checkPrintedMidRowsInterval 49 5 = true := by
  native_decide

theorem checkPrintedMidRowsInterval_54_5 :
    checkPrintedMidRowsInterval 54 5 = true := by
  native_decide

/-- Exact normalized negativity certified for the first mid-range shard. -/
theorem midUNormFast_neg_rows_14_58 (a i : Nat)
    (ha_lo : 14 ≤ a) (ha_hi : a ≤ 58) (hi : i < M a) :
    midUNormFast a (M a + 1 + i) < 0 := by
  by_cases h24 : a < 24
  · exact midUNormFast_neg_of_rowsInterval 14 10 a i
      checkPrintedMidRowsInterval_14_10 (by omega) h24 hi
  · by_cases h34 : a < 34
    · exact midUNormFast_neg_of_rowsInterval 24 10 a i
        checkPrintedMidRowsInterval_24_10 (by omega) h34 hi
    · by_cases h44 : a < 44
      · exact midUNormFast_neg_of_rowsInterval 34 10 a i
          checkPrintedMidRowsInterval_34_10 (by omega) h44 hi
      · by_cases h49 : a < 49
        · exact midUNormFast_neg_of_rowsInterval 44 5 a i
            checkPrintedMidRowsInterval_44_5 (by omega) h49 hi
        · by_cases h54 : a < 54
          · exact midUNormFast_neg_of_rowsInterval 49 5 a i
              checkPrintedMidRowsInterval_49_5 (by omega) h54 hi
          · exact midUNormFast_neg_of_rowsInterval 54 5 a i
              checkPrintedMidRowsInterval_54_5 (by omega) (by omega) hi

theorem checkPrintedMidRowsInterval_59_3 :
    checkPrintedMidRowsInterval 59 3 = true := by
  native_decide

theorem checkPrintedMidRowsInterval_62_3 :
    checkPrintedMidRowsInterval 62 3 = true := by
  native_decide

theorem checkPrintedMidRowsInterval_65_3 :
    checkPrintedMidRowsInterval 65 3 = true := by
  native_decide

theorem checkPrintedMidRowsInterval_68_2 :
    checkPrintedMidRowsInterval 68 2 = true := by
  native_decide

theorem checkPrintedMidRowsInterval_70_2 :
    checkPrintedMidRowsInterval 70 2 = true := by
  native_decide

theorem checkPrintedMidRowsInterval_72_2 :
    checkPrintedMidRowsInterval 72 2 = true := by
  native_decide

/-- Exact normalized negativity certified for the second mid-range shard. -/
theorem midUNormFast_neg_rows_59_73 (a i : Nat)
    (ha_lo : 59 ≤ a) (ha_hi : a ≤ 73) (hi : i < M a) :
    midUNormFast a (M a + 1 + i) < 0 := by
  by_cases h62 : a < 62
  · exact midUNormFast_neg_of_rowsInterval 59 3 a i
      checkPrintedMidRowsInterval_59_3 (by omega) h62 hi
  · by_cases h65 : a < 65
    · exact midUNormFast_neg_of_rowsInterval 62 3 a i
        checkPrintedMidRowsInterval_62_3 (by omega) h65 hi
    · by_cases h68 : a < 68
      · exact midUNormFast_neg_of_rowsInterval 65 3 a i
          checkPrintedMidRowsInterval_65_3 (by omega) h68 hi
      · by_cases h70 : a < 70
        · exact midUNormFast_neg_of_rowsInterval 68 2 a i
            checkPrintedMidRowsInterval_68_2 (by omega) h70 hi
        · by_cases h72 : a < 72
          · exact midUNormFast_neg_of_rowsInterval 70 2 a i
              checkPrintedMidRowsInterval_70_2 (by omega) h72 hi
          · exact midUNormFast_neg_of_rowsInterval 72 2 a i
              checkPrintedMidRowsInterval_72_2 (by omega) (by omega) hi

theorem midUNormFast_neg_rows_14_73 (a i : Nat)
    (ha_lo : 14 ≤ a) (ha_hi : a ≤ 73) (hi : i < M a) :
    midUNormFast a (M a + 1 + i) < 0 := by
  by_cases h58 : a ≤ 58
  · exact midUNormFast_neg_rows_14_58 a i ha_lo h58 hi
  · exact midUNormFast_neg_rows_59_73 a i (by omega) ha_hi hi

theorem checkPrintedMidRowInterval_74 :
    checkPrintedMidRowInterval 74 = true := by
  native_decide

theorem checkPrintedMidRowInterval_75 :
    checkPrintedMidRowInterval 75 = true := by
  native_decide

theorem checkPrintedMidRowInterval_76 :
    checkPrintedMidRowInterval 76 = true := by
  native_decide

theorem checkPrintedMidRowInterval_77 :
    checkPrintedMidRowInterval 77 = true := by
  native_decide

theorem checkPrintedMidRowInterval_78 :
    checkPrintedMidRowInterval 78 = true := by
  native_decide

theorem checkPrintedMidRowInterval_79 :
    checkPrintedMidRowInterval 79 = true := by
  native_decide

theorem checkPrintedMidRowInterval_80 :
    checkPrintedMidRowInterval 80 = true := by
  native_decide

/-- Exact normalized negativity certified for the third mid-range shard. -/
theorem midUNormFast_neg_rows_74_80 (a i : Nat)
    (ha_lo : 74 ≤ a) (ha_hi : a ≤ 80) (hi : i < M a) :
    midUNormFast a (M a + 1 + i) < 0 := by
  interval_cases a
  · exact midUNormFast_neg_of_rowInterval 74 i checkPrintedMidRowInterval_74 hi
  · exact midUNormFast_neg_of_rowInterval 75 i checkPrintedMidRowInterval_75 hi
  · exact midUNormFast_neg_of_rowInterval 76 i checkPrintedMidRowInterval_76 hi
  · exact midUNormFast_neg_of_rowInterval 77 i checkPrintedMidRowInterval_77 hi
  · exact midUNormFast_neg_of_rowInterval 78 i checkPrintedMidRowInterval_78 hi
  · exact midUNormFast_neg_of_rowInterval 79 i checkPrintedMidRowInterval_79 hi
  · exact midUNormFast_neg_of_rowInterval 80 i checkPrintedMidRowInterval_80 hi

theorem midUNormFast_neg_rows_14_80 (a i : Nat)
    (ha_lo : 14 ≤ a) (ha_hi : a ≤ 80) (hi : i < M a) :
    midUNormFast a (M a + 1 + i) < 0 := by
  by_cases h73 : a ≤ 73
  · exact midUNormFast_neg_rows_14_73 a i ha_lo h73 hi
  · exact midUNormFast_neg_rows_74_80 a i (by omega) ha_hi hi

end Prop52
