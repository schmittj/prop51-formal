/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Combined Prop52 mid-range certificate

This file gathers the sharded native interval certificates for the printed
Proposition 5.2 mid-range checker and exposes a single theorem over
`14 <= a <= 149`.
-/

import Prop52.MidCertificate
import Prop52.MidCertificateRows81_90
import Prop52.MidCertificateRows91_100
import Prop52.MidCertificateRows101_110
import Prop52.MidCertificateRows111_115
import Prop52.MidCertificateRows116_120
import Prop52.MidCertificateRows121_125
import Prop52.MidCertificateRows126_130
import Prop52.MidCertificateRows131_135
import Prop52.MidCertificateRows136_140
import Prop52.MidCertificateRows141_145
import Prop52.MidCertificateRows146_149

namespace Prop52

/-- Exact normalized negativity certified for rows `14 <= a <= 149`. -/
theorem midUNormFast_neg_rows_14_149 (a i : Nat)
    (ha_lo : 14 ≤ a) (ha_hi : a ≤ 149) (hi : i < M a) :
    midUNormFast a (M a + 1 + i) < 0 := by
  by_cases h80 : a ≤ 80
  · exact midUNormFast_neg_rows_14_80 a i ha_lo h80 hi
  by_cases h90 : a ≤ 90
  · exact midUNormFast_neg_rows_81_90 a i (by omega) h90 hi
  by_cases h100 : a ≤ 100
  · exact midUNormFast_neg_rows_91_100 a i (by omega) h100 hi
  by_cases h110 : a ≤ 110
  · exact midUNormFast_neg_rows_101_110 a i (by omega) h110 hi
  by_cases h115 : a ≤ 115
  · exact midUNormFast_neg_rows_111_115 a i (by omega) h115 hi
  by_cases h120 : a ≤ 120
  · exact midUNormFast_neg_rows_116_120 a i (by omega) h120 hi
  by_cases h125 : a ≤ 125
  · exact midUNormFast_neg_rows_121_125 a i (by omega) h125 hi
  by_cases h130 : a ≤ 130
  · exact midUNormFast_neg_rows_126_130 a i (by omega) h130 hi
  by_cases h135 : a ≤ 135
  · exact midUNormFast_neg_rows_131_135 a i (by omega) h135 hi
  by_cases h140 : a ≤ 140
  · exact midUNormFast_neg_rows_136_140 a i (by omega) h140 hi
  by_cases h145 : a ≤ 145
  · exact midUNormFast_neg_rows_141_145 a i (by omega) h145 hi
  exact midUNormFast_neg_rows_146_149 a i (by omega) ha_hi hi

theorem midUNormFast_neg_rows_14_149_of_partition (a : Nat) (μ : List Nat)
    (ha_lo : 14 ≤ a) (ha_hi : a ≤ 149)
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    midUNormFast a (N μ) < 0 := by
  by_cases h80 : a ≤ 80
  · exact midUNormFast_neg_rows_14_80_of_partition a μ ha_lo h80 hμ
  by_cases h90 : a ≤ 90
  · exact midUNormFast_neg_rows_81_90_of_partition a μ (by omega) h90 hμ
  by_cases h100 : a ≤ 100
  · exact midUNormFast_neg_rows_91_100_of_partition a μ (by omega) h100 hμ
  by_cases h110 : a ≤ 110
  · exact midUNormFast_neg_rows_101_110_of_partition a μ (by omega) h110 hμ
  by_cases h115 : a ≤ 115
  · exact midUNormFast_neg_rows_111_115_of_partition a μ (by omega) h115 hμ
  by_cases h120 : a ≤ 120
  · exact midUNormFast_neg_rows_116_120_of_partition a μ (by omega) h120 hμ
  by_cases h125 : a ≤ 125
  · exact midUNormFast_neg_rows_121_125_of_partition a μ (by omega) h125 hμ
  by_cases h130 : a ≤ 130
  · exact midUNormFast_neg_rows_126_130_of_partition a μ (by omega) h130 hμ
  by_cases h135 : a ≤ 135
  · exact midUNormFast_neg_rows_131_135_of_partition a μ (by omega) h135 hμ
  by_cases h140 : a ≤ 140
  · exact midUNormFast_neg_rows_136_140_of_partition a μ (by omega) h140 hμ
  by_cases h145 : a ≤ 145
  · exact midUNormFast_neg_rows_141_145_of_partition a μ (by omega) h145 hμ
  exact midUNormFast_neg_rows_146_149_of_partition a μ (by omega) ha_hi hμ

end Prop52
