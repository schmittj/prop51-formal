/- Axiom audit: run with `lake env lean scripts/AxiomsReport.lean`.
   CI greps the output: certificate theorems may use exactly
   [propext, Classical.choice, Quot.sound, Lean.ofReduceBool];
   everything else must avoid Lean.ofReduceBool and Lean.trustCompiler. -/
import Prop51

#print axioms Prop51.c_succ_succ
#print axioms Prop51.cList_getD_eq
#print axioms Prop51.unorm_corner_9_100
#print axioms Prop51.unorm_neg_9_60
#print axioms Prop51.bCoeff_neg_g_le_23
#print axioms Prop51.partitions_card_checks
#print axioms Prop51.coefficientNegativity_of_g_le_23
#print axioms Prop51.mem_partitions_iff
#print axioms Prop51.coefficientNegativity_of_g_le_23'
#print axioms Prop51.theta_expSeries
#print axioms Prop51.logDeriv_unique
#print axioms Prop51.Aseq_succ
#print axioms Prop51.Cseries_eq_expSeries_c
#print axioms Prop51.bridge_identity
#print axioms Prop51.bCoeff_eq_expCoeff
#print axioms Prop51.bSeries_official
#print axioms Prop51.c_pos
#print axioms Prop51.c_le_Aseq
#print axioms Prop51.expCoeff_mono
#print axioms Prop51.Cpow_mul_BSeriesQ
#print axioms Prop51.bCoeff_le_U
#print axioms Prop51.bCoeff_neg_of_unorm
#print axioms Prop51.coefficientNegativity_of_g_le_179

-- Layer B: dyadic interval arithmetic + interval certificate
#print axioms Prop51.shl_spec
#print axioms Prop51.DI.mem_mul
#print axioms Prop51.DI.mem_divNat
#print axioms Prop51.mem_cTab
#print axioms Prop51.mem_bTab
#print axioms Prop51.mem_qTab
#print axioms Prop51.checkPair_sound
#print axioms Prop51.checkRange_sound
#print axioms Prop51.checkRange_chunk1
#print axioms Prop51.unorm_neg_61_400
#print axioms Prop51.unorm_neg_9_400
#print axioms Prop51.coefficientNegativity_of_g_le_1199

-- Layer C groundwork: reciprocal binomials, d-normalization, compositions
#print axioms Prop51.sum_choose_recip_le
#print axioms Prop51.sum_choose_recip_inner_le
#print axioms Prop51.d_succ_succ
#print axioms Prop51.d_lb
#print axioms Prop51.d_ub
#print axioms Prop51.c_lb
#print axioms Prop51.c_ub
#print axioms Prop51.d_ratio_lb
#print axioms Prop51.Gcomp_le
#print axioms Prop51.sum_exp_le
#print axioms Prop51.one_add_inv_pow_le
#print axioms Prop51.factorial_lb
#print axioms Prop51.expCoeff_eq_sum_pow
#print axioms Prop51.abs_coeff_pow_le
#print axioms Prop51.abs_hpow_le
#print axioms Prop51.Eminus_split
#print axioms Prop51.Eminus_residual_le
#print axioms Prop51.DeltaRatTerm_two
#print axioms Prop51.DeltaRatTerm_succ
#print axioms Prop51.DeltaRatStepRatio_le_bound
#print axioms Prop51.DeltaRatTerm_succ_le
#print axioms Prop51.DeltaRatStepRatioBound_le_near
#print axioms Prop51.DeltaNearRatio_nonneg
#print axioms Prop51.DeltaNearRatio_lt_one_of_le_20
#print axioms Prop51.DeltaRatTerm_shifted_sum_le_geom
#print axioms Prop51.DeltaRatTerm_shifted_sum_le_inv_one_sub
#print axioms Prop51.DeltaRatTerm_Icc_sum_le_geom
#print axioms Prop51.DeltaRatTerm_Icc_sum_le_inv_one_sub
#print axioms Prop51.DeltaRatTerm_Icc_sum_le_near_geom
#print axioms Prop51.DeltaRatTerm_Icc_sum_le_near_inv_one_sub
#print axioms Prop51.DeltaRatTerm_Icc_sum_le_near_closed
#print axioms Prop51.DeltaRatNear_le_geomBound
#print axioms Prop51.DeltaRat_eq_near_add_far
#print axioms Prop51.DeltaRat_le_nearGeomBound_add_far
#print axioms Prop51.DeltaRatTerm_le_farTermBound
#print axioms Prop51.DeltaRatFar_le_termBound
#print axioms Prop51.DeltaRatFarTermBound_nonneg
#print axioms Prop51.DeltaRatFarTermBound_succ_le_half
#print axioms Prop51.DeltaRatFarTermBound_Icc_sum_le_two_first
#print axioms Prop51.DeltaRatFar_le_two_first
#print axioms Prop51.DeltaRatFarTermBound_le_inv_linear
#print axioms Prop51.DeltaRatFar_le_inv_start
#print axioms Prop51.DeltaRatFar_le_inv_m
#print axioms Prop51.Eminus_normalized_residual_le_DeltaRat
