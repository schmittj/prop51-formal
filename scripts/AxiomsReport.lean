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
