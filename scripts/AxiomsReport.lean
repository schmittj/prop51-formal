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
