/- Compact public axiom audit for the theorem facade.

Run with:

  lake env lean scripts/PublicAxiomsReport.lean

The final theorem is expected to use the standard axioms plus
`Lean.ofReduceBool` and `Lean.trustCompiler`, coming from the finite
`native_decide` certificates.
-/
import Prop51

#print axioms Prop51.Cseries_eq_expSeries_c
#print axioms Prop51.bSeries_official
#print axioms Prop51.bCoeff_le_U
#print axioms Prop51.coefficientNegativity
#print axioms Prop51.chenLarsonCoefficient_neg
#print axioms Prop51.chenLarsonCoefficient_ne_zero
#print axioms Prop51.bCoeff_neg_of_rectangle
#print axioms Prop52.correctedCoeff_eq_printedCoeff_add
#print axioms Prop52.correctedCoeffFast_eq
#print axioms Prop52.correctedCoeffMod_anchor
#print axioms Prop52.checkGeneratedModNat_9_prime1
#print axioms Prop52.checkGeneratedModNat_10_prime1
#print axioms Prop52.checkGeneratedModNat_11_prime1_chunks
#print axioms Prop52.finitePrime1_expListModNat_cast
#print axioms Prop52.finitePrime1_hCoeffModNat_cast
#print axioms Prop52.finitePrime1_kCoeffModNat_cast
#print axioms Prop52.finitePrime1_correctedCoeffModNat_cast
#print axioms Prop52.finitePrime1_correctedCoeffMod_ne_of_checkGeneratedChunks
#print axioms Prop52.finitePrime1_correctedCoeffMod_ne_of_checkGeneratedFirstParts
#print axioms Prop52.finitePrime1_correctedCoeffMod_ne_9_generated
#print axioms Prop52.finitePrime1_correctedCoeffMod_ne_10_generated
#print axioms Prop52.finitePrime1_correctedCoeffMod_ne_11_generated
#print axioms Prop52.ratCast_mul_of_good
#print axioms Prop52.ratCast_add_of_good
#print axioms Prop52.ratCast_sub_of_good
#print axioms Prop52.ratCast_list_sum_of_suffix_good
#print axioms Prop52.finitePrime1_ratCast_sPower_of_good
#print axioms Prop52.finitePrime1_ratCast_sPower_of_suffix_good
#print axioms Prop52.finitePrime1_ratCast_markedWeight_of_good
#print axioms Prop52.finitePrime1_ratCast_markedWeight_of_suffix_good
#print axioms Prop52.finitePrime1_ratCast_hCoeff_of_good
#print axioms Prop52.correctedCoeff_neg_large_of_printed
#print axioms Prop52.correctedCoeff_nonvanishing_of_finite_and_printed
#print axioms Prop52.correctedCoeff_ne_2_8
