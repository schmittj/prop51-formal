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
#print axioms Prop52.correctedCoeff_neg_large_of_printed
