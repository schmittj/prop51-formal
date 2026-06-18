import Prop51.OpenGoals

namespace Prop51

/-!
Canonical completion entry point.

The theorem below intentionally exposes only the three live assumptions from
`OpenGoals`.  The final step is to replace these parameters by concrete
certificates and leave `coefficientNegativity : CoefficientNegativity`.
-/

theorem coefficientNegativity
    (hbounded : BoundedPositiveCertificate)
    (hproduct : LargeTailProductCertificate)
    (hsolo : LargeTailSoloCertificate) :
    CoefficientNegativity :=
  completion_of_three_inputs hbounded hproduct hsolo

end Prop51
