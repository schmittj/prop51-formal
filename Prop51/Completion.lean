import Prop51.OpenGoals

namespace Prop51

/-!
Canonical completion entry point.

The theorem below intentionally exposes only the remaining live assumptions
from `OpenGoals`.  The solo large-tail certificate is now supplied by
`largeTailSoloCertificate`; the final step is to replace the bounded and
product parameters by concrete certificates and leave
`coefficientNegativity : CoefficientNegativity`.
-/

theorem coefficientNegativity
    (hbounded : BoundedPositiveCertificate)
    (hproduct : LargeTailProductCertificate) :
    CoefficientNegativity :=
  completion_of_three_inputs hbounded hproduct largeTailSoloCertificate

end Prop51
