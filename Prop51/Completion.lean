import Prop51.OpenGoals

namespace Prop51

/-!
Canonical completion entry point.

`OpenGoals` still exposes compatibility constructors for older certificate
surfaces, but the direct-saddle route now supplies the bounded, product, and
solo inputs concretely.  The theorem `coefficientNegativity` below is the
closed project target.
-/

theorem coefficientNegativity_of_bounded_product
    (hbounded : BoundedPositiveCertificate)
    (hproduct : LargeTailProductCertificate) :
    CoefficientNegativity :=
  completion_of_three_inputs hbounded hproduct largeTailSoloCertificate

theorem coefficientNegativity : CoefficientNegativity :=
  completion_of_directSaddle_closed

end Prop51
