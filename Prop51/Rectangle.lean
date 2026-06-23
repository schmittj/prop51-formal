/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Rectangle form of the Proposition 5.1 quotient negativity

Corrected Proposition 5.2 uses the Proposition 5.1 quotient sign theorem in a
slightly different bookkeeping form: the exponent `N = sum_i (m_i+1)` is
specified directly by the rectangle

  `6*a - 7 <= N <= 12*a - 8`

rather than through the two congruence classes of the genus parameter.  This
file exposes that rectangle-facing theorem from the existing certificates.
-/

import Prop51.Completion

namespace Prop51

/-- The closed direct-saddle construction, exposed at the `Unorm` level. -/
theorem unorm_neg_401_of_closedDirectSaddle :
    ∀ a, 401 ≤ a → ∀ N,
      6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 := by
  let hbounded : BoundedPositiveCertificate :=
    BoundedPositiveCertificate.ofDirectSaddle
      finiteSoloBudget_of_sharpGcompSaddleTenSeventhsCleared_const
      positiveSaddleLargeTailSoloPrefixNormUnit_of_sharpConst
  let hproduct : LargeTailProductCertificate :=
    LargeTailProductCertificate.ofDirectSaddle
  let hsolo : LargeTailSoloCertificate := largeTailSoloCertificate
  let soloNorm : PositiveSaddleLargeTailSoloNormUnitCertificate :=
    hsolo.toNormUnitOfPrefixNorm hbounded.soloPrefixNormUnit
  let pointwise : PositiveSaddleEntropyShadowLargeExpPointwiseCertificate :=
    hproduct.toPointwise hbounded.productPrefixPointwise soloNorm
  exact
    unorm_tail_of_positiveSaddleCertificate
      (hbounded.toPositiveSaddleCertificate
        pointwise
        positiveSaddleLargeTailCandidateRawClearedUnitReserveBoundsCertificate_hybridClosed)

/-- Rectangle-facing form of the Proposition 5.1 quotient negativity.

This is the sign theorem used by the corrected Proposition 5.2 proof for the
extra `(M-1) * b_a` term. -/
theorem bCoeff_neg_of_rectangle
    (μ : List Nat) (a N : Nat)
    (hμ : ∀ m ∈ μ, 1 ≤ m)
    (hN : N = (μ.map (· + 1)).sum)
    (ha : 9 ≤ a)
    (hlo : 6*a - 7 ≤ N)
    (hhi : N ≤ 12*a - 8) :
    bCoeff μ a < 0 := by
  apply bCoeff_neg_of_unorm μ a N hμ hN (by omega) (by omega)
  by_cases h60 : a ≤ 60
  · exact unorm_neg_9_60 a (by omega) ha N (by omega) hlo
  by_cases h400 : a ≤ 400
  · exact unorm_neg_61_400 a (by omega) h400 N hlo hhi
  · exact unorm_neg_401_of_closedDirectSaddle a (by omega) N hlo hhi

end Prop51
