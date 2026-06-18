import Prop51.Main

namespace Prop51

/-!
`OpenGoals` is the machine-readable dashboard for the remaining route to the
final theorem.

The intended split is `401 ≤ a < 3000` for bounded checking and `3000 ≤ a` for
the analytic tail.  The currently available Lean assembly still has separate
generated interfaces for the old `401 ≤ a ≤ 2000` finite window and the
`2001 ≤ a < 3000` prefix strip; this dashboard packages both on the bounded
side so the product and solo inputs are the genuine large-`a` analytic fields.
-/

/-- The bounded positive-saddle obligation for the current canonical route.

At present this wraps the existing active finite-window certificate together
with the lower-prefix product/solo scalar chunks.  The target shape is a single
checker-backed certificate for all `401 ≤ a < 3000`. -/
structure BoundedPositiveCertificate where
  tangentRowLen : Nat
  soloSaddleRowLen : Nat
  soloBudgetRowLen : Nat
  edgeRowLen : Nat
  tangentNLen : Nat
  soloSaddleNLen : Nat
  soloBudgetNLen : Nat
  tangentKLen : Nat
  edgeKLen : Nat
  cert :
    PositiveSaddleFixedFiniteWindowActiveAnalyticProductTangentSoloNFixedEdgeKChunkedAuditCertificate
      tangentRowLen soloSaddleRowLen soloBudgetRowLen edgeRowLen
      tangentNLen soloSaddleNLen soloBudgetNLen tangentKLen edgeKLen
  productPrefixALen : Nat
  productPrefixKLen : Nat
  productPrefix :
    PositiveSaddleLargeTailProductFastUpperEdgeLowerNProductBoundPrefixChunksCertificate
      (fun a k =>
        positiveLargeTailProductXUpperEdgeExactBound a k *
          positiveLargeTailProductYUpperEdgeExactBound a k)
      productPrefixALen productPrefixKLen
  soloPrefixALen : Nat
  soloPrefix :
    PositiveSaddleLargeTailSoloFastUpperEdgeBoundPrefixChunksCertificate
      positiveLargeTailSoloUpperEdgeExactBound
      soloPrefixALen

/-- The large-tail product obligation for the current canonical route.

This is intentionally stated as the normalized combined actual product target,
not as the older independent `Gcomp` majorant product.  This matches the TeX
combined-product route: the raw `Bq * Qq` form can be supplied via
`LargeTailProductCertificate.ofRawCleared`, while the stronger legacy
upper-edge/lower-`N` `Gcomp` scalar route remains available only as a
compatibility constructor below. -/
structure LargeTailProductCertificate where
  largeSmall :
    ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        Xnorm N k * Ynorm N (posJ a k)
          ≤ positiveSmallLargeGcompProductTarget a N k
  largeTempered :
    ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k →
        Xnorm N k * Ynorm N (posJ a k)
          ≤ positiveTemperedLargeGcompProductTarget a N k

/-- Constructor from denominator-cleared actual-product large-tail bounds.

This is the preferred proof-production shape for the remaining analytic
product work: it keeps rational denominator clearing local and uses
`Xnorm_mul_Ynorm_eq_raw_div` through the bridge in `PositiveSaddle`. -/
theorem LargeTailProductCertificate.ofRawCleared
    (hsmall :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          positiveSmallLargeXYProductRawCleared a N k)
    (htempered :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k →
          positiveTemperedLargeXYProductRawCleared a N k) :
    LargeTailProductCertificate where
  largeSmall := by
    intro a N k ha hrect hk hsmallN
    exact
      positiveSmallLargeXYProductTarget_of_rawCleared
        (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect)
        (by omega : 1 ≤ a) hk
        (hsmall ha hrect hk hsmallN)
  largeTempered := by
    intro a N k ha hrect hk htemperedN
    exact
      positiveTemperedLargeXYProductTarget_of_rawCleared
        (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect)
        (by omega : 2 ≤ a) hk
        (htempered ha hrect hk htemperedN)

/-- Constructor from the existing large-tail product-bounds certificate,
routed through the actual combined raw product.

This intentionally avoids using the older normalized independent-`Gcomp`
product as the route-facing conclusion.  The split `B`/`Q` product-bound
certificate is only a way to prove the denominator-cleared actual
`Bq * Qq` inequality, after which `LargeTailProductCertificate.ofRawCleared`
performs the final normalization. -/
theorem LargeTailProductCertificate.ofProductBounds
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    (cert : PositiveSaddleLargeTailProductBoundsCertificate
      smallXBound smallYBound temperedXBound temperedYBound) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofRawCleared
    (by
      intro a N k ha hrect hk hsmallN
      exact cert.smallXYProductRawCleared
        (by omega : 2000 < a) hrect hk hsmallN)
    (by
      intro a N k ha hrect hk htemperedN
      exact cert.temperedXYProductRawCleared
        (by omega : 2000 < a) hrect hk htemperedN)

/-- Constructor from raw actual-product bounds away from the sign-lock zone.

Cells satisfying `361 ≤ k` and `N ≤ (40/3) k` need no product estimate:
`Xnorm N k` is nonpositive by §5, while `Ynorm` and the large-tail targets are
nonnegative.  The remaining raw obligations are the only cells where the
combined-product estimate still has to do work. -/
theorem LargeTailProductCertificate.ofRawClearedAwayFromSignLock
    (hsmall :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          ¬ (361 ≤ k ∧ (N : ℚ) ≤ (40 / 3 : ℚ) * (k : ℚ)) →
          positiveSmallLargeXYProductRawCleared a N k)
    (htempered :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k →
          ¬ (361 ≤ k ∧ (N : ℚ) ≤ (40 / 3 : ℚ) * (k : ℚ)) →
          positiveTemperedLargeXYProductRawCleared a N k) :
    LargeTailProductCertificate where
  largeSmall := by
    intro a N k ha hrect hk hsmallN
    have hN : 1 ≤ N :=
      positiveRectangle_N_pos (by omega : 2 ≤ a) hrect
    by_cases hlock :
        361 ≤ k ∧ (N : ℚ) ≤ (40 / 3 : ℚ) * (k : ℚ)
    · exact
        positiveSmallLargeXYProductTarget_of_signLock
          (by omega : 2000 < a) hN hk hlock.1 hlock.2
    · exact
        positiveSmallLargeXYProductTarget_of_rawCleared hN
          (by omega : 1 ≤ a) hk
          (hsmall ha hrect hk hsmallN hlock)
  largeTempered := by
    intro a N k ha hrect hk htemperedN
    have hN : 1 ≤ N :=
      positiveRectangle_N_pos (by omega : 2 ≤ a) hrect
    by_cases hlock :
        361 ≤ k ∧ (N : ℚ) ≤ (40 / 3 : ℚ) * (k : ℚ)
    · exact
        positiveTemperedLargeXYProductTarget_of_signLock
          (by omega : 2000 < a) hN hk hlock.1 hlock.2
    · exact
        positiveTemperedLargeXYProductTarget_of_rawCleared hN
          (by omega : 2 ≤ a) hk
          (htempered ha hrect hk htemperedN hlock)

/-- Constructor from raw actual-product bounds on the denominator-cleared
complement of the sign-lock zone.

This is the preferred remaining proof surface for the product tail.  It keeps
the TeX sign-lock split, but states the non-sign-lock branch as
`k < 361 ∨ 40*k < 3*N`, avoiding rational negated conjunctions in the
eventual checker/analytic proof.  In the small branch the sign-lock case is
impossible from `k ≤ ceilSqrt N`, so no extra complement hypothesis is asked
there. -/
theorem LargeTailProductCertificate.ofRawClearedNatSignLockComplement
    (hsmall :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N →
          positiveSmallLargeXYProductRawCleared a N k)
    (htempered :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k →
          (k < 361 ∨ 40 * k < 3 * N) →
          positiveTemperedLargeXYProductRawCleared a N k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofRawClearedAwayFromSignLock
    (by
      intro a N k ha hrect hk hsmallN hnotLock
      exact hsmall ha hrect hk hsmallN)
    (by
      intro a N k ha hrect hk htemperedN hnotLock
      exact htempered ha hrect hk htemperedN
        (signLock_natAlternative_of_not hnotLock))

/-- Constructor from actual-product raw bounds only on cells where the
coefficient `B_k(N)` is positive.

This follows the combined-product route in the TeX argument: cells with
`Bq N k ≤ 0` contribute a nonpositive actual product because `Qq` is
nonnegative, so they should not be sent to any independent `Gcomp` product
majorant. -/
theorem LargeTailProductCertificate.ofRawClearedBqPositive
    (hsmall :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N → 0 < Bq N k →
          positiveSmallLargeXYProductRawCleared a N k)
    (htempered :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k → 0 < Bq N k →
          positiveTemperedLargeXYProductRawCleared a N k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofRawCleared
    (by
      intro a N k ha hrect hk hsmallN
      by_cases hB : 0 < Bq N k
      · exact hsmall ha hrect hk hsmallN hB
      · exact
          positiveSmallLargeXYProductRawCleared_of_Bq_nonpos
            (by omega : 2000 < a) hk (le_of_not_gt hB))
    (by
      intro a N k ha hrect hk htemperedN
      by_cases hB : 0 < Bq N k
      · exact htempered ha hrect hk htemperedN hB
      · exact
          positiveTemperedLargeXYProductRawCleared_of_Bq_nonpos
            (by omega : 2000 < a) hk (le_of_not_gt hB))

/-- Product-tail constructor combining the two free reductions now available
for the actual raw product: nonpositive `Bq` cells are automatic, and the
§5 sign-lock zone is automatic in the tempered branch.  The remaining
tempered work is exactly the denominator-cleared complement
`k < 361 ∨ 40*k < 3*N` with `0 < Bq N k`. -/
theorem LargeTailProductCertificate.ofRawClearedBqPositiveNatSignLockComplement
    (hsmall :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N → 0 < Bq N k →
          positiveSmallLargeXYProductRawCleared a N k)
    (htempered :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k →
          (k < 361 ∨ 40 * k < 3 * N) → 0 < Bq N k →
          positiveTemperedLargeXYProductRawCleared a N k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofRawClearedNatSignLockComplement
    (by
      intro a N k ha hrect hk hsmallN
      by_cases hB : 0 < Bq N k
      · exact hsmall ha hrect hk hsmallN hB
      · exact
          positiveSmallLargeXYProductRawCleared_of_Bq_nonpos
            (by omega : 2000 < a) hk (le_of_not_gt hB))
    (by
      intro a N k ha hrect hk htemperedN hnotLock
      by_cases hB : 0 < Bq N k
      · exact htempered ha hrect hk htemperedN hnotLock hB
      · exact
          positiveTemperedLargeXYProductRawCleared_of_Bq_nonpos
            (by omega : 2000 < a) hk (le_of_not_gt hB))

/-- Product-tail constructor after the first-coefficient sign reduction.

Since `Bq N 1 ≤ 0`, the live actual-product obligations with `0 < Bq N k`
start at `k = 2`.  This is the version future tail-product checkers should
target: it keeps both free reductions from
`ofRawClearedBqPositiveNatSignLockComplement` and removes the uniformly
nonpositive first coefficient from the remaining domain. -/
theorem LargeTailProductCertificate.ofRawClearedBqPositiveGeTwoNatSignLockComplement
    (hsmall :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N → 2 ≤ k → 0 < Bq N k →
          positiveSmallLargeXYProductRawCleared a N k)
    (htempered :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k →
          (k < 361 ∨ 40 * k < 3 * N) → 2 ≤ k → 0 < Bq N k →
          positiveTemperedLargeXYProductRawCleared a N k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofRawClearedBqPositiveNatSignLockComplement
    (by
      intro a N k ha hrect hk hsmallN hB
      exact hsmall ha hrect hk hsmallN
        (two_le_of_Bq_pos (mem_positiveKRange.mp hk).1 hB) hB)
    (by
      intro a N k ha hrect hk htemperedN hnotLock hB
      exact htempered ha hrect hk htemperedN hnotLock
        (two_le_of_Bq_pos (mem_positiveKRange.mp hk).1 hB) hB)

/-- In the large positive rectangle, the first retained `Bq` coefficient is
strictly positive. -/
theorem Bq_two_pos_of_large_positiveRectangle {a N : Nat} (ha : 3000 ≤ a)
    (hrect : positiveRectangle a N) :
    0 < Bq N 2 :=
  Bq_two_pos_of_le (by
    have hNlo : posNlo a ≤ N := hrect.1
    unfold posNlo at hNlo
    omega)

/-- Product-tail constructor that splits off the first retained product cell.

After the uniform `Bq N 1 ≤ 0` reduction, the first live cell is `k = 2`.
This Lean-side split is a proof-production surface reduction for the product
tail: a later proof may handle the `k = 2` term directly and send the true
tail to a `k ≥ 3` first-term/remainder argument.  The underlying estimate is
still the combined raw product `Bq * Qq`, not the older independent `Gcomp`
product route. -/
theorem LargeTailProductCertificate.ofRawClearedBqPositiveTwoAndGeThreeNatSignLockComplement
    (hsmallTwo :
      ∀ {a N : Nat}, 3000 ≤ a → positiveRectangle a N →
        positiveSmallLargeXYProductRawCleared a N 2)
    (hsmallGeThree :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → k ≤ ceilSqrt N → 3 ≤ k → 0 < Bq N k →
          positiveSmallLargeXYProductRawCleared a N k)
    (htemperedGeThree :
      ∀ {a N k : Nat}, 3000 ≤ a → positiveRectangle a N →
        k ∈ positiveKRange a → ceilSqrt N < k →
          (k < 361 ∨ 40 * k < 3 * N) → 3 ≤ k → 0 < Bq N k →
          positiveTemperedLargeXYProductRawCleared a N k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofRawClearedBqPositiveGeTwoNatSignLockComplement
    (by
      intro a N k ha hrect hk hsmallN hk2 hB
      by_cases hk_eq : k = 2
      · subst k
        exact hsmallTwo ha hrect
      · exact hsmallGeThree ha hrect hk hsmallN (by omega) hB)
    (by
      intro a N k ha hrect hk htemperedN hnotLock hk2 hB
      by_cases hk_eq : k = 2
      · subst k
        have hNgt : 4 < N := by
          have hNlo : posNlo a ≤ N := hrect.1
          unfold posNlo at hNlo
          omega
        have hceil : 2 < ceilSqrt N :=
          lt_ceilSqrt_of_sq_lt (n := N) (k := 2) (by
            norm_num
            exact hNgt)
        omega
      · exact htemperedGeThree ha hrect hk htemperedN hnotLock (by omega) hB)

/-- Compatibility constructor from the older upper-edge/lower-`N` split-sum
`Gcomp` scalar route.

This is stronger than the live combined-product target and should not be the
main route to completion.  It is retained because the bounded prefix strip and
some legacy generated artifacts still use the independent `Gcomp` product
majorant. -/
theorem LargeTailProductCertificate.ofFastUpperEdgeLowerNScalars
    (hsmall :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k =>
              positiveLargeTailProductXUpperEdgeExactBound a k *
                positiveLargeTailProductYUpperEdgeExactBound a k) a k)
    (htempered :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k =>
              positiveLargeTailProductXUpperEdgeExactBound a k *
                positiveLargeTailProductYUpperEdgeExactBound a k) a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofRawCleared
    (by
      intro a N k ha hrect hk hsmallN
      have hsmallEdge : k ≤ ceilSqrt (posNhi a) :=
        hsmallN.trans (ceilSqrt_mono hrect.2)
      exact
        positiveSmallLargeXYProductRawCleared_of_fastUpperEdgeLowerN
          (by omega : 2000 < a) hrect hk
          (hsmall ha hk hsmallEdge))
    (by
      intro a N k ha hrect hk htemperedN
      have htemperedEdge : ceilSqrt (posNlo a) < k :=
        lt_of_le_of_lt (ceilSqrt_mono hrect.1) htemperedN
      exact
        positiveTemperedLargeXYProductRawCleared_of_fastUpperEdgeLowerN
          (by omega : 2000 < a) hrect hk
          (htempered ha hk htemperedEdge))

/-- One-dimensional fast-scalar constructor after applying the sign-lock
split to the tempered branch.

The TeX sign-lock branch is `N ≤ (40/3)k`.  On the raw-estimate branch Lean
receives the denominator-cleared complement `k < 361 ∨ 40*k < 3*N`; since
`N ≤ posNhi a` in the rectangle, the second alternative can be weakened to
the row-only condition `40*k < 3*posNhi a`.  This is the scalar surface a
large-tail checker should target if the full tempered upper-edge/lower-`N`
inequality is too strong in sign-lock-covered cells. -/
theorem LargeTailProductCertificate.ofFastUpperEdgeLowerNScalarsNatSignLockComplement
    (hsmall :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k =>
              positiveLargeTailProductXUpperEdgeExactBound a k *
                positiveLargeTailProductYUpperEdgeExactBound a k) a k)
    (htempered :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k =>
              positiveLargeTailProductXUpperEdgeExactBound a k *
                positiveLargeTailProductYUpperEdgeExactBound a k) a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofRawClearedNatSignLockComplement
    (by
      intro a N k ha hrect hk hsmallN
      have hsmallEdge : k ≤ ceilSqrt (posNhi a) :=
        hsmallN.trans (ceilSqrt_mono hrect.2)
      exact
        positiveSmallLargeXYProductRawCleared_of_fastUpperEdgeLowerN
          (by omega : 2000 < a) hrect hk
          (hsmall ha hk hsmallEdge))
    (by
      intro a N k ha hrect hk htemperedN hnotLock
      have htemperedEdge : ceilSqrt (posNlo a) < k :=
        lt_of_le_of_lt (ceilSqrt_mono hrect.1) htemperedN
      have hrowAlt : k < 361 ∨ 40 * k < 3 * posNhi a := by
        rcases hnotLock with hsmallK | hN
        · exact Or.inl hsmallK
        · exact Or.inr (by
            have h3N_hi : 3 * N ≤ 3 * posNhi a :=
              Nat.mul_le_mul_left 3 hrect.2
            omega)
      exact
        positiveTemperedLargeXYProductRawCleared_of_fastUpperEdgeLowerN
          (by omega : 2000 < a) hrect hk
          (htempered ha hk htemperedEdge hrowAlt))

/-- Large-tail product constructor for a rational upper-edge product
surrogate, after applying the sign-lock split to the tempered branch.

This is the intended completion-facing surface.  It follows the TeX
combined-product route, but records the Lean proof-production deviation:
instead of expanding the exact upper-edge split product inside the scalar
comparison, a separate `xyBound` may dominate that product.  The tempered
scalar is only required on the denominator-cleared complement of the §5
sign-lock zone. -/
theorem LargeTailProductCertificate.ofFastUpperEdgeLowerNProductBoundScalarsNatSignLockComplement
    {xyBound : Nat → Nat → ℚ}
    (hproductBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct a k
          ≤ xyBound a k)
    (hsmall :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k)
    (htempered :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofRawClearedNatSignLockComplement
    (by
      intro a N k ha hrect hk hsmallN
      have hsmallEdge : k ≤ ceilSqrt (posNhi a) :=
        hsmallN.trans (ceilSqrt_mono hrect.2)
      exact
        positiveSmallLargeXYProductRawCleared_of_fastUpperEdgeLowerNProductBound
          (by omega : 2000 < a) hrect hk
          (hproductBound ha hk)
          (hsmall ha hk hsmallEdge))
    (by
      intro a N k ha hrect hk htemperedN hnotLock
      have htemperedEdge : ceilSqrt (posNlo a) < k :=
        lt_of_le_of_lt (ceilSqrt_mono hrect.1) htemperedN
      have hrowAlt : k < 361 ∨ 40 * k < 3 * posNhi a := by
        rcases hnotLock with hsmallK | hN
        · exact Or.inl hsmallK
        · exact Or.inr (by
            have h3N_hi : 3 * N ≤ 3 * posNhi a :=
              Nat.mul_le_mul_left 3 hrect.2
            omega)
      exact
        positiveTemperedLargeXYProductRawCleared_of_fastUpperEdgeLowerNProductBound
          (by omega : 2000 < a) hrect hk
          (hproductBound ha hk)
          (htempered ha hk htemperedEdge hrowAlt))

/-- Large-tail product constructor for separate rational upper-edge `X` and
`Y` factor surrogates, after applying the sign-lock split to the tempered
branch.

This is the product-tail proof surface to target next.  It is weaker than the
full-hybrid `PositiveSaddle` surface because the tempered scalar is only
required on the row-level complement of the §5 sign-lock zone, and it avoids
the expensive exact split-product expression in the final scalar comparison.
-/
theorem LargeTailProductCertificate.ofFastUpperEdgeLowerNXYBoundScalarsNatSignLockComplement
    {xBound yBound : Nat → Nat → ℚ}
    (hxBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        positiveLargeTailProductXClosedFactorialSplitBlockBound
            a (posNhi a) k ≤ xBound a k)
    (hyBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        positiveLargeTailProductYClosedFactorialSplitBlockBound
            a (posNhi a) k ≤ yBound a k)
    (hsmall :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k => xBound a k * yBound a k) a k)
    (htempered :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k => xBound a k * yBound a k) a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofFastUpperEdgeLowerNProductBoundScalarsNatSignLockComplement
    (xyBound := fun a k => xBound a k * yBound a k)
    (by
      intro a k ha hk
      unfold positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct
      have hx := hxBound ha hk
      have hy := hyBound ha hk
      have hYnonneg :
          0 ≤ positiveLargeTailProductYClosedFactorialSplitBlockBound
            a (posNhi a) k :=
        positiveLargeTailProductYClosedFactorialSplitBlockBound_nonneg
          a (posNhi a) k
      have hxBoundNonneg : 0 ≤ xBound a k :=
        (positiveLargeTailProductXClosedFactorialSplitBlockBound_nonneg
          a (posNhi a) k).trans hx
      exact mul_le_mul hx hy hYnonneg hxBoundNonneg)
    hsmall
    htempered

/-- Large-tail product constructor for separate rational upper-edge `X` and
`Y` factor surrogates after both cheap raw-product reductions.

This is the same completion-facing route as
`ofFastUpperEdgeLowerNXYBoundScalarsNatSignLockComplement`, with the additional
Lean-side reduction from `Bq N 1 ≤ 0`: future scalar witnesses only need to
cover retained positive-`Bq` cells, hence `2 ≤ k`.  The statement is a proof
surface reduction, not a new mathematical estimate; the raw product is still
the actual combined `Bq * Qq` term. -/
theorem LargeTailProductCertificate.ofFastUpperEdgeLowerNXYBoundScalarsGeTwoNatSignLockComplement
    {xBound yBound : Nat → Nat → ℚ}
    (hxBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        positiveLargeTailProductXClosedFactorialSplitBlockBound
            a (posNhi a) k ≤ xBound a k)
    (hyBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        positiveLargeTailProductYClosedFactorialSplitBlockBound
            a (posNhi a) k ≤ yBound a k)
    (hsmall :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) → 2 ≤ k →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k => xBound a k * yBound a k) a k)
    (htempered :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) → 2 ≤ k →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k => xBound a k * yBound a k) a k) :
    LargeTailProductCertificate := by
  have hproductBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct a k
          ≤ xBound a k * yBound a k := by
    intro a k ha hk
    unfold positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct
    have hx := hxBound ha hk
    have hy := hyBound ha hk
    have hYnonneg :
        0 ≤ positiveLargeTailProductYClosedFactorialSplitBlockBound
          a (posNhi a) k :=
      positiveLargeTailProductYClosedFactorialSplitBlockBound_nonneg
        a (posNhi a) k
    have hxBoundNonneg : 0 ≤ xBound a k :=
      (positiveLargeTailProductXClosedFactorialSplitBlockBound_nonneg
        a (posNhi a) k).trans hx
    exact mul_le_mul hx hy hYnonneg hxBoundNonneg
  exact
    LargeTailProductCertificate.ofRawClearedBqPositiveGeTwoNatSignLockComplement
      (by
        intro a N k ha hrect hk hsmallN hk2 _hB
        have hsmallEdge : k ≤ ceilSqrt (posNhi a) :=
          hsmallN.trans (ceilSqrt_mono hrect.2)
        exact
          positiveSmallLargeXYProductRawCleared_of_fastUpperEdgeLowerNProductBound
            (by omega : 2000 < a) hrect hk
            (hproductBound ha hk)
            (hsmall ha hk hsmallEdge hk2))
      (by
        intro a N k ha hrect hk htemperedN hnotLock hk2 _hB
        have htemperedEdge : ceilSqrt (posNlo a) < k :=
          lt_of_le_of_lt (ceilSqrt_mono hrect.1) htemperedN
        have hrowAlt : k < 361 ∨ 40 * k < 3 * posNhi a := by
          rcases hnotLock with hsmallK | hN
          · exact Or.inl hsmallK
          · exact Or.inr (by
              have h3N_hi : 3 * N ≤ 3 * posNhi a :=
                Nat.mul_le_mul_left 3 hrect.2
              omega)
        exact
          positiveTemperedLargeXYProductRawCleared_of_fastUpperEdgeLowerNProductBound
            (by omega : 2000 < a) hrect hk
            (hproductBound ha hk)
            (htempered ha hk htemperedEdge hrowAlt hk2))

/-- Product-bound scalar constructor with the `k = 2` cell split off.

This is the completion-facing first-term/remainder surface for a combined
rational majorant `xyBound`: prove the first retained cell directly, then
prove the row-level scalar inequalities only for the genuine tail `k ≥ 3`.
It is a proof-production split of the same combined raw product route. -/
theorem LargeTailProductCertificate.ofFastUpperEdgeLowerNProductBoundScalarsTwoAndGeThreeNatSignLockComplement
    {xyBound : Nat → Nat → ℚ}
    (hproductBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct a k
          ≤ xyBound a k)
    (hsmallTwo :
      ∀ {a N : Nat}, 3000 ≤ a → positiveRectangle a N →
        positiveSmallLargeXYProductRawCleared a N 2)
    (hsmallGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) → 3 ≤ k →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k)
    (htemperedGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) → 3 ≤ k →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            xyBound a k) :
    LargeTailProductCertificate :=
  LargeTailProductCertificate.ofRawClearedBqPositiveTwoAndGeThreeNatSignLockComplement
    hsmallTwo
    (by
      intro a N k ha hrect hk hsmallN hk3 _hB
      have hsmallEdge : k ≤ ceilSqrt (posNhi a) :=
        hsmallN.trans (ceilSqrt_mono hrect.2)
      exact
        positiveSmallLargeXYProductRawCleared_of_fastUpperEdgeLowerNProductBound
          (by omega : 2000 < a) hrect hk
          (hproductBound ha hk)
          (hsmallGeThree ha hk hsmallEdge hk3))
    (by
      intro a N k ha hrect hk htemperedN hnotLock hk3 _hB
      have htemperedEdge : ceilSqrt (posNlo a) < k :=
        lt_of_le_of_lt (ceilSqrt_mono hrect.1) htemperedN
      have hrowAlt : k < 361 ∨ 40 * k < 3 * posNhi a := by
        rcases hnotLock with hsmallK | hN
        · exact Or.inl hsmallK
        · exact Or.inr (by
            have h3N_hi : 3 * N ≤ 3 * posNhi a :=
              Nat.mul_le_mul_left 3 hrect.2
            omega)
      exact
        positiveTemperedLargeXYProductRawCleared_of_fastUpperEdgeLowerNProductBound
          (by omega : 2000 < a) hrect hk
          (hproductBound ha hk)
          (htemperedGeThree ha hk htemperedEdge hrowAlt hk3))

/-- Separate-`X`/`Y` variant of the first-term/remainder product-bound route.

The two factor majorants only serve to prove the combined `xyBound`
upper-edge product bound; the live scalar obligations remain the first
retained raw product cell and the `k ≥ 3` combined-product tail. -/
theorem LargeTailProductCertificate.ofFastUpperEdgeLowerNXYBoundScalarsTwoAndGeThreeNatSignLockComplement
    {xBound yBound : Nat → Nat → ℚ}
    (hxBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        positiveLargeTailProductXClosedFactorialSplitBlockBound
            a (posNhi a) k ≤ xBound a k)
    (hyBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        positiveLargeTailProductYClosedFactorialSplitBlockBound
            a (posNhi a) k ≤ yBound a k)
    (hsmallTwo :
      ∀ {a N : Nat}, 3000 ≤ a → positiveRectangle a N →
        positiveSmallLargeXYProductRawCleared a N 2)
    (hsmallGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) → 3 ≤ k →
          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k => xBound a k * yBound a k) a k)
    (htemperedGeThree :
      ∀ {a k : Nat}, 3000 ≤ a →
        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →
          (k < 361 ∨ 40 * k < 3 * posNhi a) → 3 ≤ k →
          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar
            (fun a k => xBound a k * yBound a k) a k) :
    LargeTailProductCertificate := by
  have hproductBound :
      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →
        positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct a k
          ≤ xBound a k * yBound a k := by
    intro a k ha hk
    unfold positiveLargeTailProductClosedFactorialSplitBlockUpperEdgeProduct
    have hx := hxBound ha hk
    have hy := hyBound ha hk
    have hYnonneg :
        0 ≤ positiveLargeTailProductYClosedFactorialSplitBlockBound
          a (posNhi a) k :=
      positiveLargeTailProductYClosedFactorialSplitBlockBound_nonneg
        a (posNhi a) k
    have hxBoundNonneg : 0 ≤ xBound a k :=
      (positiveLargeTailProductXClosedFactorialSplitBlockBound_nonneg
        a (posNhi a) k).trans hx
    exact mul_le_mul hx hy hYnonneg hxBoundNonneg
  exact
    LargeTailProductCertificate.ofFastUpperEdgeLowerNProductBoundScalarsTwoAndGeThreeNatSignLockComplement
      (xyBound := fun a k => xBound a k * yBound a k)
      hproductBound hsmallTwo hsmallGeThree htemperedGeThree

/-- Convert the live product certificate and its lower-prefix scalar chunks
directly into the large-tail pointwise estimate used by the candidate/reserve
machinery.

This is the route-facing product bridge: for `3000 ≤ a` it uses
`LargeTailProductCertificate`, and for `2000 < a < 3000` it uses the bounded
prefix chunks packaged in `BoundedPositiveCertificate`. -/
theorem LargeTailProductCertificate.toPointwise
    {aLen kLen : Nat}
    (hproduct : LargeTailProductCertificate)
    (hprefix :
      PositiveSaddleLargeTailProductFastUpperEdgeLowerNProductBoundPrefixChunksCertificate
        (fun a k =>
          positiveLargeTailProductXUpperEdgeExactBound a k *
            positiveLargeTailProductYUpperEdgeExactBound a k)
        aLen kLen)
    (hsolo : PositiveSaddleLargeTailSoloNormUnitCertificate) :
    PositiveSaddleEntropyShadowLargeExpPointwiseCertificate where
  small := by
    intro a N k ha hrect hk hsmall
    have hXY :
        Xnorm N k * Ynorm N (posJ a k)
          ≤ positiveSmallLargeGcompProductTarget a N k := by
      by_cases haLarge : 3000 ≤ a
      · exact hproduct.largeSmall haLarge hrect hk hsmall
      · have haPrefix : a < 3000 := Nat.lt_of_not_ge haLarge
        have hsmallEdge : k ≤ ceilSqrt (posNhi a) :=
          hsmall.trans (ceilSqrt_mono hrect.2)
        have hprod :
            positiveXplusYProductGcompBound a N k
              ≤ positiveSmallLargeGcompProductTarget a N k :=
          positiveXplusYProductGcompBound_le_smallLargeGcompProductTarget_of_fastUpperEdgeLowerN
            ha hrect hk
            (hprefix.toPrefixCertificate.smallScalar
              ha haPrefix hk hsmallEdge)
        exact
          (Xnorm_mul_Ynorm_le_of_Xplus_mul_Ynorm
            (XplusYnorm_le_positiveXplusYProductGcompBound a N k)).trans hprod
    exact
      normalizedPositiveIfTerm_le_smallEntropyShadowExp_of_XYProductTarget
        ha hrect hk hXY
  tempered := by
    intro a N k ha hrect hk htempered
    have hXY :
        Xnorm N k * Ynorm N (posJ a k)
          ≤ positiveTemperedLargeGcompProductTarget a N k := by
      by_cases haLarge : 3000 ≤ a
      · exact hproduct.largeTempered haLarge hrect hk htempered
      · have haPrefix : a < 3000 := Nat.lt_of_not_ge haLarge
        have htemperedEdge : ceilSqrt (posNlo a) < k :=
          lt_of_le_of_lt (ceilSqrt_mono hrect.1) htempered
        have hprod :
            positiveXplusYProductGcompBound a N k
              ≤ positiveTemperedLargeGcompProductTarget a N k :=
          positiveXplusYProductGcompBound_le_temperedLargeGcompProductTarget_of_fastUpperEdgeLowerN
            ha hrect hk
            (hprefix.toPrefixCertificate.temperedScalar
              ha haPrefix hk htemperedEdge)
        exact
          (Xnorm_mul_Ynorm_le_of_Xplus_mul_Ynorm
            (XplusYnorm_le_positiveXplusYProductGcompBound a N k)).trans hprod
    exact
      normalizedPositiveIfTerm_le_temperedEntropyShadowExp_of_XYProductTarget
        ha hrect hk hXY
  soloBudget := by
    intro a N ha hrect
    exact le_positiveSoloBudget_of_mul_200000000_le_one
      (hsolo.soloNormUnit ha hrect)

/-- The large-tail solo obligation for the current canonical route.

The final assembly only needs a unit budget for the normalized solo term
`normalizedSoloTerm`.  This intentionally diverges from older Lean
proof-production wrappers which asked for
`positiveYgcompBound N a ≤ positiveLargeTailSoloTenSeventhsBound a N`: that
quotient uses a coarse `Eplus`/`Gcomp` majorant and is too lossy as a large
tail target.  The prefix strip still reuses the generated stronger surrogate,
but the analytic `a ≥ 3000` input is the direct final solo budget. -/
structure LargeTailSoloCertificate where
  largeSolo :
    ∀ {a N : Nat}, 3000 ≤ a → positiveRectangle a N →
      (200000000 : ℚ) * normalizedSoloTerm a N ≤ 1

theorem LargeTailSoloCertificate.ofSharpGcompSaddleTenSeventhsCleared
    (hsharp :
      ∀ {a N : Nat}, 3000 ≤ a → positiveRectangle a N →
        positiveLargeTailSoloSharpGcompSaddleTenSeventhsCleared a N) :
    LargeTailSoloCertificate where
  largeSolo := by
    intro a N ha hrect
    exact
      positiveLargeTailSoloNormUnit_of_sharpGcompSaddleTenSeventhsCleared
        (by omega : 2000 < a) hrect (hsharp ha hrect)

theorem LargeTailSoloCertificate.ofSharpGcompClosedFactorialSplitBlockSumTenSeventhsClearedUpperEdge
    (hsharpEdge :
      ∀ {a : Nat}, 3000 ≤ a →
        positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSumTenSeventhsCleared
          a (posNhi a)) :
    LargeTailSoloCertificate :=
  LargeTailSoloCertificate.ofSharpGcompSaddleTenSeventhsCleared
    (by
      intro a N ha hrect
      exact
        positiveLargeTailSoloSharpGcompSaddleTenSeventhsCleared_of_closedFactorialSplitBlockSumTenSeventhsCleared
          (positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSumTenSeventhsCleared_of_upperEdge
            hrect (hsharpEdge ha)))

theorem LargeTailSoloCertificate.ofSharpDeltaBudgetBlockSumTenSeventhsClearedUpperEdge
    (hdeltaEdge :
      ∀ {a : Nat}, 3000 ≤ a →
        (4 : ℚ) * (2 : ℚ)^a *
            positiveLargeTailSoloSharpDeltaBudgetBlockSum a (posNhi a)
          ≤ 29 * (a : ℚ) * c a * (10 / 7 : ℚ)^a) :
    LargeTailSoloCertificate :=
  LargeTailSoloCertificate.ofSharpGcompClosedFactorialSplitBlockSumTenSeventhsClearedUpperEdge
    (by
      intro a ha
      exact
        positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSumTenSeventhsCleared_of_deltaBudgetBlockSum
          (hdeltaEdge ha))

theorem LargeTailSoloCertificate.ofSharpLargeDegreeSplitBudgetBlockSumTenSeventhsCleared
    (hsplit :
      ∀ {a : Nat}, 3000 ≤ a →
        (4 : ℚ) * (2 : ℚ)^a *
            positiveLargeTailSoloSharpLargeDegreeSplitBudgetBlockSum a
          ≤ 29 * (a : ℚ) * c a * (10 / 7 : ℚ)^a) :
    LargeTailSoloCertificate :=
  LargeTailSoloCertificate.ofSharpGcompClosedFactorialSplitBlockSumTenSeventhsClearedUpperEdge
    (by
      intro a ha
      exact
        positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSumTenSeventhsCleared_of_largeDegreeSplitBudgetBlockSum
          ha (hsplit ha))

theorem LargeTailSoloCertificate.ofSharpLargeDegreeRemainderBlockSumTenSeventhsCleared
    (hremainder :
      ∀ {a : Nat}, 3000 ≤ a →
        (4 : ℚ) * (2 : ℚ)^a *
            positiveLargeTailSoloSharpLargeDegreeRemainderBlockSum a
          ≤ (29 / 2 : ℚ) * (a : ℚ) * c a * (10 / 7 : ℚ)^a) :
    LargeTailSoloCertificate :=
  LargeTailSoloCertificate.ofSharpGcompClosedFactorialSplitBlockSumTenSeventhsClearedUpperEdge
    (by
      intro a ha
      exact
        positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSumTenSeventhsCleared_of_largeDegreeRemainderBlockSum
          ha (hremainder ha))

theorem LargeTailSoloCertificate.ofSharpLowDegreeRemainderBlockSumTenSeventhsCleared
    (hlow :
      ∀ {a : Nat}, 3000 ≤ a →
        (4 : ℚ) * (2 : ℚ)^a *
            positiveLargeTailSoloSharpLowDegreeRemainderBlockSum a
          ≤ (29 / 4 : ℚ) * (a : ℚ) * c a * (10 / 7 : ℚ)^a) :
    LargeTailSoloCertificate :=
  LargeTailSoloCertificate.ofSharpGcompClosedFactorialSplitBlockSumTenSeventhsClearedUpperEdge
    (by
      intro a ha
      exact
        positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSumTenSeventhsCleared_of_lowDegreeRemainderBlockSum
          ha (hlow ha))

theorem LargeTailSoloCertificate.ofSharpVeryLowDegreeRemainderBlockSumTenSeventhsCleared
    (hveryLow :
      ∀ {a : Nat}, 3000 ≤ a →
        (4 : ℚ) * (2 : ℚ)^a *
            positiveLargeTailSoloSharpVeryLowDegreeRemainderBlockSum a
          ≤ (29 / 8 : ℚ) * (a : ℚ) * c a * (10 / 7 : ℚ)^a) :
    LargeTailSoloCertificate :=
  LargeTailSoloCertificate.ofSharpGcompClosedFactorialSplitBlockSumTenSeventhsClearedUpperEdge
    (by
      intro a ha
      exact
        positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSumTenSeventhsCleared_of_veryLowDegreeRemainderBlockSum
          ha (hveryLow ha))

theorem LargeTailSoloCertificate.ofSharpDeepLowDegreeRemainderBlockSumTenSeventhsCleared
    (hdeepLow :
      ∀ {a : Nat}, 3000 ≤ a →
        (4 : ℚ) * (2 : ℚ)^a *
            positiveLargeTailSoloSharpDeepLowDegreeRemainderBlockSum a
          ≤ (29 / 16 : ℚ) * (a : ℚ) * c a * (10 / 7 : ℚ)^a) :
    LargeTailSoloCertificate :=
  LargeTailSoloCertificate.ofSharpGcompClosedFactorialSplitBlockSumTenSeventhsClearedUpperEdge
    (by
      intro a ha
      exact
        positiveLargeTailSoloSharpGcompClosedFactorialSplitBlockSumTenSeventhsCleared_of_deepLowDegreeRemainderBlockSum
          ha (hdeepLow ha))

/-- The large-tail solo certificate is now closed analytically from the
deep-low remainder bound in `PositiveSaddle`. -/
theorem largeTailSoloCertificate : LargeTailSoloCertificate :=
  LargeTailSoloCertificate.ofSharpDeepLowDegreeRemainderBlockSumTenSeventhsCleared
    (by
      intro a ha
      exact
        positiveLargeTailSoloSharpDeepLowDegreeRemainderBlockSum_scaled_le_sixteenth_target
          (a := a) ha)

theorem LargeTailSoloCertificate.toNormUnit
    {aLen : Nat}
    (hsolo : LargeTailSoloCertificate)
    (hprefix :
      PositiveSaddleLargeTailSoloFastUpperEdgeBoundPrefixChunksCertificate
        positiveLargeTailSoloUpperEdgeExactBound aLen) :
    PositiveSaddleLargeTailSoloNormUnitCertificate where
  soloNormUnit := by
    intro a N ha hrect
    by_cases haLarge : 3000 ≤ a
    · exact hsolo.largeSolo haLarge hrect
    · have haPrefix : a < 3000 := Nat.lt_of_not_ge haLarge
      have hscalar :
          positiveLargeTailSoloFastUpperEdgeBoundScalar
            positiveLargeTailSoloUpperEdgeExactBound a :=
        hprefix.toPrefixCertificate.soloScalar ha haPrefix
      have hfast :
          positiveLargeTailSoloGcompClosedFactorialSplitBlockSumFastCleared
            a (posNhi a) := by
        unfold positiveLargeTailSoloFastUpperEdgeBoundScalar at hscalar
        unfold positiveLargeTailSoloGcompClosedFactorialSplitBlockSumFastCleared
        simpa [positiveLargeTailSoloUpperEdgeExactBound] using hscalar
      have hY :
          positiveYgcompBound N a ≤
            positiveLargeTailSoloTenSeventhsBound a N :=
        positiveYgcompBound_le_positiveLargeTailSoloTenSeventhsBound_of_gcompSaddleCleared
          (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect) ha
          (positiveLargeTailSoloGcompSaddleCleared_of_closedFactorialSplitBlockSumFastCleared
            (positiveLargeTailSoloGcompClosedFactorialSplitBlockSumFastCleared_of_upperEdge
              (a := a) (N := N) hrect hfast))
      have hYUnit :
          (200000000 : ℚ) *
              (positiveDyadicDecay a / 2 * positiveYgcompBound N a)
            ≤ 1 :=
        positiveLargeTailSoloYUnit_of_Y_bound hY
          (positiveLargeTailSoloTenSeventhsScalarBudget ha hrect)
      exact positiveLargeTailSoloNormUnit_of_Y_unit
        (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect)
        (by omega : 1 ≤ a) hYUnit

/-- Final assembly from the three live obligations.

As each obligation is closed, replace the corresponding parameter here by the
concrete theorem producing it. -/
theorem completion_of_three_inputs
    (hbounded : BoundedPositiveCertificate)
    (hproduct : LargeTailProductCertificate)
    (hsolo : LargeTailSoloCertificate) :
    CoefficientNegativity := by
  let soloNorm : PositiveSaddleLargeTailSoloNormUnitCertificate :=
    hsolo.toNormUnit hbounded.soloPrefix
  let pointwise : PositiveSaddleEntropyShadowLargeExpPointwiseCertificate :=
    hproduct.toPointwise hbounded.productPrefix soloNorm
  exact
    coefficientNegativity_of_positiveSaddleTangentProductBudgetCertificate
      (hbounded.cert.toTangentProductBudgetCertificate_of_pointwise
        pointwise
        positiveSaddleLargeTailCandidateRawClearedUnitReserveBoundsCertificate_hybridClosed)

end Prop51
