/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Public facade for corrected Chen--Larson Proposition 5.2

This is the intended human-facing file for the corrected Proposition 5.2
formalization.  At this stage it exposes the corrected coefficient, the exact
correction identity, executable sanity checks against the `g = 4` example, and
the large-range reduction to the printed-series sign theorem plus the
Proposition 5.1 rectangle theorem.
-/

import Prop52.Statement
import Prop51.Rectangle
import Prop52.Finite
import Prop52.Printed

namespace Prop52

/-- The corrected coefficient differs from the printed coefficient by
`(M-1) * [t^a]F_μ(t)`. -/
theorem correctedCoeff_eq_printedCoeff_add (a : Nat) (μ : List Nat) :
    correctedCoeff a μ =
      printedCoeff μ a + ((M a : ℚ) - 1) * Prop51.bCoeff μ a := by
  simp [correctedCoeff, printedCoeff]
  ring

/-- For positive partitions of `M a`, the exponent `N` equals `M a + length`. -/
theorem N_eq_M_add_length {a : Nat} {μ : List Nat}
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    N μ = M a + μ.length := by
  obtain ⟨hsum, _hpos⟩ := hμ
  unfold N
  rw [Prop51.sum_map_add_one, hsum]

/-- A positive partition of `M a` is nonempty once `2 <= a`. -/
theorem one_le_length_of_partition {a : Nat} {μ : List Nat}
    (ha : 2 ≤ a) (hμ : Prop51.IsPartitionOf μ (M a)) :
    1 ≤ μ.length := by
  obtain ⟨hsum, _hpos⟩ := hμ
  rcases μ with - | ⟨m, μ⟩
  · simp [M] at hsum
    omega
  · simp

/-- The Prop52 partition exponent lies in the Prop51 rectangle. -/
theorem rectangle_bounds_of_partition {a : Nat} {μ : List Nat}
    (ha : 2 ≤ a) (hμ : Prop51.IsPartitionOf μ (M a)) :
    6*a - 7 ≤ N μ ∧ N μ ≤ 12*a - 8 := by
  have hN := N_eq_M_add_length hμ
  have hlen_pos := one_le_length_of_partition ha hμ
  obtain ⟨_hsum, hpos⟩ := hμ
  have hlen_le := Prop51.length_le_sum μ hpos
  have hsumM : μ.sum = M a := _hsum
  simp [M] at hN hsumM
  constructor
  · omega
  · omega

/-- Large-range reduction: once the printed-series coefficient is known
negative, corrected Proposition 5.2 is negative by the correction identity and
the Proposition 5.1 rectangle theorem. -/
theorem correctedCoeff_neg_large_of_printed
    (hprinted : PrintedCoeffNegativityLarge) :
    CorrectedCoeffNegativityLarge := by
  intro a ha μ hμ
  have hpart := hμ
  obtain ⟨_hsum, hpos⟩ := hμ
  have hrect := rectangle_bounds_of_partition (a := a) (μ := μ) (by omega) hpart
  have hb : Prop51.bCoeff μ a < 0 :=
    Prop51.bCoeff_neg_of_rectangle μ a (N μ)
      hpos rfl (by omega) hrect.1 hrect.2
  have hp : printedCoeff μ a < 0 := hprinted a ha μ hpart
  have hMpos : 0 < ((M a : ℚ) - 1) := by
    norm_num [M]
    omega
  rw [correctedCoeff_eq_printedCoeff_add]
  nlinarith

/-- Final assembly interface for corrected Proposition 5.2.

The remaining proof work is now concentrated in two independent inputs:

* `hfinite`: the exact finite nonvanishing check for `2 <= a <= 13`;
* `hprinted`: the printed-series sign theorem for `a >= 14`.

Together with the correction identity and the Proposition 5.1 rectangle
theorem, these imply the full corrected nonvanishing statement. -/
theorem correctedCoeff_nonvanishing_of_finite_and_printed
    (hfinite : CorrectedCoeffFiniteNonvanishing)
    (hprinted : PrintedCoeffNegativityLarge) :
    CorrectedCoeffNonvanishing := by
  intro a ha μ hμ
  by_cases hsmall : a ≤ 13
  · exact hfinite a ha hsmall μ hμ
  · have hlarge : correctedCoeff a μ < 0 :=
      correctedCoeff_neg_large_of_printed hprinted a (by omega) μ hμ
    exact ne_of_lt hlarge

/-! The finite input in the preceding assembly theorem is now fully proved in
`Prop52.Finite`, by exact checks for `2 <= a <= 8` and a modular-certificate
lift for `9 <= a <= 13`.  The remaining analytic input for the complete
corrected Proposition 5.2 statement is the printed-series large-range sign
theorem. -/

theorem correctedCoeff_nonvanishing_of_printed
    (hprinted : PrintedCoeffNegativityLarge) :
    CorrectedCoeffNonvanishing :=
  correctedCoeff_nonvanishing_of_finite_and_printed
    correctedCoeff_finite_nonvanishing hprinted

/-- Final assembly after the remaining printed-sign proof has been split into
the interval-certificate range `14 <= a <= 149` and the large-tail range
`a >= 150`. -/
theorem correctedCoeff_nonvanishing_of_printed_mid_tail
    (hmid : PrintedCoeffNegativityMid)
    (htail : PrintedCoeffNegativityTail) :
    CorrectedCoeffNonvanishing :=
  correctedCoeff_nonvanishing_of_printed
    (printedCoeffNegativityLarge_of_mid_tail hmid htail)

/-- Final assembly when the large-tail printed proof is supplied in the
normalized form used by the Gamma/truncation/error argument. -/
theorem correctedCoeff_nonvanishing_of_printed_mid_normalizedTail
    (hmid : PrintedCoeffNegativityMid)
    (htail : PrintedTailNormalizedLowerBound) :
    CorrectedCoeffNonvanishing :=
  correctedCoeff_nonvanishing_of_printed
    (printedCoeffNegativityLarge_of_mid_normalizedTail hmid htail)

/-- Final assembly when the printed large-tail proof is supplied through the
exact low/high split and the three finite normalized error estimates. -/
theorem correctedCoeff_nonvanishing_of_printed_mid_split_errorBounds
    (hmid : PrintedCoeffNegativityMid)
    (hsplit : PrintedTailExactSplit)
    (hmain : PrintedTailMainLowerBound)
    (hh : PrintedTailHErrorBound)
    (hk : PrintedTailKErrorBound)
    (homega : PrintedTailOmegaErrorBound) :
    CorrectedCoeffNonvanishing :=
  correctedCoeff_nonvanishing_of_printed_mid_tail hmid
    (printedCoeffNegativityTail_of_split_errorBounds
      hsplit hmain hh hk homega)

/-! ## Executable checks for the smallest corrected example

For `g = 4` (`a = 2`) and `μ = (1^6)`, the corrected note records

* `[t^2]F_μ = -195/8`,
* the printed coefficient is `45/8`,
* the corrected coefficient is `-465/4`.
-/

example : Prop51.bCoeff [1, 1, 1, 1, 1, 1] 2 = -195 / 8 := by
  native_decide

example : printedCoeff [1, 1, 1, 1, 1, 1] 2 = 45 / 8 := by
  native_decide

example : correctedCoeff 2 [1, 1, 1, 1, 1, 1] = -465 / 4 := by
  native_decide

end Prop52
