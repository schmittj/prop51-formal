/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Scalar real-exponential constants for the Prop52 Gamma margin

The Gamma-margin proof is algebraized in `Prop52.GammaMoment` up to the
finite factorial-ratio moment bound.  This file records the tiny real
exponential endpoint used after Jensen's inequality in the printed proof.
-/

import Prop52.GammaMoment
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Prop52

open Finset

/-- A three-term Taylor upper bound for `exp(3/10)`. -/
theorem real_exp_three_tenths_le :
    Real.exp (3 / 10 : ℝ) ≤ 1351 / 1000 := by
  have h := Real.exp_bound' (x := (3 / 10 : ℝ))
    (by norm_num) (by norm_num) (n := 3) (by norm_num)
  calc
    Real.exp (3 / 10 : ℝ)
        ≤ (∑ m ∈ range 3, (3 / 10 : ℝ) ^ m / (m.factorial : ℝ)) +
            (3 / 10 : ℝ) ^ 3 * (3 + 1) /
              ((Nat.factorial 3 : Nat) * 3 : ℝ) := h
    _ = 1351 / 1000 := by
      norm_num [sum_range_succ, Nat.factorial]

/-- The scalar exponential endpoint used by the printed Gamma/Jensen margin. -/
theorem real_exp_thirteen_tenths_lt :
    Real.exp (13 / 10 : ℝ) < 100 / 27 := by
  have h1 : Real.exp (1 : ℝ) < 2.7182818286 := Real.exp_one_lt_d9
  have h03 := real_exp_three_tenths_le
  rw [show (13 / 10 : ℝ) = 1 + 3 / 10 by norm_num, Real.exp_add]
  have hprod :
      Real.exp (1 : ℝ) * Real.exp (3 / 10 : ℝ) <
        (2.7182818286 : ℝ) * (1351 / 1000 : ℝ) :=
    mul_lt_mul_of_pos_of_nonneg' h1 h03 (Real.exp_pos _) (by norm_num)
  exact hprod.trans (by norm_num)

/-- Equivalent lower form, exactly as used after Jensen:
`exp(-13/10) > 27/100`. -/
theorem real_exp_neg_thirteen_tenths_gt :
    (27 / 100 : ℝ) < Real.exp (-(13 / 10 : ℝ)) := by
  rw [Real.exp_neg]
  rw [lt_inv_comm₀ (by norm_num : (0 : ℝ) < 27 / 100) (Real.exp_pos _)]
  simpa using real_exp_thirteen_tenths_lt

end Prop52
