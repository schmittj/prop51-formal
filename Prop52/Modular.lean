/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Modular finite checker for corrected Proposition 5.2

The external corrected-finite bundle (the C++ checker) verifies `2 <= a <= 13`
modulo two large primes; the Lean side below uses a single prime
(`finitePrime1 = 1000000007`), since one nonzero reduction already proves
nonvanishing over `ℚ`.  This file begins the Lean-side modular checker: it uses
the same one-pass recurrence as `Prop52.Recurrence`, but evaluates it in
`ZMod p`.

The theorems in this file are the finite-field core.  The rational-to-`ZMod`
reduction bridge (that the modular recurrence is the reduction of
`correctedCoeffFast`) is proved in `Prop52.RatModBridge` and assembled in
`Prop52.Finite`, where it yields the final rational nonvanishing theorem
`correctedCoeff_finite_nonvanishing`.
-/

import Prop52.Recurrence
import Prop51.Partitions
import Mathlib.Algebra.Field.ZMod

namespace Prop52

/-- Modular version of `s_r = sum_i q_i^{-r}`. -/
def sPowerMod (p : Nat) [Fact p.Prime] (μ : List Nat) (r : Nat) : ZMod p :=
  (μ.map fun mi : Nat => 1 / (((mi + 1 : Nat) : ZMod p)^r)).sum

/-- Modular version of `w_r = sum_i (q_i-1) q_i^{-r}`. -/
def markedWeightMod (p : Nat) [Fact p.Prime] (μ : List Nat) (r : Nat) : ZMod p :=
  (μ.map fun mi : Nat => (mi : ZMod p) / (((mi + 1 : Nat) : ZMod p)^r)).sum

/-- Modular version of `h_r = c_r (N-s_r)`. -/
def hCoeffMod (p : Nat) [Fact p.Prime] (μ : List Nat) (r : Nat) : ZMod p :=
  (Prop51.c r : ZMod p) * ((N μ : ZMod p) - sPowerMod p μ r)

/-- Prefix list for `exp(sum L_r t^r)` over `ZMod p`. -/
def expListMod (p : Nat) [Fact p.Prime] (L : Nat → ZMod p) : Nat → List (ZMod p)
  | 0 => [1]
  | (n+1) =>
      let l := expListMod p L n
      let s : ZMod p := ((List.range (n+1)).map fun t : Nat =>
        ((t+1 : Nat) : ZMod p) * L (t+1) * l.getD (n-t) 0).sum
      l ++ [s / ((n+1 : Nat) : ZMod p)]

/-- Coefficient of `exp(sum L_r t^r)` over `ZMod p`. -/
def expCoeffMod (p : Nat) [Fact p.Prime] (L : Nat → ZMod p) (a : Nat) : ZMod p :=
  (expListMod p L a).getD a 0

/-- Modular coefficient `b_a` of `F_mu`. -/
def fCoeffMod (p : Nat) [Fact p.Prime] (μ : List Nat) (a : Nat) : ZMod p :=
  expCoeffMod p (fun r => -hCoeffMod p μ r) a

/-- Modular coefficient of `K_mu(t)`. -/
def kCoeffMod (p : Nat) [Fact p.Prime] (μ : List Nat) : Nat → ZMod p
  | 0 => 0
  | 1 => 2 * markedWeightMod p μ 1
  | r + 2 =>
      12 * ((r + 1 : Nat) : ZMod p) * (Prop51.c (r + 1) : ZMod p) *
        markedWeightMod p μ (r + 2)

/-- Corrected coefficient in the modular one-pass recurrence. -/
def correctedCoeffMod (p : Nat) [Fact p.Prime] (a : Nat) (μ : List Nat) : ZMod p :=
  (M a : ZMod p) * fCoeffMod p μ a -
    ((List.range a).map fun k : Nat =>
      kCoeffMod p μ (k + 1) * fCoeffMod p μ (a - (k + 1))).sum

/-- First prime used by the corrected finite certificate bundle. -/
def finitePrime1 : Nat := 1000000007

instance finitePrime1Fact : Fact finitePrime1.Prime :=
  ⟨by native_decide⟩

/-- Small anchor: the modular recurrence sees the corrected `g = 4`,
`μ=(1^6)` coefficient as nonzero at the first certificate prime. -/
theorem correctedCoeffMod_anchor :
    correctedCoeffMod finitePrime1 2 [1, 1, 1, 1, 1, 1] ≠ 0 := by
  native_decide

end Prop52
