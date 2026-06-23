/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# One-pass recurrence for the corrected Proposition 5.2 coefficient

The public definition in `Prop52.Statement` is written in terms of
`Prop51.bCoeff` and the marked convolution.  This file records the equivalent
one-pass recurrence used by the corrected finite certificates:

* `s_r = sum_i q_i^{-r}`;
* `w_r = sum_i (q_i-1) q_i^{-r}`;
* `h_r = c_r (N-s_r)`;
* `F_mu(t) = exp(-sum h_r t^r) = sum b_r t^r`;
* `k_1 = 2w_1`, `k_r = 12(r-1)c_{r-1}w_r` for `r >= 2`;
* `T = M b_a - sum_{j=1}^a k_j b_{a-j}`.

The final theorem `correctedCoeffFast_eq` is the bridge from this executable
certificate recurrence back to the statement-level coefficient.
-/

import Prop52.Theorem

namespace Prop52

/-- `s_r = sum_i q_i^{-r}`, with `q_i = m_i+1`. -/
def sPower (μ : List Nat) (r : Nat) : ℚ :=
  (μ.map fun mi : Nat => 1 / ((mi + 1 : Nat) : ℚ)^r).sum

/-- `D_r = N - s_r`, in the notation of the corrected finite certificate. -/
theorem Dr_eq_N_sub_sPower (μ : List Nat) (r : Nat) :
    Prop51.Dr μ r = (N μ : ℚ) - sPower μ r := by
  induction μ with
  | nil =>
      simp [Prop51.Dr, N, sPower]
  | cons mi μ ih =>
      simp only [Prop51.Dr, N, sPower, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      push_cast
      ring

/-- `h_r = c_r (N-s_r)`. -/
def hCoeff (μ : List Nat) (r : Nat) : ℚ :=
  Prop51.c r * ((N μ : ℚ) - sPower μ r)

/-- The coefficient `b_r` of `F_mu(t) = exp(-sum h_r t^r)`. -/
def fCoeff (μ : List Nat) (a : Nat) : ℚ :=
  Prop51.expCoeff (fun r => -hCoeff μ r) a

/-- The one-pass recurrence computes the same `F_mu` coefficients as
`Prop51.bCoeff`. -/
theorem bCoeff_eq_fCoeff (μ : List Nat) (a : Nat) :
    Prop51.bCoeff μ a = fCoeff μ a := by
  rw [Prop51.bCoeff_eq_expCoeff]
  unfold fCoeff hCoeff
  congr 1
  funext r
  rw [Dr_eq_N_sub_sPower]
  ring

/-- The coefficient `k_r` of `K_mu(t) = sum_i (q_i-1) Phi(t/q_i)`. -/
def kCoeff (μ : List Nat) : Nat → ℚ
  | 0 => 0
  | 1 => 2 * markedWeight μ 1
  | r + 2 => 12 * ((r + 1 : Nat) : ℚ) * Prop51.c (r + 1) * markedWeight μ (r + 2)

theorem kCoeff_eq_markedCoeff (μ : List Nat) (r : Nat) :
    kCoeff μ r = markedCoeff μ r := by
  cases r with
  | zero =>
      simp [kCoeff, markedCoeff, phiCoeff]
  | succ r =>
      cases r with
      | zero =>
          simp [kCoeff, markedCoeff, phiCoeff]
      | succ r =>
          simp [kCoeff, markedCoeff, phiCoeff]

/-- Corrected coefficient in the one-pass recurrence form used by the finite
certificate programs. -/
def correctedCoeffFast (a : Nat) (μ : List Nat) : ℚ :=
  (M a : ℚ) * fCoeff μ a -
    ((List.range a).map fun k : Nat =>
      kCoeff μ (k + 1) * fCoeff μ (a - (k + 1))).sum

/-- The one-pass recurrence is exactly the statement-level corrected
coefficient. -/
theorem correctedCoeffFast_eq (a : Nat) (μ : List Nat) :
    correctedCoeffFast a μ = correctedCoeff a μ := by
  unfold correctedCoeffFast correctedCoeff markedConvolution
  rw [← bCoeff_eq_fCoeff μ a]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun k _hk => ?_)
  rw [kCoeff_eq_markedCoeff, ← bCoeff_eq_fCoeff μ (a - (k + 1))]

end Prop52
