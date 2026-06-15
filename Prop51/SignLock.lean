/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Sign-lock setup (paper §5)

This file starts the formalization of the sign-lock argument.  The present
layer is deliberately algebraic: it splits the linear `c_1 X` term out of
`B_m(N) = [X^m] C(X)^{-N}` and rewrites the coefficient as a finite sum of
the nonlinear coefficients `Eminus`.

The later error-budget files can estimate this finite decomposition without
re-proving power-series algebra.
-/

import Prop51.Envelope

namespace Prop51

open PowerSeries

/-! ## Basic normalized quantities -/

/-- The rational parameter `ζ = 5N/(36m)` from paper §5.  It is only used
under hypotheses `m > 0`; at `m = 0` it is the harmless rational expression
with zero denominator convention from `ℚ`. -/
def zetaQ (N m : Nat) : ℚ := 5 * (N : ℚ) / (36 * (m : ℚ))

/-- The normalized coefficient `X_m(N) = B_m(N)/(N c_m)`. -/
def Xnorm (N m : Nat) : ℚ := Bq N m / ((N : ℚ) * c m)

/-- The paper's factor
`Π_s = m^s (m-s-1)!/(m-1)! = ∏_{i=1}^s (1-i/m)^{-1}`,
used only when `s < m`. -/
def PiFactor (m s : Nat) : ℚ :=
  (m : ℚ)^s * (((m-s-1).factorial : Nat) : ℚ) / (((m-1).factorial : Nat) : ℚ)

/-- The `d`-ratio `D_s = d_{m-s}/d_m`. -/
def DFactor (m s : Nat) : ℚ := d (m-s) / d m

/-- The normalized nonlinear coefficient `-E^-_p(N)/(N c_p)`. -/
def EminusNorm (N p : Nat) : ℚ := -(Eminus (N : ℚ) p) / ((N : ℚ) * c p)

/-! ## Splitting off the linear exponential -/

/-- The sequence with a single nonzero logarithmic coefficient in degree `1`. -/
def linearExpSeq (a : ℚ) : Nat → ℚ := fun r => if r = 1 then a else 0

private theorem linearExpSeq_zero (a : ℚ) : linearExpSeq a 0 = 0 := by
  simp [linearExpSeq]

private theorem linearExpSeq_mul (a b : ℚ) (r : Nat) :
    linearExpSeq (a * b) r = a * linearExpSeq b r := by
  by_cases h : r = 1
  · simp [linearExpSeq, h]
  · simp [linearExpSeq, h]

/-- Coefficients of `exp(aX)`. -/
theorem expCoeff_linearExpSeq (a : ℚ) (n : Nat) :
    expCoeff (linearExpSeq a) n = a^n / (n.factorial : ℚ) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hrec := expCoeff_succ_mul (linearExpSeq a) n
      have hsum :
          (∑ t ∈ Finset.range (n+1),
              ((t+1 : Nat) : ℚ) * linearExpSeq a (t+1) *
                expCoeff (linearExpSeq a) (n-t))
            = a * expCoeff (linearExpSeq a) n := by
        rw [Finset.sum_eq_single 0]
        · simp [linearExpSeq]
        · intro t ht ht0
          have hlin : linearExpSeq a (t+1) = 0 := by
            unfold linearExpSeq
            rw [if_neg]
            omega
          rw [hlin]
          ring
        · intro h0
          exact False.elim (h0 (by simp))
      rw [hsum] at hrec
      have hnz : ((n+1 : Nat) : ℚ) ≠ 0 := by positivity
      have hstep :
          expCoeff (linearExpSeq a) (n+1)
            = (a * expCoeff (linearExpSeq a) n) / ((n+1 : Nat) : ℚ) := by
        rw [eq_div_iff hnz]
        rw [mul_comm]
        exact hrec
      rw [hstep, ih]
      have hfac : (((n+1).factorial : Nat) : ℚ)
          = ((n+1 : Nat) : ℚ) * (n.factorial : ℚ) := by
        norm_num [Nat.factorial_succ]
      rw [hfac]
      field_simp [hnz]
      ring

private theorem c_eq_linear_add_Hcoef (r : Nat) :
    c r = linearExpSeq (c 1) r + Hcoef r := by
  cases r with
  | zero =>
      simp [linearExpSeq, Hcoef]
  | succ r =>
      cases r with
      | zero =>
          simp [linearExpSeq, Hcoef]
      | succ r =>
          simp [linearExpSeq, Hcoef]

private theorem BSeriesQ_eq_linear_mul_EminusSeries (N : Nat) :
    BSeriesQ N =
      expSeries (linearExpSeq (-(N : ℚ) * c 1)) *
        expSeries (fun r => -(N : ℚ) * Hcoef r) := by
  unfold BSeriesQ
  rw [expSeries_mul]
  congr 1
  funext r
  rw [linearExpSeq_mul]
  rw [c_eq_linear_add_Hcoef r]
  ring

/-- Finite decomposition of `B_m(N)` into the linear exponential and the
nonlinear coefficients `Eminus`. -/
theorem Bq_eq_linear_Eminus_sum (N m : Nat) :
    Bq N m =
      ∑ s ∈ Finset.range (m+1),
        ((-(N : ℚ) * c 1)^s / (s.factorial : ℚ)) *
          Eminus (N : ℚ) (m-s) := by
  have hcoeff := congrArg (fun F : ℚ⟦X⟧ => coeff m F)
    (BSeriesQ_eq_linear_mul_EminusSeries N)
  change coeff m (BSeriesQ N) =
    coeff m (expSeries (linearExpSeq (-(N : ℚ) * c 1)) *
      expSeries (fun r => -(N : ℚ) * Hcoef r)) at hcoeff
  rw [coeff_BSeriesQ, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hcoeff
  simpa [Eminus, expCoeff_linearExpSeq] using hcoeff

/-- Finite decomposition of `-X_m(N)` in the form used by the sign-lock
argument. -/
theorem neg_Xnorm_eq_linear_Eminus_sum (N m : Nat) :
    -Xnorm N m =
      ∑ s ∈ Finset.range (m+1),
        ((-(N : ℚ) * c 1)^s / (s.factorial : ℚ)) *
          (-(Eminus (N : ℚ) (m-s)) / ((N : ℚ) * c m)) := by
  unfold Xnorm
  rw [Bq_eq_linear_Eminus_sum]
  calc
    -((∑ s ∈ Finset.range (m+1),
        ((-(N : ℚ) * c 1)^s / (s.factorial : ℚ)) *
          Eminus (N : ℚ) (m-s)) / ((N : ℚ) * c m))
        =
          (∑ s ∈ Finset.range (m+1),
            ((-(N : ℚ) * c 1)^s / (s.factorial : ℚ)) *
              Eminus (N : ℚ) (m-s)) * (-(1 / ((N : ℚ) * c m))) := by
            ring
    _ = ∑ s ∈ Finset.range (m+1),
          (((-(N : ℚ) * c 1)^s / (s.factorial : ℚ)) *
            Eminus (N : ℚ) (m-s)) * (-(1 / ((N : ℚ) * c m))) := by
          rw [Finset.sum_mul]
    _ = ∑ s ∈ Finset.range (m+1),
          ((-(N : ℚ) * c 1)^s / (s.factorial : ℚ)) *
            (-(Eminus (N : ℚ) (m-s)) / ((N : ℚ) * c m)) := by
          refine Finset.sum_congr rfl fun s hs => ?_
          ring

/-! ## The `Π_s D_s` summand factorization -/

/-- Each non-boundary summand of the finite decomposition has the paper's
`(-ζ)^s/s! · Π_s · D_s · (-E^-_{m-s}/(N c_{m-s}))` form. -/
theorem signLock_summand_factor (N m s : Nat) (hN : 1 ≤ N) (hs : s < m) :
    ((-(N : ℚ) * c 1)^s / (s.factorial : ℚ)) *
        (-(Eminus (N : ℚ) (m-s)) / ((N : ℚ) * c m))
      =
    ((-zetaQ N m)^s / (s.factorial : ℚ)) *
        PiFactor m s * DFactor m s * EminusNorm N (m-s) := by
  have hm : 1 ≤ m := by omega
  have hp : 1 ≤ m - s := by omega
  have hNq : ((N : ℚ) ≠ 0) := by
    exact_mod_cast (by omega : N ≠ 0)
  have hm_q : ((m : ℚ) ≠ 0) := by
    exact_mod_cast (by omega : m ≠ 0)
  have hdm : d m ≠ 0 := (d_pos m hm).ne'
  have hdp : d (m-s) ≠ 0 := (d_pos (m-s) hp).ne'
  have hcm : c m ≠ 0 := (c_pos m hm).ne'
  have hcp : c (m-s) ≠ 0 := (c_pos (m-s) hp).ne'
  have hfac_s : ((s.factorial : Nat) : ℚ) ≠ 0 := by positivity
  have hfac_m : ((((m-1).factorial : Nat) : ℚ)) ≠ 0 := by positivity
  have hfac_p : ((((m-s-1).factorial : Nat) : ℚ)) ≠ 0 := by positivity
  have hm_decomp : m = (m-s) + s := by omega
  have hpow6 : (6 : ℚ)^m = (6 : ℚ)^(m-s) * (6 : ℚ)^s := by
    calc
      (6 : ℚ)^m = (6 : ℚ)^((m-s) + s) := congrArg (fun n : Nat => (6 : ℚ)^n) hm_decomp
      _ = (6 : ℚ)^(m-s) * (6 : ℚ)^s := by rw [pow_add]
  unfold zetaQ PiFactor DFactor EminusNorm
  rw [c_one, c_eq_d m, c_eq_d (m-s)]
  rw [hpow6]
  field_simp [hNq, hm_q, hdm, hdp, hcm, hcp, hfac_s, hfac_m, hfac_p]
  ring_nf
  have hm_pow : (m : ℚ)^s * ((m : ℚ)⁻¹)^s = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hm_q, one_pow]
  have hconst : ((-5 / 36 : ℚ)^s) * (6 : ℚ)^s = (-5 / 6 : ℚ)^s := by
    rw [← mul_pow]
    norm_num
  calc
    -(↑N ^ s * Eminus (↑N) (m - s) * (-5 / 6 : ℚ)^s)
        =
      -(↑N ^ s * Eminus (↑N) (m - s) *
          (((m : ℚ)^s * ((m : ℚ)⁻¹)^s) * (((-5 / 36 : ℚ)^s) * (6 : ℚ)^s))) := by
        rw [hm_pow, hconst]
        ring
    _ =
      -(↑N ^ s * Eminus (↑N) (m - s) * (m : ℚ)^s *
          ((m : ℚ)⁻¹)^s * (-5 / 36 : ℚ)^s * (6 : ℚ)^s) := by
        ring

end Prop51
