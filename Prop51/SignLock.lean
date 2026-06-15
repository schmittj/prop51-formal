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

/-- The sign-lock nonlinear residual `ε_p`, defined by
`E^-_p(N) = -N c_p (1+ε_p)`. -/
def epsilonMinus (N p : Nat) : ℚ := EminusNorm N p - 1

/-- `e_1(s)=s(s+1)/2`, the first correction in the `Π_s` expansion. -/
def eOne (s : Nat) : ℚ := (s : ℚ) * ((s+1 : Nat) : ℚ) / 2

/-- The pointwise sign-lock error `w_s` from paper §5. -/
def signLockErrorW (N m s : Nat) : ℚ :=
  PiFactor m s * DFactor m s * (1 + epsilonMinus N (m-s))
    - 1 - eOne s / (m : ℚ) + zetaQ N m / (m : ℚ)

/-- By definition, the normalized nonlinear coefficient is `1+ε_p`. -/
theorem EminusNorm_eq_one_add_epsilonMinus (N p : Nat) :
    EminusNorm N p = 1 + epsilonMinus N p := by
  unfold epsilonMinus
  ring

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

/-- The same summand factorization, with the nonlinear coefficient written as
`1 + ε_{m-s}`. -/
theorem signLock_summand_factor_epsilon
    (N m s : Nat) (hN : 1 ≤ N) (hs : s < m) :
    ((-(N : ℚ) * c 1)^s / (s.factorial : ℚ)) *
        (-(Eminus (N : ℚ) (m-s)) / ((N : ℚ) * c m))
      =
    ((-zetaQ N m)^s / (s.factorial : ℚ)) *
        PiFactor m s * DFactor m s * (1 + epsilonMinus N (m-s)) := by
  rw [signLock_summand_factor N m s hN hs,
    EminusNorm_eq_one_add_epsilonMinus]

private theorem epsilonMinus_eq_envelope_residual (N p : Nat) :
    epsilonMinus N p =
      Eminus (N : ℚ) p / (-(N : ℚ) * c p) - 1 := by
  unfold epsilonMinus EminusNorm
  ring

/-- The completed Δ-envelope translated into sign-lock `ε_p` notation. -/
theorem abs_epsilonMinus_le_final {N m p : Nat}
    (hN : 1 ≤ N) (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ))
    (hm : 361 ≤ m) (hpm : 2*m ≤ 3*p) :
    |epsilonMinus N p| ≤ (66/5) / (m : ℚ) := by
  have hNpos : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  rw [epsilonMinus_eq_envelope_residual]
  exact Eminus_normalized_residual_le_final (p := p) (m := m)
    (N := (N : ℚ)) hNpos hN40 hm hpm

/-- Near-range version used in the P1--P4 audit: if `s≤m/3`, then
`p=m-s` is in the Δ-envelope range. -/
theorem abs_epsilonMinus_le_final_of_three_mul_le
    {N m s : Nat} (hN : 1 ≤ N)
    (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ))
    (hm : 361 ≤ m) (hs : 3*s ≤ m) :
    |epsilonMinus N (m-s)| ≤ (66/5) / (m : ℚ) := by
  apply abs_epsilonMinus_le_final hN hN40 hm
  omega

/-! ## Rational Poisson moment bounds -/

/-- Closed-form upper surrogate for finite exponential sums, using the
partial-exp majorant from `ExpBounds.lean`. -/
def partialExpUpper (y : ℚ) (T₀ : Nat) : ℚ :=
  (∑ t ∈ Finset.range T₀, y^t / (t.factorial : ℚ))
    + (y^T₀ / (T₀.factorial : ℚ)) * (1 / (1 - y/(T₀ : ℚ)))

theorem poissonFirst_sum_range (y : ℚ) :
    ∀ T : Nat,
      (∑ s ∈ Finset.range T, (s : ℚ) * y^s / (s.factorial : ℚ))
        = y * ∑ t ∈ Finset.range (T-1), y^t / (t.factorial : ℚ)
  | 0 => by simp
  | T+1 => by
      cases T with
      | zero =>
          simp
      | succ T =>
          rw [Finset.sum_range_succ, poissonFirst_sum_range y (T+1)]
          rw [show T+1+1-1 = T+1 by omega, Finset.sum_range_succ, mul_add]
          congr 1
          have hfac : ((((T+1).factorial : Nat) : ℚ))
              = ((T+1 : Nat) : ℚ) * (T.factorial : ℚ) := by
            norm_num [Nat.factorial_succ]
          rw [hfac, pow_succ]
          field_simp [show ((T+1 : Nat) : ℚ) ≠ 0 by positivity,
            show ((T.factorial : Nat) : ℚ) ≠ 0 by positivity]

theorem poissonFallingSecond_sum_range (y : ℚ) :
    ∀ T : Nat,
      (∑ s ∈ Finset.range T,
          (s : ℚ) * ((s-1 : Nat) : ℚ) * y^s / (s.factorial : ℚ))
        = y^2 * ∑ t ∈ Finset.range (T-2), y^t / (t.factorial : ℚ)
  | 0 => by simp
  | 1 => by simp
  | T+2 => by
      cases T with
      | zero =>
          norm_num [Finset.sum_range_succ]
      | succ T =>
          rw [Finset.sum_range_succ, poissonFallingSecond_sum_range y (T+2)]
          rw [show T+1+2-2 = T+1 by omega, Finset.sum_range_succ, mul_add]
          congr 1
          have hfac1 : (((T+1+1).factorial : Nat) : ℚ)
              = ((T+1+1 : Nat) : ℚ) * ((T+1).factorial : ℚ) := by
            norm_num [Nat.factorial_succ]
          have hfac2 : (((T+1).factorial : Nat) : ℚ)
              = ((T+1 : Nat) : ℚ) * (T.factorial : ℚ) := by
            norm_num [Nat.factorial_succ]
          rw [hfac1, hfac2, pow_succ, pow_succ]
          field_simp [show ((T+1+1 : Nat) : ℚ) ≠ 0 by positivity,
            show ((T+1 : Nat) : ℚ) ≠ 0 by positivity,
            show ((T.factorial : Nat) : ℚ) ≠ 0 by positivity]
          rw [show T + 2 - 1 = T + 1 by omega]
          ring

private theorem sq_eq_falling_add (s : Nat) :
    (s : ℚ)^2 = (s : ℚ) * ((s-1 : Nat) : ℚ) + (s : ℚ) := by
  cases s with
  | zero =>
      norm_num
  | succ s =>
      simp
      ring

theorem poissonFirst_sum_le_partialExpUpper
    (y : ℚ) (T₀ T : Nat) (hy : 0 ≤ y) (hyT : y < (T₀ : ℚ)) :
    ∑ s ∈ Finset.range T, (s : ℚ) * y^s / (s.factorial : ℚ)
      ≤ y * partialExpUpper y T₀ := by
  rw [poissonFirst_sum_range]
  exact mul_le_mul_of_nonneg_left
    (sum_exp_le y T₀ hy hyT (T-1)) hy

theorem poissonSecond_sum_le_partialExpUpper
    (y : ℚ) (T₀ T : Nat) (hy : 0 ≤ y) (hyT : y < (T₀ : ℚ)) :
    ∑ s ∈ Finset.range T, (s : ℚ)^2 * y^s / (s.factorial : ℚ)
      ≤ (y^2 + y) * partialExpUpper y T₀ := by
  have hsplit :
      (∑ s ∈ Finset.range T, (s : ℚ)^2 * y^s / (s.factorial : ℚ))
        =
      (∑ s ∈ Finset.range T,
          ((s : ℚ) * ((s-1 : Nat) : ℚ)) * y^s / (s.factorial : ℚ))
        + ∑ s ∈ Finset.range T, (s : ℚ) * y^s / (s.factorial : ℚ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [sq_eq_falling_add s]
    ring
  rw [hsplit]
  have hfall :
      (∑ s ∈ Finset.range T,
          ((s : ℚ) * ((s-1 : Nat) : ℚ)) * y^s / (s.factorial : ℚ))
        = y^2 * ∑ t ∈ Finset.range (T-2), y^t / (t.factorial : ℚ) := by
    simpa [mul_assoc] using poissonFallingSecond_sum_range y T
  rw [hfall, poissonFirst_sum_range]
  have h2 := sum_exp_le y T₀ hy hyT (T-2)
  have h1 := sum_exp_le y T₀ hy hyT (T-1)
  calc
    y^2 * (∑ t ∈ Finset.range (T-2), y^t / (t.factorial : ℚ))
        + y * (∑ t ∈ Finset.range (T-1), y^t / (t.factorial : ℚ))
      ≤ y^2 * partialExpUpper y T₀ + y * partialExpUpper y T₀ := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left h2 (sq_nonneg y))
            (mul_le_mul_of_nonneg_left h1 hy)
    _ = (y^2 + y) * partialExpUpper y T₀ := by ring

/-- The endpoint `ζ` used throughout §5. -/
def zetaMax : ℚ := 50/27

theorem poissonZero_sum_le_partialExpUpper
    (y : ℚ) (T₀ T : Nat) (hy : 0 ≤ y) (hyT : y < (T₀ : ℚ)) :
    ∑ s ∈ Finset.range T, y^s / (s.factorial : ℚ)
      ≤ partialExpUpper y T₀ :=
  sum_exp_le y T₀ hy hyT T

theorem poissonZero_zetaMax_le (T : Nat) :
    ∑ s ∈ Finset.range T, zetaMax^s / (s.factorial : ℚ) ≤ 32/5 := by
  calc
    ∑ s ∈ Finset.range T, zetaMax^s / (s.factorial : ℚ)
        ≤ partialExpUpper zetaMax 18 :=
          poissonZero_sum_le_partialExpUpper zetaMax 18 T (by norm_num [zetaMax])
            (by norm_num [zetaMax])
    _ ≤ 32/5 := by
          norm_num [zetaMax, partialExpUpper, Finset.sum_range_succ, Nat.factorial]

theorem poissonZero_zetaMax_le_tight (T : Nat) :
    ∑ s ∈ Finset.range T, zetaMax^s / (s.factorial : ℚ) ≤ 319/50 := by
  calc
    ∑ s ∈ Finset.range T, zetaMax^s / (s.factorial : ℚ)
        ≤ partialExpUpper zetaMax 18 :=
          poissonZero_sum_le_partialExpUpper zetaMax 18 T (by norm_num [zetaMax])
            (by norm_num [zetaMax])
    _ ≤ 319/50 := by
          norm_num [zetaMax, partialExpUpper, Finset.sum_range_succ, Nat.factorial]

theorem poissonFirst_zetaMax_le (T : Nat) :
    ∑ s ∈ Finset.range T, (s : ℚ) * zetaMax^s / (s.factorial : ℚ) ≤ 12 := by
  calc
    ∑ s ∈ Finset.range T, (s : ℚ) * zetaMax^s / (s.factorial : ℚ)
        ≤ zetaMax * partialExpUpper zetaMax 18 :=
          poissonFirst_sum_le_partialExpUpper zetaMax 18 T (by norm_num [zetaMax])
            (by norm_num [zetaMax])
    _ ≤ 12 := by
          norm_num [zetaMax, partialExpUpper, Finset.sum_range_succ, Nat.factorial]

theorem poissonFirst_zetaMax_le_sharp (T : Nat) :
    ∑ s ∈ Finset.range T, (s : ℚ) * zetaMax^s / (s.factorial : ℚ) ≤ 59/5 := by
  calc
    ∑ s ∈ Finset.range T, (s : ℚ) * zetaMax^s / (s.factorial : ℚ)
        ≤ zetaMax * partialExpUpper zetaMax 18 :=
          poissonFirst_sum_le_partialExpUpper zetaMax 18 T (by norm_num [zetaMax])
            (by norm_num [zetaMax])
    _ ≤ 59/5 := by
          norm_num [zetaMax, partialExpUpper, Finset.sum_range_succ, Nat.factorial]

theorem poissonSecond_zetaMax_le (T : Nat) :
    ∑ s ∈ Finset.range T, (s : ℚ)^2 * zetaMax^s / (s.factorial : ℚ) ≤ 34 := by
  calc
    ∑ s ∈ Finset.range T, (s : ℚ)^2 * zetaMax^s / (s.factorial : ℚ)
        ≤ (zetaMax^2 + zetaMax) * partialExpUpper zetaMax 18 :=
          poissonSecond_sum_le_partialExpUpper zetaMax 18 T (by norm_num [zetaMax])
            (by norm_num [zetaMax])
    _ ≤ 34 := by
          norm_num [zetaMax, partialExpUpper, Finset.sum_range_succ, Nat.factorial]

/-! ## P2: `d`-drift budget -/

theorem one_sub_DFactor_le_quadratic
    {m s : Nat} (hm : 1 ≤ m) (hs : 3*s ≤ m) :
    1 - DFactor m s
      ≤ (2304/3125) *
          ((s : ℚ)/(m : ℚ)^2 + 2*(s : ℚ)^2/(m : ℚ)^3) := by
  have hslt : s < m := by
    rcases s with rfl | s
    · omega
    · omega
  have hratio := d_ratio_lb m s hslt
  have hfirst :
      1 - DFactor m s
        ≤ (2304/3125) * ((s:ℚ) / ((m:ℚ) * ((m-s : Nat):ℚ))) := by
    unfold DFactor
    linarith
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  have hmspos : (0 : ℚ) < ((m-s : Nat) : ℚ) := by
    exact_mod_cast (by omega : 0 < m-s)
  have hquad :
      (s:ℚ) / ((m:ℚ) * ((m-s : Nat):ℚ))
        ≤ (s : ℚ)/(m : ℚ)^2 + 2*(s : ℚ)^2/(m : ℚ)^3 := by
    have hms_cast : ((m-s : Nat) : ℚ) = (m : ℚ) - (s : ℚ) := by
      rw [Nat.cast_sub hslt.le]
    rw [hms_cast]
    have hs_nonneg : (0 : ℚ) ≤ s := by positivity
    have hm_two_s : (2 : ℚ) * s ≤ m := by exact_mod_cast (by omega : 2*s ≤ m)
    have hsubpos : (0 : ℚ) < (m : ℚ) - (s : ℚ) := by
      rw [← hms_cast]
      exact hmspos
    have hmain : (m : ℚ)^2 ≤ ((m : ℚ) + 2*(s : ℚ)) * ((m : ℚ) - (s : ℚ)) := by
      nlinarith [mul_nonneg hs_nonneg (sub_nonneg.mpr hm_two_s)]
    have hrecip :
        (1 : ℚ) / ((m : ℚ) * ((m : ℚ) - (s : ℚ)))
          ≤ ((m : ℚ) + 2*(s : ℚ)) / (m : ℚ)^3 := by
      field_simp [hmpos.ne', hsubpos.ne']
      nlinarith [hmain, mul_pos hmpos hmpos]
    have hmul := mul_le_mul_of_nonneg_left hrecip hs_nonneg
    convert hmul using 1
    · ring_nf
    · field_simp [hmpos.ne']
  exact hfirst.trans (mul_le_mul_of_nonneg_left hquad (by norm_num))

/-- P2 drift contribution with the rationalized `d` constants. -/
theorem signLock_P2_budget_zetaMax {m : Nat} (hm : 361 ≤ m) :
    ∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) * (1 - DFactor m s)
      ≤ 13 / (m : ℚ)^2 := by
  have hm1 : 1 ≤ m := by omega
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  have hpoint :
      ∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) * (1 - DFactor m s)
      ≤
      ∑ s ∈ Finset.range (m/3 + 1),
        (((2304/3125) / (m : ℚ)^2) *
            ((s : ℚ) * zetaMax^s / (s.factorial : ℚ))
          + ((2*(2304/3125)) / (m : ℚ)^3) *
            ((s : ℚ)^2 * zetaMax^s / (s.factorial : ℚ))) := by
    refine Finset.sum_le_sum fun s hs => ?_
    have hs3 : 3*s ≤ m := by
      have hsle : s ≤ m/3 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
      have hmul : 3*s ≤ 3*(m/3) := Nat.mul_le_mul_left 3 hsle
      have hdiv : 3*(m/3) ≤ m := by
        exact Nat.mul_div_le m 3
      exact hmul.trans hdiv
    have hquad := one_sub_DFactor_le_quadratic (m := m) (s := s) hm1 hs3
    have hweight : 0 ≤ zetaMax^s / (s.factorial : ℚ) := by
      have hz : 0 ≤ zetaMax := by norm_num [zetaMax]
      positivity
    calc
      (zetaMax^s / (s.factorial : ℚ)) * (1 - DFactor m s)
        ≤ (zetaMax^s / (s.factorial : ℚ)) *
            ((2304/3125) *
              ((s : ℚ)/(m : ℚ)^2 + 2*(s : ℚ)^2/(m : ℚ)^3)) :=
              mul_le_mul_of_nonneg_left hquad hweight
      _ =
          ((2304/3125) / (m : ℚ)^2) *
              ((s : ℚ) * zetaMax^s / (s.factorial : ℚ))
            + ((2*(2304/3125)) / (m : ℚ)^3) *
              ((s : ℚ)^2 * zetaMax^s / (s.factorial : ℚ)) := by
              ring
  calc
    ∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) * (1 - DFactor m s)
      ≤
      ∑ s ∈ Finset.range (m/3 + 1),
        (((2304/3125) / (m : ℚ)^2) *
            ((s : ℚ) * zetaMax^s / (s.factorial : ℚ))
          + ((2*(2304/3125)) / (m : ℚ)^3) *
            ((s : ℚ)^2 * zetaMax^s / (s.factorial : ℚ))) := hpoint
    _ =
      ((2304/3125) / (m : ℚ)^2) *
          (∑ s ∈ Finset.range (m/3 + 1),
            (s : ℚ) * zetaMax^s / (s.factorial : ℚ))
        + ((2*(2304/3125)) / (m : ℚ)^3) *
          (∑ s ∈ Finset.range (m/3 + 1),
            (s : ℚ)^2 * zetaMax^s / (s.factorial : ℚ)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤
      ((2304/3125) / (m : ℚ)^2) * 12
        + ((2*(2304/3125)) / (m : ℚ)^3) * 34 := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (poissonFirst_zetaMax_le _) (by positivity))
            (mul_le_mul_of_nonneg_left (poissonSecond_zetaMax_le _) (by positivity))
    _ ≤ 13 / (m : ℚ)^2 := by
          have hmQ : (361 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
          field_simp [hmpos.ne']
          nlinarith

/-! ## P3a: leading two-block recentering -/

/-- The endpoint part of the two-block nonlinear correction:
`5N/(36(p-1)(p-2)) * d_{p-2}/d_p`. -/
def twoEndpointCorrection (N p : Nat) : ℚ :=
  (5 * (N : ℚ)) / (36 * (((p-1 : Nat) : ℚ) * ((p-2 : Nat) : ℚ)))
    * DFactor p 2

/-- The extracted recentring term `5N/(36m²) = ζ/m`. -/
def twoEndpointTarget (N m : Nat) : ℚ :=
  (5 * (N : ℚ)) / (36 * (m : ℚ)^2)

theorem DFactor_nonneg (m s : Nat) : 0 ≤ DFactor m s := by
  unfold DFactor
  exact div_nonneg (d_nonneg (m-s)) (d_nonneg m)

theorem DFactor_le_one {m s : Nat} (hm : 1 ≤ m) :
    DFactor m s ≤ 1 := by
  have hdm : 0 < d m := d_pos m hm
  unfold DFactor
  rw [div_le_one₀ hdm]
  exact d_mono (Nat.sub_le m s)

theorem one_sub_DFactor_two_le {p : Nat} (hp : 3 ≤ p) :
    1 - DFactor p 2
      ≤ (2304/3125) * (2 / ((p : ℚ) * ((p-2 : Nat) : ℚ))) := by
  have hratio := d_ratio_lb p 2 (by omega : 2 < p)
  unfold DFactor
  linarith

private theorem abs_scaled_ratio_sub_le
    {C A M D : ℚ} (hC : 0 ≤ C) (hA : 0 < A) (hM : 0 < M)
    (hD1 : D ≤ 1) (hAM : A ≤ M) :
    |C * (D / A - 1 / M)|
      ≤ C * ((1 - D) / A + (M - A) / (A * M)) := by
  rw [abs_mul, abs_of_nonneg hC]
  apply mul_le_mul_of_nonneg_left ?_ hC
  calc
    |D / A - 1 / M|
        = |(D / A - 1 / A) + (1 / A - 1 / M)| := by
            congr 1
            ring
    _ ≤ |D / A - 1 / A| + |1 / A - 1 / M| := abs_add_le _ _
    _ = (1 - D) / A + (M - A) / (A * M) := by
        have h1D : 0 ≤ 1 - D := by linarith
        have hMA : 0 ≤ M - A := by linarith
        have hAMpos : 0 < A * M := mul_pos hA hM
        rw [show D / A - 1 / A = -((1 - D) / A) by ring]
        rw [abs_neg, abs_of_nonneg (div_nonneg h1D hA.le)]
        rw [show 1 / A - 1 / M = (M - A) / (A * M) by
          field_simp [hA.ne', hM.ne']]
        rw [abs_of_nonneg (div_nonneg hMA hAMpos.le)]

private theorem cast_sub_one (p : Nat) (hp : 1 ≤ p) :
    (((p-1 : Nat) : ℚ)) = (p : ℚ) - 1 := by
  rw [Nat.cast_sub hp]
  norm_num

private theorem cast_sub_two (p : Nat) (hp : 2 ≤ p) :
    (((p-2 : Nat) : ℚ)) = (p : ℚ) - 2 := by
  rw [Nat.cast_sub hp]
  norm_num

private theorem near_p_lower {m s : Nat} (hs : 3*s ≤ m) :
    (2 : ℚ) * (m : ℚ) / 3 ≤ ((m-s : Nat) : ℚ) := by
  rw [Nat.cast_sub (by omega : s ≤ m)]
  have hsQ : (3 : ℚ) * (s : ℚ) ≤ (m : ℚ) := by exact_mod_cast hs
  linarith

private theorem near_p_sub_one_half {m s : Nat} (hm : 361 ≤ m) (hs : 3*s ≤ m) :
    (m : ℚ) / 2 ≤ (((m-s-1 : Nat) : ℚ)) := by
  have hp : 1 ≤ m-s := by omega
  rw [cast_sub_one (m-s) hp]
  have hplower := near_p_lower (m := m) (s := s) hs
  have hmQ : (361 : ℚ) ≤ m := by exact_mod_cast hm
  nlinarith

private theorem near_p_sub_two_half {m s : Nat} (hm : 361 ≤ m) (hs : 3*s ≤ m) :
    (m : ℚ) / 2 ≤ (((m-s-2 : Nat) : ℚ)) := by
  have hp : 2 ≤ m-s := by omega
  rw [cast_sub_two (m-s) hp]
  have hplower := near_p_lower (m := m) (s := s) hs
  have hmQ : (361 : ℚ) ≤ m := by exact_mod_cast hm
  nlinarith

private theorem near_endpoint_denominator_lower
    {m s : Nat} (hm : 361 ≤ m) (hs : 3*s ≤ m) :
    (87/200) * (m : ℚ)^2
      ≤ (((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ)) := by
  have hp1 : 1 ≤ m-s := by omega
  have hp2 : 2 ≤ m-s := by omega
  rw [cast_sub_one (m-s) hp1, cast_sub_two (m-s) hp2]
  have hplower := near_p_lower (m := m) (s := s) hs
  have hmQ : (361 : ℚ) ≤ m := by exact_mod_cast hm
  nlinarith

private theorem near_endpoint_denominator_change
    {m s : Nat} (hm : 361 ≤ m) (hs : 3*s ≤ m) :
    (m : ℚ)^2 - (((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ))
      ≤ (2*(s : ℚ) + 3) * (m : ℚ) := by
  have hp1 : 1 ≤ m-s := by omega
  have hp2 : 2 ≤ m-s := by omega
  rw [cast_sub_one (m-s) hp1, cast_sub_two (m-s) hp2,
    Nat.cast_sub (by omega : s ≤ m)]
  nlinarith [show (0 : ℚ) ≤ m by positivity]

theorem twoEndpointCorrection_abs_le_split
    {N m s : Nat} (hm : 361 ≤ m) (hs : 3*s ≤ m) :
    |twoEndpointCorrection N (m-s) - twoEndpointTarget N m|
      ≤ (5 * (N : ℚ)) / 36 *
          ((1 - DFactor (m-s) 2)
              / ((((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ)))
            + (((m : ℚ)^2
                - (((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ)))
              / (((((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ))) * (m : ℚ)^2))) := by
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  have hp1pos : (0 : ℚ) < (((m-s-1 : Nat) : ℚ)) := by
    exact_mod_cast (by omega : 0 < m-s-1)
  have hp2pos : (0 : ℚ) < (((m-s-2 : Nat) : ℚ)) := by
    exact_mod_cast (by omega : 0 < m-s-2)
  have hApos : 0 < (((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ)) :=
    mul_pos hp1pos hp2pos
  have hMpos : 0 < (m : ℚ)^2 := sq_pos_of_ne_zero hmpos.ne'
  have hD1 : DFactor (m-s) 2 ≤ 1 :=
    DFactor_le_one (m := m-s) (s := 2) (by omega)
  have hAM :
      (((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ)) ≤ (m : ℚ)^2 := by
    have hp1_le : (((m-s-1 : Nat) : ℚ)) ≤ (m : ℚ) := by
      exact_mod_cast (by omega : m-s-1 ≤ m)
    have hp2_le : (((m-s-2 : Nat) : ℚ)) ≤ (m : ℚ) := by
      exact_mod_cast (by omega : m-s-2 ≤ m)
    have hmul := mul_le_mul hp1_le hp2_le hp2pos.le hmpos.le
    simpa [pow_two] using hmul
  have hsplit := abs_scaled_ratio_sub_le
    (C := (5 * (N : ℚ)) / 36)
    (A := (((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ)))
    (M := (m : ℚ)^2)
    (D := DFactor (m-s) 2)
    (by positivity) hApos hMpos hD1 hAM
  have hrewrite :
      twoEndpointCorrection N (m-s) - twoEndpointTarget N m
        =
      (5 * (N : ℚ)) / 36 *
        (DFactor (m-s) 2
            / ((((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ)))
          - 1 / (m : ℚ)^2) := by
    unfold twoEndpointCorrection twoEndpointTarget
    field_simp [show (36 : ℚ) ≠ 0 by norm_num,
      hApos.ne', hMpos.ne']
  rw [hrewrite]
  exact hsplit

theorem twoEndpoint_denominator_change_P3a
    {N m s : Nat} (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ))
    (hm : 361 ≤ m) (hs : 3*s ≤ m) :
    (5 * (N : ℚ)) / 36 *
      ((((m : ℚ)^2
          - (((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ)))
        / (((((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ))) * (m : ℚ)^2)))
      ≤ (213/50) * (2*(s : ℚ) + 3) / (m : ℚ)^2 := by
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  have hp1pos : (0 : ℚ) < (((m-s-1 : Nat) : ℚ)) := by
    exact_mod_cast (by omega : 0 < m-s-1)
  have hp2pos : (0 : ℚ) < (((m-s-2 : Nat) : ℚ)) := by
    exact_mod_cast (by omega : 0 < m-s-2)
  have hApos : 0 < (((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ)) :=
    mul_pos hp1pos hp2pos
  have hMpos : 0 < (m : ℚ)^2 := sq_pos_of_ne_zero hmpos.ne'
  have hC : (5 * (N : ℚ)) / 36 ≤ (50/27) * (m : ℚ) := by
    nlinarith
  have hden := near_endpoint_denominator_lower (m := m) (s := s) hm hs
  have hchange := near_endpoint_denominator_change (m := m) (s := s) hm hs
  have hnum_nonneg :
      0 ≤ (m : ℚ)^2
          - (((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ)) := by
    have hp1_le : (((m-s-1 : Nat) : ℚ)) ≤ (m : ℚ) := by
      exact_mod_cast (by omega : m-s-1 ≤ m)
    have hp2_le : (((m-s-2 : Nat) : ℚ)) ≤ (m : ℚ) := by
      exact_mod_cast (by omega : m-s-2 ≤ m)
    have hmul := mul_le_mul hp1_le hp2_le hp2pos.le hmpos.le
    nlinarith [show (((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ)) ≤ (m : ℚ)^2 by
      simpa [pow_two] using hmul]
  calc
    (5 * (N : ℚ)) / 36 *
      ((((m : ℚ)^2
          - (((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ)))
        / (((((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ))) * (m : ℚ)^2)))
      ≤ (50/27) * (m : ℚ) *
        (((2*(s : ℚ) + 3) * (m : ℚ)) /
          (((87/200) * (m : ℚ)^2) * (m : ℚ)^2)) := by
        refine mul_le_mul hC ?_ (div_nonneg hnum_nonneg (mul_pos hApos hMpos).le)
          (by positivity)
        have hbound_nonneg : 0 ≤ (2*(s : ℚ) + 3) * (m : ℚ) := by positivity
        have hden_actual_pos :
            0 < ((((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ))) * (m : ℚ)^2 :=
          mul_pos hApos hMpos
        have hden_lower_pos :
            0 < (((87/200) * (m : ℚ)^2) * (m : ℚ)^2) :=
          mul_pos (mul_pos (by norm_num) hMpos) hMpos
        calc
          (((m : ℚ)^2
              - (((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ)))
            / (((((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ))) * (m : ℚ)^2))
            ≤ (((2*(s : ℚ) + 3) * (m : ℚ))
                / (((((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ))) * (m : ℚ)^2)) :=
                div_le_div_of_nonneg_right hchange hden_actual_pos.le
          _ ≤ (((2*(s : ℚ) + 3) * (m : ℚ)) /
                (((87/200) * (m : ℚ)^2) * (m : ℚ)^2)) := by
                exact div_le_div_of_nonneg_left hbound_nonneg hden_lower_pos
                  (mul_le_mul_of_nonneg_right hden hMpos.le)
    _ ≤ (213/50) * (2*(s : ℚ) + 3) / (m : ℚ)^2 := by
        field_simp [hmpos.ne']
        nlinarith

theorem twoEndpoint_drift_P3a
    {N m s : Nat} (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ))
    (hm : 361 ≤ m) (hs : 3*s ≤ m) :
    ((5 * (N : ℚ)) / 36 *
      ((1 - DFactor (m-s) 2)
        / ((((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ)))))
      ≤ (1/4) / (m : ℚ)^2 := by
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  have hppos : (0 : ℚ) < ((m-s : Nat) : ℚ) := by
    exact_mod_cast (by omega : 0 < m-s)
  have hp2pos : (0 : ℚ) < (((m-s-2 : Nat) : ℚ)) := by
    exact_mod_cast (by omega : 0 < m-s-2)
  have hp1pos : (0 : ℚ) < (((m-s-1 : Nat) : ℚ)) := by
    exact_mod_cast (by omega : 0 < m-s-1)
  have hApos : 0 < (((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ)) :=
    mul_pos hp1pos hp2pos
  have hC : (5 * (N : ℚ)) / 36 ≤ (50/27) * (m : ℚ) := by
    nlinarith
  have hdrift := one_sub_DFactor_two_le (p := m-s) (by omega : 3 ≤ m-s)
  have hstep :
      ((1 - DFactor (m-s) 2)
        / ((((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ))))
      ≤ ((2304/3125) *
            (2 / (((m-s : Nat) : ℚ) * (((m-s-2 : Nat) : ℚ)))))
          / ((((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ))) := by
    exact div_le_div_of_nonneg_right hdrift hApos.le
  have hp_half : (m : ℚ) / 2 ≤ ((m-s : Nat) : ℚ) := by
    have hplower := near_p_lower (m := m) (s := s) hs
    linarith
  have hp1_half := near_p_sub_one_half (m := m) (s := s) hm hs
  have hp2_half := near_p_sub_two_half (m := m) (s := s) hm hs
  have hdenprod :
      (m : ℚ)^4 / 16
        ≤ ((m-s : Nat) : ℚ) * (((m-s-2 : Nat) : ℚ))
            * ((((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ))) := by
    have hprod :
        ((m : ℚ)/2) * ((m : ℚ)/2) * (((m : ℚ)/2) * ((m : ℚ)/2))
          ≤ ((m-s : Nat) : ℚ) * (((m-s-2 : Nat) : ℚ))
              * ((((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ))) := by
      have hleft := mul_le_mul hp_half hp2_half (by positivity : 0 ≤ (m : ℚ)/2) hppos.le
      have hright := mul_le_mul hp1_half hp2_half (by positivity : 0 ≤ (m : ℚ)/2) hp1pos.le
      exact mul_le_mul hleft hright
        (mul_nonneg (by positivity) (by positivity))
        (mul_nonneg hppos.le hp2pos.le)
    nlinarith
  have hdenprod_nf :
      (m : ℚ)^4 / 16
        ≤ ((m-s : Nat) : ℚ) * (((m-s-2 : Nat) : ℚ))^2
            * (((m-s-1 : Nat) : ℚ)) := by
    nlinarith [hdenprod]
  have hstep_nonneg :
      0 ≤ ((2304/3125) *
            (2 / (((m-s : Nat) : ℚ) * (((m-s-2 : Nat) : ℚ)))))
          / ((((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ))) := by
    exact div_nonneg
      (mul_nonneg (by norm_num)
        (div_nonneg (by norm_num) (mul_pos hppos hp2pos).le))
      hApos.le
  have hleft_nonneg :
      0 ≤ ((1 - DFactor (m-s) 2)
        / ((((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ)))) := by
    have hD1 : DFactor (m-s) 2 ≤ 1 :=
      DFactor_le_one (m := m-s) (s := 2) (by omega)
    exact div_nonneg (sub_nonneg.mpr hD1) hApos.le
  calc
    (5 * (N : ℚ)) / 36 *
      ((1 - DFactor (m-s) 2)
        / ((((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ))))
      ≤ (50/27) * (m : ℚ) *
          (((2304/3125) *
              (2 / (((m-s : Nat) : ℚ) * (((m-s-2 : Nat) : ℚ)))))
            / ((((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ)))) := by
          exact mul_le_mul hC hstep
            hleft_nonneg
            (by positivity)
    _ ≤ (1/4) / (m : ℚ)^2 := by
          have hmQ : (361 : ℚ) ≤ m := by exact_mod_cast hm
          have hconst :
              50 * (m : ℚ)^3 * 2304 * 2 * 4
                ≤ 27 * 3125 * ((m : ℚ)^4 / 16) := by
            have hlin : (50 * 2304 * 2 * 4 : ℚ) ≤ 27 * 3125 * ((m : ℚ) / 16) := by
              nlinarith
            have hm3 : 0 ≤ (m : ℚ)^3 := by positivity
            calc
              50 * (m : ℚ)^3 * 2304 * 2 * 4
                  = (50 * 2304 * 2 * 4 : ℚ) * (m : ℚ)^3 := by ring
              _ ≤ (27 * 3125 * ((m : ℚ) / 16)) * (m : ℚ)^3 :=
                    mul_le_mul_of_nonneg_right hlin hm3
              _ = 27 * 3125 * ((m : ℚ)^4 / 16) := by ring
          have hden_scaled :
              27 * 3125 * ((m : ℚ)^4 / 16)
                ≤ 27 * 3125 *
                  (((m-s : Nat) : ℚ) * (((m-s-2 : Nat) : ℚ))^2
                    * (((m-s-1 : Nat) : ℚ))) := by
            exact mul_le_mul_of_nonneg_left hdenprod_nf (by norm_num)
          field_simp [hmpos.ne', hppos.ne', hp2pos.ne', hApos.ne']
          nlinarith [hconst, hden_scaled]

theorem twoEndpointCorrection_pointwise_P3a
    {N m s : Nat} (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ))
    (hm : 361 ≤ m) (hs : 3*s ≤ m) :
    |twoEndpointCorrection N (m-s) - twoEndpointTarget N m|
      ≤ ((213/50) * (2*(s : ℚ) + 3) + 1/4) / (m : ℚ)^2 := by
  have hsplit := twoEndpointCorrection_abs_le_split (N := N) (m := m) (s := s) hm hs
  have hdrift := twoEndpoint_drift_P3a (N := N) (m := m) (s := s) hN40 hm hs
  have hden := twoEndpoint_denominator_change_P3a (N := N) (m := m) (s := s) hN40 hm hs
  calc
    |twoEndpointCorrection N (m-s) - twoEndpointTarget N m|
      ≤ (5 * (N : ℚ)) / 36 *
          ((1 - DFactor (m-s) 2)
              / ((((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ)))
            + (((m : ℚ)^2
                - (((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ)))
              / (((((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ))) * (m : ℚ)^2))) := hsplit
    _ =
        (5 * (N : ℚ)) / 36 *
          ((1 - DFactor (m-s) 2)
            / ((((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ))))
        + (5 * (N : ℚ)) / 36 *
          ((((m : ℚ)^2
              - (((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ)))
            / (((((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ))) * (m : ℚ)^2))) := by
          ring
    _ ≤ (1/4) / (m : ℚ)^2
          + (213/50) * (2*(s : ℚ) + 3) / (m : ℚ)^2 :=
          add_le_add hdrift hden
    _ = ((213/50) * (2*(s : ℚ) + 3) + 1/4) / (m : ℚ)^2 := by
          ring

theorem signLock_P3a_budget_zetaMax {N m : Nat}
    (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ)) (hm : 361 ≤ m) :
    ∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) *
          |twoEndpointCorrection N (m-s) - twoEndpointTarget N m|
      ≤ 184 / (m : ℚ)^2 := by
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  have hpoint :
      ∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) *
          |twoEndpointCorrection N (m-s) - twoEndpointTarget N m|
      ≤
      ∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) *
          (((213/50) * (2*(s : ℚ) + 3) + 1/4) / (m : ℚ)^2) := by
    refine Finset.sum_le_sum fun s hs => ?_
    have hs3 : 3*s ≤ m := by
      have hsle : s ≤ m/3 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
      exact (Nat.mul_le_mul_left 3 hsle).trans (Nat.mul_div_le m 3)
    have hweight : 0 ≤ zetaMax^s / (s.factorial : ℚ) := by
      have hz : 0 ≤ zetaMax := by norm_num [zetaMax]
      positivity
    exact mul_le_mul_of_nonneg_left
      (twoEndpointCorrection_pointwise_P3a hN40 hm hs3) hweight
  calc
    ∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) *
          |twoEndpointCorrection N (m-s) - twoEndpointTarget N m|
      ≤
      ∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) *
          (((213/50) * (2*(s : ℚ) + 3) + 1/4) / (m : ℚ)^2) := hpoint
    _ =
      ∑ s ∈ Finset.range (m/3 + 1),
        (((213/50) * 2 / (m : ℚ)^2) *
            ((s : ℚ) * zetaMax^s / (s.factorial : ℚ))
          + (((213/50) * 3 + 1/4) / (m : ℚ)^2) *
            (zetaMax^s / (s.factorial : ℚ))) := by
          refine Finset.sum_congr rfl fun s hs => ?_
          ring
    _ =
      ((213/50) * 2 / (m : ℚ)^2) *
          (∑ s ∈ Finset.range (m/3 + 1),
            (s : ℚ) * zetaMax^s / (s.factorial : ℚ))
        + (((213/50) * 3 + 1/4) / (m : ℚ)^2) *
          (∑ s ∈ Finset.range (m/3 + 1),
            zetaMax^s / (s.factorial : ℚ)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ ((213/50) * 2 / (m : ℚ)^2) * (59/5)
        + (((213/50) * 3 + 1/4) / (m : ℚ)^2) * (32/5) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (poissonFirst_zetaMax_le_sharp _) (by positivity))
            (mul_le_mul_of_nonneg_left (poissonZero_zetaMax_le _) (by positivity))
    _ ≤ 184 / (m : ℚ)^2 := by
          field_simp [hmpos.ne']
          norm_num

/-! ## P3b: non-endpoint two-block budget -/

/-- Rational majorant for the non-endpoint two-blocks
`Σ₂^{(3+)}(p)`.  The index `i` is `j-1`, so the sum is over
`2 ≤ i ≤ p-4`, i.e. `Ico 2 (p-3)`, with ambient binomial parameter `p-2`. -/
def twoNonEndpointMajorant (p : Nat) : ℚ :=
  (576/3125) / (((p-1 : Nat) : ℚ)) *
    ∑ i ∈ Finset.Ico 2 (p-3), (1:ℚ)/((p-2).choose i)

/-- The normalized P3b contribution controlled by the non-endpoint two-block
majorant. -/
def twoNonEndpointCorrectionBound (N p : Nat) : ℚ :=
  ((N : ℚ) / 2) * twoNonEndpointMajorant p

theorem twoNonEndpointMajorant_le_large {p : Nat} (hp : 241 ≤ p) :
    twoNonEndpointMajorant p
      ≤ (576/625) /
          ((((p-1 : Nat) : ℚ)) * (((p-2 : Nat) : ℚ)) * (((p-3 : Nat) : ℚ))) := by
  have hsum := sum_choose_recip_inner_le_large (p-2) (by omega : 239 ≤ p-2)
  rw [show p-2-1 = p-3 by omega] at hsum
  have hsub : (((p-2 : Nat) : ℚ) - 1) = (((p-3 : Nat) : ℚ)) := by
    rw [show p-2 = (p-3)+1 by omega]
    push_cast
    ring
  rw [hsub] at hsum
  have hcoef_nonneg : 0 ≤ (576/3125) / (((p-1 : Nat) : ℚ)) := by
    positivity
  have hp1 : (((p-1 : Nat) : ℚ)) ≠ 0 := by
    exact_mod_cast (by omega : p-1 ≠ 0)
  have hp2 : (((p-2 : Nat) : ℚ)) ≠ 0 := by
    exact_mod_cast (by omega : p-2 ≠ 0)
  have hp3 : (((p-3 : Nat) : ℚ)) ≠ 0 := by
    exact_mod_cast (by omega : p-3 ≠ 0)
  calc
    twoNonEndpointMajorant p
      ≤ (576/3125) / (((p-1 : Nat) : ℚ)) *
          (5 / (((p-2 : Nat) : ℚ) * (((p-3 : Nat) : ℚ)))) := by
        unfold twoNonEndpointMajorant
        exact mul_le_mul_of_nonneg_left hsum hcoef_nonneg
    _ = (576/625) /
          ((((p-1 : Nat) : ℚ)) * (((p-2 : Nat) : ℚ)) * (((p-3 : Nat) : ℚ))) := by
        field_simp [hp1, hp2, hp3]
        ring

private theorem near_p_sub_three_three_fifths
    {m s : Nat} (hm : 361 ≤ m) (hs : 3*s ≤ m) :
    (3/5) * (m : ℚ) ≤ (((m-s-3 : Nat) : ℚ)) := by
  have hp3 : 3 ≤ m-s := by omega
  rw [Nat.cast_sub hp3]
  have hplower := near_p_lower (m := m) (s := s) hs
  have hmQ : (361 : ℚ) ≤ m := by exact_mod_cast hm
  nlinarith

private theorem near_three_denominator_product
    {m s : Nat} (hm : 361 ≤ m) (hs : 3*s ≤ m) :
    (27/125) * (m : ℚ)^3
      ≤ (((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ))
          * (((m-s-3 : Nat) : ℚ)) := by
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  have h3 := near_p_sub_three_three_fifths (m := m) (s := s) hm hs
  have h2 : (3/5) * (m : ℚ) ≤ (((m-s-2 : Nat) : ℚ)) := by
    have hmono : (((m-s-3 : Nat) : ℚ)) ≤ (((m-s-2 : Nat) : ℚ)) := by
      exact_mod_cast (by omega : m-s-3 ≤ m-s-2)
    exact h3.trans hmono
  have h1 : (3/5) * (m : ℚ) ≤ (((m-s-1 : Nat) : ℚ)) := by
    have hmono : (((m-s-3 : Nat) : ℚ)) ≤ (((m-s-1 : Nat) : ℚ)) := by
      exact_mod_cast (by omega : m-s-3 ≤ m-s-1)
    exact h3.trans hmono
  have hbase_nonneg : 0 ≤ (3/5) * (m : ℚ) := by positivity
  have hp1pos : (0 : ℚ) < (((m-s-1 : Nat) : ℚ)) := by
    exact_mod_cast (by omega : 0 < m-s-1)
  have hp2pos : (0 : ℚ) < (((m-s-2 : Nat) : ℚ)) := by
    exact_mod_cast (by omega : 0 < m-s-2)
  have h12 :
      ((3/5) * (m : ℚ)) * ((3/5) * (m : ℚ))
        ≤ (((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ)) :=
    mul_le_mul h1 h2 hbase_nonneg hp1pos.le
  have h123 :
      ((3/5) * (m : ℚ)) * ((3/5) * (m : ℚ)) * ((3/5) * (m : ℚ))
        ≤ (((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ))
            * (((m-s-3 : Nat) : ℚ)) :=
    mul_le_mul h12 h3 hbase_nonneg
      (mul_nonneg hp1pos.le hp2pos.le)
  nlinarith

theorem twoNonEndpointCorrectionBound_pointwise_P3b
    {N m s : Nat} (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ))
    (hm : 361 ≤ m) (hs : 3*s ≤ m) :
    twoNonEndpointCorrectionBound N (m-s) ≤ (183/5) / (m : ℚ)^2 := by
  have hp : 241 ≤ m-s := by omega
  have hmaj := twoNonEndpointMajorant_le_large (p := m-s) hp
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  have hNhalf : (N : ℚ) / 2 ≤ (20/3) * (m : ℚ) := by
    nlinarith
  have hNhalf_nonneg : 0 ≤ (N : ℚ) / 2 := by positivity
  have hp1pos : (0 : ℚ) < (((m-s-1 : Nat) : ℚ)) := by
    exact_mod_cast (by omega : 0 < m-s-1)
  have hp2pos : (0 : ℚ) < (((m-s-2 : Nat) : ℚ)) := by
    exact_mod_cast (by omega : 0 < m-s-2)
  have hp3pos : (0 : ℚ) < (((m-s-3 : Nat) : ℚ)) := by
    exact_mod_cast (by omega : 0 < m-s-3)
  have hupper_nonneg :
      0 ≤ (576/625) /
        ((((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ)) * (((m-s-3 : Nat) : ℚ))) := by
    positivity
  have hden := near_three_denominator_product (m := m) (s := s) hm hs
  have hden_scaled :
      20 * (m : ℚ)^3 * 576 * 5
        ≤ 3 * 625 * 183 *
          ((((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ))
            * (((m-s-3 : Nat) : ℚ))) := by
    have hconst : (20 * 576 * 5 : ℚ) ≤ 3 * 625 * 183 * (27/125) := by
      norm_num
    have hm3_nonneg : 0 ≤ (m : ℚ)^3 := by positivity
    calc
      20 * (m : ℚ)^3 * 576 * 5
          = (20 * 576 * 5 : ℚ) * (m : ℚ)^3 := by ring
      _ ≤ (3 * 625 * 183 * (27/125)) * (m : ℚ)^3 :=
          mul_le_mul_of_nonneg_right hconst hm3_nonneg
      _ = 3 * 625 * 183 * ((27/125) * (m : ℚ)^3) := by ring
      _ ≤ 3 * 625 * 183 *
          ((((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ))
            * (((m-s-3 : Nat) : ℚ)) ) :=
          mul_le_mul_of_nonneg_left hden (by norm_num)
  calc
    twoNonEndpointCorrectionBound N (m-s)
      ≤ ((N : ℚ) / 2) *
          ((576/625) /
            ((((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ))
              * (((m-s-3 : Nat) : ℚ)))) := by
        unfold twoNonEndpointCorrectionBound
        exact mul_le_mul_of_nonneg_left hmaj hNhalf_nonneg
    _ ≤ ((20/3) * (m : ℚ)) *
          ((576/625) /
            ((((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ))
              * (((m-s-3 : Nat) : ℚ)))) := by
        exact mul_le_mul_of_nonneg_right hNhalf hupper_nonneg
    _ ≤ (183/5) / (m : ℚ)^2 := by
        field_simp [hmpos.ne', hp1pos.ne', hp2pos.ne', hp3pos.ne']
        nlinarith [hden_scaled]

/-- Scalar budget for the P3b pointwise bound
`(183/5)/m² = 36.6/m²`. -/
theorem signLock_P3b_scalar_budget_zetaMax {m : Nat} (hm : 1 ≤ m) :
    ∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) * ((183/5) / (m : ℚ)^2)
      ≤ 234 / (m : ℚ)^2 := by
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  calc
    ∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) * ((183/5) / (m : ℚ)^2)
      =
        ((183/5) / (m : ℚ)^2) *
          (∑ s ∈ Finset.range (m/3 + 1), zetaMax^s / (s.factorial : ℚ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun s hs => ?_
          ring
    _ ≤ ((183/5) / (m : ℚ)^2) * (319/50) := by
          exact mul_le_mul_of_nonneg_left
            (poissonZero_zetaMax_le_tight _) (by positivity)
    _ ≤ 234 / (m : ℚ)^2 := by
          field_simp [hmpos.ne']
          norm_num

/-- Weighted P3b budget for the explicit non-endpoint two-block majorant. -/
theorem signLock_P3b_budget_zetaMax {N m : Nat}
    (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ)) (hm : 361 ≤ m) :
    ∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) *
          twoNonEndpointCorrectionBound N (m-s)
      ≤ 234 / (m : ℚ)^2 := by
  have hpoint :
      ∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) *
          twoNonEndpointCorrectionBound N (m-s)
      ≤
      ∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) * ((183/5) / (m : ℚ)^2) := by
    refine Finset.sum_le_sum fun s hs => ?_
    have hs3 : 3*s ≤ m := by
      have hsle : s ≤ m/3 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
      exact (Nat.mul_le_mul_left 3 hsle).trans (Nat.mul_div_le m 3)
    have hweight : 0 ≤ zetaMax^s / (s.factorial : ℚ) := by
      have hz : 0 ≤ zetaMax := by norm_num [zetaMax]
      positivity
    exact mul_le_mul_of_nonneg_left
      (twoNonEndpointCorrectionBound_pointwise_P3b hN40 hm hs3) hweight
  exact hpoint.trans (signLock_P3b_scalar_budget_zetaMax (by omega : 1 ≤ m))

/-! ## Final rational positivity margin -/

/-- Alternating partial sum surrogate for `exp(-x)`. -/
def expNegPartial (x : ℚ) (T : Nat) : ℚ :=
  ∑ k ∈ Finset.range T, (-x)^k / (k.factorial : ℚ)

/-- A concrete rational lower surrogate for `exp(-50/27)`.
Ten terms already leave far more than the required sign-lock margin. -/
def expNegLower50 : ℚ := expNegPartial (50/27) 10

theorem expNegLower50_eq :
    expNegLower50 = 678107852315029 / 4323713773987629 := by
  norm_num [expNegLower50, expNegPartial, Finset.sum_range_succ, Nat.factorial]

theorem expNegLower50_pos : 0 < expNegLower50 := by
  rw [expNegLower50_eq]
  norm_num

/-- Exact rational audit of the endpoint margin. -/
theorem signLock_final_margin_endpoint :
    (2215 : ℚ) <
      (361 : ℚ)^2 * expNegLower50 * (1 - 2/(361 : ℚ)) := by
  rw [expNegLower50_eq]
  norm_num

/-- The endpoint margin propagates to every `m ≥ 361` through the increasing
factor `m^2(1-2/m) = m^2-2m`. -/
theorem signLock_final_margin_of_ge_361 {m : Nat} (hm : 361 ≤ m) :
    (2215 : ℚ) <
      (m : ℚ)^2 * expNegLower50 * (1 - 2/(m : ℚ)) := by
  have hmQ : (361 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  have hpoly :
      (361 : ℚ)^2 - 2*(361 : ℚ) ≤ (m : ℚ)^2 - 2*(m : ℚ) := by
    have hleft : 0 ≤ (m : ℚ) - 361 := by linarith
    have hright : 0 ≤ (m : ℚ) + 361 - 2 := by linarith
    have hprod : 0 ≤ ((m : ℚ) - 361) * ((m : ℚ) + 361 - 2) :=
      mul_nonneg hleft hright
    nlinarith
  have hmono :
      (361 : ℚ)^2 * expNegLower50 * (1 - 2/(361 : ℚ))
        ≤ (m : ℚ)^2 * expNegLower50 * (1 - 2/(m : ℚ)) := by
    have h361 :
        (361 : ℚ)^2 * expNegLower50 * (1 - 2/(361 : ℚ))
          = expNegLower50 * ((361 : ℚ)^2 - 2*(361 : ℚ)) := by
        ring
    have hmrew :
        (m : ℚ)^2 * expNegLower50 * (1 - 2/(m : ℚ))
          = expNegLower50 * ((m : ℚ)^2 - 2*(m : ℚ)) := by
        field_simp [hmpos.ne']
    rw [h361, hmrew]
    exact mul_le_mul_of_nonneg_left hpoly expNegLower50_pos.le
  exact lt_of_lt_of_le signLock_final_margin_endpoint hmono

end Prop51
