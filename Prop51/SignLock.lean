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

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
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

/-- The gamma-product residual after extracting the first-order term. -/
def piResidual (m s : Nat) : ℚ := PiFactor m s - 1 - eOne s / (m : ℚ)

theorem eOne_nonneg (s : Nat) : 0 ≤ eOne s := by
  unfold eOne
  positivity

/-! ## Real logarithm bridge for the `Π_s` product

Most of this file keeps the numerical audit in `ℚ`.  The actual product
estimate for `Π_s`, however, follows the TeX proof most directly through
`log`/`exp`; the lemmas in this short section are the explicit real-analysis
bridge that the later rational budget lemmas consume.
-/

/-- The logarithmic factor estimate used in the paper:
`-log(1-x) ≤ x + 3x²/4` for `0 ≤ x ≤ 1/3`. -/
theorem neg_log_one_sub_le_quadratic {x : ℝ} (h0 : 0 ≤ x) (h13 : x ≤ 1/3) :
    -Real.log (1 - x) ≤ x + (3/4) * x^2 := by
  let f : ℝ → ℝ := fun t => t + (3/4) * t^2 + Real.log (1 - t)
  have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) (1/3)) := by
    unfold f
    refine ContinuousOn.add (ContinuousOn.add continuousOn_id ?_) ?_
    · exact ContinuousOn.mul continuousOn_const (ContinuousOn.pow continuousOn_id 2)
    · exact (ContinuousOn.sub continuousOn_const continuousOn_id).log (fun t ht => by
        have ht2 : t ≤ 1/3 := ht.2
        simp only [id_eq]
        linarith)
  have hderiv : ∀ y ∈ interior (Set.Icc (0 : ℝ) (1/3)),
      HasDerivWithinAt f (y * (1 - 3*y) / (2*(1-y)))
        (interior (Set.Icc (0 : ℝ) (1/3))) y := by
    intro y hy
    simp only [interior_Icc, Set.mem_Ioo] at hy
    have hy1 : 1 - y ≠ 0 := by linarith
    unfold f
    convert (((hasDerivAt_id y).add
      (((hasDerivAt_const y (3/4)).mul ((hasDerivAt_id y).pow 2)))).add
      (((hasDerivAt_const y (1)).sub (hasDerivAt_id y)).log hy1)).hasDerivWithinAt
      using 1
    simp only [id_eq, Pi.sub_apply]
    field_simp [hy1]
    ring_nf
  have hderiv_nonneg : ∀ y ∈ interior (Set.Icc (0 : ℝ) (1/3)),
      0 ≤ y * (1 - 3*y) / (2*(1-y)) := by
    intro y hy
    simp only [interior_Icc, Set.mem_Ioo] at hy
    have hy_nonneg : 0 ≤ y := le_of_lt hy.1
    have h13y : 0 ≤ 1 - 3*y := by linarith
    have hden : 0 < 2*(1-y) := by nlinarith
    positivity
  have hmono : MonotoneOn f (Set.Icc (0 : ℝ) (1/3)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) (1/3))
      hfcont hderiv hderiv_nonneg
  have hxmem : x ∈ Set.Icc (0 : ℝ) (1/3) := ⟨h0, h13⟩
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1/3) := by norm_num
  have hfx := hmono h0mem hxmem h0
  have hf0 : f 0 = 0 := by norm_num [f]
  have hfx0 : 0 ≤ f x := by simpa [hf0] using hfx
  unfold f at hfx0
  linarith

/-- Elementary exponential remainder estimate used to convert logarithmic
product bounds into product bounds. -/
theorem real_exp_sub_one_le_mul_exp (x : ℝ) :
    Real.exp x - 1 ≤ x * Real.exp x := by
  have h := Real.add_one_le_exp (-x)
  have hmul := mul_le_mul_of_nonneg_right h (Real.exp_nonneg x)
  rw [Real.exp_neg] at hmul
  have hxpos : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  field_simp [hxpos] at hmul
  linarith

/-- Second-order exponential remainder estimate used for the extracted
gamma-product residual. -/
theorem real_exp_sub_one_sub_id_le_half_sq_mul_exp {x : ℝ} (hx : 0 ≤ x) :
    Real.exp x - 1 - x ≤ (1/2) * x^2 * Real.exp x := by
  let g : ℝ → ℝ := fun t => (1/2) * t^2 * Real.exp t - Real.exp t + 1 + t
  let gp : ℝ → ℝ := fun t => Real.exp t * ((1/2) * t^2 + t - 1) + 1
  have hgpcont : ContinuousOn gp (Set.Icc (0 : ℝ) x) := by
    unfold gp
    fun_prop
  have hgpderiv : ∀ y ∈ interior (Set.Icc (0 : ℝ) x),
      HasDerivWithinAt gp (Real.exp y * ((1/2) * y^2 + 2*y))
        (interior (Set.Icc (0 : ℝ) x)) y := by
    intro y hy
    unfold gp
    convert (((Real.hasDerivAt_exp y).mul
      ((((hasDerivAt_const y (1/2)).mul ((hasDerivAt_id y).pow 2)).add
        (hasDerivAt_id y)).sub (hasDerivAt_const y 1))).add
        (hasDerivAt_const y 1)).hasDerivWithinAt using 1
    simp only [id_eq, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
    ring_nf
  have hgpderiv_nonneg : ∀ y ∈ interior (Set.Icc (0 : ℝ) x),
      0 ≤ Real.exp y * ((1/2) * y^2 + 2*y) := by
    intro y hy
    simp only [interior_Icc, Set.mem_Ioo] at hy
    have hpoly : 0 ≤ (1/2) * y^2 + 2*y := by
      nlinarith [sq_nonneg y, le_of_lt hy.1]
    exact mul_nonneg (Real.exp_nonneg y) hpoly
  have hgpmono : MonotoneOn gp (Set.Icc (0 : ℝ) x) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) x)
      hgpcont hgpderiv hgpderiv_nonneg
  have hgp_nonneg : ∀ y ∈ interior (Set.Icc (0 : ℝ) x), 0 ≤ gp y := by
    intro y hy
    simp only [interior_Icc, Set.mem_Ioo] at hy
    have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) x := ⟨le_rfl, hx⟩
    have hymem : y ∈ Set.Icc (0 : ℝ) x := ⟨hy.1.le, hy.2.le⟩
    have h := hgpmono h0mem hymem hy.1.le
    have hgp0 : gp 0 = 0 := by norm_num [gp]
    simpa [hgp0] using h
  have hgcont : ContinuousOn g (Set.Icc (0 : ℝ) x) := by
    unfold g
    fun_prop
  have hgderiv : ∀ y ∈ interior (Set.Icc (0 : ℝ) x),
      HasDerivWithinAt g (gp y) (interior (Set.Icc (0 : ℝ) x)) y := by
    intro y hy
    unfold g gp
    convert ((((((hasDerivAt_const y (1/2)).mul ((hasDerivAt_id y).pow 2)).mul
      (Real.hasDerivAt_exp y)).sub (Real.hasDerivAt_exp y)).add
        (hasDerivAt_const y 1)).add (hasDerivAt_id y)).hasDerivWithinAt using 1
    simp only [id_eq, Pi.mul_apply, Pi.pow_apply]
    ring_nf
  have hgmono : MonotoneOn g (Set.Icc (0 : ℝ) x) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) x)
      hgcont hgderiv hgp_nonneg
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) x := ⟨le_rfl, hx⟩
  have hxmem : x ∈ Set.Icc (0 : ℝ) x := ⟨hx, le_rfl⟩
  have h := hgmono h0mem hxmem hx
  have hg0 : g 0 = 0 := by norm_num [g]
  have hgx_nonneg : 0 ≤ g x := by simpa [hg0] using h
  unfold g at hgx_nonneg
  linarith

theorem PiFactor_zero (m : Nat) (hm : 1 ≤ m) : PiFactor m 0 = 1 := by
  unfold PiFactor
  rw [show m-0-1 = m-1 by omega]
  field_simp [show (((m-1).factorial : Nat) : ℚ) ≠ 0 by positivity]

theorem PiFactor_succ {m s : Nat} (hs : s+1 < m) :
    PiFactor m (s+1) =
      PiFactor m s * (m : ℚ) / (((m-s-1 : Nat) : ℚ)) := by
  have hfac :
      (((m-s-1).factorial : Nat) : ℚ)
        = (((m-s-1 : Nat) : ℚ)) * (((m-s-2).factorial : Nat) : ℚ) := by
    rw [show m-s-1 = (m-s-2)+1 by omega, Nat.factorial_succ]
    push_cast
    ring
  have hden : (((m-s-1 : Nat) : ℚ)) ≠ 0 := by
    exact_mod_cast (by omega : m-s-1 ≠ 0)
  have hfac_m : (((m-1).factorial : Nat) : ℚ) ≠ 0 := by positivity
  have hfac_prev : (((m-s-1).factorial : Nat) : ℚ) ≠ 0 := by positivity
  have hfac_next : (((m-s-2).factorial : Nat) : ℚ) ≠ 0 := by positivity
  unfold PiFactor
  rw [show m-(s+1)-1 = m-s-2 by omega, hfac]
  field_simp [hden, hfac_m, hfac_prev, hfac_next]
  ring

theorem PiFactor_prod {m s : Nat} (hs : s < m) :
    PiFactor m s =
      ∏ i ∈ Finset.range s, (m : ℚ) / (((m-(i+1) : Nat) : ℚ)) := by
  induction s with
  | zero =>
      rw [PiFactor_zero m (by omega)]
      simp
  | succ s ih =>
      rw [PiFactor_succ (m := m) (s := s) hs]
      rw [ih (by omega : s < m), Finset.prod_range_succ]
      rw [show m-(s+1) = m-s-1 by omega]
      ring

theorem PiFactor_pos {m s : Nat} (hs : s < m) : 0 < PiFactor m s := by
  unfold PiFactor
  exact div_pos
    (mul_pos (pow_pos (by exact_mod_cast (by omega : 0 < m)) s) (by positivity))
    (by positivity)

theorem one_le_PiFactor {m s : Nat} (hs : s < m) : 1 ≤ PiFactor m s := by
  induction s with
  | zero =>
      rw [PiFactor_zero m (by omega)]
  | succ s ih =>
      have hs_prev : s < m := by omega
      have hdenpos : (0 : ℚ) < (((m-s-1 : Nat) : ℚ)) := by
        exact_mod_cast (by omega : 0 < m-s-1)
      have hdenle : (((m-s-1 : Nat) : ℚ)) ≤ (m : ℚ) := by
        exact_mod_cast (by omega : m-s-1 ≤ m)
      have hfactor : 1 ≤ (m : ℚ) / (((m-s-1 : Nat) : ℚ)) := by
        rw [one_le_div₀ hdenpos]
        exact hdenle
      rw [PiFactor_succ (m := m) (s := s) hs]
      rw [show PiFactor m s * (m : ℚ) / (((m-s-1 : Nat) : ℚ))
          = PiFactor m s * ((m : ℚ) / (((m-s-1 : Nat) : ℚ))) by ring]
      exact one_le_mul_of_one_le_of_one_le (ih hs_prev) hfactor

theorem one_add_eOne_div_le_PiFactor {m s : Nat} (hs : s < m) :
    1 + eOne s / (m : ℚ) ≤ PiFactor m s := by
  induction s with
  | zero =>
      rw [PiFactor_zero m (by omega)]
      norm_num [eOne]
  | succ s ih =>
      have hs_prev : s < m := by omega
      have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
      have hdenpos : (0 : ℚ) < (((m-s-1 : Nat) : ℚ)) := by
        exact_mod_cast (by omega : 0 < m-s-1)
      have hden_cast :
          (((m-s-1 : Nat) : ℚ)) = (m : ℚ) - (s : ℚ) - 1 := by
        rw [show m-s-1 = m-(s+1) by omega, Nat.cast_sub (by omega : s+1 ≤ m)]
        push_cast
        ring
      have hdenlin_pos : (0 : ℚ) < (m : ℚ) - (s : ℚ) - 1 := by
        rwa [← hden_cast]
      have hfactor_nonneg : 0 ≤ (m : ℚ) / (((m-s-1 : Nat) : ℚ)) := by positivity
      rw [PiFactor_succ (m := m) (s := s) hs]
      calc
        1 + eOne (s+1) / (m : ℚ)
            ≤ (1 + eOne s / (m : ℚ)) *
                ((m : ℚ) / (((m-s-1 : Nat) : ℚ))) := by
              have hdiff :
                  (1 + eOne s / (m : ℚ)) *
                      ((m : ℚ) / (((m-s-1 : Nat) : ℚ)))
                    - (1 + eOne (s+1) / (m : ℚ))
                    =
                  (((s+1 : Nat) : ℚ)^2 * (((s+2 : Nat) : ℚ))) /
                    (2 * (m : ℚ) * (((m-s-1 : Nat) : ℚ))) := by
                unfold eOne
                rw [hden_cast]
                field_simp [hmpos.ne', hdenlin_pos.ne']
                push_cast
                ring
              have hnonneg :
                  0 ≤ (((s+1 : Nat) : ℚ)^2 * (((s+2 : Nat) : ℚ))) /
                    (2 * (m : ℚ) * (((m-s-1 : Nat) : ℚ))) := by
                positivity
              linarith
        _ ≤ PiFactor m s * ((m : ℚ) / (((m-s-1 : Nat) : ℚ))) :=
              mul_le_mul_of_nonneg_right (ih hs_prev) hfactor_nonneg
        _ = PiFactor m s * (m : ℚ) / (((m-s-1 : Nat) : ℚ)) := by ring

theorem piResidual_nonneg {m s : Nat} (hs : s < m) :
    0 ≤ piResidual m s := by
  unfold piResidual
  linarith [one_add_eOne_div_le_PiFactor (m := m) (s := s) hs]

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

theorem poissonFallingThird_sum_range (y : ℚ) :
    ∀ T : Nat,
      (∑ s ∈ Finset.range T,
          (s : ℚ) * ((s-1 : Nat) : ℚ) * ((s-2 : Nat) : ℚ) *
            y^s / (s.factorial : ℚ))
        = y^3 * ∑ t ∈ Finset.range (T-3), y^t / (t.factorial : ℚ)
  | 0 => by simp
  | 1 => by simp
  | 2 => by norm_num [Finset.sum_range_succ]
  | T+3 => by
      cases T with
      | zero =>
          norm_num [Finset.sum_range_succ]
      | succ T =>
          rw [Finset.sum_range_succ, poissonFallingThird_sum_range y (T+3)]
          rw [show T+1+3-3 = T+1 by omega, Finset.sum_range_succ, mul_add]
          congr 1
          have hfac1 : (((T+3).factorial : Nat) : ℚ)
              = ((T+3 : Nat) : ℚ) * ((T+2).factorial : ℚ) := by
            rw [show T+3 = (T+2)+1 by omega, Nat.factorial_succ]
            push_cast
            ring
          have hfac2 : (((T+2).factorial : Nat) : ℚ)
              = ((T+2 : Nat) : ℚ) * ((T+1).factorial : ℚ) := by
            rw [show T+2 = (T+1)+1 by omega, Nat.factorial_succ]
            push_cast
            ring
          have hfac3 : (((T+1).factorial : Nat) : ℚ)
              = ((T+1 : Nat) : ℚ) * (T.factorial : ℚ) := by
            rw [show T+1 = T+1 by rfl, Nat.factorial_succ]
            push_cast
            ring
          rw [hfac1, hfac2, hfac3, pow_succ, pow_succ, pow_succ]
          push_cast
          field_simp [show ((T : ℚ) + 2 + 1) ≠ 0 by positivity,
            show ((T : ℚ) + 1 + 1) ≠ 0 by positivity,
            show ((T : ℚ) + 1) ≠ 0 by positivity,
            show ((T.factorial : Nat) : ℚ) ≠ 0 by positivity]

theorem poissonFallingFourth_sum_range (y : ℚ) :
    ∀ T : Nat,
      (∑ s ∈ Finset.range T,
          (s : ℚ) * ((s-1 : Nat) : ℚ) * ((s-2 : Nat) : ℚ) *
            ((s-3 : Nat) : ℚ) * y^s / (s.factorial : ℚ))
        = y^4 * ∑ t ∈ Finset.range (T-4), y^t / (t.factorial : ℚ)
  | 0 => by simp
  | 1 => by simp
  | 2 => by norm_num [Finset.sum_range_succ]
  | 3 => by norm_num [Finset.sum_range_succ]
  | T+4 => by
      cases T with
      | zero =>
          norm_num [Finset.sum_range_succ]
      | succ T =>
          rw [Finset.sum_range_succ, poissonFallingFourth_sum_range y (T+4)]
          rw [show T+1+4-4 = T+1 by omega, Finset.sum_range_succ, mul_add]
          congr 1
          have hfac1 : (((T+4).factorial : Nat) : ℚ)
              = ((T+4 : Nat) : ℚ) * ((T+3).factorial : ℚ) := by
            rw [show T+4 = (T+3)+1 by omega, Nat.factorial_succ]
            push_cast
            ring
          have hfac2 : (((T+3).factorial : Nat) : ℚ)
              = ((T+3 : Nat) : ℚ) * ((T+2).factorial : ℚ) := by
            rw [show T+3 = (T+2)+1 by omega, Nat.factorial_succ]
            push_cast
            ring
          have hfac3 : (((T+2).factorial : Nat) : ℚ)
              = ((T+2 : Nat) : ℚ) * ((T+1).factorial : ℚ) := by
            rw [show T+2 = (T+1)+1 by omega, Nat.factorial_succ]
            push_cast
            ring
          have hfac4 : (((T+1).factorial : Nat) : ℚ)
              = ((T+1 : Nat) : ℚ) * (T.factorial : ℚ) := by
            rw [show T+1 = T+1 by rfl, Nat.factorial_succ]
            push_cast
            ring
          rw [hfac1, hfac2, hfac3, hfac4, pow_succ, pow_succ, pow_succ,
            pow_succ]
          push_cast
          field_simp [show ((T : ℚ) + 3 + 1) ≠ 0 by positivity,
            show ((T : ℚ) + 2 + 1) ≠ 0 by positivity,
            show ((T : ℚ) + 1 + 1) ≠ 0 by positivity,
            show ((T : ℚ) + 1) ≠ 0 by positivity,
            show ((T.factorial : Nat) : ℚ) ≠ 0 by positivity]

private theorem sq_eq_falling_add (s : Nat) :
    (s : ℚ)^2 = (s : ℚ) * ((s-1 : Nat) : ℚ) + (s : ℚ) := by
  cases s with
  | zero =>
      norm_num
  | succ s =>
      simp
      ring

private theorem cube_eq_falling_add (s : Nat) :
    (s : ℚ)^3 =
      (s : ℚ) * ((s-1 : Nat) : ℚ) * ((s-2 : Nat) : ℚ)
        + 3 * ((s : ℚ) * ((s-1 : Nat) : ℚ)) + (s : ℚ) := by
  cases s with
  | zero =>
      norm_num
  | succ s =>
      cases s with
      | zero =>
          norm_num
      | succ s =>
          cases s with
          | zero =>
              norm_num
          | succ s =>
              simp
              ring

private theorem fourth_eq_falling_add (s : Nat) :
    (s : ℚ)^4 =
      (s : ℚ) * ((s-1 : Nat) : ℚ) * ((s-2 : Nat) : ℚ) *
          ((s-3 : Nat) : ℚ)
        + 6 * ((s : ℚ) * ((s-1 : Nat) : ℚ) * ((s-2 : Nat) : ℚ))
        + 7 * ((s : ℚ) * ((s-1 : Nat) : ℚ)) + (s : ℚ) := by
  cases s with
  | zero =>
      norm_num
  | succ s =>
      cases s with
      | zero =>
          norm_num
      | succ s =>
          cases s with
          | zero =>
              norm_num
          | succ s =>
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

theorem poissonThird_sum_le_partialExpUpper
    (y : ℚ) (T₀ T : Nat) (hy : 0 ≤ y) (hyT : y < (T₀ : ℚ)) :
    ∑ s ∈ Finset.range T, (s : ℚ)^3 * y^s / (s.factorial : ℚ)
      ≤ (y^3 + 3*y^2 + y) * partialExpUpper y T₀ := by
  have hsplit :
      (∑ s ∈ Finset.range T, (s : ℚ)^3 * y^s / (s.factorial : ℚ))
        =
      (∑ s ∈ Finset.range T,
          ((s : ℚ) * ((s-1 : Nat) : ℚ) * ((s-2 : Nat) : ℚ))
            * y^s / (s.factorial : ℚ))
        + 3 * (∑ s ∈ Finset.range T,
          ((s : ℚ) * ((s-1 : Nat) : ℚ)) * y^s / (s.factorial : ℚ))
        + ∑ s ∈ Finset.range T, (s : ℚ) * y^s / (s.factorial : ℚ) := by
    calc
      (∑ s ∈ Finset.range T, (s : ℚ)^3 * y^s / (s.factorial : ℚ))
          =
        ∑ s ∈ Finset.range T,
          (((s : ℚ) * ((s-1 : Nat) : ℚ) * ((s-2 : Nat) : ℚ))
              * y^s / (s.factorial : ℚ)
            + 3 * (((s : ℚ) * ((s-1 : Nat) : ℚ)) * y^s / (s.factorial : ℚ))
            + (s : ℚ) * y^s / (s.factorial : ℚ)) := by
            refine Finset.sum_congr rfl fun s hs => ?_
            rw [cube_eq_falling_add s]
            ring
      _ =
        (∑ s ∈ Finset.range T,
          ((s : ℚ) * ((s-1 : Nat) : ℚ) * ((s-2 : Nat) : ℚ))
            * y^s / (s.factorial : ℚ))
        + 3 * (∑ s ∈ Finset.range T,
          ((s : ℚ) * ((s-1 : Nat) : ℚ)) * y^s / (s.factorial : ℚ))
        + ∑ s ∈ Finset.range T, (s : ℚ) * y^s / (s.factorial : ℚ) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsplit]
  have hfall3 :
      (∑ s ∈ Finset.range T,
          ((s : ℚ) * ((s-1 : Nat) : ℚ) * ((s-2 : Nat) : ℚ))
            * y^s / (s.factorial : ℚ))
        = y^3 * ∑ t ∈ Finset.range (T-3), y^t / (t.factorial : ℚ) := by
    simpa [mul_assoc] using poissonFallingThird_sum_range y T
  have hfall2 :
      (∑ s ∈ Finset.range T,
          ((s : ℚ) * ((s-1 : Nat) : ℚ)) * y^s / (s.factorial : ℚ))
        = y^2 * ∑ t ∈ Finset.range (T-2), y^t / (t.factorial : ℚ) := by
    simpa [mul_assoc] using poissonFallingSecond_sum_range y T
  rw [hfall3, hfall2, poissonFirst_sum_range]
  have h3 := sum_exp_le y T₀ hy hyT (T-3)
  have h2 := sum_exp_le y T₀ hy hyT (T-2)
  have h1 := sum_exp_le y T₀ hy hyT (T-1)
  calc
    y^3 * (∑ t ∈ Finset.range (T-3), y^t / (t.factorial : ℚ))
        + 3 * (y^2 * (∑ t ∈ Finset.range (T-2), y^t / (t.factorial : ℚ)))
        + y * (∑ t ∈ Finset.range (T-1), y^t / (t.factorial : ℚ))
      ≤ y^3 * partialExpUpper y T₀
          + 3 * (y^2 * partialExpUpper y T₀)
          + y * partialExpUpper y T₀ := by
          exact add_le_add
            (add_le_add
              (mul_le_mul_of_nonneg_left h3 (by positivity))
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left h2 (sq_nonneg y)) (by norm_num)))
            (mul_le_mul_of_nonneg_left h1 hy)
    _ = (y^3 + 3*y^2 + y) * partialExpUpper y T₀ := by ring

theorem poissonFourth_sum_le_partialExpUpper
    (y : ℚ) (T₀ T : Nat) (hy : 0 ≤ y) (hyT : y < (T₀ : ℚ)) :
    ∑ s ∈ Finset.range T, (s : ℚ)^4 * y^s / (s.factorial : ℚ)
      ≤ (y^4 + 6*y^3 + 7*y^2 + y) * partialExpUpper y T₀ := by
  have hsplit :
      (∑ s ∈ Finset.range T, (s : ℚ)^4 * y^s / (s.factorial : ℚ))
        =
      (∑ s ∈ Finset.range T,
          ((s : ℚ) * ((s-1 : Nat) : ℚ) * ((s-2 : Nat) : ℚ) *
              ((s-3 : Nat) : ℚ)) * y^s / (s.factorial : ℚ))
        + 6 * (∑ s ∈ Finset.range T,
          ((s : ℚ) * ((s-1 : Nat) : ℚ) * ((s-2 : Nat) : ℚ))
            * y^s / (s.factorial : ℚ))
        + 7 * (∑ s ∈ Finset.range T,
          ((s : ℚ) * ((s-1 : Nat) : ℚ)) * y^s / (s.factorial : ℚ))
        + ∑ s ∈ Finset.range T, (s : ℚ) * y^s / (s.factorial : ℚ) := by
    calc
      (∑ s ∈ Finset.range T, (s : ℚ)^4 * y^s / (s.factorial : ℚ))
          =
        ∑ s ∈ Finset.range T,
          (((s : ℚ) * ((s-1 : Nat) : ℚ) * ((s-2 : Nat) : ℚ) *
              ((s-3 : Nat) : ℚ)) * y^s / (s.factorial : ℚ)
            + 6 * (((s : ℚ) * ((s-1 : Nat) : ℚ) * ((s-2 : Nat) : ℚ))
                * y^s / (s.factorial : ℚ))
            + 7 * (((s : ℚ) * ((s-1 : Nat) : ℚ)) * y^s / (s.factorial : ℚ))
            + (s : ℚ) * y^s / (s.factorial : ℚ)) := by
            refine Finset.sum_congr rfl fun s hs => ?_
            rw [fourth_eq_falling_add s]
            ring
      _ =
        (∑ s ∈ Finset.range T,
          ((s : ℚ) * ((s-1 : Nat) : ℚ) * ((s-2 : Nat) : ℚ) *
              ((s-3 : Nat) : ℚ)) * y^s / (s.factorial : ℚ))
        + 6 * (∑ s ∈ Finset.range T,
          ((s : ℚ) * ((s-1 : Nat) : ℚ) * ((s-2 : Nat) : ℚ))
            * y^s / (s.factorial : ℚ))
        + 7 * (∑ s ∈ Finset.range T,
          ((s : ℚ) * ((s-1 : Nat) : ℚ)) * y^s / (s.factorial : ℚ))
        + ∑ s ∈ Finset.range T, (s : ℚ) * y^s / (s.factorial : ℚ) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
              Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  rw [hsplit]
  have hfall4 :
      (∑ s ∈ Finset.range T,
          ((s : ℚ) * ((s-1 : Nat) : ℚ) * ((s-2 : Nat) : ℚ) *
              ((s-3 : Nat) : ℚ)) * y^s / (s.factorial : ℚ))
        = y^4 * ∑ t ∈ Finset.range (T-4), y^t / (t.factorial : ℚ) := by
    simpa [mul_assoc] using poissonFallingFourth_sum_range y T
  have hfall3 :
      (∑ s ∈ Finset.range T,
          ((s : ℚ) * ((s-1 : Nat) : ℚ) * ((s-2 : Nat) : ℚ))
            * y^s / (s.factorial : ℚ))
        = y^3 * ∑ t ∈ Finset.range (T-3), y^t / (t.factorial : ℚ) := by
    simpa [mul_assoc] using poissonFallingThird_sum_range y T
  have hfall2 :
      (∑ s ∈ Finset.range T,
          ((s : ℚ) * ((s-1 : Nat) : ℚ)) * y^s / (s.factorial : ℚ))
        = y^2 * ∑ t ∈ Finset.range (T-2), y^t / (t.factorial : ℚ) := by
    simpa [mul_assoc] using poissonFallingSecond_sum_range y T
  rw [hfall4, hfall3, hfall2, poissonFirst_sum_range]
  have h4 := sum_exp_le y T₀ hy hyT (T-4)
  have h3 := sum_exp_le y T₀ hy hyT (T-3)
  have h2 := sum_exp_le y T₀ hy hyT (T-2)
  have h1 := sum_exp_le y T₀ hy hyT (T-1)
  calc
    y^4 * (∑ t ∈ Finset.range (T-4), y^t / (t.factorial : ℚ))
        + 6 * (y^3 * (∑ t ∈ Finset.range (T-3), y^t / (t.factorial : ℚ)))
        + 7 * (y^2 * (∑ t ∈ Finset.range (T-2), y^t / (t.factorial : ℚ)))
        + y * (∑ t ∈ Finset.range (T-1), y^t / (t.factorial : ℚ))
      ≤ y^4 * partialExpUpper y T₀
          + 6 * (y^3 * partialExpUpper y T₀)
          + 7 * (y^2 * partialExpUpper y T₀)
          + y * partialExpUpper y T₀ := by
          exact add_le_add
            (add_le_add
              (add_le_add
                (mul_le_mul_of_nonneg_left h4 (by positivity))
                (mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left h3 (by positivity)) (by norm_num)))
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left h2 (sq_nonneg y)) (by norm_num)))
            (mul_le_mul_of_nonneg_left h1 hy)
    _ = (y^4 + 6*y^3 + 7*y^2 + y) * partialExpUpper y T₀ := by ring

/-- The endpoint `ζ` used throughout §5. -/
def zetaMax : ℚ := 50/27

theorem zetaQ_nonneg (N m : Nat) : 0 ≤ zetaQ N m := by
  unfold zetaQ
  positivity

theorem zetaQ_le_zetaMax {N m : Nat}
    (hm : 1 ≤ m) (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ)) :
    zetaQ N m ≤ zetaMax := by
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  unfold zetaQ zetaMax
  calc
    5 * (N : ℚ) / (36 * (m : ℚ))
        ≤ 5 * ((40/3) * (m : ℚ)) / (36 * (m : ℚ)) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hN40 (by norm_num))
            (by positivity)
    _ = 50/27 := by
          field_simp [hmpos.ne']
          ring

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

theorem poissonThird_zetaMax_le (T : Nat) :
    ∑ s ∈ Finset.range T, (s : ℚ)^3 * zetaMax^s / (s.factorial : ℚ) ≤ 118 := by
  calc
    ∑ s ∈ Finset.range T, (s : ℚ)^3 * zetaMax^s / (s.factorial : ℚ)
        ≤ (zetaMax^3 + 3*zetaMax^2 + zetaMax) * partialExpUpper zetaMax 18 :=
          poissonThird_sum_le_partialExpUpper zetaMax 18 T (by norm_num [zetaMax])
            (by norm_num [zetaMax])
    _ ≤ 118 := by
          norm_num [zetaMax, partialExpUpper, Finset.sum_range_succ, Nat.factorial]

private theorem three_mul_le_of_mem_near {m s : Nat}
    (hs : s ∈ Finset.range (m/3 + 1)) : 3*s ≤ m := by
  have hsle : s ≤ m/3 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  exact (Nat.mul_le_mul_left 3 hsle).trans (Nat.mul_div_le m 3)

/-! ## P1: gamma-product residual numerical budget

Formalization note: the paper writes the product estimates with `exp(0.2237s)`.
This file keeps the sign-lock audit in `ℚ`; the factor
`(gammaTilt / zetaMax)^s` below is the rational surrogate for that exponential,
chosen so that multiplying by the weight `zetaMax^s` gives `gammaTilt^s`.
-/

/-- `q₂(s)=s(s+1)(2s+1)/6`, the quadratic-sum correction in the
gamma-product estimate. -/
def qTwo (s : Nat) : ℚ :=
  (s : ℚ) * ((s+1 : Nat) : ℚ) * (2*(s : ℚ) + 1) / 6

/-- Rational upper endpoint for `ζ·exp(0.2237)`, rounded up. -/
def gammaTilt : ℚ := 11581/5000

/-- Taylor-certified scalar inequality behind the rational exponential tilt:
`exp(0.2237) ≤ gammaTilt/zetaMax`. -/
theorem real_exp_tilt_scalar_le :
    Real.exp (2237/10000 : ℝ) ≤ ((gammaTilt / zetaMax : ℚ) : ℝ) := by
  let x : ℝ := 2237/10000
  let S : ℝ := ∑ k ∈ Finset.range 5, x^k / (k.factorial : ℝ)
  let tail : ℝ := |x|^5 * ((6 : ℝ) / (((5 : Nat).factorial : ℝ) * 5))
  have hxabs : |x| ≤ 1 := by
    dsimp [x]
    norm_num
  have hb := Real.exp_bound (x := x) hxabs (n := 5) (by norm_num)
  have hupper : Real.exp x ≤ S + tail := by
    have hleabs : Real.exp x - S ≤ |Real.exp x - S| := le_abs_self _
    dsimp [S, tail]
    linarith
  change Real.exp x ≤ ((gammaTilt / zetaMax : ℚ) : ℝ)
  calc
    Real.exp x ≤ S + tail := hupper
    _ ≤ ((gammaTilt / zetaMax : ℚ) : ℝ) := by
        dsimp [S, tail, x]
        norm_num [gammaTilt, zetaMax, Finset.sum_range_succ, Nat.factorial]

/-- Power form of the rational exponential tilt used in the weighted budgets. -/
theorem real_exp_tilt_linear_le_pow (s : Nat) :
    Real.exp ((2237/10000 : ℝ) * (s : ℝ))
      ≤ (((gammaTilt / zetaMax : ℚ)^s : ℚ) : ℝ) := by
  have hscalar := real_exp_tilt_scalar_le
  have hpow :
      (Real.exp (2237/10000 : ℝ))^s
        ≤ (((gammaTilt / zetaMax : ℚ) : ℝ))^s :=
    pow_le_pow_left₀ (Real.exp_nonneg _) hscalar s
  calc
    Real.exp ((2237/10000 : ℝ) * (s : ℝ))
        = Real.exp ((s : ℝ) * (2237/10000 : ℝ)) := by ring_nf
    _ = (Real.exp (2237/10000 : ℝ))^s := by
        rw [Real.exp_nat_mul]
    _ ≤ (((gammaTilt / zetaMax : ℚ) : ℝ))^s := hpow
    _ = (((gammaTilt / zetaMax : ℚ)^s : ℚ) : ℝ) := by norm_num

private theorem zetaMax_pow_mul_tilt_pow (s : Nat) :
    zetaMax^s * (gammaTilt / zetaMax)^s = gammaTilt^s := by
  rw [← mul_pow]
  have hbase : zetaMax * (gammaTilt / zetaMax) = gammaTilt := by
    norm_num [zetaMax, gammaTilt]
  rw [hbase]

/-- Rational upper bound for the logarithmic product estimate:
`e₁(s)/m + 3q₂(s)/(4m²)` in the paper.  This is not yet a logarithm in Lean;
it is the rational arithmetic expression that will feed the product/log bridge. -/
def piLogUpperBound (m s : Nat) : ℚ :=
  eOne s / (m : ℚ) + (3/4) * qTwo s / (m : ℚ)^2

theorem piLogUpperBound_nonneg {m s : Nat} (hm : 1 ≤ m) :
    0 ≤ piLogUpperBound m s := by
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  have hq : 0 ≤ qTwo s := by
    unfold qTwo
    positivity
  unfold piLogUpperBound
  exact add_nonneg
    (div_nonneg (eOne_nonneg s) hmpos.le)
    (div_nonneg (mul_nonneg (by norm_num) hq) (sq_nonneg (m : ℚ)))

theorem piLogUpperBound_succ (m s : Nat) :
    piLogUpperBound m (s+1)
      = piLogUpperBound m s
        + (((s+1 : Nat) : ℚ) / (m : ℚ)
          + (3/4) * (((s+1 : Nat) : ℚ)^2 / (m : ℚ)^2)) := by
  unfold piLogUpperBound eOne qTwo
  norm_num [Nat.cast_add, Nat.cast_one, Nat.cast_succ]
  ring_nf

/-- The paper's logarithmic product estimate in the near range:
`log Π_s ≤ e₁(s)/m + 3q₂(s)/(4m²)`. -/
theorem real_log_PiFactor_le_piLogUpperBound
    {m s : Nat} (hm : 361 ≤ m) (hs3 : 3*s ≤ m) :
    Real.log (PiFactor m s : ℝ) ≤ (piLogUpperBound m s : ℝ) := by
  revert m
  induction s with
  | zero =>
      intro m hm hs3
      rw [PiFactor_zero m (by omega)]
      norm_num [piLogUpperBound, eOne, qTwo]
  | succ s ih =>
      intro m hm hs3
      have hmposQ : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
      have hmposR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
      have hslt : s < m := by omega
      have hsucc_lt : s+1 < m := by omega
      have hprev := ih hm (by omega : 3*s ≤ m)
      have hsuccQ := PiFactor_succ (m := m) (s := s) hsucc_lt
      have hsuccR :
          (PiFactor m (s+1) : ℝ)
            = (PiFactor m s : ℝ) * (m : ℝ) / (((m-s-1 : Nat) : ℝ)) := by
        exact_mod_cast hsuccQ
      have hPi_pos : 0 < (PiFactor m s : ℝ) := by
        exact_mod_cast (PiFactor_pos (m := m) (s := s) hslt)
      have hdenpos : (0 : ℝ) < (((m-s-1 : Nat) : ℝ)) := by
        exact_mod_cast (by omega : 0 < m-s-1)
      have hfac_pos : 0 < (m : ℝ) / (((m-s-1 : Nat) : ℝ)) := by positivity
      have hden_cast :
          (((m-s-1 : Nat) : ℝ)) = (m : ℝ) - ((s+1 : Nat) : ℝ) := by
        rw [show m-s-1 = m-(s+1) by omega, Nat.cast_sub (by omega : s+1 ≤ m)]
      have hfac :
          Real.log ((m : ℝ) / (((m-s-1 : Nat) : ℝ)))
            ≤ (((s+1 : Nat) : ℝ) / (m : ℝ))
              + (3/4) * (((s+1 : Nat) : ℝ) / (m : ℝ))^2 := by
        let x : ℝ := ((s+1 : Nat) : ℝ) / (m : ℝ)
        have hx0 : 0 ≤ x := by
          dsimp [x]
          positivity
        have hx13 : x ≤ 1/3 := by
          dsimp [x]
          rw [div_le_iff₀ hmposR]
          have hsQ : (3 : ℝ) * (((s+1 : Nat) : ℝ)) ≤ (m : ℝ) := by
            exact_mod_cast hs3
          linarith
        have hfactor :
            (m : ℝ) / (((m-s-1 : Nat) : ℝ)) = (1 - x)⁻¹ := by
          dsimp [x]
          rw [hden_cast]
          field_simp [hmposR.ne']
        rw [hfactor, Real.log_inv]
        exact neg_log_one_sub_le_quadratic hx0 hx13
      have hLsuccQ := piLogUpperBound_succ m s
      have hLsuccR :
          (piLogUpperBound m (s+1) : ℝ)
            =
          (piLogUpperBound m s : ℝ)
            + ((((s+1 : Nat) : ℚ) / (m : ℚ)
              + (3/4) * (((s+1 : Nat) : ℚ)^2 / (m : ℚ)^2) : ℚ) : ℝ) := by
        exact_mod_cast hLsuccQ
      calc
        Real.log (PiFactor m (s+1) : ℝ)
            = Real.log ((PiFactor m s : ℝ) * ((m : ℝ) / (((m-s-1 : Nat) : ℝ)))) := by
              rw [hsuccR]
              ring
        _ = Real.log (PiFactor m s : ℝ)
              + Real.log ((m : ℝ) / (((m-s-1 : Nat) : ℝ))) := by
              rw [Real.log_mul hPi_pos.ne' hfac_pos.ne']
        _ ≤ (piLogUpperBound m s : ℝ)
              + ((((s+1 : Nat) : ℝ) / (m : ℝ))
                + (3/4) * (((s+1 : Nat) : ℝ) / (m : ℝ))^2) :=
              add_le_add hprev hfac
        _ = (piLogUpperBound m (s+1) : ℝ) := by
              rw [hLsuccR]
              norm_num
              field_simp [hmposQ.ne']

/-- Arithmetic part of the paper's `L_s ≤ 1.168 e₁(s)/m` estimate. -/
theorem piLogUpperBound_le_u_linear
    {m s : Nat} (hm : 361 ≤ m) (hs3 : 3*s ≤ m) :
    piLogUpperBound m s ≤ (146/125) * eOne s / (m : ℚ) := by
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  have hmQ : (361 : ℚ) ≤ m := by exact_mod_cast hm
  have hsQ : (3 : ℚ) * (s : ℚ) ≤ m := by exact_mod_cast hs3
  unfold piLogUpperBound eOne qTwo
  field_simp [hmpos.ne']
  nlinarith

/-- Arithmetic part of the paper's `L_s < 0.2237s` estimate, weakened to a
closed rational inequality. -/
theorem piLogUpperBound_le_tilt_linear
    {m s : Nat} (hm : 361 ≤ m) (hs3 : 3*s ≤ m) :
    piLogUpperBound m s ≤ (2237/10000) * (s : ℚ) := by
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  have hmQ : (361 : ℚ) ≤ m := by exact_mod_cast hm
  have hsQ : (3 : ℚ) * (s : ℚ) ≤ m := by exact_mod_cast hs3
  rcases (by omega : s = 0 ∨ s = 1 ∨ 2 ≤ s) with rfl | hsmall
  · norm_num [piLogUpperBound, eOne, qTwo]
  rcases hsmall with rfl | hsge2
  · have hm2lower : (361 : ℚ)^2 ≤ (m : ℚ)^2 := by
      nlinarith [hmQ, hmpos.le]
    norm_num [piLogUpperBound, eOne, qTwo]
    field_simp [hmpos.ne']
    nlinarith [hmQ, hm2lower]
  have hs_nonneg : (0 : ℚ) ≤ s := by positivity
  have heOne :
      eOne s / (m : ℚ) ≤ (1/6) * (s : ℚ) + (1/722) * (s : ℚ) := by
    have hs2_bound : (s : ℚ)^2 ≤ (s : ℚ) * (m : ℚ) / 3 := by
      nlinarith [mul_nonneg hs_nonneg (sub_nonneg.mpr hsQ)]
    have hs1_bound : (s : ℚ) ≤ (s : ℚ) * (m : ℚ) / 361 := by
      nlinarith [mul_nonneg hs_nonneg (sub_nonneg.mpr hmQ)]
    unfold eOne
    push_cast
    field_simp [hmpos.ne']
    nlinarith [hs2_bound, hs1_bound]
  have hqpoly : (((s+1 : Nat) : ℚ)) * (2*(s : ℚ) + 1) ≤ 4*(s : ℚ)^2 := by
    have hsge2Q : (2 : ℚ) ≤ s := by exact_mod_cast hsge2
    push_cast
    nlinarith
  have hs_sq_bound : 9 * (s : ℚ)^2 ≤ (m : ℚ)^2 := by
    nlinarith [hsQ, hs_nonneg, hmpos.le]
  have hq :
      (3/4) * qTwo s / (m : ℚ)^2 ≤ (1/18) * (s : ℚ) := by
    unfold qTwo
    field_simp [sq_pos_of_pos hmpos]
    nlinarith [hqpoly, hs_sq_bound, hs_nonneg]
  calc
    piLogUpperBound m s
      = eOne s / (m : ℚ) + (3/4) * qTwo s / (m : ℚ)^2 := rfl
    _ ≤ ((1/6) * (s : ℚ) + (1/722) * (s : ℚ)) + (1/18) * (s : ℚ) :=
        add_le_add heOne hq
    _ ≤ (2237/10000) * (s : ℚ) := by
        nlinarith [hs_nonneg]

/-- Exponential form of `L_s < 0.2237s`, with the rational tilt replacing
the paper's decimal exponential. -/
theorem real_exp_piLogUpperBound_le_tilt_pow
    {m s : Nat} (hm : 361 ≤ m) (hs3 : 3*s ≤ m) :
    Real.exp (piLogUpperBound m s : ℝ)
      ≤ (((gammaTilt / zetaMax : ℚ)^s : ℚ) : ℝ) := by
  have hlinearQ := piLogUpperBound_le_tilt_linear (m := m) (s := s) hm hs3
  have hlinearCast :
      ((piLogUpperBound m s : ℚ) : ℝ)
        ≤ (((2237/10000 : ℚ) * (s : ℚ) : ℚ) : ℝ) := by
    exact_mod_cast hlinearQ
  have hlinear :
      (piLogUpperBound m s : ℝ)
        ≤ (2237/10000 : ℝ) * (s : ℝ) := by
    simpa using hlinearCast
  exact (Real.exp_le_exp.mpr hlinear).trans (real_exp_tilt_linear_le_pow s)

/-- Pointwise product estimate feeding the P4 bridge:
`Π_s-1 ≤ L_s·(gammaTilt/zetaMax)^s`.  This is the Lean replacement for the
paper's `exp(0.2237s)` factor, certified by `real_exp_tilt_scalar_le`. -/
theorem PiFactor_sub_one_le_piLogUpperProductBound
    {m s : Nat} (hm : 361 ≤ m) (hs3 : 3*s ≤ m) :
    PiFactor m s - 1
      ≤ piLogUpperBound m s * (gammaTilt / zetaMax)^s := by
  have hslt : s < m := by omega
  have hPi_pos : 0 < (PiFactor m s : ℝ) := by
    exact_mod_cast (PiFactor_pos (m := m) (s := s) hslt)
  have hL_nonnegQ : 0 ≤ piLogUpperBound m s :=
    piLogUpperBound_nonneg (m := m) (s := s) (by omega : 1 ≤ m)
  have hL_nonneg : 0 ≤ (piLogUpperBound m s : ℝ) := by
    exact_mod_cast hL_nonnegQ
  have hlog := real_log_PiFactor_le_piLogUpperBound (m := m) (s := s) hm hs3
  have hPi_le_expL :
      (PiFactor m s : ℝ) ≤ Real.exp (piLogUpperBound m s : ℝ) :=
    (Real.log_le_iff_le_exp hPi_pos).mp hlog
  have hexp_tilt :
      Real.exp (piLogUpperBound m s : ℝ)
        ≤ (((gammaTilt / zetaMax : ℚ)^s : ℚ) : ℝ) :=
    real_exp_piLogUpperBound_le_tilt_pow (m := m) (s := s) hm hs3
  have hreal :
      ((PiFactor m s - 1 : ℚ) : ℝ)
        ≤ ((piLogUpperBound m s * (gammaTilt / zetaMax)^s : ℚ) : ℝ) := by
    calc
      ((PiFactor m s - 1 : ℚ) : ℝ)
          = (PiFactor m s : ℝ) - 1 := by norm_num
      _ ≤ Real.exp (piLogUpperBound m s : ℝ) - 1 :=
          sub_le_sub_right hPi_le_expL 1
      _ ≤ (piLogUpperBound m s : ℝ) *
            Real.exp (piLogUpperBound m s : ℝ) :=
          real_exp_sub_one_le_mul_exp _
      _ ≤ (piLogUpperBound m s : ℝ) *
            (((gammaTilt / zetaMax : ℚ)^s : ℚ) : ℝ) :=
          mul_le_mul_of_nonneg_left hexp_tilt hL_nonneg
      _ = ((piLogUpperBound m s * (gammaTilt / zetaMax)^s : ℚ) : ℝ) := by
          norm_num
  exact_mod_cast hreal

theorem poissonFirst_gammaTilt_le (T : Nat) :
    ∑ s ∈ Finset.range T, (s : ℚ) * gammaTilt^s / (s.factorial : ℚ) ≤ 47/2 := by
  calc
    ∑ s ∈ Finset.range T, (s : ℚ) * gammaTilt^s / (s.factorial : ℚ)
        ≤ gammaTilt * partialExpUpper gammaTilt 18 :=
          poissonFirst_sum_le_partialExpUpper gammaTilt 18 T (by norm_num [gammaTilt])
            (by norm_num [gammaTilt])
    _ ≤ 47/2 := by
          norm_num [gammaTilt, partialExpUpper, Finset.sum_range_succ, Nat.factorial]

theorem poissonSecond_gammaTilt_le (T : Nat) :
    ∑ s ∈ Finset.range T, (s : ℚ)^2 * gammaTilt^s / (s.factorial : ℚ) ≤ 78 := by
  calc
    ∑ s ∈ Finset.range T, (s : ℚ)^2 * gammaTilt^s / (s.factorial : ℚ)
        ≤ (gammaTilt^2 + gammaTilt) * partialExpUpper gammaTilt 18 :=
          poissonSecond_sum_le_partialExpUpper gammaTilt 18 T (by norm_num [gammaTilt])
            (by norm_num [gammaTilt])
    _ ≤ 78 := by
          norm_num [gammaTilt, partialExpUpper, Finset.sum_range_succ, Nat.factorial]

theorem poissonThird_gammaTilt_le (T : Nat) :
    ∑ s ∈ Finset.range T, (s : ℚ)^3 * gammaTilt^s / (s.factorial : ℚ) ≤ 3131/10 := by
  calc
    ∑ s ∈ Finset.range T, (s : ℚ)^3 * gammaTilt^s / (s.factorial : ℚ)
        ≤ (gammaTilt^3 + 3*gammaTilt^2 + gammaTilt) * partialExpUpper gammaTilt 18 :=
          poissonThird_sum_le_partialExpUpper gammaTilt 18 T (by norm_num [gammaTilt])
            (by norm_num [gammaTilt])
    _ ≤ 3131/10 := by
          norm_num [gammaTilt, partialExpUpper, Finset.sum_range_succ, Nat.factorial]

theorem poissonFourth_gammaTilt_le (T : Nat) :
    ∑ s ∈ Finset.range T, (s : ℚ)^4 * gammaTilt^s / (s.factorial : ℚ) ≤ 1455 := by
  calc
    ∑ s ∈ Finset.range T, (s : ℚ)^4 * gammaTilt^s / (s.factorial : ℚ)
        ≤ (gammaTilt^4 + 6*gammaTilt^3 + 7*gammaTilt^2 + gammaTilt)
            * partialExpUpper gammaTilt 18 :=
          poissonFourth_sum_le_partialExpUpper gammaTilt 18 T (by norm_num [gammaTilt])
            (by norm_num [gammaTilt])
    _ ≤ 1455 := by
          norm_num [gammaTilt, partialExpUpper, Finset.sum_range_succ, Nat.factorial]

theorem poissonEOneSq_gammaTilt_le (T : Nat) :
    ∑ s ∈ Finset.range T, (eOne s)^2 * gammaTilt^s / (s.factorial : ℚ) ≤ 540 := by
  have hsplit :
      (∑ s ∈ Finset.range T, (eOne s)^2 * gammaTilt^s / (s.factorial : ℚ))
        =
      (1/4) * (∑ s ∈ Finset.range T,
          (s : ℚ)^4 * gammaTilt^s / (s.factorial : ℚ))
        + (1/2) * (∑ s ∈ Finset.range T,
          (s : ℚ)^3 * gammaTilt^s / (s.factorial : ℚ))
        + (1/4) * (∑ s ∈ Finset.range T,
          (s : ℚ)^2 * gammaTilt^s / (s.factorial : ℚ)) := by
    calc
      (∑ s ∈ Finset.range T, (eOne s)^2 * gammaTilt^s / (s.factorial : ℚ))
          =
        ∑ s ∈ Finset.range T,
          ((1/4) * ((s : ℚ)^4 * gammaTilt^s / (s.factorial : ℚ))
            + (1/2) * ((s : ℚ)^3 * gammaTilt^s / (s.factorial : ℚ))
            + (1/4) * ((s : ℚ)^2 * gammaTilt^s / (s.factorial : ℚ))) := by
            refine Finset.sum_congr rfl fun s hs => ?_
            unfold eOne
            push_cast
            ring
      _ =
        (1/4) * (∑ s ∈ Finset.range T,
          (s : ℚ)^4 * gammaTilt^s / (s.factorial : ℚ))
        + (1/2) * (∑ s ∈ Finset.range T,
          (s : ℚ)^3 * gammaTilt^s / (s.factorial : ℚ))
        + (1/4) * (∑ s ∈ Finset.range T,
          (s : ℚ)^2 * gammaTilt^s / (s.factorial : ℚ)) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum,
              Finset.mul_sum, Finset.mul_sum]
  rw [hsplit]
  calc
    (1/4) * (∑ s ∈ Finset.range T,
          (s : ℚ)^4 * gammaTilt^s / (s.factorial : ℚ))
        + (1/2) * (∑ s ∈ Finset.range T,
          (s : ℚ)^3 * gammaTilt^s / (s.factorial : ℚ))
        + (1/4) * (∑ s ∈ Finset.range T,
          (s : ℚ)^2 * gammaTilt^s / (s.factorial : ℚ))
      ≤ (1/4) * 1455 + (1/2) * (3131/10) + (1/4) * 78 := by
          exact add_le_add
            (add_le_add
              (mul_le_mul_of_nonneg_left (poissonFourth_gammaTilt_le T) (by norm_num))
              (mul_le_mul_of_nonneg_left (poissonThird_gammaTilt_le T) (by norm_num)))
            (mul_le_mul_of_nonneg_left (poissonSecond_gammaTilt_le T) (by norm_num))
    _ ≤ 540 := by norm_num

theorem poissonEOne_gammaTilt_le (T : Nat) :
    ∑ s ∈ Finset.range T, eOne s * gammaTilt^s / (s.factorial : ℚ) ≤ 203/4 := by
  have hsplit :
      (∑ s ∈ Finset.range T, eOne s * gammaTilt^s / (s.factorial : ℚ))
        =
      (1/2) * (∑ s ∈ Finset.range T,
          (s : ℚ)^2 * gammaTilt^s / (s.factorial : ℚ))
        + (1/2) * (∑ s ∈ Finset.range T,
          (s : ℚ) * gammaTilt^s / (s.factorial : ℚ)) := by
    calc
      (∑ s ∈ Finset.range T, eOne s * gammaTilt^s / (s.factorial : ℚ))
          =
        ∑ s ∈ Finset.range T,
          ((1/2) * ((s : ℚ)^2 * gammaTilt^s / (s.factorial : ℚ))
            + (1/2) * ((s : ℚ) * gammaTilt^s / (s.factorial : ℚ))) := by
            refine Finset.sum_congr rfl fun s hs => ?_
            unfold eOne
            push_cast
            ring
      _ =
        (1/2) * (∑ s ∈ Finset.range T,
          (s : ℚ)^2 * gammaTilt^s / (s.factorial : ℚ))
        + (1/2) * (∑ s ∈ Finset.range T,
          (s : ℚ) * gammaTilt^s / (s.factorial : ℚ)) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  rw [hsplit]
  calc
    (1/2) * (∑ s ∈ Finset.range T,
          (s : ℚ)^2 * gammaTilt^s / (s.factorial : ℚ))
        + (1/2) * (∑ s ∈ Finset.range T,
          (s : ℚ) * gammaTilt^s / (s.factorial : ℚ))
      ≤ (1/2) * 78 + (1/2) * (47/2) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (poissonSecond_gammaTilt_le T) (by norm_num))
            (mul_le_mul_of_nonneg_left (poissonFirst_gammaTilt_le T) (by norm_num))
    _ = 203/4 := by norm_num

theorem poissonEOneMulS_gammaTilt_le (T : Nat) :
    ∑ s ∈ Finset.range T, eOne s * (s : ℚ) * gammaTilt^s / (s.factorial : ℚ)
      ≤ 196 := by
  have hsplit :
      (∑ s ∈ Finset.range T, eOne s * (s : ℚ) * gammaTilt^s / (s.factorial : ℚ))
        =
      (1/2) * (∑ s ∈ Finset.range T,
          (s : ℚ)^3 * gammaTilt^s / (s.factorial : ℚ))
        + (1/2) * (∑ s ∈ Finset.range T,
          (s : ℚ)^2 * gammaTilt^s / (s.factorial : ℚ)) := by
    calc
      (∑ s ∈ Finset.range T, eOne s * (s : ℚ) * gammaTilt^s / (s.factorial : ℚ))
          =
        ∑ s ∈ Finset.range T,
          ((1/2) * ((s : ℚ)^3 * gammaTilt^s / (s.factorial : ℚ))
            + (1/2) * ((s : ℚ)^2 * gammaTilt^s / (s.factorial : ℚ))) := by
            refine Finset.sum_congr rfl fun s hs => ?_
            unfold eOne
            push_cast
            ring
      _ =
        (1/2) * (∑ s ∈ Finset.range T,
          (s : ℚ)^3 * gammaTilt^s / (s.factorial : ℚ))
        + (1/2) * (∑ s ∈ Finset.range T,
          (s : ℚ)^2 * gammaTilt^s / (s.factorial : ℚ)) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  rw [hsplit]
  calc
    (1/2) * (∑ s ∈ Finset.range T,
          (s : ℚ)^3 * gammaTilt^s / (s.factorial : ℚ))
        + (1/2) * (∑ s ∈ Finset.range T,
          (s : ℚ)^2 * gammaTilt^s / (s.factorial : ℚ))
      ≤ (1/2) * (3131/10) + (1/2) * 78 := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (poissonThird_gammaTilt_le T) (by norm_num))
            (mul_le_mul_of_nonneg_left (poissonSecond_gammaTilt_le T) (by norm_num))
    _ ≤ 196 := by norm_num

theorem poissonQTwo_zetaMax_le (T : Nat) :
    ∑ s ∈ Finset.range T, qTwo s * zetaMax^s / (s.factorial : ℚ) ≤ 59 := by
  have hsplit :
      (∑ s ∈ Finset.range T, qTwo s * zetaMax^s / (s.factorial : ℚ))
        =
      (1/3) * (∑ s ∈ Finset.range T,
          (s : ℚ)^3 * zetaMax^s / (s.factorial : ℚ))
        + (1/2) * (∑ s ∈ Finset.range T,
          (s : ℚ)^2 * zetaMax^s / (s.factorial : ℚ))
        + (1/6) * (∑ s ∈ Finset.range T,
          (s : ℚ) * zetaMax^s / (s.factorial : ℚ)) := by
    calc
      (∑ s ∈ Finset.range T, qTwo s * zetaMax^s / (s.factorial : ℚ))
          =
        ∑ s ∈ Finset.range T,
          ((1/3) * ((s : ℚ)^3 * zetaMax^s / (s.factorial : ℚ))
            + (1/2) * ((s : ℚ)^2 * zetaMax^s / (s.factorial : ℚ))
            + (1/6) * ((s : ℚ) * zetaMax^s / (s.factorial : ℚ))) := by
            refine Finset.sum_congr rfl fun s hs => ?_
            unfold qTwo
            push_cast
            ring
      _ =
        (1/3) * (∑ s ∈ Finset.range T,
          (s : ℚ)^3 * zetaMax^s / (s.factorial : ℚ))
        + (1/2) * (∑ s ∈ Finset.range T,
          (s : ℚ)^2 * zetaMax^s / (s.factorial : ℚ))
        + (1/6) * (∑ s ∈ Finset.range T,
          (s : ℚ) * zetaMax^s / (s.factorial : ℚ)) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum,
              Finset.mul_sum, Finset.mul_sum]
  rw [hsplit]
  calc
    (1/3) * (∑ s ∈ Finset.range T,
          (s : ℚ)^3 * zetaMax^s / (s.factorial : ℚ))
        + (1/2) * (∑ s ∈ Finset.range T,
          (s : ℚ)^2 * zetaMax^s / (s.factorial : ℚ))
        + (1/6) * (∑ s ∈ Finset.range T,
          (s : ℚ) * zetaMax^s / (s.factorial : ℚ))
      ≤ (1/3) * 118 + (1/2) * 34 + (1/6) * 12 := by
          exact add_le_add
            (add_le_add
              (mul_le_mul_of_nonneg_left (poissonThird_zetaMax_le T) (by norm_num))
              (mul_le_mul_of_nonneg_left (poissonSecond_zetaMax_le T) (by norm_num)))
            (mul_le_mul_of_nonneg_left (poissonFirst_zetaMax_le T) (by norm_num))
    _ ≤ 59 := by norm_num

/-- Explicit P1 weighted majorant term:
the first part is the tilted `e₁²` contribution, and the second is the
`q₂` correction. -/
def gammaResidualBudgetTerm (m s : Nat) : ℚ :=
  ((1/2) * (146/125)^2 * (eOne s)^2 * gammaTilt^s / (s.factorial : ℚ)
    + (3/4) * qTwo s * zetaMax^s / (s.factorial : ℚ)) / (m : ℚ)^2

/-- Rational pointwise majorant for the extracted `Π_s` residual
`π_s = Π_s - 1 - e₁(s)/m`, matching the paper's
`1/2·(1.168e₁/m)^2·exp(0.2237s) + 3q₂/(4m²)` after the exponential is replaced
by `(gammaTilt/zetaMax)^s`. -/
def piResidualBridgeBound (m s : Nat) : ℚ :=
  ((1/2) * (146/125)^2 * (eOne s)^2 * (gammaTilt / zetaMax)^s
    + (3/4) * qTwo s) / (m : ℚ)^2

/-- Intermediate P1 remainder bound coming directly from
`exp(x)-1-x ≤ x² exp(x)/2` after replacing `exp(0.2237s)` by the rational
tilt.  The next lemma converts this expression to `piResidualBridgeBound`
using `piLogUpperBound ≤ 1.168e₁/m`. -/
def piResidualExpRemainderBound (m s : Nat) : ℚ :=
  (1/2) * (piLogUpperBound m s)^2 * (gammaTilt / zetaMax)^s
    + (3/4) * qTwo s / (m : ℚ)^2

/-- Pointwise P1 gamma-product residual estimate:
after extracting `e₁(s)/m`, the remaining product error is controlled by the
quadratic exponential remainder plus the `q₂` logarithmic correction. -/
theorem piResidual_le_piResidualExpRemainderBound
    {m s : Nat} (hm : 361 ≤ m) (hs3 : 3*s ≤ m) :
    piResidual m s ≤ piResidualExpRemainderBound m s := by
  have hslt : s < m := by omega
  have hPi_pos : 0 < (PiFactor m s : ℝ) := by
    exact_mod_cast (PiFactor_pos (m := m) (s := s) hslt)
  have hL_nonnegQ : 0 ≤ piLogUpperBound m s :=
    piLogUpperBound_nonneg (m := m) (s := s) (by omega : 1 ≤ m)
  have hL_nonneg : 0 ≤ (piLogUpperBound m s : ℝ) := by
    exact_mod_cast hL_nonnegQ
  have hlog := real_log_PiFactor_le_piLogUpperBound (m := m) (s := s) hm hs3
  have hPi_le_expL :
      (PiFactor m s : ℝ) ≤ Real.exp (piLogUpperBound m s : ℝ) :=
    (Real.log_le_iff_le_exp hPi_pos).mp hlog
  let L : ℝ := (piLogUpperBound m s : ℝ)
  let A : ℝ := ((eOne s / (m : ℚ) : ℚ) : ℝ)
  let B : ℝ := (((3/4) * qTwo s / (m : ℚ)^2 : ℚ) : ℝ)
  let R : ℝ := (((gammaTilt / zetaMax : ℚ)^s : ℚ) : ℝ)
  have hLsplit : L = A + B := by
    dsimp [L, A, B]
    norm_num [piLogUpperBound]
  have hexp_tilt : Real.exp L ≤ R := by
    dsimp [L, R]
    exact real_exp_piLogUpperBound_le_tilt_pow (m := m) (s := s) hm hs3
  have hquad :
      Real.exp L - 1 - L ≤ (1/2) * L^2 * R := by
    calc
      Real.exp L - 1 - L
          ≤ (1/2) * L^2 * Real.exp L :=
          real_exp_sub_one_sub_id_le_half_sq_mul_exp (by simpa [L] using hL_nonneg)
      _ ≤ (1/2) * L^2 * R :=
          mul_le_mul_of_nonneg_left hexp_tilt (by positivity)
  have hreal :
      ((piResidual m s : ℚ) : ℝ)
        ≤ ((piResidualExpRemainderBound m s : ℚ) : ℝ) := by
    calc
      ((piResidual m s : ℚ) : ℝ)
          = (PiFactor m s : ℝ) - 1 - A := by
          dsimp [A]
          norm_num [piResidual]
      _ ≤ Real.exp L - 1 - A := by
          dsimp [L]
          linarith
      _ = (Real.exp L - 1 - L) + B := by
          rw [hLsplit]
          ring
      _ ≤ (1/2) * L^2 * R + B := by
          exact add_le_add hquad le_rfl
      _ = ((piResidualExpRemainderBound m s : ℚ) : ℝ) := by
          dsimp [L, B, R]
          norm_num [piResidualExpRemainderBound]
  exact_mod_cast hreal

theorem piResidualBridgeBound_nonneg (m s : Nat) :
    0 ≤ piResidualBridgeBound m s := by
  have htilt : 0 ≤ gammaTilt / zetaMax := by norm_num [gammaTilt, zetaMax]
  have hq : 0 ≤ qTwo s := by
    unfold qTwo
    positivity
  unfold piResidualBridgeBound
  exact div_nonneg
    (add_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg (eOne s)))
        (pow_nonneg htilt s))
      (mul_nonneg (by norm_num) hq))
    (sq_nonneg (m : ℚ))

theorem piResidualExpRemainderBound_le_bridgeBound
    {m s : Nat} (hm : 361 ≤ m) (hs3 : 3*s ≤ m) :
    piResidualExpRemainderBound m s ≤ piResidualBridgeBound m s := by
  have htilt : 0 ≤ (gammaTilt / zetaMax)^s := by
    exact pow_nonneg (by norm_num [gammaTilt, zetaMax]) s
  have hL_nonneg : 0 ≤ piLogUpperBound m s :=
    piLogUpperBound_nonneg (m := m) (s := s) (by omega : 1 ≤ m)
  have hL := piLogUpperBound_le_u_linear (m := m) (s := s) hm hs3
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  have hU_nonneg : 0 ≤ (146/125) * eOne s / (m : ℚ) := by
    exact div_nonneg
      (mul_nonneg (by norm_num) (eOne_nonneg s))
      hmpos.le
  have hL_lower : -((146/125) * eOne s / (m : ℚ)) ≤ piLogUpperBound m s := by
    linarith
  have hLsq :
      (piLogUpperBound m s)^2
        ≤ ((146/125) * eOne s / (m : ℚ))^2 := by
    exact sq_le_sq' hL_lower hL
  have hmain :
      (1/2) * (piLogUpperBound m s)^2 * (gammaTilt / zetaMax)^s
        ≤ (1/2) * ((146/125) * eOne s / (m : ℚ))^2 *
            (gammaTilt / zetaMax)^s := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hLsq (by norm_num)) htilt
  unfold piResidualExpRemainderBound piResidualBridgeBound
  calc
    (1/2) * (piLogUpperBound m s)^2 * (gammaTilt / zetaMax)^s
        + (3/4) * qTwo s / (m : ℚ)^2
      ≤ (1/2) * ((146/125) * eOne s / (m : ℚ))^2 *
            (gammaTilt / zetaMax)^s
          + (3/4) * qTwo s / (m : ℚ)^2 := by
          exact add_le_add hmain le_rfl
    _ =
        ((1/2) * (146/125)^2 * (eOne s)^2 * (gammaTilt / zetaMax)^s
          + (3/4) * qTwo s) / (m : ℚ)^2 := by
          ring

private theorem weighted_piResidualBridgeBound_eq_gammaResidualBudgetTerm
    (m s : Nat) :
    (zetaMax^s / (s.factorial : ℚ)) * piResidualBridgeBound m s
      = gammaResidualBudgetTerm m s := by
  unfold piResidualBridgeBound gammaResidualBudgetTerm
  calc
    (zetaMax^s / (s.factorial : ℚ)) *
        (((1/2) * (146/125)^2 * (eOne s)^2 * (gammaTilt / zetaMax)^s
          + (3/4) * qTwo s) / (m : ℚ)^2)
      =
        ((1/2) * (146/125)^2 * (eOne s)^2 *
          (zetaMax^s * (gammaTilt / zetaMax)^s) / (s.factorial : ℚ)
          + (3/4) * qTwo s * zetaMax^s / (s.factorial : ℚ)) /
            (m : ℚ)^2 := by
          ring
    _ =
        ((1/2) * (146/125)^2 * (eOne s)^2 *
          gammaTilt^s / (s.factorial : ℚ)
          + (3/4) * qTwo s * zetaMax^s / (s.factorial : ℚ)) /
            (m : ℚ)^2 := by
          rw [zetaMax_pow_mul_tilt_pow]

/-- Conditional P1 bridge: once the product/log estimate supplies the
pointwise `π_s` majorant, the weighted term is exactly the P1 budget term. -/
theorem weighted_piResidual_le_gammaResidualBudgetTerm
    {m s : Nat} (hs : s < m)
    (hpi : piResidual m s ≤ piResidualBridgeBound m s) :
    (zetaMax^s / (s.factorial : ℚ)) * |piResidual m s|
      ≤ gammaResidualBudgetTerm m s := by
  have hweight : 0 ≤ zetaMax^s / (s.factorial : ℚ) := by
    have hz : 0 ≤ zetaMax := by norm_num [zetaMax]
    positivity
  have hpi_nonneg : 0 ≤ piResidual m s :=
    piResidual_nonneg (m := m) (s := s) hs
  calc
    (zetaMax^s / (s.factorial : ℚ)) * |piResidual m s|
      = (zetaMax^s / (s.factorial : ℚ)) * piResidual m s := by
          rw [abs_of_nonneg hpi_nonneg]
    _ ≤ (zetaMax^s / (s.factorial : ℚ)) * piResidualBridgeBound m s :=
          mul_le_mul_of_nonneg_left hpi hweight
    _ = gammaResidualBudgetTerm m s :=
          weighted_piResidualBridgeBound_eq_gammaResidualBudgetTerm m s

/-- Conditional P1 bridge in the form produced by the product/log proof:
`π_s` is first bounded by the quadratic exponential remainder, then by the
weighted P1 budget term. -/
theorem weighted_piResidual_le_gammaResidualBudgetTerm_of_expRemainder
    {m s : Nat} (hm : 361 ≤ m) (hs3 : 3*s ≤ m) (hs : s < m)
    (hpi : piResidual m s ≤ piResidualExpRemainderBound m s) :
    (zetaMax^s / (s.factorial : ℚ)) * |piResidual m s|
      ≤ gammaResidualBudgetTerm m s :=
  weighted_piResidual_le_gammaResidualBudgetTerm (m := m) (s := s) hs
    (hpi.trans (piResidualExpRemainderBound_le_bridgeBound
      (m := m) (s := s) hm hs3))

/-- Closed P1 pointwise weighted bridge in the near range. -/
theorem weighted_piResidual_le_gammaResidualBudgetTerm_near
    {m s : Nat} (hm : 361 ≤ m) (hs3 : 3*s ≤ m) :
    (zetaMax^s / (s.factorial : ℚ)) * |piResidual m s|
      ≤ gammaResidualBudgetTerm m s :=
  weighted_piResidual_le_gammaResidualBudgetTerm_of_expRemainder
    (m := m) (s := s) hm hs3 (by omega : s < m)
    (piResidual_le_piResidualExpRemainderBound (m := m) (s := s) hm hs3)

theorem signLock_P1_budget_zetaMax {m : Nat} (hm : 1 ≤ m) :
    ∑ s ∈ Finset.range (m/3 + 1), gammaResidualBudgetTerm m s
      ≤ 426 / (m : ℚ)^2 := by
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  have hsplit :
      (∑ s ∈ Finset.range (m/3 + 1), gammaResidualBudgetTerm m s)
        =
      (((1/2) * (146/125)^2) *
          (∑ s ∈ Finset.range (m/3 + 1),
            (eOne s)^2 * gammaTilt^s / (s.factorial : ℚ))
        + (3/4) *
          (∑ s ∈ Finset.range (m/3 + 1),
            qTwo s * zetaMax^s / (s.factorial : ℚ))) / (m : ℚ)^2 := by
    unfold gammaResidualBudgetTerm
    rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    ring_nf
    simp [mul_comm, mul_left_comm]
  rw [hsplit]
  calc
    (((1/2) * (146/125)^2) *
          (∑ s ∈ Finset.range (m/3 + 1),
            (eOne s)^2 * gammaTilt^s / (s.factorial : ℚ))
        + (3/4) *
          (∑ s ∈ Finset.range (m/3 + 1),
            qTwo s * zetaMax^s / (s.factorial : ℚ))) / (m : ℚ)^2
      ≤ (((1/2) * (146/125)^2) * 540 + (3/4) * 59) / (m : ℚ)^2 := by
          exact div_le_div_of_nonneg_right
            (add_le_add
              (mul_le_mul_of_nonneg_left (poissonEOneSq_gammaTilt_le _) (by positivity))
              (mul_le_mul_of_nonneg_left (poissonQTwo_zetaMax_le _) (by positivity)))
            (sq_nonneg (m : ℚ))
    _ ≤ 426 / (m : ℚ)^2 := by
          field_simp [hmpos.ne']
          norm_num

/-- Closed P1 contribution for the actual gamma-product residual in the near
range. -/
theorem signLock_P1_actual_budget_zetaMax {m : Nat} (hm : 361 ≤ m) :
    ∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) * |piResidual m s|
      ≤ 426 / (m : ℚ)^2 := by
  have hpoint :
      ∑ s ∈ Finset.range (m/3 + 1),
          (zetaMax^s / (s.factorial : ℚ)) * |piResidual m s|
        ≤ ∑ s ∈ Finset.range (m/3 + 1), gammaResidualBudgetTerm m s := by
    exact Finset.sum_le_sum fun s hs =>
      weighted_piResidual_le_gammaResidualBudgetTerm_near
        (m := m) (s := s) hm (three_mul_le_of_mem_near hs)
  exact hpoint.trans (signLock_P1_budget_zetaMax (by omega : 1 ≤ m))

/-! ## P2: `d`-drift budget

Formalization note: the paper records the sharper decimal drift constant
`1.095` for `v_s = 1-D_s`.  The rational `d`-normalization currently proves
the slightly coarser `28/25 = 1.12` near-range bound below.  The P4 numerical
reserve has been recomputed with this coarser constant, so this is a deliberate
Lean-vs-TeX constant degradation, not an extra assumption.
-/

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

/-- A linear near-range `d`-drift bound used by the P4 bridge.  This is
slightly weaker than the paper's `1.095`, but still fits in the P4 reserve. -/
theorem one_sub_DFactor_le_linear_near
    {m s : Nat} (hm : 1 ≤ m) (hs : 3*s ≤ m) :
    1 - DFactor m s ≤ (28/25) * (s : ℚ) / (m : ℚ)^2 := by
  have hslt : s < m := by
    rcases s with rfl | s
    · omega
    · omega
  have hratio := d_ratio_lb m s hslt
  have hfirst :
      1 - DFactor m s
        ≤ (2304/3125) * ((s : ℚ) / ((m : ℚ) * ((m-s : Nat) : ℚ))) := by
    unfold DFactor
    linarith
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  have hmspos : (0 : ℚ) < ((m-s : Nat) : ℚ) := by
    exact_mod_cast (by omega : 0 < m-s)
  have hms_cast : ((m-s : Nat) : ℚ) = (m : ℚ) - (s : ℚ) := by
    rw [Nat.cast_sub hslt.le]
  have hq :
      (s : ℚ) / ((m : ℚ) * ((m-s : Nat) : ℚ))
        ≤ (3/2) * (s : ℚ) / (m : ℚ)^2 := by
    rw [hms_cast]
    have hsubpos : (0 : ℚ) < (m : ℚ) - (s : ℚ) := by
      rw [← hms_cast]
      exact hmspos
    have hs_nonneg : (0 : ℚ) ≤ s := by positivity
    have hsQ : (3 : ℚ) * (s : ℚ) ≤ (m : ℚ) := by exact_mod_cast hs
    field_simp [hmpos.ne', hsubpos.ne']
    nlinarith [mul_nonneg hs_nonneg (sub_nonneg.mpr hsQ)]
  calc
    1 - DFactor m s
      ≤ (2304/3125) * ((s : ℚ) / ((m : ℚ) * ((m-s : Nat) : ℚ))) := hfirst
    _ ≤ (2304/3125) * ((3/2) * (s : ℚ) / (m : ℚ)^2) :=
        mul_le_mul_of_nonneg_left hq (by norm_num)
    _ ≤ (28/25) * (s : ℚ) / (m : ℚ)^2 := by
        have hs_nonneg : (0 : ℚ) ≤ s := by positivity
        have hsm_nonneg : 0 ≤ (s : ℚ) / (m : ℚ)^2 := by positivity
        have hconst : (2304/3125 : ℚ) * (3/2) ≤ 28/25 := by norm_num
        calc
          (2304/3125 : ℚ) * ((3/2) * (s : ℚ) / (m : ℚ)^2)
              = ((2304/3125 : ℚ) * (3/2)) * ((s : ℚ) / (m : ℚ)^2) := by ring
          _ ≤ (28/25) * ((s : ℚ) / (m : ℚ)^2) :=
              mul_le_mul_of_nonneg_right hconst hsm_nonneg
          _ = (28/25) * (s : ℚ) / (m : ℚ)^2 := by ring

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

/-- Exact endpoint normalization for the two-block term.

This is the Lean counterpart of extracting the two endpoint products
`c₂ c_{p-2}` and `c_{p-2} c₂` from `[t^p]H(t)^2`: after the `2!` in the
exponential coefficient, those two endpoint products contribute
`N c₂ c_{p-2}/c_p`, which is exactly `twoEndpointCorrection`. -/
theorem twoEndpointCorrection_eq_endpoint_ratio
    {N p : Nat} (hp : 5 ≤ p) :
    twoEndpointCorrection N p = (N : ℚ) * c 2 * c (p-2) / c p := by
  have hdp : d p ≠ 0 := (d_pos p (by omega : 1 ≤ p)).ne'
  have hcp : c p ≠ 0 := (c_pos p (by omega : 1 ≤ p)).ne'
  have hdp2 : d (p-2) ≠ 0 := (d_pos (p-2) (by omega : 1 ≤ p-2)).ne'
  have hp1 : (((p-1 : Nat) : ℚ)) ≠ 0 := by
    exact_mod_cast (by omega : p-1 ≠ 0)
  have hp2 : (((p-2 : Nat) : ℚ)) ≠ 0 := by
    exact_mod_cast (by omega : p-2 ≠ 0)
  have hfacp : ((((p-1).factorial : Nat) : ℚ)) ≠ 0 := by positivity
  have hfacp2 : ((((p-3).factorial : Nat) : ℚ)) ≠ 0 := by positivity
  unfold twoEndpointCorrection DFactor
  rw [c_two, c_eq_d p, c_eq_d (p-2)]
  rw [show p-2-1 = p-3 by omega]
  have hpow6 : (6 : ℚ)^p = (6 : ℚ)^2 * (6 : ℚ)^(p-2) := by
    rw [← pow_add]
    congr 1
    omega
  have hfac :
      (((p-1).factorial : Nat) : ℚ)
        = (((p-1 : Nat) : ℚ)) * (((p-2 : Nat) : ℚ)) *
            (((p-3).factorial : Nat) : ℚ) := by
    rw [show p-1 = (p-2)+1 by omega, Nat.factorial_succ,
      show p-2 = (p-3)+1 by omega, Nat.factorial_succ]
    push_cast
    ring
  rw [hpow6, hfac]
  field_simp [hdp, hcp, hdp2, hp1, hp2, hfacp, hfacp2]
  ring

/-- Exact residual form of `ε_p` obtained from the finite `E^-` block split. -/
private theorem epsilonMinus_eq_residual_sum
    {N p : Nat} (hN : 1 ≤ N) (hp : 2 ≤ p) :
    epsilonMinus N p =
      -(∑ r ∈ Finset.Icc 2 p,
          (-(N : ℚ))^r * hpow r p / (r.factorial : ℚ))
        / ((N : ℚ) * c p) := by
  have hNq : ((N : ℚ) ≠ 0) := by exact_mod_cast (by omega : N ≠ 0)
  have hcp : c p ≠ 0 := (c_pos p (by omega : 1 ≤ p)).ne'
  unfold epsilonMinus EminusNorm
  rw [Eminus_split (N : ℚ) p hp]
  field_simp [hNq, hcp]
  ring

private theorem sum_Icc_two_eq_head_tail (F : Nat → ℚ) {p : Nat} (hp : 2 ≤ p) :
    ∑ r ∈ Finset.Icc 2 p, F r = F 2 + ∑ r ∈ Finset.Icc 3 p, F r := by
  have hIcc2 : Finset.Icc 2 p = Finset.Ico 2 (p+1) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hIcc3 : Finset.Icc 3 p = Finset.Ico 3 (p+1) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc2, Finset.sum_eq_sum_Ico_succ_bot (by omega : 2 < p+1), hIcc3]

/-- Exact split of `ε_p` into the full two-block coefficient and the
three-and-more-block tail. -/
private theorem epsilonMinus_eq_twoBlock_tail
    {N p : Nat} (hN : 1 ≤ N) (hp : 2 ≤ p) :
    epsilonMinus N p =
      -((N : ℚ) * hpow 2 p) / (2 * c p)
        - (∑ r ∈ Finset.Icc 3 p,
            (-(N : ℚ))^r * hpow r p / (r.factorial : ℚ))
          / ((N : ℚ) * c p) := by
  have hNq : ((N : ℚ) ≠ 0) := by exact_mod_cast (by omega : N ≠ 0)
  have hcp : c p ≠ 0 := (c_pos p (by omega : 1 ≤ p)).ne'
  rw [epsilonMinus_eq_residual_sum hN hp]
  rw [sum_Icc_two_eq_head_tail
    (fun r => (-(N : ℚ))^r * hpow r p / (r.factorial : ℚ)) hp]
  norm_num [Nat.factorial]
  field_simp [hNq, hcp]
  ring

/-- Exact nonlinear recentering identity after endpoint cancellation.

This is the point where the formal proof mirrors the TeX endpoint extraction:
`twoEndpointCorrection` cancels precisely the two endpoint products in the
two-block coefficient, leaving the non-endpoint two-block middle sum and the
three-and-more-block tail. -/
theorem epsilonMinus_add_twoEndpointCorrection_eq_middle_tail
    {N p : Nat} (hN : 1 ≤ N) (hp : 5 ≤ p) :
    epsilonMinus N p + twoEndpointCorrection N p =
      -((N : ℚ) * hpowTwoMiddle p) / (2 * c p)
        - (∑ r ∈ Finset.Icc 3 p,
            (-(N : ℚ))^r * hpow r p / (r.factorial : ℚ))
          / ((N : ℚ) * c p) := by
  have hNq : ((N : ℚ) ≠ 0) := by exact_mod_cast (by omega : N ≠ 0)
  have hcp : c p ≠ 0 := (c_pos p (by omega : 1 ≤ p)).ne'
  rw [epsilonMinus_eq_twoBlock_tail hN (by omega : 2 ≤ p)]
  rw [twoEndpointCorrection_eq_endpoint_ratio (N := N) (p := p) hp]
  rw [hpow_two_eq_endpoints_add_middle p hp]
  field_simp [hNq, hcp]
  ring

/-- Normalized non-endpoint two-block contribution left after endpoint
recentering. -/
def twoBlockMiddleNormalized (N p : Nat) : ℚ :=
  -((N : ℚ) * hpowTwoMiddle p) / (2 * c p)

/-- Exact normalized `r ≥ 3` contribution left after endpoint recentering. -/
noncomputable def threeBlockExactTail (N p : Nat) : ℚ :=
  -(∑ r ∈ Finset.Icc 3 p,
      (-(N : ℚ))^r * hpow r p / (r.factorial : ℚ))
    / ((N : ℚ) * c p)

theorem epsilonMinus_add_twoEndpointCorrection_eq_exactPieces
    {N p : Nat} (hN : 1 ≤ N) (hp : 5 ≤ p) :
    epsilonMinus N p + twoEndpointCorrection N p =
      twoBlockMiddleNormalized N p + threeBlockExactTail N p := by
  rw [epsilonMinus_add_twoEndpointCorrection_eq_middle_tail hN hp]
  unfold twoBlockMiddleNormalized threeBlockExactTail
  ring

/-- Rationalized Δ-tail corresponding to the exact `r ≥ 3` contribution. -/
def threeBlockDeltaTail (N p : Nat) : ℚ :=
  ∑ r ∈ Finset.Icc 3 (p/2), DeltaRatTerm p (N : ℚ) r

private theorem abs_hpow_block_le_EminusResidualBlock
    (p r : Nat) {N : ℚ} (hN : 0 ≤ N) :
    |(-N)^r * hpow r p / (r.factorial : ℚ)|
      ≤ EminusResidualBlock p N r := by
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_of_nonneg hN,
    abs_of_nonneg (by positivity : (0:ℚ) ≤ ((r.factorial : ℕ) : ℚ))]
  have hfpos : (0:ℚ) < ((r.factorial : ℕ) : ℚ) := by
    exact_mod_cast r.factorial_pos
  unfold EminusResidualBlock
  apply div_le_div_of_nonneg_right ?_ hfpos.le
  calc
    N^r * |hpow r p| ≤ N^r * ((4/25)^r * 6^p * Gcomp r p) := by
      exact mul_le_mul_of_nonneg_left (abs_hpow_le r p) (by positivity)
    _ = (N*(4/25))^r * 6^p * Gcomp r p := by
      rw [mul_pow]
      ring

/-- The exact `r ≥ 3` tail is dominated by the corresponding rationalized
Δ-tail.  The comparison to the closed P3c term is the remaining pure
Δ-tail estimate. -/
theorem abs_threeBlockExactTail_le_threeBlockDeltaTail
    {N p : Nat} (hN : 1 ≤ N) (hp : 5 ≤ p) :
    |threeBlockExactTail N p| ≤ threeBlockDeltaTail N p := by
  let T : Nat → ℚ :=
    fun r => (-(N : ℚ))^r * hpow r p / (r.factorial : ℚ)
  have hNq_pos : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  have hNq_nonneg : (0 : ℚ) ≤ (N : ℚ) := hNq_pos.le
  have hcp_pos : 0 < c p := c_pos p (by omega : 1 ≤ p)
  have hden_pos : 0 < (N : ℚ) * c p := mul_pos hNq_pos hcp_pos
  have htrunc :
      (∑ r ∈ Finset.Icc 3 p, T r)
        = ∑ r ∈ Finset.Icc 3 (p/2), T r := by
    symm
    apply Finset.sum_subset
    · intro r hr
      obtain ⟨hr3, hrhalf⟩ := Finset.mem_Icc.mp hr
      exact Finset.mem_Icc.mpr ⟨hr3, by omega⟩
    · intro r hr hnot
      obtain ⟨hr3, _hrp⟩ := Finset.mem_Icc.mp hr
      have hhalf : p/2 < r := by
        by_contra hle
        exact hnot (Finset.mem_Icc.mpr ⟨hr3, Nat.le_of_not_gt hle⟩)
      have hplt : p < 2*r := by
        have hnotle : ¬ r ≤ p/2 := Nat.not_le.mpr hhalf
        rw [Nat.le_div_two_iff_mul_two_le] at hnotle
        omega
      unfold T
      rw [hpow_eq_zero (by omega : 1 ≤ r) hplt, mul_zero, zero_div]
  unfold threeBlockExactTail threeBlockDeltaTail
  change |-(∑ r ∈ Finset.Icc 3 p, T r) / ((N : ℚ) * c p)|
      ≤ ∑ r ∈ Finset.Icc 3 (p/2), DeltaRatTerm p (N : ℚ) r
  rw [htrunc]
  calc
    |-(∑ r ∈ Finset.Icc 3 (p/2), T r) / ((N : ℚ) * c p)|
        = |∑ r ∈ Finset.Icc 3 (p/2), T r| / ((N : ℚ) * c p) := by
          rw [abs_div, abs_neg, abs_of_pos hden_pos]
    _ ≤ (∑ r ∈ Finset.Icc 3 (p/2), |T r|) / ((N : ℚ) * c p) := by
          exact div_le_div_of_nonneg_right
            (Finset.abs_sum_le_sum_abs _ _) hden_pos.le
    _ = ∑ r ∈ Finset.Icc 3 (p/2), |T r| / ((N : ℚ) * c p) := by
          rw [Finset.sum_div]
    _ ≤ ∑ r ∈ Finset.Icc 3 (p/2), DeltaRatTerm p (N : ℚ) r := by
          refine Finset.sum_le_sum fun r hr => ?_
          obtain ⟨hr3, hrhalf⟩ := Finset.mem_Icc.mp hr
          have hrp : 2*r ≤ p := by
            have h := Nat.le_div_two_iff_mul_two_le.mp hrhalf
            omega
          have hblock := abs_hpow_block_le_EminusResidualBlock
            p r (N := (N : ℚ)) hNq_nonneg
          have hdelta := EminusResidualBlock_le_Nc_mul_DeltaRatTerm
            (p := p) (r := r) (N := (N : ℚ)) hNq_nonneg
            (by omega : 2 ≤ p) (by omega : 1 ≤ r) hrp
          calc
            |T r| / ((N : ℚ) * c p)
              ≤ EminusResidualBlock p (N : ℚ) r / ((N : ℚ) * c p) := by
                exact div_le_div_of_nonneg_right hblock hden_pos.le
            _ ≤ DeltaRatTerm p (N : ℚ) r := by
                rw [div_le_iff₀ hden_pos]
                simpa [mul_comm, mul_left_comm, mul_assoc] using hdelta

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

private theorem twoNonEndpointMajorant_eq_middle_index {p : Nat} (hp : 5 ≤ p) :
    twoNonEndpointMajorant p =
      (576/3125) / (((p-1 : Nat) : ℚ)) *
        ∑ j ∈ Finset.Ico 3 (p-2), (1:ℚ)/((p-2).choose (j-1)) := by
  unfold twoNonEndpointMajorant
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  rw [show p-3-2 = p-2-3 by omega]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [show 3 + k - 1 = 2 + k by omega]

private theorem middle_twoBlock_term_div_c_le
    {p j : Nat} (hp : 5 ≤ p) (hj : j ∈ Finset.Ico 3 (p-2)) :
    c j * c (p-j) / c p
      ≤ (576/3125) / (((p-1 : Nat) : ℚ)) *
          ((1:ℚ)/((p-2).choose (j-1))) := by
  obtain ⟨hj3, hjlt⟩ := Finset.mem_Ico.mp hj
  have hj1 : 1 ≤ j := by omega
  have hpj1 : 1 ≤ p-j := by omega
  have hcp_pos : 0 < c p := c_pos p (by omega : 1 ≤ p)
  have hden_lb := c_lb p (by omega : 1 ≤ p)
  have hden_lb_pos :
      0 < (5/36) * (6^p * ((p-1).factorial : ℚ)) := by positivity
  have hnum_le :
      c j * c (p-j)
        ≤ (4/25 * (6^j * ((j-1).factorial : ℚ))) *
            (4/25 * (6^(p-j) * ((p-j-1).factorial : ℚ))) := by
    exact mul_le_mul (c_ub j hj1) (c_ub (p-j) hpj1)
      (c_nonneg (p-j)) (by positivity)
  have hnum_bound_nonneg :
      0 ≤ (4/25 * (6^j * ((j-1).factorial : ℚ))) *
            (4/25 * (6^(p-j) * ((p-j-1).factorial : ℚ))) := by
    positivity
  have hchoose_ne : (((p-2).choose (j-1) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : j-1 ≤ p-2)).ne'
  have hp1_ne : (((p-1 : Nat) : ℚ)) ≠ 0 := by
    exact_mod_cast (by omega : p-1 ≠ 0)
  have hfac_j_ne : (((j-1).factorial : Nat) : ℚ) ≠ 0 := by positivity
  have hfac_pj_ne : (((p-j-1).factorial : Nat) : ℚ) ≠ 0 := by positivity
  have hfac_p2_ne : (((p-2).factorial : Nat) : ℚ) ≠ 0 := by positivity
  have hpow6 : (6:ℚ)^j * (6:ℚ)^(p-j) = 6^p := by
    rw [← pow_add]
    congr 1
    omega
  have hchoose :
      (((p-2).choose (j-1) : ℕ) : ℚ)
          * (((j-1).factorial : Nat) : ℚ)
          * (((p-j-1).factorial : Nat) : ℚ)
        = (((p-2).factorial : Nat) : ℚ) := by
    have h := Nat.choose_mul_factorial_mul_factorial
      (show j-1 ≤ p-2 by omega)
    rw [show p-2-(j-1) = p-j-1 by omega] at h
    exact_mod_cast h
  have hfacp :
      (((p-1).factorial : Nat) : ℚ)
        = (((p-1 : Nat) : ℚ)) * (((p-2).factorial : Nat) : ℚ) := by
    rw [show p-1 = (p-2)+1 by omega, Nat.factorial_succ]
    push_cast
    ring
  have halg :
      ((4/25 * (6^j * ((j-1).factorial : ℚ))) *
          (4/25 * (6^(p-j) * ((p-j-1).factorial : ℚ))))
        / ((5/36) * (6^p * ((p-1).factorial : ℚ)))
      =
        (576/3125) / (((p-1 : Nat) : ℚ)) *
          ((1:ℚ)/((p-2).choose (j-1))) := by
    rw [hfacp, ← hchoose, ← hpow6]
    field_simp [hp1_ne, hchoose_ne, hfac_j_ne, hfac_pj_ne, hfac_p2_ne]
    ring
  calc
    c j * c (p-j) / c p
      ≤ ((4/25 * (6^j * ((j-1).factorial : ℚ))) *
          (4/25 * (6^(p-j) * ((p-j-1).factorial : ℚ)))) / c p := by
        exact div_le_div_of_nonneg_right hnum_le hcp_pos.le
    _ ≤
        ((4/25 * (6^j * ((j-1).factorial : ℚ))) *
          (4/25 * (6^(p-j) * ((p-j-1).factorial : ℚ))))
        / ((5/36) * (6^p * ((p-1).factorial : ℚ))) := by
        exact div_le_div_of_nonneg_left hnum_bound_nonneg hden_lb_pos hden_lb
    _ = (576/3125) / (((p-1 : Nat) : ℚ)) *
          ((1:ℚ)/((p-2).choose (j-1))) := halg

/-- The exact middle two-block contribution is bounded by the P3b
reciprocal-binomial majorant. -/
theorem hpowTwoMiddle_div_c_le_twoNonEndpointMajorant
    {p : Nat} (hp : 5 ≤ p) :
    hpowTwoMiddle p / c p ≤ twoNonEndpointMajorant p := by
  calc
    hpowTwoMiddle p / c p
        = ∑ j ∈ Finset.Ico 3 (p-2), c j * c (p-j) / c p := by
            unfold hpowTwoMiddle
            rw [Finset.sum_div]
    _ ≤ ∑ j ∈ Finset.Ico 3 (p-2),
          (576/3125) / (((p-1 : Nat) : ℚ)) *
            ((1:ℚ)/((p-2).choose (j-1))) := by
            exact Finset.sum_le_sum fun j hj =>
              middle_twoBlock_term_div_c_le hp hj
    _ =
        (576/3125) / (((p-1 : Nat) : ℚ)) *
          ∑ j ∈ Finset.Ico 3 (p-2), (1:ℚ)/((p-2).choose (j-1)) := by
            rw [Finset.mul_sum]
    _ = twoNonEndpointMajorant p := by
            rw [twoNonEndpointMajorant_eq_middle_index hp]

/-- Normalized absolute-value form of the P3b bridge for the exact middle
two-block term left after endpoint cancellation. -/
theorem abs_twoBlockMiddle_normalized_le_twoNonEndpointCorrectionBound
    {N p : Nat} (hp : 5 ≤ p) :
    |-((N : ℚ) * hpowTwoMiddle p) / (2 * c p)|
      ≤ twoNonEndpointCorrectionBound N p := by
  have hmajor := hpowTwoMiddle_div_c_le_twoNonEndpointMajorant (p := p) hp
  have hcp_pos : 0 < c p := c_pos p (by omega : 1 ≤ p)
  have hmiddle_nonneg : 0 ≤ hpowTwoMiddle p := hpowTwoMiddle_nonneg p
  have hnonneg :
      0 ≤ ((N : ℚ) * hpowTwoMiddle p) / (2 * c p) := by
    exact div_nonneg
      (mul_nonneg (by positivity : 0 ≤ (N : ℚ)) hmiddle_nonneg)
      (mul_pos (by norm_num) hcp_pos).le
  rw [show -((N : ℚ) * hpowTwoMiddle p) / (2 * c p)
      = -(((N : ℚ) * hpowTwoMiddle p) / (2 * c p)) by ring]
  rw [abs_neg, abs_of_nonneg hnonneg]
  have hrewrite :
      ((N : ℚ) * hpowTwoMiddle p) / (2 * c p)
        = ((N : ℚ) / 2) * (hpowTwoMiddle p / c p) := by
    field_simp [hcp_pos.ne']
  rw [hrewrite]
  unfold twoNonEndpointCorrectionBound
  exact mul_le_mul_of_nonneg_left hmajor (by positivity)

theorem abs_twoBlockMiddleNormalized_le_twoNonEndpointCorrectionBound
    {N p : Nat} (hp : 5 ≤ p) :
    |twoBlockMiddleNormalized N p| ≤ twoNonEndpointCorrectionBound N p := by
  simpa [twoBlockMiddleNormalized] using
    abs_twoBlockMiddle_normalized_le_twoNonEndpointCorrectionBound
      (N := N) (p := p) hp

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

/-! ## P3c: three-and-more-block nonlinear tail -/

/-- Explicit geometric-tail majorant for the `r ≥ 3` nonlinear blocks, starting
from the rationalized three-block Δ term and using the uniform multiplier
`25/23`. -/
def threeBlockTailBound (N p : Nat) : ℚ :=
  (6144/78125) * (N : ℚ)^2 /
      ((((p-1 : Nat) : ℚ)) * (((p-2 : Nat) : ℚ))
        * (((p-3 : Nat) : ℚ)) * (((p-4 : Nat) : ℚ)))
    * (25/23)

private theorem DeltaRatTerm_three_eq_tailBase (p : Nat) (N : ℚ) (hp : 6 ≤ p) :
    DeltaRatTerm p N 3 =
      (6144/78125) * N^2 /
        ((((p-1 : Nat) : ℚ)) * (((p-2 : Nat) : ℚ))
          * (((p-3 : Nat) : ℚ)) * (((p-4 : Nat) : ℚ))) := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 6 := ⟨p-6, by omega⟩
  simp only [DeltaRatTerm]
  norm_num [Nat.factorial_succ]
  have hk2 : (2 + (k:ℚ)) ≠ 0 := by positivity
  have hk3 : (3 + (k:ℚ)) ≠ 0 := by positivity
  have hk4 : (4 + (k:ℚ)) ≠ 0 := by positivity
  have hk5 : (5 + (k:ℚ)) ≠ 0 := by positivity
  ring_nf
  field_simp [hk2, hk3, hk4, hk5]
  ring

private theorem DeltaNearRatio_twenty_le_two_twentyseven {p : Nat} (hp : 231 ≤ p) :
    DeltaNearRatio p (20 : ℚ) ≤ 2/27 := by
  unfold DeltaNearRatio
  have hpQ : (0:ℚ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp231 : (231:ℚ) ≤ p := by exact_mod_cast hp
  field_simp [hpQ.ne']
  nlinarith

private theorem DeltaRatTerm_Icc_three_sum_le_geom (p M : Nat) {N q : ℚ}
    (hM : 3 ≤ M) (hN : 0 ≤ N) (hq0 : 0 ≤ q)
    (hratio : ∀ r, 3 ≤ r → r < M → DeltaRatStepRatioBound p N r ≤ q)
    (hpstep : ∀ r, 3 ≤ r → r < M → 2*(r+1) ≤ p) :
    ∑ r ∈ Finset.Icc 3 M, DeltaRatTerm p N r
      ≤ DeltaRatTerm p N 3 * ∑ j ∈ Finset.range (M-2), q^j := by
  have hshift :
      ∑ r ∈ Finset.Icc 3 M, DeltaRatTerm p N r
        = ∑ j ∈ Finset.range (M-2), DeltaRatTerm p N (j+3) := by
    have hIccIco : Finset.Icc 3 M = Finset.Ico 3 (M+1) := by
      ext r
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIccIco, Finset.sum_Ico_eq_sum_range,
      show M + 1 - 3 = M - 2 by omega]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.add_comm]
  rw [hshift]
  let F : Nat → ℚ := fun j => DeltaRatTerm p N (j+3)
  have hchain : ∀ j, j < M-2 → F j ≤ F 0 * q^j := by
    intro j hj
    induction j with
    | zero =>
        simp [F]
    | succ j ih =>
        have hjprev : j < M - 2 := Nat.lt_of_succ_lt hj
        have hstep :
            F (j+1) ≤ F j * q := by
          unfold F
          calc
            DeltaRatTerm p N (j+1+3)
                = DeltaRatTerm p N ((j+3)+1) := by
                    congr 1
            _ ≤ DeltaRatTerm p N (j+3) * DeltaRatStepRatioBound p N (j+3) := by
                    exact DeltaRatTerm_succ_le p (j+3) hN (by omega)
                      (hpstep (j+3) (by omega) (by omega))
            _ ≤ DeltaRatTerm p N (j+3) * q := by
                    exact mul_le_mul_of_nonneg_left
                      (hratio (j+3) (by omega) (by omega))
                      (DeltaRatTerm_nonneg p (j+3) hN)
        calc
          F (j+1) ≤ F j * q := hstep
          _ ≤ (F 0 * q^j) * q := by
              exact mul_le_mul_of_nonneg_right (ih hjprev) hq0
          _ = F 0 * q^(j+1) := by
              rw [pow_succ]
              ring
  calc
    ∑ j ∈ Finset.range (M-2), DeltaRatTerm p N (j+3)
        = ∑ j ∈ Finset.range (M-2), F j := rfl
    _ ≤ ∑ j ∈ Finset.range (M-2), F 0 * q^j := by
        refine Finset.sum_le_sum fun j hj => ?_
        exact hchain j (Finset.mem_range.mp hj)
    _ = DeltaRatTerm p N 3 * ∑ j ∈ Finset.range (M-2), q^j := by
        simp [F, Finset.mul_sum]

private theorem DeltaRatTerm_Icc_three_sum_le_inv_one_sub (p M : Nat) {N q : ℚ}
    (hM : 3 ≤ M) (hN : 0 ≤ N) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hratio : ∀ r, 3 ≤ r → r < M → DeltaRatStepRatioBound p N r ≤ q)
    (hpstep : ∀ r, 3 ≤ r → r < M → 2*(r+1) ≤ p) :
    ∑ r ∈ Finset.Icc 3 M, DeltaRatTerm p N r
      ≤ DeltaRatTerm p N 3 * (1/(1-q)) := by
  have hgeom :=
    DeltaRatTerm_Icc_three_sum_le_geom p M hM hN hq0 hratio hpstep
  exact hgeom.trans
    (mul_le_mul_of_nonneg_left
      (geom_sum_le_inv_one_sub q hq0 hq1 (M-2))
      (DeltaRatTerm_nonneg p 3 hN))

/-- Near part of the rationalized P3c tail, with a sharper ratio than the
global envelope.  The multiplier `27/25` leaves room for the separately
handled far slice. -/
theorem threeBlockDeltaTail_near_le
    {N p : Nat} (hN20 : (N : ℚ) ≤ 20 * (p : ℚ)) (hp : 241 ≤ p) :
    ∑ r ∈ Finset.Icc 3 (p/4), DeltaRatTerm p (N : ℚ) r
      ≤ DeltaRatTerm p (N : ℚ) 3 * (27/25) := by
  have hNnonneg : (0 : ℚ) ≤ N := by positivity
  have hratio20 := DeltaNearRatio_twenty_le_two_twentyseven (p := p) (by omega)
  have hslice := DeltaRatTerm_Icc_three_sum_le_inv_one_sub
    p (p/4) (N := (N : ℚ)) (q := (2/27 : ℚ))
    (by omega : 3 ≤ p/4) hNnonneg (by norm_num) (by norm_num) ?_ ?_
  · calc
      ∑ r ∈ Finset.Icc 3 (p/4), DeltaRatTerm p (N : ℚ) r
        ≤ DeltaRatTerm p (N : ℚ) 3 * (1 / (1 - (2/27 : ℚ))) := hslice
      _ = DeltaRatTerm p (N : ℚ) 3 * (27/25) := by ring
  · intro r hr3 hrM
    have hnear : 4*r ≤ p := by omega
    exact (DeltaRatStepRatioBound_le_near p r
      (N := (N : ℚ)) (R := (20 : ℚ)) (by norm_num) hN20
      (by omega : 1 ≤ p) hnear).trans hratio20
  · intro r hr3 hrM
    have hnear : 4*r ≤ p := by omega
    omega

theorem threeBlockTailBound_eq_delta_three {N p : Nat} (hp : 6 ≤ p) :
    threeBlockTailBound N p = DeltaRatTerm p (N : ℚ) 3 * (25/23) := by
  unfold threeBlockTailBound
  rw [DeltaRatTerm_three_eq_tailBase p (N : ℚ) hp]

private theorem threeBlockDeltaTail_split_near_far {N p : Nat} (hp : 12 ≤ p) :
    threeBlockDeltaTail N p =
      (∑ r ∈ Finset.Icc 3 (p/4), DeltaRatTerm p (N : ℚ) r)
        + DeltaRatFar p (N : ℚ) := by
  unfold threeBlockDeltaTail DeltaRatFar
  have hsplit :
      Finset.Icc 3 (p/2)
        = Finset.Icc 3 (p/4) ∪ Finset.Icc (p/4 + 1) (p/2) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_union]
    constructor
    · intro hr
      by_cases hle : r ≤ p/4
      · exact Or.inl ⟨hr.1, hle⟩
      · exact Or.inr ⟨Nat.succ_le_of_lt (Nat.lt_of_not_ge hle), hr.2⟩
    · intro hr
      rcases hr with hnear | hfar
      · exact ⟨hnear.1, by omega⟩
      · exact ⟨by omega, hfar.2⟩
  have hdisj :
      Disjoint (Finset.Icc 3 (p/4)) (Finset.Icc (p/4 + 1) (p/2)) := by
    rw [Finset.disjoint_left]
    intro r hrnear hrfar
    obtain ⟨_, hle⟩ := Finset.mem_Icc.mp hrnear
    obtain ⟨hlt, _⟩ := Finset.mem_Icc.mp hrfar
    omega
  rw [hsplit, Finset.sum_union hdisj]

/-- The full P3c Δ-tail comparison is reduced to a far-slice reserve.  The
near slice uses the proved `27/25` geometric multiplier; the remaining
`4/575` is exactly the slack to reach the target multiplier `25/23`. -/
theorem threeBlockDeltaTail_le_threeBlockTailBound_of_farReserve
    {N p : Nat} (hN20 : (N : ℚ) ≤ 20 * (p : ℚ)) (hp : 241 ≤ p)
    (hfar :
      DeltaRatFar p (N : ℚ) ≤ DeltaRatTerm p (N : ℚ) 3 * (4/575)) :
    threeBlockDeltaTail N p ≤ threeBlockTailBound N p := by
  have hnear := threeBlockDeltaTail_near_le (N := N) (p := p) hN20 hp
  have hterm_nonneg : 0 ≤ DeltaRatTerm p (N : ℚ) 3 :=
    DeltaRatTerm_nonneg p 3 (by positivity : (0 : ℚ) ≤ (N : ℚ))
  rw [threeBlockDeltaTail_split_near_far (N := N) (p := p) (by omega : 12 ≤ p)]
  rw [threeBlockTailBound_eq_delta_three (N := N) (p := p) (by omega : 6 ≤ p)]
  calc
    (∑ r ∈ Finset.Icc 3 (p/4), DeltaRatTerm p (N : ℚ) r)
        + DeltaRatFar p (N : ℚ)
      ≤ DeltaRatTerm p (N : ℚ) 3 * (27/25)
          + DeltaRatTerm p (N : ℚ) 3 * (4/575) :=
            add_le_add hnear hfar
    _ = DeltaRatTerm p (N : ℚ) 3 * (25/23) := by ring

private theorem DeltaRatFarTermBound_61_le_inv_fourth :
    DeltaRatFarTermBound 61 ≤ 1 / (10^10 * (61:ℚ)^4) := by
  have h61 : ((25*(61:ℚ))/68)^61 ≤ ((61).factorial : ℚ) := factorial_lb 61
  have h121 : ((25*(121:ℚ))/68)^121 ≤ ((121).factorial : ℚ) := factorial_lb 121
  have hden_lb :
      ((25*(61:ℚ))/68)^61 * ((25*(121:ℚ))/68)^121
        ≤ ((61).factorial : ℚ) * ((121).factorial : ℚ) := by
    exact mul_le_mul h61 h121 (by positivity) (by positivity)
  have hden_pos :
      (0:ℚ) < ((25*(61:ℚ))/68)^61 * ((25*(121:ℚ))/68)^121 := by
    positivity
  have hnum_nonneg :
      0 ≤ (9/5:ℚ) * (16/25)^61 * (80*(61:ℚ))^60 := by
    positivity
  unfold DeltaRatFarTermBound
  change (9/5:ℚ) * (16/25)^61 * (80*(61:ℚ))^60
      / (((61).factorial : ℚ) * ((121).factorial : ℚ))
    ≤ 1 / (10^10 * (61:ℚ)^4)
  calc
    (9/5:ℚ) * (16/25)^61 * (80*(61:ℚ))^60
        / (((61).factorial : ℚ) * ((121).factorial : ℚ))
        ≤ (9/5:ℚ) * (16/25)^61 * (80*(61:ℚ))^60
            / (((25*(61:ℚ))/68)^61 * ((25*(121:ℚ))/68)^121) := by
          exact div_le_div_of_nonneg_left hnum_nonneg hden_pos hden_lb
    _ ≤ 1 / (10^10 * (61:ℚ)^4) := by norm_num

theorem DeltaRatFarTermBound_le_inv_fourth (r : Nat) (hr : 61 ≤ r) :
    DeltaRatFarTermBound r ≤ 1 / (10^10 * (r:ℚ)^4) := by
  suffices h : ∀ k : Nat,
      DeltaRatFarTermBound (61+k)
        ≤ 1 / (10^10 * ((61+k : Nat) : ℚ)^4) by
    obtain ⟨k, rfl⟩ : ∃ k, r = 61 + k := ⟨r - 61, by omega⟩
    exact h k
  intro k
  induction k with
  | zero =>
      simpa using DeltaRatFarTermBound_61_le_inv_fourth
  | succ k ih =>
      have hstep := DeltaRatFarTermBound_succ_le_half (61+k) (by omega : 61 ≤ 61+k)
      have hden₁ : (0:ℚ) < 10^10 * ((61+k : Nat) : ℚ)^4 := by positivity
      have hden₂ : (0:ℚ) < 10^10 * ((61+(k+1) : Nat) : ℚ)^4 := by positivity
      calc
        DeltaRatFarTermBound (61 + (k+1))
            = DeltaRatFarTermBound ((61+k)+1) := by rw [Nat.add_assoc]
        _ ≤ DeltaRatFarTermBound (61+k) * (1/2) := hstep
        _ ≤ (1 / (10^10 * ((61+k : Nat) : ℚ)^4)) * (1/2) := by
              exact mul_le_mul_of_nonneg_right ih (by norm_num)
        _ ≤ 1 / (10^10 * ((61+(k+1) : Nat) : ℚ)^4) := by
              field_simp [ne_of_gt hden₁, ne_of_gt hden₂]
              norm_num
              have hk0 : (0:ℚ) ≤ k := by exact_mod_cast Nat.zero_le k
              have hratio :
                  (((61+(k+1) : Nat) : ℚ))
                    ≤ (62/61) * (((61+k : Nat) : ℚ)) := by
                field_simp
                norm_num
                nlinarith
              have hpow := pow_le_pow_left₀
                (by positivity : (0:ℚ) ≤ (((61+(k+1) : Nat) : ℚ))) hratio 4
              have hconst : (62/61 : ℚ)^4 ≤ 2 := by norm_num
              have hpow2 :
                  (((61+(k+1 : Nat) : Nat) : ℚ))^4
                    ≤ 2 * (((61+k : Nat) : ℚ))^4 := by
                calc
                  (((61+(k+1 : Nat) : Nat) : ℚ))^4
                    ≤ ((62/61 : ℚ) * (((61+k : Nat) : ℚ)))^4 := hpow
                  _ = (62/61 : ℚ)^4 * (((61+k : Nat) : ℚ))^4 := by
                      rw [mul_pow]
                  _ ≤ 2 * (((61+k : Nat) : ℚ))^4 := by
                      exact mul_le_mul_of_nonneg_right hconst (by positivity)
              have hpow2' :
                  (61 + ((k : ℚ) + 1))^4 ≤ (61 + (k : ℚ))^4 * 2 := by
                norm_num at hpow2 ⊢
                simpa [mul_comm, add_comm, add_left_comm, add_assoc] using hpow2
              linarith

private theorem near_denominator_four_le_start_fourth {p : Nat} (hp : 5 ≤ p) :
    (((p-1 : Nat) : ℚ)) * (((p-2 : Nat) : ℚ))
        * (((p-3 : Nat) : ℚ)) * (((p-4 : Nat) : ℚ))
      ≤ 256 * (((p/4 + 1 : Nat) : ℚ)^4) := by
  let a : Nat := p/4 + 1
  have hpaNat : p ≤ 4 * a := by
    unfold a
    omega
  have hpa : (p : ℚ) ≤ 4 * (a : ℚ) := by exact_mod_cast hpaNat
  have hp_nonneg : (0 : ℚ) ≤ p := by positivity
  have ha_nonneg : (0 : ℚ) ≤ a := by positivity
  have hp1le : (((p-1 : Nat) : ℚ)) ≤ (p : ℚ) := by
    exact_mod_cast Nat.sub_le p 1
  have hp2le : (((p-2 : Nat) : ℚ)) ≤ (p : ℚ) := by
    exact_mod_cast Nat.sub_le p 2
  have hp3le : (((p-3 : Nat) : ℚ)) ≤ (p : ℚ) := by
    exact_mod_cast Nat.sub_le p 3
  have hp4le : (((p-4 : Nat) : ℚ)) ≤ (p : ℚ) := by
    exact_mod_cast Nat.sub_le p 4
  have hp1_nonneg : (0 : ℚ) ≤ (((p-1 : Nat) : ℚ)) := by positivity
  have hp2_nonneg : (0 : ℚ) ≤ (((p-2 : Nat) : ℚ)) := by positivity
  have hp3_nonneg : (0 : ℚ) ≤ (((p-3 : Nat) : ℚ)) := by positivity
  have hp4_nonneg : (0 : ℚ) ≤ (((p-4 : Nat) : ℚ)) := by positivity
  have h12 :
      (((p-1 : Nat) : ℚ)) * (((p-2 : Nat) : ℚ)) ≤ (p : ℚ) * (p : ℚ) :=
    mul_le_mul hp1le hp2le hp2_nonneg hp_nonneg
  have h123 :
      (((p-1 : Nat) : ℚ)) * (((p-2 : Nat) : ℚ))
          * (((p-3 : Nat) : ℚ)) ≤ (p : ℚ)^3 := by
    have hmul := mul_le_mul h12 hp3le hp3_nonneg
      (mul_nonneg hp_nonneg hp_nonneg)
    nlinarith
  have h1234 :
      (((p-1 : Nat) : ℚ)) * (((p-2 : Nat) : ℚ))
          * (((p-3 : Nat) : ℚ)) * (((p-4 : Nat) : ℚ)) ≤ (p : ℚ)^4 := by
    have hmul := mul_le_mul h123 hp4le hp4_nonneg (by positivity : 0 ≤ (p : ℚ)^3)
    nlinarith
  have hp4a : (p : ℚ)^4 ≤ (4 * (a : ℚ))^4 :=
    pow_le_pow_left₀ hp_nonneg hpa 4
  calc
    (((p-1 : Nat) : ℚ)) * (((p-2 : Nat) : ℚ))
        * (((p-3 : Nat) : ℚ)) * (((p-4 : Nat) : ℚ))
      ≤ (p : ℚ)^4 := h1234
    _ ≤ (4 * (a : ℚ))^4 := hp4a
    _ = 256 * ((a : ℚ)^4) := by ring

theorem DeltaRatFar_le_delta_three_reserve
    {N p : Nat} (hN : 1 ≤ N) (hN20 : (N : ℚ) ≤ 20 * (p : ℚ)) (hp : 241 ≤ p) :
    DeltaRatFar p (N : ℚ) ≤ DeltaRatTerm p (N : ℚ) 3 * (4/575) := by
  let a : Nat := p/4 + 1
  have hfar := DeltaRatFar_le_two_first
    (p := p) (N := (N : ℚ)) (by positivity : (0 : ℚ) ≤ (N : ℚ))
    hN20 (by omega : 240 ≤ p)
  have hfirst := DeltaRatFarTermBound_le_inv_fourth a (by
    unfold a
    omega)
  have hfirst2 :
      2 * DeltaRatFarTermBound a ≤ 2 / (10^10 * (a : ℚ)^4) := by
    calc
      2 * DeltaRatFarTermBound a
        ≤ 2 * (1 / (10^10 * (a : ℚ)^4)) := by
            exact mul_le_mul_of_nonneg_left hfirst (by norm_num)
      _ = 2 / (10^10 * (a : ℚ)^4) := by ring
  have hdenprod :=
    near_denominator_four_le_start_fourth (p := p) (by omega : 5 ≤ p)
  have hNsq : (1 : ℚ) ≤ (N : ℚ)^2 := by
    have hNQ : (1 : ℚ) ≤ N := by exact_mod_cast hN
    nlinarith
  have ha_pos : (0 : ℚ) < (a : ℚ) := by
    unfold a
    positivity
  have hden_pos :
      (0 : ℚ) <
        (((p-1 : Nat) : ℚ)) * (((p-2 : Nat) : ℚ))
          * (((p-3 : Nat) : ℚ)) * (((p-4 : Nat) : ℚ)) := by
    have hp1 : (0 : ℚ) < (((p-1 : Nat) : ℚ)) := by exact_mod_cast (by omega : 0 < p-1)
    have hp2 : (0 : ℚ) < (((p-2 : Nat) : ℚ)) := by exact_mod_cast (by omega : 0 < p-2)
    have hp3 : (0 : ℚ) < (((p-3 : Nat) : ℚ)) := by exact_mod_cast (by omega : 0 < p-3)
    have hp4 : (0 : ℚ) < (((p-4 : Nat) : ℚ)) := by exact_mod_cast (by omega : 0 < p-4)
    positivity
  have hscaled :
      2 / (10^10 * (a : ℚ)^4)
        ≤ ((6144/78125) * (N : ℚ)^2 /
              ((((p-1 : Nat) : ℚ)) * (((p-2 : Nat) : ℚ))
                * (((p-3 : Nat) : ℚ)) * (((p-4 : Nat) : ℚ)))) * (4/575) := by
    have hconst :
        (2 : ℚ) / 10^10 ≤ ((6144/78125) * (4/575)) / 256 := by
      norm_num
    have ha4_pos : (0 : ℚ) < (a : ℚ)^4 := by positivity
    have hstep1 :
        2 / (10^10 * (a : ℚ)^4)
          ≤ (((6144/78125) * (4/575)) / 256) / ((a : ℚ)^4) := by
      field_simp [ha4_pos.ne']
      nlinarith
    have hstep2 :
        (((6144/78125) * (4/575)) / 256) / ((a : ℚ)^4)
          =
        ((6144/78125) * (4/575)) / (256 * (a : ℚ)^4) := by ring
    have hnum_nonneg : 0 ≤ (6144/78125 : ℚ) * (4/575) * (N : ℚ)^2 := by positivity
    calc
      2 / (10^10 * (a : ℚ)^4)
        ≤ (((6144/78125) * (4/575)) / 256) / ((a : ℚ)^4) := hstep1
      _ = ((6144/78125) * (4/575)) / (256 * (a : ℚ)^4) := hstep2
      _ ≤ ((6144/78125) * (4/575) * (N : ℚ)^2)
            / (256 * (a : ℚ)^4) := by
            have hcoef_nonneg : 0 ≤ (6144/78125 : ℚ) * (4/575) := by norm_num
            have hnum_le :
                (6144/78125 : ℚ) * (4/575)
                  ≤ (6144/78125 : ℚ) * (4/575) * (N : ℚ)^2 := by
              simpa [mul_one] using
                (mul_le_mul_of_nonneg_left hNsq hcoef_nonneg)
            exact div_le_div_of_nonneg_right
              hnum_le
              (mul_pos (by norm_num) ha4_pos).le
      _ ≤ ((6144/78125) * (4/575) * (N : ℚ)^2)
            / ((((p-1 : Nat) : ℚ)) * (((p-2 : Nat) : ℚ))
                * (((p-3 : Nat) : ℚ)) * (((p-4 : Nat) : ℚ))) := by
            exact div_le_div_of_nonneg_left hnum_nonneg hden_pos
              (by simpa [a] using hdenprod)
      _ = ((6144/78125) * (N : ℚ)^2 /
              ((((p-1 : Nat) : ℚ)) * (((p-2 : Nat) : ℚ))
                * (((p-3 : Nat) : ℚ)) * (((p-4 : Nat) : ℚ)))) * (4/575) := by
            ring
  calc
    DeltaRatFar p (N : ℚ)
      ≤ 2 * DeltaRatFarTermBound a := by
          simpa [a] using hfar
    _ ≤ 2 / (10^10 * (a : ℚ)^4) := hfirst2
    _ ≤ DeltaRatTerm p (N : ℚ) 3 * (4/575) := by
          rw [DeltaRatTerm_three_eq_tailBase p (N : ℚ) (by omega : 6 ≤ p)]
          exact hscaled

theorem threeBlockDeltaTail_le_threeBlockTailBound
    {N p : Nat} (hN : 1 ≤ N) (hN20 : (N : ℚ) ≤ 20 * (p : ℚ)) (hp : 241 ≤ p) :
    threeBlockDeltaTail N p ≤ threeBlockTailBound N p :=
  threeBlockDeltaTail_le_threeBlockTailBound_of_farReserve
    (N := N) (p := p) hN20 hp
    (DeltaRatFar_le_delta_three_reserve
      (N := N) (p := p) hN hN20 hp)

theorem threeBlockDeltaTail_le_threeBlockTailBound_near
    {N m s : Nat} (hN : 1 ≤ N)
    (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ))
    (hm : 361 ≤ m) (hs : 3*s ≤ m) :
    threeBlockDeltaTail N (m-s) ≤ threeBlockTailBound N (m-s) := by
  have hp : 241 ≤ m-s := by omega
  have hN20 : (N : ℚ) ≤ 20 * ((m-s : Nat) : ℚ) := by
    have hp_lower0 := near_p_lower (m := m) (s := s) hs
    have hp_lower : (2/3) * (m : ℚ) ≤ ((m-s : Nat) : ℚ) := by
      nlinarith
    have hscale : (40/3) * (m : ℚ) ≤ 20 * ((m-s : Nat) : ℚ) := by
      nlinarith
    exact hN40.trans hscale
  exact threeBlockDeltaTail_le_threeBlockTailBound
    (N := N) (p := m-s) hN hN20 hp

/-- Tail bridge reduced to a pure rationalized-Δ estimate. -/
theorem abs_threeBlockExactTail_le_threeBlockTailBound_of_DeltaTail
    {N p : Nat} (hN : 1 ≤ N) (hp : 5 ≤ p)
    (hdelta : threeBlockDeltaTail N p ≤ threeBlockTailBound N p) :
    |threeBlockExactTail N p| ≤ threeBlockTailBound N p :=
  (abs_threeBlockExactTail_le_threeBlockDeltaTail
    (N := N) (p := p) hN hp).trans hdelta

private theorem near_p_sub_four_linear_lower
    {m s k : Nat} (hm : 361 ≤ m) (hs : 3*s ≤ m) (hk : 1 ≤ k) (hk4 : k ≤ 4) :
    (2/3) * (m : ℚ) - (k : ℚ) ≤ (((m-s-k : Nat) : ℚ)) := by
  have hsk : s + k ≤ m := by
    omega
  rw [show m-s-k = m-(s+k) by omega, Nat.cast_sub hsk]
  push_cast
  have hsQ : (3 : ℚ) * (s : ℚ) ≤ (m : ℚ) := by exact_mod_cast hs
  linarith

private theorem near_four_denominator_product
    {m s : Nat} (hm : 361 ≤ m) (hs : 3*s ≤ m) :
    (3/16) * (m : ℚ)^4
      ≤ (((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ))
          * (((m-s-3 : Nat) : ℚ)) * (((m-s-4 : Nat) : ℚ)) := by
  have hmQ : (361 : ℚ) ≤ m := by exact_mod_cast hm
  have h1 := near_p_sub_four_linear_lower (m := m) (s := s) (k := 1) hm hs
    (by norm_num) (by norm_num)
  have h2 := near_p_sub_four_linear_lower (m := m) (s := s) (k := 2) hm hs
    (by norm_num) (by norm_num)
  have h3 := near_p_sub_four_linear_lower (m := m) (s := s) (k := 3) hm hs
    (by norm_num) (by norm_num)
  have h4 := near_p_sub_four_linear_lower (m := m) (s := s) (k := 4) hm hs
    (by norm_num) (by norm_num)
  have hl1_nonneg : 0 ≤ (2/3) * (m : ℚ) - 1 := by nlinarith
  have hl2_nonneg : 0 ≤ (2/3) * (m : ℚ) - 2 := by nlinarith
  have hl3_nonneg : 0 ≤ (2/3) * (m : ℚ) - 3 := by nlinarith
  have hl4_nonneg : 0 ≤ (2/3) * (m : ℚ) - 4 := by nlinarith
  have hp1pos : (0 : ℚ) < (((m-s-1 : Nat) : ℚ)) := by
    exact_mod_cast (by omega : 0 < m-s-1)
  have hp2pos : (0 : ℚ) < (((m-s-2 : Nat) : ℚ)) := by
    exact_mod_cast (by omega : 0 < m-s-2)
  have hp3pos : (0 : ℚ) < (((m-s-3 : Nat) : ℚ)) := by
    exact_mod_cast (by omega : 0 < m-s-3)
  have h12 :
      ((2/3) * (m : ℚ) - 1) * ((2/3) * (m : ℚ) - 2)
        ≤ (((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ)) :=
    mul_le_mul h1 h2 hl2_nonneg hp1pos.le
  have h123 :
      ((2/3) * (m : ℚ) - 1) * ((2/3) * (m : ℚ) - 2)
          * ((2/3) * (m : ℚ) - 3)
        ≤ (((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ))
          * (((m-s-3 : Nat) : ℚ)) :=
    mul_le_mul h12 h3 hl3_nonneg
      (mul_nonneg hp1pos.le hp2pos.le)
  have h1234 :
      ((2/3) * (m : ℚ) - 1) * ((2/3) * (m : ℚ) - 2)
          * ((2/3) * (m : ℚ) - 3) * ((2/3) * (m : ℚ) - 4)
        ≤ (((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ))
          * (((m-s-3 : Nat) : ℚ)) * (((m-s-4 : Nat) : ℚ)) :=
    mul_le_mul h123 h4 hl4_nonneg
      (mul_nonneg (mul_nonneg hp1pos.le hp2pos.le) hp3pos.le)
  have hpoly :
      (3/16) * (m : ℚ)^4
        ≤ ((2/3) * (m : ℚ) - 1) * ((2/3) * (m : ℚ) - 2)
          * ((2/3) * (m : ℚ) - 3) * ((2/3) * (m : ℚ) - 4) := by
    have hc1 : (33/50) * (m : ℚ) ≤ (2/3) * (m : ℚ) - 1 := by nlinarith
    have hc2 : (33/50) * (m : ℚ) ≤ (2/3) * (m : ℚ) - 2 := by nlinarith
    have hc3 : (79/120) * (m : ℚ) ≤ (2/3) * (m : ℚ) - 3 := by nlinarith
    have hc4 : (59/90) * (m : ℚ) ≤ (2/3) * (m : ℚ) - 4 := by nlinarith
    have hcbase1 : 0 ≤ (33/50) * (m : ℚ) := by positivity
    have hcbase2 : 0 ≤ (79/120) * (m : ℚ) := by positivity
    have hcbase3 : 0 ≤ (59/90) * (m : ℚ) := by positivity
    have hc12 :
        ((33/50) * (m : ℚ)) * ((33/50) * (m : ℚ))
          ≤ ((2/3) * (m : ℚ) - 1) * ((2/3) * (m : ℚ) - 2) :=
      mul_le_mul hc1 hc2 hcbase1 hl1_nonneg
    have hc123 :
        ((33/50) * (m : ℚ)) * ((33/50) * (m : ℚ)) * ((79/120) * (m : ℚ))
          ≤ ((2/3) * (m : ℚ) - 1) * ((2/3) * (m : ℚ) - 2)
            * ((2/3) * (m : ℚ) - 3) :=
      mul_le_mul hc12 hc3 hcbase2 (mul_nonneg hl1_nonneg hl2_nonneg)
    have hc1234 :
        ((33/50) * (m : ℚ)) * ((33/50) * (m : ℚ)) * ((79/120) * (m : ℚ))
            * ((59/90) * (m : ℚ))
          ≤ ((2/3) * (m : ℚ) - 1) * ((2/3) * (m : ℚ) - 2)
            * ((2/3) * (m : ℚ) - 3) * ((2/3) * (m : ℚ) - 4) :=
      mul_le_mul hc123 hc4 hcbase3
        (mul_nonneg (mul_nonneg hl1_nonneg hl2_nonneg) hl3_nonneg)
    have hconst : (3/16 : ℚ) ≤ (33/50) * (33/50) * (79/120) * (59/90) := by
      norm_num
    have hm4_nonneg : 0 ≤ (m : ℚ)^4 := by positivity
    have hconstprod :
        (3/16) * (m : ℚ)^4
          ≤ ((33/50) * (m : ℚ)) * ((33/50) * (m : ℚ))
              * ((79/120) * (m : ℚ)) * ((59/90) * (m : ℚ)) := by
      calc
        (3/16) * (m : ℚ)^4
            ≤ ((33/50) * (33/50) * (79/120) * (59/90)) * (m : ℚ)^4 :=
              mul_le_mul_of_nonneg_right hconst hm4_nonneg
        _ = ((33/50) * (m : ℚ)) * ((33/50) * (m : ℚ))
              * ((79/120) * (m : ℚ)) * ((59/90) * (m : ℚ)) := by
              ring
    exact hconstprod.trans hc1234
  exact hpoly.trans h1234

theorem threeBlockTailBound_pointwise_P3c
    {N m s : Nat} (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ))
    (hm : 361 ≤ m) (hs : 3*s ≤ m) :
    threeBlockTailBound N (m-s) ≤ 89 / (m : ℚ)^2 := by
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  have hp1pos : (0 : ℚ) < (((m-s-1 : Nat) : ℚ)) := by
    exact_mod_cast (by omega : 0 < m-s-1)
  have hp2pos : (0 : ℚ) < (((m-s-2 : Nat) : ℚ)) := by
    exact_mod_cast (by omega : 0 < m-s-2)
  have hp3pos : (0 : ℚ) < (((m-s-3 : Nat) : ℚ)) := by
    exact_mod_cast (by omega : 0 < m-s-3)
  have hp4pos : (0 : ℚ) < (((m-s-4 : Nat) : ℚ)) := by
    exact_mod_cast (by omega : 0 < m-s-4)
  have hN2 : (N : ℚ)^2 ≤ (1600/9) * (m : ℚ)^2 := by
    have hNnonneg : (0 : ℚ) ≤ N := by positivity
    nlinarith
  have hden := near_four_denominator_product (m := m) (s := s) hm hs
  have hNscaled :
      (N : ℚ)^2 * (6144 * 25 * (m : ℚ)^2)
        ≤ ((1600/9) * (m : ℚ)^2) * (6144 * 25 * (m : ℚ)^2) := by
    exact mul_le_mul_of_nonneg_right hN2 (by positivity)
  have hden_scaled :
      ((1600/9) * (m : ℚ)^2) * (6144 * 25 * (m : ℚ)^2)
        ≤ 78125 * 23 * 89 *
          ((((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ))
            * (((m-s-3 : Nat) : ℚ)) * (((m-s-4 : Nat) : ℚ))) := by
    have hconst : (6144 * (1600/9) * 25 : ℚ)
        ≤ 78125 * 23 * 89 * (3/16) := by
      norm_num
    have hm4_nonneg : 0 ≤ (m : ℚ)^4 := by positivity
    calc
      ((1600/9) * (m : ℚ)^2) * (6144 * 25 * (m : ℚ)^2)
          = (6144 * (1600/9) * 25 : ℚ) * (m : ℚ)^4 := by ring
      _ ≤ (78125 * 23 * 89 * (3/16)) * (m : ℚ)^4 :=
          mul_le_mul_of_nonneg_right hconst hm4_nonneg
      _ = 78125 * 23 * 89 * ((3/16) * (m : ℚ)^4) := by ring
      _ ≤ 78125 * 23 * 89 *
          ((((m-s-1 : Nat) : ℚ)) * (((m-s-2 : Nat) : ℚ))
            * (((m-s-3 : Nat) : ℚ)) * (((m-s-4 : Nat) : ℚ))) :=
          mul_le_mul_of_nonneg_left hden (by norm_num)
  unfold threeBlockTailBound
  field_simp [hmpos.ne', hp1pos.ne', hp2pos.ne', hp3pos.ne', hp4pos.ne']
  nlinarith [hNscaled, hden_scaled]

theorem signLock_P3c_scalar_budget_zetaMax {m : Nat} (hm : 1 ≤ m) :
    ∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) * (89 / (m : ℚ)^2)
      ≤ 573 / (m : ℚ)^2 := by
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  calc
    ∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) * (89 / (m : ℚ)^2)
      =
        (89 / (m : ℚ)^2) *
          (∑ s ∈ Finset.range (m/3 + 1), zetaMax^s / (s.factorial : ℚ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun s hs => ?_
          ring
    _ ≤ (89 / (m : ℚ)^2) * (319/50) := by
          exact mul_le_mul_of_nonneg_left
            (poissonZero_zetaMax_le_tight _) (by positivity)
    _ ≤ 573 / (m : ℚ)^2 := by
          field_simp [hmpos.ne']
          norm_num

/-- Weighted P3c budget for the explicit three-and-more-block tail majorant. -/
theorem signLock_P3c_budget_zetaMax {N m : Nat}
    (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ)) (hm : 361 ≤ m) :
    ∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) *
          threeBlockTailBound N (m-s)
      ≤ 573 / (m : ℚ)^2 := by
  have hpoint :
      ∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) *
          threeBlockTailBound N (m-s)
      ≤
      ∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) * (89 / (m : ℚ)^2) := by
    refine Finset.sum_le_sum fun s hs => ?_
    have hs3 : 3*s ≤ m := by
      have hsle : s ≤ m/3 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
      exact (Nat.mul_le_mul_left 3 hsle).trans (Nat.mul_div_le m 3)
    have hweight : 0 ≤ zetaMax^s / (s.factorial : ℚ) := by
      have hz : 0 ≤ zetaMax := by norm_num [zetaMax]
      positivity
    exact mul_le_mul_of_nonneg_left
      (threeBlockTailBound_pointwise_P3c hN40 hm hs3) hweight
  exact hpoint.trans (signLock_P3c_scalar_budget_zetaMax (by omega : 1 ≤ m))

/-! ## P4: cross-term numerical reserve -/

/-- The product cross residual after removing the linear `u`, `v`, and `ε`
pieces from `(1+u)(1-v)(1+ε)`. -/
def productCrossResidual (N m s : Nat) : ℚ :=
  PiFactor m s * DFactor m s * (1 + epsilonMinus N (m-s))
    - (1 + (PiFactor m s - 1) - (1 - DFactor m s) + epsilonMinus N (m-s))

private theorem abs_four_sub_le (a b c d : ℚ) :
    |a - b - c - d| ≤ |a| + |b| + |c| + |d| := by
  have h1 : |a - b - c - d| ≤ |a - b - c| + |d| := by
    simpa [sub_eq_add_neg, add_assoc] using abs_add_le (a - b - c) (-d)
  have h2 : |a - b - c| ≤ |a - b| + |c| := by
    simpa [sub_eq_add_neg, add_assoc] using abs_add_le (a - b) (-c)
  have h3 : |a - b| ≤ |a| + |b| := by
    simpa [sub_eq_add_neg] using abs_add_le a (-b)
  linarith

private theorem abs_product_cross_le {u v eps : ℚ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |(1+u) * (1-v) * (1+eps) - (1+u-v+eps)|
      ≤ u * (v + |eps|) + v * |eps| * (1 + u) := by
  have hrewrite :
      (1+u) * (1-v) * (1+eps) - (1+u-v+eps)
        = u*eps - v*eps - u*v - u*v*eps := by
    ring
  rw [hrewrite]
  calc
    |u*eps - v*eps - u*v - u*v*eps|
      ≤ |u*eps| + |v*eps| + |u*v| + |u*v*eps| :=
        abs_four_sub_le (u*eps) (v*eps) (u*v) (u*v*eps)
    _ = u * |eps| + v * |eps| + u*v + u*v*|eps| := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul]
        simp [abs_of_nonneg hu, abs_of_nonneg hv]
    _ = u * (v + |eps|) + v * |eps| * (1 + u) := by ring

theorem abs_productCrossResidual_le
    {N m s : Nat} (hs : s < m) (hD : DFactor m s ≤ 1) :
    |productCrossResidual N m s|
      ≤ (PiFactor m s - 1) * ((1 - DFactor m s) + |epsilonMinus N (m-s)|)
          + (1 - DFactor m s) * |epsilonMinus N (m-s)| *
            (1 + (PiFactor m s - 1)) := by
  have hu : 0 ≤ PiFactor m s - 1 := by
    linarith [one_le_PiFactor (m := m) (s := s) hs]
  have hv : 0 ≤ 1 - DFactor m s := by linarith
  simpa [productCrossResidual] using
    (abs_product_cross_le
      (u := PiFactor m s - 1)
      (v := 1 - DFactor m s)
      (eps := epsilonMinus N (m-s)) hu hv)

/-- Dominant P4 cross-term budget, corresponding to
`1.168 * 13.2 * e₁(s) * exp(0.2237s) / m²` after absorbing
`ζ^s` into `gammaTilt^s`. -/
def crossDominantBudgetTerm (m s : Nat) : ℚ :=
  ((146/125) * (66/5) * eOne s * gammaTilt^s / (s.factorial : ℚ))
    / (m : ℚ)^2

/-- P4 smaller cross term `u_s v_s`, using
`u_s ≤ 1.168 e₁(s)e^{0.2237s}/m` and the formalized
`v_s ≤ 1.12s/m²`. -/
def crossUVBudgetTerm (m s : Nat) : ℚ :=
  ((146/125) * (28/25) * eOne s * (s : ℚ) * gammaTilt^s / (s.factorial : ℚ))
    / (m : ℚ)^3

/-- P4 smaller cross term `v_s|ε_p|`. -/
def crossVEpsBudgetTerm (m s : Nat) : ℚ :=
  ((28/25) * (66/5) * (s : ℚ) * zetaMax^s / (s.factorial : ℚ))
    / (m : ℚ)^3

/-- P4 smaller cross term `v_s|ε_p|u_s`. -/
def crossVEpsUBudgetTerm (m s : Nat) : ℚ :=
  ((28/25) * (66/5) * (146/125) * eOne s * (s : ℚ) *
      gammaTilt^s / (s.factorial : ℚ)) / (m : ℚ)^4

/-- The explicitly budgeted smaller P4 cross terms. -/
def crossSmallBudgetTerm (m s : Nat) : ℚ :=
  crossUVBudgetTerm m s + crossVEpsBudgetTerm m s + crossVEpsUBudgetTerm m s

/-- Pointwise P4 majorant for `u_s = Π_s-1`.  The hard remaining product
estimate is to prove `Π_s-1 ≤ piUBridgeBound m s`; the bridge lemmas below
then convert it into the weighted P4 budgets. -/
def piUBridgeBound (m s : Nat) : ℚ :=
  ((146/125) * eOne s * (gammaTilt / zetaMax)^s) / (m : ℚ)

theorem piUBridgeBound_nonneg {m s : Nat} (hm : 1 ≤ m) :
    0 ≤ piUBridgeBound m s := by
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  have htilt : 0 ≤ gammaTilt / zetaMax := by norm_num [gammaTilt, zetaMax]
  unfold piUBridgeBound
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) (eOne_nonneg s))
      (pow_nonneg htilt s))
    hmpos.le

/-- Reduces the P4 `u_s` input to the natural product/log target
`Π_s-1 ≤ L_s·r^s`, where `L_s = piLogUpperBound m s` and
`r = gammaTilt/zetaMax`. -/
theorem piUBridgeBound_of_piLogUpperProductBound
    {m s : Nat} (hm : 361 ≤ m) (hs3 : 3*s ≤ m)
    (hprod :
      PiFactor m s - 1
        ≤ piLogUpperBound m s * (gammaTilt / zetaMax)^s) :
    PiFactor m s - 1 ≤ piUBridgeBound m s := by
  have htilt : 0 ≤ (gammaTilt / zetaMax)^s := by
    exact pow_nonneg (by norm_num [gammaTilt, zetaMax]) s
  have hL := piLogUpperBound_le_u_linear (m := m) (s := s) hm hs3
  calc
    PiFactor m s - 1
      ≤ piLogUpperBound m s * (gammaTilt / zetaMax)^s := hprod
    _ ≤ ((146/125) * eOne s / (m : ℚ)) * (gammaTilt / zetaMax)^s :=
        mul_le_mul_of_nonneg_right hL htilt
    _ = piUBridgeBound m s := by
        unfold piUBridgeBound
        ring

private theorem weighted_piUBridgeBound_epsBound_eq_crossDominant
    (m s : Nat) :
    (zetaMax^s / (s.factorial : ℚ)) *
        (piUBridgeBound m s * ((66/5) / (m : ℚ)))
      = crossDominantBudgetTerm m s := by
  unfold piUBridgeBound crossDominantBudgetTerm
  calc
    (zetaMax^s / (s.factorial : ℚ)) *
        ((((146/125) * eOne s * (gammaTilt / zetaMax)^s) / (m : ℚ)) *
          ((66/5) / (m : ℚ)))
      = ((146/125) * (66/5) * eOne s *
          (zetaMax^s * (gammaTilt / zetaMax)^s) / (s.factorial : ℚ)) /
          (m : ℚ)^2 := by
          ring
    _ = ((146/125) * (66/5) * eOne s * gammaTilt^s /
          (s.factorial : ℚ)) / (m : ℚ)^2 := by
          rw [zetaMax_pow_mul_tilt_pow]

private theorem weighted_piUBridgeBound_vBound_eq_crossUV (m s : Nat) :
    (zetaMax^s / (s.factorial : ℚ)) *
        (piUBridgeBound m s * ((28/25) * (s : ℚ) / (m : ℚ)^2))
      = crossUVBudgetTerm m s := by
  unfold piUBridgeBound crossUVBudgetTerm
  calc
    (zetaMax^s / (s.factorial : ℚ)) *
        ((((146/125) * eOne s * (gammaTilt / zetaMax)^s) / (m : ℚ)) *
          ((28/25) * (s : ℚ) / (m : ℚ)^2))
      = ((146/125) * (28/25) * eOne s * (s : ℚ) *
          (zetaMax^s * (gammaTilt / zetaMax)^s) / (s.factorial : ℚ)) /
          (m : ℚ)^3 := by
          ring
    _ = ((146/125) * (28/25) * eOne s * (s : ℚ) * gammaTilt^s /
          (s.factorial : ℚ)) / (m : ℚ)^3 := by
          rw [zetaMax_pow_mul_tilt_pow]

private theorem weighted_vBound_epsBound_piUBridgeBound_eq_crossVEpsU
    (m s : Nat) :
    (zetaMax^s / (s.factorial : ℚ)) *
        (((28/25) * (s : ℚ) / (m : ℚ)^2) *
          ((66/5) / (m : ℚ)) * piUBridgeBound m s)
      = crossVEpsUBudgetTerm m s := by
  unfold piUBridgeBound crossVEpsUBudgetTerm
  calc
    (zetaMax^s / (s.factorial : ℚ)) *
        (((28/25) * (s : ℚ) / (m : ℚ)^2) *
          ((66/5) / (m : ℚ)) *
          (((146/125) * eOne s * (gammaTilt / zetaMax)^s) / (m : ℚ)))
      =
        ((28/25) * (66/5) * (146/125) * eOne s * (s : ℚ) *
          (zetaMax^s * (gammaTilt / zetaMax)^s) / (s.factorial : ℚ)) /
          (m : ℚ)^4 := by
          ring
    _ =
        ((28/25) * (66/5) * (146/125) * eOne s * (s : ℚ) *
          gammaTilt^s / (s.factorial : ℚ)) / (m : ℚ)^4 := by
          rw [zetaMax_pow_mul_tilt_pow]

/-- Pointwise bridge from the actual product cross residual to the four P4
budget terms, assuming the displayed pointwise `u`, `v`, and `ε` estimates have
already been converted into the corresponding weighted inequalities. -/
theorem productCrossResidual_weighted_le_P4_budgetTerm
    {N m s : Nat} (hs : s < m) (hD : DFactor m s ≤ 1)
    (hDominant :
      (zetaMax^s / (s.factorial : ℚ)) *
          (PiFactor m s - 1) * |epsilonMinus N (m-s)|
        ≤ crossDominantBudgetTerm m s)
    (hUV :
      (zetaMax^s / (s.factorial : ℚ)) *
          (PiFactor m s - 1) * (1 - DFactor m s)
        ≤ crossUVBudgetTerm m s)
    (hVEps :
      (zetaMax^s / (s.factorial : ℚ)) *
          (1 - DFactor m s) * |epsilonMinus N (m-s)|
        ≤ crossVEpsBudgetTerm m s)
    (hVEpsU :
      (zetaMax^s / (s.factorial : ℚ)) *
          (1 - DFactor m s) * |epsilonMinus N (m-s)| *
          (PiFactor m s - 1)
        ≤ crossVEpsUBudgetTerm m s) :
    (zetaMax^s / (s.factorial : ℚ)) * |productCrossResidual N m s|
      ≤ crossDominantBudgetTerm m s + crossSmallBudgetTerm m s := by
  have hweight : 0 ≤ zetaMax^s / (s.factorial : ℚ) := by
    have hz : 0 ≤ zetaMax := by norm_num [zetaMax]
    positivity
  have hcross := abs_productCrossResidual_le (N := N) (m := m) (s := s) hs hD
  calc
    (zetaMax^s / (s.factorial : ℚ)) * |productCrossResidual N m s|
      ≤ (zetaMax^s / (s.factorial : ℚ)) *
          ((PiFactor m s - 1) *
              ((1 - DFactor m s) + |epsilonMinus N (m-s)|)
            + (1 - DFactor m s) * |epsilonMinus N (m-s)| *
              (1 + (PiFactor m s - 1))) :=
          mul_le_mul_of_nonneg_left hcross hweight
    _ =
        (zetaMax^s / (s.factorial : ℚ)) *
            (PiFactor m s - 1) * |epsilonMinus N (m-s)|
          + (zetaMax^s / (s.factorial : ℚ)) *
            (PiFactor m s - 1) * (1 - DFactor m s)
          + (zetaMax^s / (s.factorial : ℚ)) *
            (1 - DFactor m s) * |epsilonMinus N (m-s)|
          + (zetaMax^s / (s.factorial : ℚ)) *
            (1 - DFactor m s) * |epsilonMinus N (m-s)| *
            (PiFactor m s - 1) := by
          ring
    _ ≤ crossDominantBudgetTerm m s + crossUVBudgetTerm m s
          + crossVEpsBudgetTerm m s + crossVEpsUBudgetTerm m s := by
          exact add_le_add
            (add_le_add
              (add_le_add hDominant hUV)
              hVEps)
            hVEpsU
    _ = crossDominantBudgetTerm m s + crossSmallBudgetTerm m s := by
          unfold crossSmallBudgetTerm
          ring

/-- The P4 `v_s|ε_p|` bridge input follows from the formalized near-range
`d`-drift bound and the completed nonlinear envelope. -/
theorem weighted_VEps_le_crossVEpsBudgetTerm
    {N m s : Nat} (hN : 1 ≤ N)
    (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ))
    (hm : 361 ≤ m) (hs3 : 3*s ≤ m) :
    (zetaMax^s / (s.factorial : ℚ)) *
        (1 - DFactor m s) * |epsilonMinus N (m-s)|
      ≤ crossVEpsBudgetTerm m s := by
  have hweight : 0 ≤ zetaMax^s / (s.factorial : ℚ) := by
    have hz : 0 ≤ zetaMax := by norm_num [zetaMax]
    positivity
  have hV := one_sub_DFactor_le_linear_near (m := m) (s := s) (by omega : 1 ≤ m) hs3
  have hE := abs_epsilonMinus_le_final_of_three_mul_le
    (N := N) (m := m) (s := s) hN hN40 hm hs3
  have hVbound_nonneg : 0 ≤ (28/25) * (s : ℚ) / (m : ℚ)^2 := by positivity
  have hmul :
      (1 - DFactor m s) * |epsilonMinus N (m-s)|
        ≤ ((28/25) * (s : ℚ) / (m : ℚ)^2) * ((66/5) / (m : ℚ)) :=
    mul_le_mul hV hE (abs_nonneg _) hVbound_nonneg
  calc
    (zetaMax^s / (s.factorial : ℚ)) *
        (1 - DFactor m s) * |epsilonMinus N (m-s)|
      ≤ (zetaMax^s / (s.factorial : ℚ)) *
          (((28/25) * (s : ℚ) / (m : ℚ)^2) * ((66/5) / (m : ℚ))) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hmul hweight
    _ = crossVEpsBudgetTerm m s := by
          unfold crossVEpsBudgetTerm
          ring

/-- Conditional P4 dominant bridge: a pointwise `u_s` bound plus the
completed `ε` envelope gives the weighted dominant cross budget. -/
theorem weighted_uEps_le_crossDominantBudgetTerm
    {N m s : Nat} (hN : 1 ≤ N)
    (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ))
    (hm : 361 ≤ m) (hs3 : 3*s ≤ m)
    (hU : PiFactor m s - 1 ≤ piUBridgeBound m s) :
    (zetaMax^s / (s.factorial : ℚ)) *
        (PiFactor m s - 1) * |epsilonMinus N (m-s)|
      ≤ crossDominantBudgetTerm m s := by
  have hweight : 0 ≤ zetaMax^s / (s.factorial : ℚ) := by
    have hz : 0 ≤ zetaMax := by norm_num [zetaMax]
    positivity
  have hE := abs_epsilonMinus_le_final_of_three_mul_le
    (N := N) (m := m) (s := s) hN hN40 hm hs3
  have hUbound_nonneg : 0 ≤ piUBridgeBound m s :=
    piUBridgeBound_nonneg (m := m) (s := s) (by omega : 1 ≤ m)
  have hmul :
      (PiFactor m s - 1) * |epsilonMinus N (m-s)|
        ≤ piUBridgeBound m s * ((66/5) / (m : ℚ)) :=
    mul_le_mul hU hE (abs_nonneg _) hUbound_nonneg
  calc
    (zetaMax^s / (s.factorial : ℚ)) *
        (PiFactor m s - 1) * |epsilonMinus N (m-s)|
      = (zetaMax^s / (s.factorial : ℚ)) *
          ((PiFactor m s - 1) * |epsilonMinus N (m-s)|) := by
          ring
    _ ≤ (zetaMax^s / (s.factorial : ℚ)) *
          (piUBridgeBound m s * ((66/5) / (m : ℚ))) :=
          mul_le_mul_of_nonneg_left hmul hweight
    _ = crossDominantBudgetTerm m s :=
          weighted_piUBridgeBound_epsBound_eq_crossDominant m s

/-- Conditional P4 `u_s v_s` bridge from the pointwise `u_s` estimate and the
formal near-range `d`-drift bound. -/
theorem weighted_uV_le_crossUVBudgetTerm
    {m s : Nat} (hm : 361 ≤ m) (hs3 : 3*s ≤ m)
    (hU : PiFactor m s - 1 ≤ piUBridgeBound m s) :
    (zetaMax^s / (s.factorial : ℚ)) *
        (PiFactor m s - 1) * (1 - DFactor m s)
      ≤ crossUVBudgetTerm m s := by
  have hweight : 0 ≤ zetaMax^s / (s.factorial : ℚ) := by
    have hz : 0 ≤ zetaMax := by norm_num [zetaMax]
    positivity
  have hD := DFactor_le_one (m := m) (s := s) (by omega : 1 ≤ m)
  have hV := one_sub_DFactor_le_linear_near (m := m) (s := s) (by omega : 1 ≤ m) hs3
  have hV_nonneg : 0 ≤ 1 - DFactor m s := by linarith
  have hUbound_nonneg : 0 ≤ piUBridgeBound m s :=
    piUBridgeBound_nonneg (m := m) (s := s) (by omega : 1 ≤ m)
  have hmul :
      (PiFactor m s - 1) * (1 - DFactor m s)
        ≤ piUBridgeBound m s * ((28/25) * (s : ℚ) / (m : ℚ)^2) :=
    mul_le_mul hU hV hV_nonneg hUbound_nonneg
  calc
    (zetaMax^s / (s.factorial : ℚ)) *
        (PiFactor m s - 1) * (1 - DFactor m s)
      = (zetaMax^s / (s.factorial : ℚ)) *
          ((PiFactor m s - 1) * (1 - DFactor m s)) := by
          ring
    _ ≤ (zetaMax^s / (s.factorial : ℚ)) *
          (piUBridgeBound m s * ((28/25) * (s : ℚ) / (m : ℚ)^2)) :=
          mul_le_mul_of_nonneg_left hmul hweight
    _ = crossUVBudgetTerm m s :=
          weighted_piUBridgeBound_vBound_eq_crossUV m s

/-- Conditional P4 `v_s|ε_p|u_s` bridge from the pointwise `u_s` estimate, the
formal near-range `d`-drift bound, and the completed `ε` envelope. -/
theorem weighted_VEpsU_le_crossVEpsUBudgetTerm
    {N m s : Nat} (hN : 1 ≤ N)
    (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ))
    (hm : 361 ≤ m) (hs3 : 3*s ≤ m)
    (hU : PiFactor m s - 1 ≤ piUBridgeBound m s) :
    (zetaMax^s / (s.factorial : ℚ)) *
        (1 - DFactor m s) * |epsilonMinus N (m-s)| *
        (PiFactor m s - 1)
      ≤ crossVEpsUBudgetTerm m s := by
  have hslt : s < m := by omega
  have hweight : 0 ≤ zetaMax^s / (s.factorial : ℚ) := by
    have hz : 0 ≤ zetaMax := by norm_num [zetaMax]
    positivity
  have hV := one_sub_DFactor_le_linear_near (m := m) (s := s) (by omega : 1 ≤ m) hs3
  have hE := abs_epsilonMinus_le_final_of_three_mul_le
    (N := N) (m := m) (s := s) hN hN40 hm hs3
  have hVbound_nonneg : 0 ≤ (28/25) * (s : ℚ) / (m : ℚ)^2 := by positivity
  have hVE :
      (1 - DFactor m s) * |epsilonMinus N (m-s)|
        ≤ ((28/25) * (s : ℚ) / (m : ℚ)^2) * ((66/5) / (m : ℚ)) :=
    mul_le_mul hV hE (abs_nonneg _) hVbound_nonneg
  have hu_nonneg : 0 ≤ PiFactor m s - 1 := by
    linarith [one_le_PiFactor (m := m) (s := s) hslt]
  have hVEbound_nonneg :
      0 ≤ ((28/25) * (s : ℚ) / (m : ℚ)^2) * ((66/5) / (m : ℚ)) := by
    positivity
  have hmul :
      (1 - DFactor m s) * |epsilonMinus N (m-s)| * (PiFactor m s - 1)
        ≤ ((28/25) * (s : ℚ) / (m : ℚ)^2) *
            ((66/5) / (m : ℚ)) * piUBridgeBound m s :=
    mul_le_mul hVE hU hu_nonneg hVEbound_nonneg
  calc
    (zetaMax^s / (s.factorial : ℚ)) *
        (1 - DFactor m s) * |epsilonMinus N (m-s)| *
        (PiFactor m s - 1)
      = (zetaMax^s / (s.factorial : ℚ)) *
          ((1 - DFactor m s) * |epsilonMinus N (m-s)| *
            (PiFactor m s - 1)) := by
          ring
    _ ≤ (zetaMax^s / (s.factorial : ℚ)) *
          (((28/25) * (s : ℚ) / (m : ℚ)^2) *
            ((66/5) / (m : ℚ)) * piUBridgeBound m s) :=
          mul_le_mul_of_nonneg_left hmul hweight
    _ = crossVEpsUBudgetTerm m s :=
          weighted_vBound_epsBound_piUBridgeBound_eq_crossVEpsU m s

/-- Packaged pointwise P4 bridge: after the remaining pointwise `u_s` product
estimate is supplied, the actual weighted product-cross residual is bounded by
the P4 budget terms. -/
theorem productCrossResidual_weighted_le_P4_budgetTerm_of_u_bound
    {N m s : Nat} (hN : 1 ≤ N)
    (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ))
    (hm : 361 ≤ m) (hs3 : 3*s ≤ m)
    (hU : PiFactor m s - 1 ≤ piUBridgeBound m s) :
    (zetaMax^s / (s.factorial : ℚ)) * |productCrossResidual N m s|
      ≤ crossDominantBudgetTerm m s + crossSmallBudgetTerm m s := by
  exact productCrossResidual_weighted_le_P4_budgetTerm
    (N := N) (m := m) (s := s)
    (by omega : s < m)
    (DFactor_le_one (m := m) (s := s) (by omega : 1 ≤ m))
    (weighted_uEps_le_crossDominantBudgetTerm
      (N := N) (m := m) (s := s) hN hN40 hm hs3 hU)
    (weighted_uV_le_crossUVBudgetTerm
      (m := m) (s := s) hm hs3 hU)
    (weighted_VEps_le_crossVEpsBudgetTerm
      (N := N) (m := m) (s := s) hN hN40 hm hs3)
    (weighted_VEpsU_le_crossVEpsUBudgetTerm
      (N := N) (m := m) (s := s) hN hN40 hm hs3 hU)

/-- P4 bridge in the form expected from the product/log estimate
`Π_s-1 ≤ L_s·r^s`. -/
theorem productCrossResidual_weighted_le_P4_budgetTerm_of_piLogUpperProductBound
    {N m s : Nat} (hN : 1 ≤ N)
    (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ))
    (hm : 361 ≤ m) (hs3 : 3*s ≤ m)
    (hprod :
      PiFactor m s - 1
        ≤ piLogUpperBound m s * (gammaTilt / zetaMax)^s) :
    (zetaMax^s / (s.factorial : ℚ)) * |productCrossResidual N m s|
      ≤ crossDominantBudgetTerm m s + crossSmallBudgetTerm m s :=
  productCrossResidual_weighted_le_P4_budgetTerm_of_u_bound
    (N := N) (m := m) (s := s) hN hN40 hm hs3
    (piUBridgeBound_of_piLogUpperProductBound
      (m := m) (s := s) hm hs3 hprod)

/-- Closed P4 weighted product-cross bridge in the near range. -/
theorem productCrossResidual_weighted_le_P4_budgetTerm_near
    {N m s : Nat} (hN : 1 ≤ N)
    (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ))
    (hm : 361 ≤ m) (hs3 : 3*s ≤ m) :
    (zetaMax^s / (s.factorial : ℚ)) * |productCrossResidual N m s|
      ≤ crossDominantBudgetTerm m s + crossSmallBudgetTerm m s :=
  productCrossResidual_weighted_le_P4_budgetTerm_of_piLogUpperProductBound
    (N := N) (m := m) (s := s) hN hN40 hm hs3
    (PiFactor_sub_one_le_piLogUpperProductBound (m := m) (s := s) hm hs3)

/-- The smaller P4 cross terms fit inside the `3/2·m⁻²` reserve used by
`signLock_P4_numerical_budget_zetaMax`. -/
theorem signLock_P4_small_budget_zetaMax {m : Nat} (hm : 361 ≤ m) :
    ∑ s ∈ Finset.range (m/3 + 1), crossSmallBudgetTerm m s
      ≤ (3/2) / (m : ℚ)^2 := by
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  have hmQ : (361 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have hUV :
      (∑ s ∈ Finset.range (m/3 + 1), crossUVBudgetTerm m s)
        =
      ((146/125) * (28/25) / (m : ℚ)^3) *
        (∑ s ∈ Finset.range (m/3 + 1),
          eOne s * (s : ℚ) * gammaTilt^s / (s.factorial : ℚ)) := by
    unfold crossUVBudgetTerm
    rw [← Finset.sum_div]
    calc
      (∑ i ∈ Finset.range (m/3 + 1),
          (146/125) * (28/25) * eOne i * (i : ℚ) *
            gammaTilt^i / (i.factorial : ℚ)) / (m : ℚ)^3
        =
        ((146/125) * (28/25) *
          (∑ i ∈ Finset.range (m/3 + 1),
            eOne i * (i : ℚ) * gammaTilt^i / (i.factorial : ℚ))) / (m : ℚ)^3 := by
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          ring
      _ =
        ((146/125) * (28/25) / (m : ℚ)^3) *
          (∑ s ∈ Finset.range (m/3 + 1),
            eOne s * (s : ℚ) * gammaTilt^s / (s.factorial : ℚ)) := by
          ring
  have hVEps :
      (∑ s ∈ Finset.range (m/3 + 1), crossVEpsBudgetTerm m s)
        =
      ((28/25) * (66/5) / (m : ℚ)^3) *
        (∑ s ∈ Finset.range (m/3 + 1),
          (s : ℚ) * zetaMax^s / (s.factorial : ℚ)) := by
    unfold crossVEpsBudgetTerm
    rw [← Finset.sum_div]
    calc
      (∑ i ∈ Finset.range (m/3 + 1),
          (28/25) * (66/5) * (i : ℚ) * zetaMax^i / (i.factorial : ℚ)) /
          (m : ℚ)^3
        =
        ((28/25) * (66/5) *
          (∑ i ∈ Finset.range (m/3 + 1),
            (i : ℚ) * zetaMax^i / (i.factorial : ℚ))) / (m : ℚ)^3 := by
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          ring
      _ =
        ((28/25) * (66/5) / (m : ℚ)^3) *
          (∑ s ∈ Finset.range (m/3 + 1),
            (s : ℚ) * zetaMax^s / (s.factorial : ℚ)) := by
          ring
  have hVEpsU :
      (∑ s ∈ Finset.range (m/3 + 1), crossVEpsUBudgetTerm m s)
        =
      ((28/25) * (66/5) * (146/125) / (m : ℚ)^4) *
        (∑ s ∈ Finset.range (m/3 + 1),
          eOne s * (s : ℚ) * gammaTilt^s / (s.factorial : ℚ)) := by
    unfold crossVEpsUBudgetTerm
    rw [← Finset.sum_div]
    calc
      (∑ i ∈ Finset.range (m/3 + 1),
          (28/25) * (66/5) * (146/125) * eOne i * (i : ℚ) *
            gammaTilt^i / (i.factorial : ℚ)) / (m : ℚ)^4
        =
        ((28/25) * (66/5) * (146/125) *
          (∑ i ∈ Finset.range (m/3 + 1),
            eOne i * (i : ℚ) * gammaTilt^i / (i.factorial : ℚ))) / (m : ℚ)^4 := by
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          ring
      _ =
        ((28/25) * (66/5) * (146/125) / (m : ℚ)^4) *
          (∑ s ∈ Finset.range (m/3 + 1),
            eOne s * (s : ℚ) * gammaTilt^s / (s.factorial : ℚ)) := by
          ring
  have hsplit :
      (∑ s ∈ Finset.range (m/3 + 1), crossSmallBudgetTerm m s)
        =
      ((146/125) * (28/25) / (m : ℚ)^3) *
          (∑ s ∈ Finset.range (m/3 + 1),
            eOne s * (s : ℚ) * gammaTilt^s / (s.factorial : ℚ))
        + ((28/25) * (66/5) / (m : ℚ)^3) *
          (∑ s ∈ Finset.range (m/3 + 1),
            (s : ℚ) * zetaMax^s / (s.factorial : ℚ))
        + ((28/25) * (66/5) * (146/125) / (m : ℚ)^4) *
          (∑ s ∈ Finset.range (m/3 + 1),
            eOne s * (s : ℚ) * gammaTilt^s / (s.factorial : ℚ)) := by
    unfold crossSmallBudgetTerm
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hUV, hVEps, hVEpsU]
  rw [hsplit]
  calc
    ((146/125) * (28/25) / (m : ℚ)^3) *
          (∑ s ∈ Finset.range (m/3 + 1),
            eOne s * (s : ℚ) * gammaTilt^s / (s.factorial : ℚ))
        + ((28/25) * (66/5) / (m : ℚ)^3) *
          (∑ s ∈ Finset.range (m/3 + 1),
            (s : ℚ) * zetaMax^s / (s.factorial : ℚ))
        + ((28/25) * (66/5) * (146/125) / (m : ℚ)^4) *
          (∑ s ∈ Finset.range (m/3 + 1),
            eOne s * (s : ℚ) * gammaTilt^s / (s.factorial : ℚ))
      ≤ ((146/125) * (28/25) / (m : ℚ)^3) * 196
          + ((28/25) * (66/5) / (m : ℚ)^3) * 12
          + ((28/25) * (66/5) * (146/125) / (m : ℚ)^4) * 196 := by
          exact add_le_add
            (add_le_add
              (mul_le_mul_of_nonneg_left (poissonEOneMulS_gammaTilt_le _)
                (by positivity))
              (mul_le_mul_of_nonneg_left (poissonFirst_zetaMax_le _)
                (by positivity)))
            (mul_le_mul_of_nonneg_left (poissonEOneMulS_gammaTilt_le _)
              (by positivity))
    _ ≤ (3/2) / (m : ℚ)^2 := by
          field_simp [hmpos.ne']
          nlinarith

/-- P4 numerical reserve: the dominant cross term plus a `3/2·m⁻²`
allowance for the smaller `u_s v_s` and `v_s |ε_p| (1+u_s)` pieces is within
the paper's `784/m²` budget. -/
theorem signLock_P4_numerical_budget_zetaMax {m : Nat} (hm : 1 ≤ m) :
    ∑ s ∈ Finset.range (m/3 + 1), crossDominantBudgetTerm m s
        + (3/2) / (m : ℚ)^2
      ≤ 784 / (m : ℚ)^2 := by
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  have hsplit :
      (∑ s ∈ Finset.range (m/3 + 1), crossDominantBudgetTerm m s)
        =
      ((146/125) * (66/5) *
          (∑ s ∈ Finset.range (m/3 + 1),
            eOne s * gammaTilt^s / (s.factorial : ℚ))) / (m : ℚ)^2 := by
    unfold crossDominantBudgetTerm
    rw [← Finset.sum_div, Finset.mul_sum]
    rw [mul_comm]
    congr 1
    refine Finset.sum_congr rfl fun s hs => ?_
    ring
  rw [hsplit]
  have hdom :
      (146/125) * (66/5) *
          (∑ s ∈ Finset.range (m/3 + 1),
            eOne s * gammaTilt^s / (s.factorial : ℚ))
        ≤ (146/125) * (66/5) * (203/4) := by
    exact mul_le_mul_of_nonneg_left (poissonEOne_gammaTilt_le _) (by norm_num)
  have hdom_div :
      ((146/125) * (66/5) *
          (∑ s ∈ Finset.range (m/3 + 1),
            eOne s * gammaTilt^s / (s.factorial : ℚ))) / (m : ℚ)^2
        ≤ ((146/125) * (66/5) * (203/4)) / (m : ℚ)^2 :=
    div_le_div_of_nonneg_right hdom (sq_nonneg (m : ℚ))
  calc
    ((146/125) * (66/5) *
          (∑ s ∈ Finset.range (m/3 + 1),
            eOne s * gammaTilt^s / (s.factorial : ℚ))) / (m : ℚ)^2
        + (3/2) / (m : ℚ)^2
      ≤ ((146/125) * (66/5) * (203/4)) / (m : ℚ)^2
          + (3/2) / (m : ℚ)^2 := by
          exact add_le_add hdom_div le_rfl
    _ ≤ 784 / (m : ℚ)^2 := by
          field_simp [hmpos.ne']
          norm_num

/-- P4 numerical budget with the smaller cross terms expanded explicitly. -/
theorem signLock_P4_budget_zetaMax {m : Nat} (hm : 361 ≤ m) :
    ∑ s ∈ Finset.range (m/3 + 1), crossDominantBudgetTerm m s
        + ∑ s ∈ Finset.range (m/3 + 1), crossSmallBudgetTerm m s
      ≤ 784 / (m : ℚ)^2 := by
  calc
    ∑ s ∈ Finset.range (m/3 + 1), crossDominantBudgetTerm m s
        + ∑ s ∈ Finset.range (m/3 + 1), crossSmallBudgetTerm m s
      ≤ ∑ s ∈ Finset.range (m/3 + 1), crossDominantBudgetTerm m s
          + (3/2) / (m : ℚ)^2 := by
          exact add_le_add le_rfl (signLock_P4_small_budget_zetaMax hm)
    _ ≤ 784 / (m : ℚ)^2 :=
          signLock_P4_numerical_budget_zetaMax (by omega : 1 ≤ m)

/-- Closed P4 contribution for the actual product-cross residual in the near
range. -/
theorem signLock_P4_actual_budget_zetaMax {N m : Nat}
    (hN : 1 ≤ N) (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ)) (hm : 361 ≤ m) :
    ∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) * |productCrossResidual N m s|
      ≤ 784 / (m : ℚ)^2 := by
  have hpoint :
      ∑ s ∈ Finset.range (m/3 + 1),
          (zetaMax^s / (s.factorial : ℚ)) * |productCrossResidual N m s|
        ≤ ∑ s ∈ Finset.range (m/3 + 1),
            (crossDominantBudgetTerm m s + crossSmallBudgetTerm m s) := by
    exact Finset.sum_le_sum fun s hs =>
      productCrossResidual_weighted_le_P4_budgetTerm_near
        (N := N) (m := m) (s := s) hN hN40 hm (three_mul_le_of_mem_near hs)
  calc
    ∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) * |productCrossResidual N m s|
      ≤ ∑ s ∈ Finset.range (m/3 + 1),
          (crossDominantBudgetTerm m s + crossSmallBudgetTerm m s) := hpoint
    _ =
        ∑ s ∈ Finset.range (m/3 + 1), crossDominantBudgetTerm m s
          + ∑ s ∈ Finset.range (m/3 + 1), crossSmallBudgetTerm m s := by
          rw [Finset.sum_add_distrib]
    _ ≤ 784 / (m : ℚ)^2 := signLock_P4_budget_zetaMax hm

/-! ## Near-range component assembly -/

/-- The six formalized near-range component budgets add to `2214/m²`.

This is the summed audit before the final `1/m²` tail allowance.  It packages
the now-closed P1/P4 actual bridges together with the existing P2/P3 budgets.
The remaining assembly step is to connect the exact nonlinear recentering
identity for `ε_p` to the P3a/P3b/P3c majorants and then add the far-tail
allowance. -/
theorem signLock_near_component_budget_zetaMax {N m : Nat}
    (hN : 1 ≤ N) (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ)) (hm : 361 ≤ m) :
    (∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) * |piResidual m s|)
      + (∑ s ∈ Finset.range (m/3 + 1),
          (zetaMax^s / (s.factorial : ℚ)) * (1 - DFactor m s))
      + (∑ s ∈ Finset.range (m/3 + 1),
          (zetaMax^s / (s.factorial : ℚ)) *
            |twoEndpointCorrection N (m-s) - twoEndpointTarget N m|)
      + (∑ s ∈ Finset.range (m/3 + 1),
          (zetaMax^s / (s.factorial : ℚ)) *
            twoNonEndpointCorrectionBound N (m-s))
      + (∑ s ∈ Finset.range (m/3 + 1),
          (zetaMax^s / (s.factorial : ℚ)) *
            threeBlockTailBound N (m-s))
      + (∑ s ∈ Finset.range (m/3 + 1),
          (zetaMax^s / (s.factorial : ℚ)) * |productCrossResidual N m s|)
      ≤ 2214 / (m : ℚ)^2 := by
  have hP1 := signLock_P1_actual_budget_zetaMax (m := m) hm
  have hP2 := signLock_P2_budget_zetaMax (m := m) hm
  have hP3a := signLock_P3a_budget_zetaMax (N := N) (m := m) hN40 hm
  have hP3b := signLock_P3b_budget_zetaMax (N := N) (m := m) hN40 hm
  have hP3c := signLock_P3c_budget_zetaMax (N := N) (m := m) hN40 hm
  have hP4 := signLock_P4_actual_budget_zetaMax
    (N := N) (m := m) hN hN40 hm
  calc
    (∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) * |piResidual m s|)
      + (∑ s ∈ Finset.range (m/3 + 1),
          (zetaMax^s / (s.factorial : ℚ)) * (1 - DFactor m s))
      + (∑ s ∈ Finset.range (m/3 + 1),
          (zetaMax^s / (s.factorial : ℚ)) *
            |twoEndpointCorrection N (m-s) - twoEndpointTarget N m|)
      + (∑ s ∈ Finset.range (m/3 + 1),
          (zetaMax^s / (s.factorial : ℚ)) *
            twoNonEndpointCorrectionBound N (m-s))
      + (∑ s ∈ Finset.range (m/3 + 1),
          (zetaMax^s / (s.factorial : ℚ)) *
            threeBlockTailBound N (m-s))
      + (∑ s ∈ Finset.range (m/3 + 1),
          (zetaMax^s / (s.factorial : ℚ)) * |productCrossResidual N m s|)
      ≤ 426 / (m : ℚ)^2 + 13 / (m : ℚ)^2 + 184 / (m : ℚ)^2
          + 234 / (m : ℚ)^2 + 573 / (m : ℚ)^2 + 784 / (m : ℚ)^2 := by
          exact add_le_add
            (add_le_add
              (add_le_add
                (add_le_add
                  (add_le_add hP1 hP2)
                  hP3a)
                hP3b)
              hP3c)
            hP4
    _ = 2214 / (m : ℚ)^2 := by ring_nf

/-! ## Conditional assembly of the near-range `w_s` error -/

/-- The nonlinear recentering residual after extracting the leading
two-endpoint correction from `ε_p`.  The remaining exact P3 bridge is to bound
this by the non-endpoint two-block and three-and-more-block majorants. -/
def nonlinearRecenteringRemainder (N m s : Nat) : ℚ :=
  epsilonMinus N (m-s) + twoEndpointCorrection N (m-s)

/-- Exact-piece version of the nonlinear recentering residual. -/
theorem nonlinearRecenteringRemainder_eq_exactPieces
    {N m s : Nat} (hN : 1 ≤ N) (hp : 5 ≤ m-s) :
    nonlinearRecenteringRemainder N m s =
      twoBlockMiddleNormalized N (m-s) + threeBlockExactTail N (m-s) := by
  unfold nonlinearRecenteringRemainder
  exact epsilonMinus_add_twoEndpointCorrection_eq_exactPieces hN hp

/-- Once the exact `r ≥ 3` tail is bounded by the P3c majorant, the full
nonlinear recentering hypothesis follows from the proved P3b bridge. -/
theorem abs_nonlinearRecenteringRemainder_le_of_threeBlockExactTail
    {N m s : Nat} (hN : 1 ≤ N) (hp : 5 ≤ m-s)
    (htail : |threeBlockExactTail N (m-s)| ≤ threeBlockTailBound N (m-s)) :
    |nonlinearRecenteringRemainder N m s|
      ≤ twoNonEndpointCorrectionBound N (m-s) + threeBlockTailBound N (m-s) := by
  rw [nonlinearRecenteringRemainder_eq_exactPieces hN hp]
  calc
    |twoBlockMiddleNormalized N (m-s) + threeBlockExactTail N (m-s)|
      ≤ |twoBlockMiddleNormalized N (m-s)| + |threeBlockExactTail N (m-s)| :=
          abs_add_le _ _
    _ ≤ twoNonEndpointCorrectionBound N (m-s) + threeBlockTailBound N (m-s) :=
          add_le_add
            (abs_twoBlockMiddleNormalized_le_twoNonEndpointCorrectionBound
              (N := N) (p := m-s) hp)
            htail

/-- The P3 pointwise budget attached to the nonlinear recentering residual. -/
def nonlinearRecenteringBudgetTerm (N m s : Nat) : ℚ :=
  |twoEndpointCorrection N (m-s) - twoEndpointTarget N m|
    + twoNonEndpointCorrectionBound N (m-s)
    + threeBlockTailBound N (m-s)

theorem twoEndpointTarget_eq_zeta_div (N : Nat) {m : Nat} (hm : 1 ≤ m) :
    twoEndpointTarget N m = zetaQ N m / (m : ℚ) := by
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  unfold twoEndpointTarget zetaQ
  field_simp [hmpos.ne']

theorem abs_epsilon_zeta_le_nonlinearRecenteringBudget
    {N m s : Nat} (hm : 1 ≤ m)
    (hrem :
      |nonlinearRecenteringRemainder N m s|
        ≤ twoNonEndpointCorrectionBound N (m-s) + threeBlockTailBound N (m-s)) :
    |epsilonMinus N (m-s) + zetaQ N m / (m : ℚ)|
      ≤ nonlinearRecenteringBudgetTerm N m s := by
  have htarget := twoEndpointTarget_eq_zeta_div N (m := m) hm
  calc
    |epsilonMinus N (m-s) + zetaQ N m / (m : ℚ)|
        =
      |(epsilonMinus N (m-s) + twoEndpointCorrection N (m-s))
        + (twoEndpointTarget N m - twoEndpointCorrection N (m-s))| := by
          rw [← htarget]
          congr 1
          ring_nf
    _ ≤ |epsilonMinus N (m-s) + twoEndpointCorrection N (m-s)|
          + |twoEndpointTarget N m - twoEndpointCorrection N (m-s)| :=
          abs_add_le _ _
    _ = |nonlinearRecenteringRemainder N m s|
          + |twoEndpointCorrection N (m-s) - twoEndpointTarget N m| := by
          unfold nonlinearRecenteringRemainder
          rw [show twoEndpointTarget N m - twoEndpointCorrection N (m-s)
              = -(twoEndpointCorrection N (m-s) - twoEndpointTarget N m) by ring_nf,
            abs_neg]
    _ ≤ (twoNonEndpointCorrectionBound N (m-s) + threeBlockTailBound N (m-s))
          + |twoEndpointCorrection N (m-s) - twoEndpointTarget N m| :=
          add_le_add hrem le_rfl
    _ = nonlinearRecenteringBudgetTerm N m s := by
          unfold nonlinearRecenteringBudgetTerm
          ring_nf

private theorem abs_cross_pi_v_eps_le
    (cross pi v eps : ℚ) (hv : 0 ≤ v) :
    |cross + pi - v + eps| ≤ |pi| + v + |eps| + |cross| := by
  calc
    |cross + pi - v + eps| = |cross - (-pi) - v - (-eps)| := by ring_nf
    _ ≤ |cross| + |-pi| + |v| + |-eps| := abs_four_sub_le cross (-pi) v (-eps)
    _ = |pi| + v + |eps| + |cross| := by
        rw [abs_neg, abs_neg, abs_of_nonneg hv]
        ring_nf

theorem signLockErrorW_eq_components (N m s : Nat) :
    signLockErrorW N m s =
      productCrossResidual N m s + piResidual m s - (1 - DFactor m s)
        + (epsilonMinus N (m-s) + zetaQ N m / (m : ℚ)) := by
  unfold signLockErrorW productCrossResidual piResidual
  ring_nf

/-- Pointwise near-range `w_s` assembly, conditional on the remaining exact P3
bridge for the nonlinear recentering residual. -/
theorem abs_signLockErrorW_le_components_of_nonlinearRecentering
    {N m s : Nat} (hm : 1 ≤ m) (hD : DFactor m s ≤ 1)
    (hrem :
      |nonlinearRecenteringRemainder N m s|
        ≤ twoNonEndpointCorrectionBound N (m-s) + threeBlockTailBound N (m-s)) :
    |signLockErrorW N m s|
      ≤ |piResidual m s| + (1 - DFactor m s)
          + |twoEndpointCorrection N (m-s) - twoEndpointTarget N m|
          + twoNonEndpointCorrectionBound N (m-s)
          + threeBlockTailBound N (m-s)
          + |productCrossResidual N m s| := by
  have hv : 0 ≤ 1 - DFactor m s := by linarith
  have hnonlin :=
    abs_epsilon_zeta_le_nonlinearRecenteringBudget
      (N := N) (m := m) (s := s) hm hrem
  rw [signLockErrorW_eq_components]
  have htri := abs_cross_pi_v_eps_le
    (cross := productCrossResidual N m s)
    (pi := piResidual m s)
    (v := 1 - DFactor m s)
    (eps := epsilonMinus N (m-s) + zetaQ N m / (m : ℚ)) hv
  unfold nonlinearRecenteringBudgetTerm at hnonlin
  linarith

/-- Conditional near-range audit for the actual `w_s` errors.  The sole
remaining hypothesis is the exact nonlinear recentering bridge from the
coefficient expansion of `E^-_p`. -/
theorem signLock_near_error_budget_zetaMax_of_nonlinearRecentering
    {N m : Nat} (hN : 1 ≤ N)
    (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ)) (hm : 361 ≤ m)
    (hrem : ∀ s, s ∈ Finset.range (m/3 + 1) →
      |nonlinearRecenteringRemainder N m s|
        ≤ twoNonEndpointCorrectionBound N (m-s) + threeBlockTailBound N (m-s)) :
    ∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) * |signLockErrorW N m s|
      ≤ 2214 / (m : ℚ)^2 := by
  have hpoint :
      ∑ s ∈ Finset.range (m/3 + 1),
          (zetaMax^s / (s.factorial : ℚ)) * |signLockErrorW N m s|
        ≤
      ∑ s ∈ Finset.range (m/3 + 1),
          (zetaMax^s / (s.factorial : ℚ)) *
            (|piResidual m s| + (1 - DFactor m s)
              + |twoEndpointCorrection N (m-s) - twoEndpointTarget N m|
              + twoNonEndpointCorrectionBound N (m-s)
              + threeBlockTailBound N (m-s)
              + |productCrossResidual N m s|) := by
    refine Finset.sum_le_sum fun s hs => ?_
    have hweight : 0 ≤ zetaMax^s / (s.factorial : ℚ) := by
      have hz : 0 ≤ zetaMax := by norm_num [zetaMax]
      positivity
    exact mul_le_mul_of_nonneg_left
      (abs_signLockErrorW_le_components_of_nonlinearRecentering
        (N := N) (m := m) (s := s) (by omega : 1 ≤ m)
        (DFactor_le_one (m := m) (s := s) (by omega : 1 ≤ m))
        (hrem s hs))
      hweight
  calc
    ∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) * |signLockErrorW N m s|
      ≤
      ∑ s ∈ Finset.range (m/3 + 1),
          (zetaMax^s / (s.factorial : ℚ)) *
            (|piResidual m s| + (1 - DFactor m s)
              + |twoEndpointCorrection N (m-s) - twoEndpointTarget N m|
              + twoNonEndpointCorrectionBound N (m-s)
              + threeBlockTailBound N (m-s)
              + |productCrossResidual N m s|) := hpoint
    _ =
      (∑ s ∈ Finset.range (m/3 + 1),
          (zetaMax^s / (s.factorial : ℚ)) * |piResidual m s|)
        + (∑ s ∈ Finset.range (m/3 + 1),
            (zetaMax^s / (s.factorial : ℚ)) * (1 - DFactor m s))
        + (∑ s ∈ Finset.range (m/3 + 1),
            (zetaMax^s / (s.factorial : ℚ)) *
              |twoEndpointCorrection N (m-s) - twoEndpointTarget N m|)
        + (∑ s ∈ Finset.range (m/3 + 1),
            (zetaMax^s / (s.factorial : ℚ)) *
              twoNonEndpointCorrectionBound N (m-s))
        + (∑ s ∈ Finset.range (m/3 + 1),
            (zetaMax^s / (s.factorial : ℚ)) *
              threeBlockTailBound N (m-s))
        + (∑ s ∈ Finset.range (m/3 + 1),
            (zetaMax^s / (s.factorial : ℚ)) * |productCrossResidual N m s|) := by
        calc
          ∑ s ∈ Finset.range (m/3 + 1),
              (zetaMax^s / (s.factorial : ℚ)) *
                (|piResidual m s| + (1 - DFactor m s)
                  + |twoEndpointCorrection N (m-s) - twoEndpointTarget N m|
                  + twoNonEndpointCorrectionBound N (m-s)
                  + threeBlockTailBound N (m-s)
                  + |productCrossResidual N m s|)
            =
          ∑ s ∈ Finset.range (m/3 + 1),
              ((zetaMax^s / (s.factorial : ℚ)) * |piResidual m s|
                + (zetaMax^s / (s.factorial : ℚ)) * (1 - DFactor m s)
                + (zetaMax^s / (s.factorial : ℚ)) *
                    |twoEndpointCorrection N (m-s) - twoEndpointTarget N m|
                + (zetaMax^s / (s.factorial : ℚ)) *
                    twoNonEndpointCorrectionBound N (m-s)
                + (zetaMax^s / (s.factorial : ℚ)) *
                    threeBlockTailBound N (m-s)
                + (zetaMax^s / (s.factorial : ℚ)) *
                    |productCrossResidual N m s|) := by
                refine Finset.sum_congr rfl fun s hs => ?_
                ring_nf
          _ =
              (∑ s ∈ Finset.range (m/3 + 1),
                  (zetaMax^s / (s.factorial : ℚ)) * |piResidual m s|)
                + (∑ s ∈ Finset.range (m/3 + 1),
                    (zetaMax^s / (s.factorial : ℚ)) * (1 - DFactor m s))
                + (∑ s ∈ Finset.range (m/3 + 1),
                    (zetaMax^s / (s.factorial : ℚ)) *
                      |twoEndpointCorrection N (m-s) - twoEndpointTarget N m|)
                + (∑ s ∈ Finset.range (m/3 + 1),
                    (zetaMax^s / (s.factorial : ℚ)) *
                      twoNonEndpointCorrectionBound N (m-s))
                + (∑ s ∈ Finset.range (m/3 + 1),
                    (zetaMax^s / (s.factorial : ℚ)) *
                      threeBlockTailBound N (m-s))
                + (∑ s ∈ Finset.range (m/3 + 1),
                    (zetaMax^s / (s.factorial : ℚ)) *
                      |productCrossResidual N m s|) := by
                rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
                  Finset.sum_add_distrib, Finset.sum_add_distrib,
                  Finset.sum_add_distrib]
    _ ≤ 2214 / (m : ℚ)^2 :=
        signLock_near_component_budget_zetaMax (N := N) (m := m) hN hN40 hm

/-- Near-range `w_s` audit with the P3b middle bridge discharged.  The only
remaining exact coefficient bridge is the `r ≥ 3` tail estimate. -/
theorem signLock_near_error_budget_zetaMax_of_threeBlockExactTail
    {N m : Nat} (hN : 1 ≤ N)
    (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ)) (hm : 361 ≤ m)
    (htail : ∀ s, s ∈ Finset.range (m/3 + 1) →
      |threeBlockExactTail N (m-s)| ≤ threeBlockTailBound N (m-s)) :
    ∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) * |signLockErrorW N m s|
      ≤ 2214 / (m : ℚ)^2 := by
  refine signLock_near_error_budget_zetaMax_of_nonlinearRecentering
    (N := N) (m := m) hN hN40 hm ?_
  intro s hs
  have hs3 : 3*s ≤ m := by
    have hsle : s ≤ m/3 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    exact (Nat.mul_le_mul_left 3 hsle).trans (Nat.mul_div_le m 3)
  exact abs_nonlinearRecenteringRemainder_le_of_threeBlockExactTail
    (N := N) (m := m) (s := s) hN (by omega : 5 ≤ m-s) (htail s hs)

/-- Near-range `w_s` audit reduced to a pure rationalized-Δ P3c tail
estimate. -/
theorem signLock_near_error_budget_zetaMax_of_threeBlockDeltaTail
    {N m : Nat} (hN : 1 ≤ N)
    (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ)) (hm : 361 ≤ m)
    (hdelta : ∀ s, s ∈ Finset.range (m/3 + 1) →
      threeBlockDeltaTail N (m-s) ≤ threeBlockTailBound N (m-s)) :
    ∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) * |signLockErrorW N m s|
      ≤ 2214 / (m : ℚ)^2 := by
  refine signLock_near_error_budget_zetaMax_of_threeBlockExactTail
    (N := N) (m := m) hN hN40 hm ?_
  intro s hs
  have hs3 : 3*s ≤ m := by
    have hsle : s ≤ m/3 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    exact (Nat.mul_le_mul_left 3 hsle).trans (Nat.mul_div_le m 3)
  exact abs_threeBlockExactTail_le_threeBlockTailBound_of_DeltaTail
    (N := N) (p := m-s) hN (by omega : 5 ≤ m-s) (hdelta s hs)

/-- Closed near-range audit for the actual `w_s` errors: the exact
nonlinear recentering bridge is fully discharged through the P3b/P3c
majorants. -/
theorem signLock_near_error_budget_zetaMax
    {N m : Nat} (hN : 1 ≤ N)
    (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ)) (hm : 361 ≤ m) :
    ∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) * |signLockErrorW N m s|
      ≤ 2214 / (m : ℚ)^2 := by
  refine signLock_near_error_budget_zetaMax_of_threeBlockDeltaTail
    (N := N) (m := m) hN hN40 hm ?_
  intro s hs
  have hs3 : 3*s ≤ m := by
    have hsle : s ≤ m/3 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    exact (Nat.mul_le_mul_left 3 hsle).trans (Nat.mul_div_le m 3)
  exact threeBlockDeltaTail_le_threeBlockTailBound_near
    (N := N) (m := m) (s := s) hN hN40 hm hs3

/-! ## Far-tail allowance for `s > m/3` -/

/-- Rational replacement for the paper's `exp(6.37)` in the far-tail saddle
bound.  Lean proves the needed coefficient estimate below from the finite
`expCoeff` recurrence, instead of appealing to the analytic saddle phrasing in
the TeX file. -/
def farTailExpUpper : ℚ := 600

/-- The paper's `2.04` tail multiplier, kept as an exact rational. -/
def farTailPoissonFactor : ℚ := 51/25

/-- The omitted actual coefficient tail in the sign-lock decomposition,
corresponding to the `s > m/3` terms in the TeX proof. -/
def signLockFarTail (N m : Nat) : ℚ :=
  ∑ s ∈ Finset.Ico (m/3 + 1) (m+1),
    (((N : ℚ) * c 1)^s / (s.factorial : ℚ))
      * |Eminus (N : ℚ) (m-s)| / ((N : ℚ) * c m)

/-- The scalar saddle/Stirling expression displayed in the paper, with
`exp(6.37)` replaced by `farTailExpUpper` and `2.04` by
`farTailPoissonFactor`. -/
def signLockFarTailScalar (N m : Nat) : ℚ :=
  ((36 * farTailExpUpper) / (5 * (N : ℚ)))
    * ((m : ℚ)^m / (((m-1).factorial : Nat) : ℚ))
    * farTailPoissonFactor
    * ((zetaQ N m)^(m/3 + 1) / (((m/3 + 1).factorial : Nat) : ℚ))

/-- An `N`-free upper envelope for `signLockFarTailScalar`, using only
`N ≥ 1` and `zetaQ N m ≤ zetaMax`. -/
def farTailScalarEnvelope (m : Nat) : ℚ :=
  ((36 * farTailExpUpper) / 5)
    * ((m : ℚ)^m / (((m-1).factorial : Nat) : ℚ))
    * farTailPoissonFactor
    * (zetaMax^(m/3 + 1) / (((m/3 + 1).factorial : Nat) : ℚ))

/-- The same far-tail scalar envelope, multiplied by `m²`; this is the
quantity certified below to be at most `1`. -/
def farTailScalarEnvelopeScaled (m : Nat) : ℚ :=
  farTailScalarEnvelope m * (m : ℚ)^2

/-- The displayed far-tail scalar is bounded by the `N`-free rational envelope.
This is a small formal divergence from the TeX presentation: Lean first
maximizes the scalar over the permitted `N` range, and then certifies the
resulting one-variable envelope. -/
theorem signLockFarTailScalar_le_envelope
    {N m : Nat} (hN : 1 ≤ N)
    (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ)) (hm : 361 ≤ m) :
    signLockFarTailScalar N m ≤ farTailScalarEnvelope m := by
  have hNpos : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  have hm1 : 1 ≤ m := by omega
  have hz_nonneg : 0 ≤ zetaQ N m := zetaQ_nonneg N m
  have hz_le : zetaQ N m ≤ zetaMax := by
    exact zetaQ_le_zetaMax hm1 hN40
  have hpow_le :
      (zetaQ N m)^(m/3 + 1) ≤ zetaMax^(m/3 + 1) :=
    pow_le_pow_left₀ hz_nonneg hz_le _
  have hfac_pos : (0 : ℚ) < (((m/3 + 1).factorial : Nat) : ℚ) := by
    exact_mod_cast (Nat.factorial_pos (m/3 + 1))
  have hpois_arg :
      (zetaQ N m)^(m/3 + 1)
          / (((m/3 + 1).factorial : Nat) : ℚ)
        ≤ zetaMax^(m/3 + 1)
          / (((m/3 + 1).factorial : Nat) : ℚ) := by
    exact div_le_div_of_nonneg_right hpow_le hfac_pos.le
  have hcoef_env_nonneg :
      0 ≤ (36 * farTailExpUpper) / 5 := by
    norm_num [farTailExpUpper]
  have hcoef :
      (36 * farTailExpUpper) / (5 * (N : ℚ))
        ≤ (36 * farTailExpUpper) / 5 := by
    have hNq : (1 : ℚ) ≤ (N : ℚ) := by exact_mod_cast hN
    have hinv : 1 / (N : ℚ) ≤ 1 := by
      rw [div_le_iff₀ hNpos]
      nlinarith
    calc
        (36 * farTailExpUpper) / (5 * (N : ℚ))
            = ((36 * farTailExpUpper) / 5) * (1 / (N : ℚ)) := by
              field_simp [hNpos.ne']
          _ ≤ ((36 * farTailExpUpper) / 5) * 1 :=
                mul_le_mul_of_nonneg_left hinv hcoef_env_nonneg
          _ = (36 * farTailExpUpper) / 5 := by ring
  have hmain_nonneg :
      0 ≤ (m : ℚ)^m / (((m-1).factorial : Nat) : ℚ) := by
    exact div_nonneg (pow_nonneg (by exact_mod_cast Nat.zero_le m) m)
      (by exact_mod_cast Nat.zero_le ((m-1).factorial))
  have hpois_arg_nonneg :
      0 ≤ (zetaQ N m)^(m/3 + 1)
          / (((m/3 + 1).factorial : Nat) : ℚ) := by
    exact div_nonneg (pow_nonneg hz_nonneg _)
      (by exact_mod_cast Nat.zero_le ((m/3 + 1).factorial))
  have hpois_nonneg :
      0 ≤ zetaMax^(m/3 + 1) / (((m/3 + 1).factorial : Nat) : ℚ) := by
    exact div_nonneg (pow_nonneg (by norm_num [zetaMax]) _)
      (by exact_mod_cast Nat.zero_le ((m/3 + 1).factorial))
  unfold signLockFarTailScalar farTailScalarEnvelope
  exact mul_le_mul
    (mul_le_mul
      (mul_le_mul hcoef le_rfl hmain_nonneg hcoef_env_nonneg)
      le_rfl
      (by norm_num [farTailPoissonFactor])
      (mul_nonneg (by exact div_nonneg (by norm_num [farTailExpUpper]) (by norm_num))
          hmain_nonneg))
    hpois_arg
    hpois_arg_nonneg
    (mul_nonneg
      (mul_nonneg (by exact div_nonneg (by norm_num [farTailExpUpper]) (by norm_num))
        hmain_nonneg)
      (by norm_num [farTailPoissonFactor]))

private theorem farTailScalarEnvelopeScaled_362_le_one :
    farTailScalarEnvelopeScaled 362 ≤ 1 := by
  native_decide

private theorem farTailScalarEnvelopeScaled_361_le_one :
    farTailScalarEnvelopeScaled 361 ≤ 1 := by
  native_decide

private theorem farTailScalarEnvelopeScaled_363_le_one :
    farTailScalarEnvelopeScaled 363 ≤ 1 := by
  native_decide

/-- Exact ratio for the scaled far-tail envelope under `m ↦ m+3`. -/
def farTailThreeStepRatio (m : Nat) : ℚ :=
  (((m+3 : Nat) : ℚ)^(m+5) * zetaMax) /
    ((m : ℚ)^(m+2) * (m : ℚ) * ((m+1 : Nat) : ℚ)
      * ((m+2 : Nat) : ℚ) * ((m/3+2 : Nat) : ℚ))

private theorem farTailScalarEnvelopeScaled_add_three_eq
    {m : Nat} (hm : 1 ≤ m) :
    farTailScalarEnvelopeScaled (m+3)
      = farTailScalarEnvelopeScaled m * farTailThreeStepRatio m := by
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  have hmfac_ne : ((((m-1).factorial : Nat) : ℚ)) ≠ 0 := by positivity
  have hLfac_ne : ((((m/3+1).factorial : Nat) : ℚ)) ≠ 0 := by positivity
  have hLnext_ne : (((m/3+2 : Nat) : ℚ)) ≠ 0 := by positivity
  have hfac_m :
      (((m+2).factorial : Nat) : ℚ)
        = ((m+2 : Nat) : ℚ) * ((m+1 : Nat) : ℚ) * (m : ℚ)
            * (((m-1).factorial : Nat) : ℚ) := by
    rw [show m+2 = (m+1)+1 by omega, Nat.factorial_succ,
      show m+1 = m+1 by rfl, Nat.factorial_succ,
      show m = (m-1)+1 by omega, Nat.factorial_succ]
    push_cast
    ring
  have hfac_L :
      (((m/3+2).factorial : Nat) : ℚ)
        = ((m/3+2 : Nat) : ℚ) * (((m/3+1).factorial : Nat) : ℚ) := by
    rw [show m/3+2 = (m/3+1)+1 by omega, Nat.factorial_succ]
    push_cast
    ring
  unfold farTailScalarEnvelopeScaled farTailScalarEnvelope farTailThreeStepRatio
  rw [show (m+3)/3 + 1 = m/3 + 2 by omega]
  rw [show (m+3)-1 = m+2 by omega, hfac_m, hfac_L]
  field_simp [hmpos.ne', hmfac_ne, hLfac_ne, hLnext_ne]
  ring

private theorem farTail_three_step_exp_factor_le
    {m : Nat} (hm : 361 ≤ m) :
    (((m+3 : Nat) : ℚ) / (m : ℚ))^(m+2)
      ≤ (68/25 : ℚ)^3 * (121/120 : ℚ)^4 := by
  let q : Nat := m/3
  have hmpos : (0 : ℚ) < (m : ℚ) := by
    exact_mod_cast (by omega : 0 < m)
  have hq120 : 120 ≤ q := by
    dsimp [q]
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 3)]
    omega
  have hq1 : 1 ≤ q := by omega
  have hqpos : (0 : ℚ) < (q : ℚ) := by exact_mod_cast (by omega : 0 < q)
  have hqbase_nonneg : 0 ≤ 1 + 1 / (q : ℚ) := by positivity
  have hbase_le :
      (((m+3 : Nat) : ℚ) / (m : ℚ)) ≤ 1 + 1 / (q : ℚ) := by
    have hdiv : 3 * q ≤ m := by
      dsimp [q]
      simpa [Nat.mul_comm] using Nat.div_mul_le_self m 3
    rw [show (((m+3 : Nat) : ℚ) / (m : ℚ)) = 1 + 3 / (m : ℚ) by
      push_cast
      field_simp [hmpos.ne']]
    rw [add_le_add_iff_left]
    rw [div_le_div_iff₀ hmpos hqpos]
    norm_num
    exact_mod_cast hdiv
  have hpow_base :
      (((m+3 : Nat) : ℚ) / (m : ℚ))^(m+2)
        ≤ (1 + 1 / (q : ℚ))^(m+2) := by
    exact pow_le_pow_left₀ (by positivity) hbase_le _
  have hmod : m % 3 < 3 := Nat.mod_lt m (by norm_num : 0 < 3)
  have hdecomp : m = 3 * q + m % 3 := by
    dsimp [q]
    simpa [Nat.mul_comm] using (Nat.div_add_mod m 3).symm
  have hexp_le : m + 2 ≤ 3*q + 4 := by omega
  have hbase_one : (1 : ℚ) ≤ 1 + 1 / (q : ℚ) := by
    have hinv_nonneg : (0 : ℚ) ≤ 1 / (q : ℚ) := by positivity
    linarith
  have hpow_mono :
      (1 + 1 / (q : ℚ))^(m+2)
        ≤ (1 + 1 / (q : ℚ))^(3*q + 4) :=
    pow_right_mono₀ hbase_one hexp_le
  have hqpow : (1 + 1 / (q : ℚ))^q ≤ 68/25 :=
    one_add_inv_pow_le q hq1
  have hbase_120 : 1 + 1 / (q : ℚ) ≤ 121/120 := by
    have hq120q : (120 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq120
    rw [show (121/120 : ℚ) = 1 + 1/120 by norm_num]
    simpa [add_comm] using add_le_add_left
      (one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 120) hq120q)
      1
  have htail : (1 + 1 / (q : ℚ))^4 ≤ (121/120 : ℚ)^4 :=
    pow_le_pow_left₀ hqbase_nonneg hbase_120 4
  calc
    (((m+3 : Nat) : ℚ) / (m : ℚ))^(m+2)
        ≤ (1 + 1 / (q : ℚ))^(m+2) := hpow_base
    _ ≤ (1 + 1 / (q : ℚ))^(3*q + 4) := hpow_mono
    _ = ((1 + 1 / (q : ℚ))^q)^3 * (1 + 1 / (q : ℚ))^4 := by
        rw [show 3*q + 4 = q*3 + 4 by omega, pow_add, pow_mul]
    _ ≤ (68/25 : ℚ)^3 * (121/120 : ℚ)^4 := by
        exact mul_le_mul
          (pow_le_pow_left₀ (pow_nonneg hqbase_nonneg q) hqpow 3)
          htail
          (pow_nonneg hqbase_nonneg 4)
          (pow_nonneg (by norm_num) 3)

private theorem farTailThreeStepRatio_eq_factors
    {m : Nat} (hm : 1 ≤ m) :
    farTailThreeStepRatio m =
      (((m+3 : Nat) : ℚ) / (m : ℚ))^(m+2)
        * ((((m+3 : Nat) : ℚ)^3)
            / ((m : ℚ) * ((m+1 : Nat) : ℚ) * ((m+2 : Nat) : ℚ)))
        * (zetaMax / ((m/3+2 : Nat) : ℚ)) := by
  have hmpos : (0 : ℚ) < (m : ℚ) := by
    exact_mod_cast (by omega : 0 < m)
  have h1pos : (0 : ℚ) < ((m+1 : Nat) : ℚ) := by positivity
  have h2pos : (0 : ℚ) < ((m+2 : Nat) : ℚ) := by positivity
  have hLpos : (0 : ℚ) < ((m/3+2 : Nat) : ℚ) := by positivity
  unfold farTailThreeStepRatio
  rw [show m+5 = (m+2)+3 by omega, pow_add]
  field_simp [hmpos.ne', h1pos.ne', h2pos.ne', hLpos.ne']
  rw [div_pow]
  field_simp [hmpos.ne']

private theorem farTail_three_step_cubic_factor_le
    {m : Nat} (hm : 361 ≤ m) :
    ((((m+3 : Nat) : ℚ)^3)
        / ((m : ℚ) * ((m+1 : Nat) : ℚ) * ((m+2 : Nat) : ℚ)))
      ≤ 2 := by
  have hmpos : (0 : ℚ) < (m : ℚ) := by
    exact_mod_cast (by omega : 0 < m)
  have hden :
      (0 : ℚ) < (m : ℚ) * ((m+1 : Nat) : ℚ) * ((m+2 : Nat) : ℚ) := by
    positivity
  have hm3_le : ((m+3 : Nat) : ℚ) ≤ (6/5) * (m : ℚ) := by
    have hmq : (361 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
    push_cast
    nlinarith
  have hnum_le : (((m+3 : Nat) : ℚ)^3) ≤ ((6/5) * (m : ℚ))^3 := by
    exact pow_le_pow_left₀ (by positivity) hm3_le 3
  have hden_lb :
      (m : ℚ)^3 ≤ (m : ℚ) * ((m+1 : Nat) : ℚ) * ((m+2 : Nat) : ℚ) := by
    calc
      (m : ℚ)^3 ≤ (m : ℚ)^3 + (m : ℚ) * (3 * (m : ℚ) + 2) := by
        exact le_add_of_nonneg_right
          (mul_nonneg hmpos.le (by nlinarith [hmpos]))
      _ = (m : ℚ) * ((m+1 : Nat) : ℚ) * ((m+2 : Nat) : ℚ) := by
        push_cast
        ring
  calc
    (((m+3 : Nat) : ℚ)^3)
        / ((m : ℚ) * ((m+1 : Nat) : ℚ) * ((m+2 : Nat) : ℚ))
      ≤ (((6/5) * (m : ℚ))^3)
          / ((m : ℚ) * ((m+1 : Nat) : ℚ) * ((m+2 : Nat) : ℚ)) := by
        exact div_le_div_of_nonneg_right hnum_le hden.le
    _ ≤ (((6/5) * (m : ℚ))^3) / ((m : ℚ)^3) := by
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden_lb
    _ = (216/125 : ℚ) := by
        field_simp [hmpos.ne']
        ring
    _ ≤ 2 := by norm_num

private theorem farTail_three_step_zeta_factor_le
    {m : Nat} (hm : 361 ≤ m) :
    zetaMax / ((m/3+2 : Nat) : ℚ) ≤ 50 / (27 * 122) := by
  have hL122 : 122 ≤ m/3 + 2 := by
    have hq120 : 120 ≤ m/3 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 3)]
      omega
    omega
  have hLq : (122 : ℚ) ≤ ((m/3+2 : Nat) : ℚ) := by exact_mod_cast hL122
  have hLpos : (0 : ℚ) < ((m/3+2 : Nat) : ℚ) := by positivity
  rw [zetaMax]
  rw [div_le_div_iff₀ hLpos (by norm_num : (0 : ℚ) < 27 * 122)]
  nlinarith

private theorem farTailThreeStepRatio_le_one
    {m : Nat} (hm : 361 ≤ m) :
    farTailThreeStepRatio m ≤ 1 := by
  have hm1 : 1 ≤ m := by omega
  rw [farTailThreeStepRatio_eq_factors (m := m) hm1]
  have hA := farTail_three_step_exp_factor_le (m := m) hm
  have hB := farTail_three_step_cubic_factor_le (m := m) hm
  have hC := farTail_three_step_zeta_factor_le (m := m) hm
  have hA_nonneg :
      0 ≤ (((m+3 : Nat) : ℚ) / (m : ℚ))^(m+2) := by positivity
  have hB_nonneg :
      0 ≤ ((((m+3 : Nat) : ℚ)^3)
        / ((m : ℚ) * ((m+1 : Nat) : ℚ) * ((m+2 : Nat) : ℚ))) := by
    positivity
  have hC_nonneg : 0 ≤ zetaMax / ((m/3+2 : Nat) : ℚ) := by
    rw [zetaMax]
    positivity
  calc
    (((m+3 : Nat) : ℚ) / (m : ℚ))^(m+2)
        * ((((m+3 : Nat) : ℚ)^3)
            / ((m : ℚ) * ((m+1 : Nat) : ℚ) * ((m+2 : Nat) : ℚ)))
        * (zetaMax / ((m/3+2 : Nat) : ℚ))
      ≤ ((68/25 : ℚ)^3 * (121/120 : ℚ)^4) * 2 * (50 / (27 * 122)) := by
        exact mul_le_mul
          (mul_le_mul hA hB hB_nonneg (by positivity))
          hC
          hC_nonneg
          (mul_nonneg (by positivity) (by norm_num))
      _ ≤ 1 := by norm_num

private theorem farTailScalarEnvelopeScaled_nonneg (m : Nat) :
    0 ≤ farTailScalarEnvelopeScaled m := by
  unfold farTailScalarEnvelopeScaled farTailScalarEnvelope
  norm_num [farTailExpUpper, farTailPoissonFactor, zetaMax]
  positivity

private theorem farTailScalarEnvelopeScaled_add_three_le
    {m : Nat} (hm : 361 ≤ m) :
    farTailScalarEnvelopeScaled (m+3) ≤ farTailScalarEnvelopeScaled m := by
  have hm1 : 1 ≤ m := by omega
  calc
    farTailScalarEnvelopeScaled (m+3)
        = farTailScalarEnvelopeScaled m * farTailThreeStepRatio m :=
          farTailScalarEnvelopeScaled_add_three_eq (m := m) hm1
    _ ≤ farTailScalarEnvelopeScaled m * 1 :=
        mul_le_mul_of_nonneg_left
          (farTailThreeStepRatio_le_one (m := m) hm)
          (farTailScalarEnvelopeScaled_nonneg m)
    _ = farTailScalarEnvelopeScaled m := by ring

theorem farTailScalarEnvelopeScaled_le_one
    {m : Nat} (hm : 361 ≤ m) :
    farTailScalarEnvelopeScaled m ≤ 1 := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      by_cases h361 : m = 361
      · simpa [h361] using farTailScalarEnvelopeScaled_361_le_one
      by_cases h362 : m = 362
      · simpa [h362] using farTailScalarEnvelopeScaled_362_le_one
      by_cases h363 : m = 363
      · simpa [h363] using farTailScalarEnvelopeScaled_363_le_one
      have hm364 : 364 ≤ m := by omega
      have hm3_ge : 361 ≤ m - 3 := by omega
      have hm3_lt : m - 3 < m := by omega
      have hstep := farTailScalarEnvelopeScaled_add_three_le (m := m - 3) hm3_ge
      have hprev := ih (m - 3) hm3_lt hm3_ge
      have hrewrite : (m - 3) + 3 = m := by omega
      calc
        farTailScalarEnvelopeScaled m
            = farTailScalarEnvelopeScaled ((m - 3) + 3) := by rw [hrewrite]
        _ ≤ farTailScalarEnvelopeScaled (m - 3) := hstep
        _ ≤ 1 := hprev

theorem farTailScalarEnvelope_le_one_over_m_sq
    {m : Nat} (hm : 361 ≤ m) :
    farTailScalarEnvelope m ≤ 1 / (m : ℚ)^2 := by
  have hmpos : (0 : ℚ) < (m : ℚ)^2 := by positivity
  have hscaled := farTailScalarEnvelopeScaled_le_one (m := m) hm
  unfold farTailScalarEnvelopeScaled at hscaled
  exact (le_div_iff₀ hmpos).mpr (by simpa [mul_comm] using hscaled)

theorem signLockFarTailScalar_le_one_over_m_sq
    {N m : Nat} (hN : 1 ≤ N)
    (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ)) (hm : 361 ≤ m) :
    signLockFarTailScalar N m ≤ 1 / (m : ℚ)^2 :=
  (signLockFarTailScalar_le_envelope
    (N := N) (m := m) hN hN40 hm).trans
      (farTailScalarEnvelope_le_one_over_m_sq (m := m) hm)

/-- The finite factorial gas appearing in the far-tail coefficient recurrence:
`k! / m^k`. -/
def farTailFactorialGas (m k : Nat) : ℚ :=
  (k.factorial : ℚ) / (m : ℚ)^k

private theorem farTailFactorialGas_nonneg (m k : Nat) :
    0 ≤ farTailFactorialGas m k := by
  unfold farTailFactorialGas
  positivity

private theorem farTailFactorialGas_succ
    {m k : Nat} (hm : 1 ≤ m) :
    farTailFactorialGas m (k+1)
      = farTailFactorialGas m k * (((k+1 : Nat) : ℚ) / (m : ℚ)) := by
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  unfold farTailFactorialGas
  rw [show ((k+1).factorial : ℚ)
      = ((k+1 : Nat) : ℚ) * (k.factorial : ℚ) by
        push_cast [Nat.factorial_succ]
        ring]
  rw [pow_succ]
  field_simp [hmpos.ne']

private theorem farTailFactorialGas_succ_le_two_thirds
    {m p k : Nat} (hm : 1 ≤ m) (hpm : 3*p ≤ 2*m) (hk : k+1 ≤ p) :
    farTailFactorialGas m (k+1)
      ≤ farTailFactorialGas m k * (2/3) := by
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  have hratio : (((k+1 : Nat) : ℚ) / (m : ℚ)) ≤ 2/3 := by
    rw [div_le_iff₀ hmpos]
    have hkq : ((k+1 : Nat) : ℚ) ≤ (p : ℚ) := by exact_mod_cast hk
    have hpmq : (3 : ℚ) * (p : ℚ) ≤ 2 * (m : ℚ) := by exact_mod_cast hpm
    nlinarith
  rw [farTailFactorialGas_succ (m := m) (k := k) hm]
  exact mul_le_mul_of_nonneg_left hratio (farTailFactorialGas_nonneg m k)

private theorem farTail_geom_chain_bound_from (F : Nat → ℚ) {q : ℚ} (hq0 : 0 ≤ q)
    {a K : Nat} (hstep : ∀ j, j + 1 < K → F (a+j+1) ≤ F (a+j) * q) :
    ∀ j, j < K → F (a+j) ≤ F a * q^j := by
  intro j hj
  induction j with
  | zero =>
      simp
  | succ j ih =>
      calc F (a + (j+1))
          = F (a+j+1) := by rw [Nat.add_assoc]
        _ ≤ F (a+j) * q := hstep j hj
        _ ≤ (F a * q^j) * q := by
            exact mul_le_mul_of_nonneg_right (ih (Nat.lt_of_succ_lt hj)) hq0
        _ = F a * q^(j+1) := by
            rw [pow_succ]
            ring

private theorem farTail_geom_chain_sum_from_le (F : Nat → ℚ) {q : ℚ} (hq0 : 0 ≤ q)
    {a K : Nat} (hstep : ∀ j, j + 1 < K → F (a+j+1) ≤ F (a+j) * q) :
    ∑ j ∈ Finset.range K, F (a+j)
      ≤ F a * ∑ j ∈ Finset.range K, q^j := by
  calc ∑ j ∈ Finset.range K, F (a+j)
      ≤ ∑ j ∈ Finset.range K, F a * q^j := by
          refine Finset.sum_le_sum fun j hj => ?_
          exact farTail_geom_chain_bound_from F hq0 hstep j (Finset.mem_range.mp hj)
    _ = F a * ∑ j ∈ Finset.range K, q^j := by
          rw [Finset.mul_sum]

private theorem farTail_sum_Icc_eq_shift_from (F : Nat → ℚ) (a b : Nat) :
    ∑ r ∈ Finset.Icc a b, F r = ∑ j ∈ Finset.range (b+1-a), F (a+j) := by
  have hIccIco : Finset.Icc a b = Finset.Ico a (b+1) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIccIco, Finset.sum_Ico_eq_sum_range]

/-- The truncated factorial gas is controlled by the first term and a
geometric ratio `≤ 2/3` throughout `p ≤ 2m/3`. -/
theorem farTailFactorialGas_sum_le
    {m p : Nat} (hm : 361 ≤ m) (hp : 2 ≤ p) (hpm : 3*p ≤ 2*m) :
    ∑ k ∈ Finset.Icc 2 p, farTailFactorialGas m k
      ≤ 6 / (m : ℚ)^2 := by
  have hm1 : 1 ≤ m := by omega
  rw [farTail_sum_Icc_eq_shift_from (fun k => farTailFactorialGas m k) 2 p]
  have hgeom :
      ∑ j ∈ Finset.range (p + 1 - 2), farTailFactorialGas m (2+j)
        ≤ farTailFactorialGas m 2
            * ∑ j ∈ Finset.range (p + 1 - 2), (2/3 : ℚ)^j := by
    refine farTail_geom_chain_sum_from_le (fun k => farTailFactorialGas m k)
      (by norm_num : (0 : ℚ) ≤ 2/3) ?_
    intro j hj
    exact farTailFactorialGas_succ_le_two_thirds
      (m := m) (p := p) (k := 2+j) hm1 hpm (by omega)
  calc
    ∑ j ∈ Finset.range (p + 1 - 2), farTailFactorialGas m (2+j)
      ≤ farTailFactorialGas m 2
          * ∑ j ∈ Finset.range (p + 1 - 2), (2/3 : ℚ)^j := hgeom
    _ ≤ farTailFactorialGas m 2 * (1 / (1 - (2/3 : ℚ))) := by
          exact mul_le_mul_of_nonneg_left
            (geom_sum_le_inv_one_sub (2/3) (by norm_num) (by norm_num) _)
            (farTailFactorialGas_nonneg m 2)
    _ = 6 / (m : ℚ)^2 := by
          unfold farTailFactorialGas
          norm_num
          ring_nf

private theorem farTail_recurrence_majorant_rewrite
    {N m p k : Nat} (hm : 1 ≤ m) (hk : 1 ≤ k) (hkp : k ≤ p) :
    (k : ℚ) * ((N : ℚ) * ((4/25) * ((6:ℚ)^k * ((k-1).factorial : ℚ)))) *
        (farTailExpUpper * (6 * (m : ℚ))^(p-k))
      =
    farTailExpUpper * (6 * (m : ℚ))^p *
      ((4 * (N : ℚ) / 25) * farTailFactorialGas m k) := by
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  have hfac : (k : ℚ) * ((k-1).factorial : ℚ) = (k.factorial : ℚ) := by
    exact_mod_cast (Nat.mul_factorial_pred (by omega : k ≠ 0))
  have hp_decomp : p = (p-k) + k := by omega
  have hpow6 : (6 : ℚ)^p = (6 : ℚ)^(p-k) * (6 : ℚ)^k := by
    calc
      (6 : ℚ)^p = (6 : ℚ)^((p-k)+k) :=
        congrArg (fun n : Nat => (6 : ℚ)^n) hp_decomp
      _ = (6 : ℚ)^(p-k) * (6 : ℚ)^k := by rw [pow_add]
  have hpowm : (m : ℚ)^p = (m : ℚ)^(p-k) * (m : ℚ)^k := by
    calc
      (m : ℚ)^p = (m : ℚ)^((p-k)+k) :=
        congrArg (fun n : Nat => (m : ℚ)^n) hp_decomp
      _ = (m : ℚ)^(p-k) * (m : ℚ)^k := by rw [pow_add]
  unfold farTailFactorialGas farTailExpUpper
  rw [mul_pow]
  conv_rhs => rw [mul_pow, hpow6, hpowm]
  rw [show (k : ℚ) * ((N : ℚ) * ((4/25) *
          ((6:ℚ)^k * ((k-1).factorial : ℚ)))) *
        (600 * ((6:ℚ)^(p-k) * (m:ℚ)^(p-k)))
      = 600 * (6:ℚ)^(p-k) * (6:ℚ)^k * (m:ℚ)^(p-k) *
          ((4 * (N:ℚ) / 25) * ((k:ℚ) * ((k-1).factorial : ℚ))) by ring]
  rw [hfac]
  field_simp [hmpos.ne']

private theorem farTailFactorialGas_weighted_sum_le
    {N m p : Nat} (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ))
    (hm : 361 ≤ m) (hp : 2 ≤ p) (hpm : 3*p ≤ 2*m) :
    (4 * (N : ℚ) / 25) *
        (∑ k ∈ Finset.Icc 2 p, farTailFactorialGas m k)
      ≤ (p : ℚ) := by
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  have hcoef_nonneg : 0 ≤ 4 * (N : ℚ) / 25 := by positivity
  have hsum := farTailFactorialGas_sum_le (m := m) (p := p) hm hp hpm
  calc
    (4 * (N : ℚ) / 25) *
        (∑ k ∈ Finset.Icc 2 p, farTailFactorialGas m k)
      ≤ (4 * (N : ℚ) / 25) * (6 / (m : ℚ)^2) :=
          mul_le_mul_of_nonneg_left hsum hcoef_nonneg
    _ ≤ (p : ℚ) := by
          have hNbound : 4 * (N : ℚ) / 25
              ≤ (32/15) * (m : ℚ) := by
            calc
              4 * (N : ℚ) / 25 ≤ 4 * ((40/3) * (m : ℚ)) / 25 := by
                exact div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hN40 (by norm_num))
                  (by norm_num)
              _ = (32/15) * (m : ℚ) := by ring
          have hp2q : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
          have hm361 : (361 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
          calc
            (4 * (N : ℚ) / 25) * (6 / (m : ℚ)^2)
              ≤ ((32/15) * (m : ℚ)) * (6 / (m : ℚ)^2) :=
                mul_le_mul_of_nonneg_right hNbound
                  (by positivity : (0 : ℚ) ≤ 6 / (m : ℚ)^2)
            _ = 64 / (5 * (m : ℚ)) := by
                field_simp [hmpos.ne']
                ring
            _ ≤ 2 := by
                rw [div_le_iff₀ (by positivity : (0 : ℚ) < 5 * (m : ℚ))]
                nlinarith
            _ ≤ (p : ℚ) := hp2q

private theorem farTail_range_if_gas_sum_eq (m p : Nat) (hp : 1 ≤ p) :
    ∑ t ∈ Finset.range p,
        (if t = 0 then 0 else farTailFactorialGas m (t+1))
      = ∑ k ∈ Finset.Icc 2 p, farTailFactorialGas m k := by
  rw [Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < p)]
  simp only [↓reduceIte, zero_add]
  rw [Finset.sum_Ico_eq_sum_range]
  rw [farTail_sum_Icc_eq_shift_from (fun k => farTailFactorialGas m k) 2 p]
  have hlen : p - 1 = p + 1 - 2 := by omega
  rw [hlen]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [if_neg (by omega : ¬ 1 + j = 0)]
  ring_nf

private theorem farTail_recurrence_abs_term_le
    {N m p t : Nat} (hN : 1 ≤ N) (hm : 1 ≤ m) (ht0 : t ≠ 0) (htp : t < p)
    (hprev :
      |Eminus (N : ℚ) (p-(t+1))|
        ≤ farTailExpUpper * (6 * (m : ℚ))^(p-(t+1))) :
    |((t+1 : Nat) : ℚ) * (-(N : ℚ) * Hcoef (t+1)) *
        Eminus (N : ℚ) (p-(t+1))|
      ≤ farTailExpUpper * (6 * (m : ℚ))^p *
          ((4 * (N : ℚ) / 25) * farTailFactorialGas m (t+1)) := by
  have hk2 : 2 ≤ t+1 := by omega
  have hk1 : 1 ≤ t+1 := by omega
  have hkp : t+1 ≤ p := by omega
  have hNpos : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  have hterm_abs :
      |((t+1 : Nat) : ℚ) * (-(N : ℚ) * Hcoef (t+1)) *
          Eminus (N : ℚ) (p-(t+1))|
        =
      ((t+1 : Nat) : ℚ) * ((N : ℚ) * c (t+1)) *
          |Eminus (N : ℚ) (p-(t+1))| := by
    rw [Hcoef_of_ge_two hk2]
    rw [abs_mul, abs_mul, abs_mul, abs_neg,
      abs_of_nonneg (by positivity : 0 ≤ (((t+1 : Nat) : ℚ))),
      abs_of_nonneg hNpos.le,
      abs_of_nonneg (c_nonneg (t+1))]
  have hcub := c_ub (t+1) hk1
  have hNc :
      (N : ℚ) * c (t+1)
        ≤ (N : ℚ) * ((4/25) * ((6:ℚ)^(t+1) * ((t+1-1).factorial : ℚ))) :=
    mul_le_mul_of_nonneg_left hcub hNpos.le
  rw [hterm_abs]
  calc
    ((t+1 : Nat) : ℚ) * ((N : ℚ) * c (t+1)) *
        |Eminus (N : ℚ) (p-(t+1))|
      = ((t+1 : Nat) : ℚ) *
          (((N : ℚ) * c (t+1)) * |Eminus (N : ℚ) (p-(t+1))|) := by
        ring
    _ ≤ ((t+1 : Nat) : ℚ) *
          (((N : ℚ) * ((4/25) * ((6:ℚ)^(t+1) * ((t+1-1).factorial : ℚ)))) *
            (farTailExpUpper * (6 * (m : ℚ))^(p-(t+1)))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hNc hprev (abs_nonneg _)
            (by positivity : 0 ≤
              (N : ℚ) * ((4/25) * ((6:ℚ)^(t+1) * ((t+1-1).factorial : ℚ)))))
          (by exact_mod_cast (Nat.zero_le (t+1)) : 0 ≤ (((t+1 : Nat) : ℚ)))
    _ =
      ((t+1 : Nat) : ℚ) *
          ((N : ℚ) * ((4/25) * ((6:ℚ)^(t+1) * ((t+1-1).factorial : ℚ)))) *
          (farTailExpUpper * (6 * (m : ℚ))^(p-(t+1))) := by
        ring
    _ = farTailExpUpper * (6 * (m : ℚ))^p *
          ((4 * (N : ℚ) / 25) * farTailFactorialGas m (t+1)) := by
        rw [show t+1-1 = t by omega]
        exact farTail_recurrence_majorant_rewrite
          (N := N) (m := m) (p := p) (k := t+1) hm hk1 hkp

/-- Far-tail coefficient bound for the nonlinear exponential coefficients.

This is the Lean recurrence version of the TeX saddle estimate
`|E^-_p(N)| ≤ exp(6.37)(6m)^p`, with the rational replacement
`exp(6.37) ≤ 600`.  It intentionally uses only the finite recurrence for
`expCoeff`, so no analytic convergence statement for `H` is involved. -/
theorem abs_Eminus_le_farTailExpUpper_mul
    {N m p : Nat} (hN : 1 ≤ N)
    (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ)) (hm : 361 ≤ m)
    (hpm : 3*p ≤ 2*m) :
    |Eminus (N : ℚ) p| ≤ farTailExpUpper * (6 * (m : ℚ))^p := by
  induction p using Nat.strong_induction_on with
  | h p ih =>
      match p with
      | 0 =>
          norm_num [Eminus, farTailExpUpper]
      | 1 =>
          have hE1 : Eminus (N : ℚ) 1 = 0 := by
            unfold Eminus
            have h := expCoeff_succ_mul (fun r => -(N : ℚ) * Hcoef r) 0
            norm_num [Hcoef] at h
            simpa [Hcoef] using h
          rw [hE1]
          norm_num [farTailExpUpper]
      | n+2 =>
          let P : Nat := n+2
          let common : ℚ := farTailExpUpper * (6 * (m : ℚ))^P
          have hm1 : 1 ≤ m := by omega
          have hP2 : 2 ≤ P := by dsimp [P]; omega
          have hPpm : 3*P ≤ 2*m := by simpa [P] using hpm
          have hPpos : (0 : ℚ) < (P : ℚ) := by positivity
          let L : Nat → ℚ := fun r => -(N : ℚ) * Hcoef r
          have hrec :=
            expCoeff_succ_mul L (n+1)
          have hrecE :
              (P : ℚ) * expCoeff L P =
                ∑ t ∈ Finset.range P,
                  ((t+1 : Nat) : ℚ) * L (t+1) *
                    Eminus (N : ℚ) (P-(t+1)) := by
            dsimp [P, L]
            rw [hrec]
            refine Finset.sum_congr rfl fun t ht => ?_
            rw [show n + 1 - t = n + 2 - (t + 1) by omega]
            rfl
          have hsum_abs :
              ∑ t ∈ Finset.range P,
                  |((t+1 : Nat) : ℚ) * L (t+1) *
                    Eminus (N : ℚ) (P-(t+1))|
                ≤ common * ((4 * (N : ℚ) / 25) *
                    ∑ k ∈ Finset.Icc 2 P, farTailFactorialGas m k) := by
            calc
              ∑ t ∈ Finset.range P,
                  |((t+1 : Nat) : ℚ) * L (t+1) *
                    Eminus (N : ℚ) (P-(t+1))|
                ≤ ∑ t ∈ Finset.range P,
                    common * ((4 * (N : ℚ) / 25) *
                      (if t = 0 then 0 else farTailFactorialGas m (t+1))) := by
                  refine Finset.sum_le_sum fun t ht => ?_
                  have htp : t < P := Finset.mem_range.mp ht
                  by_cases ht0 : t = 0
                  · subst ht0
                    dsimp [L]
                    simp [Hcoef, common]
                  · have hprev :
                        |Eminus (N : ℚ) (P-(t+1))|
                          ≤ farTailExpUpper * (6 * (m : ℚ))^(P-(t+1)) := by
                        exact ih (P-(t+1)) (by omega)
                          (by omega : 3 * (P - (t + 1)) ≤ 2 * m)
                    have hterm := farTail_recurrence_abs_term_le
                      (N := N) (m := m) (p := P) (t := t)
                      hN hm1 ht0 htp hprev
                    dsimp [L] at hterm ⊢
                    rw [if_neg ht0]
                    exact hterm
              _ = common * ∑ t ∈ Finset.range P,
                    ((4 * (N : ℚ) / 25) *
                      (if t = 0 then 0 else farTailFactorialGas m (t+1))) := by
                    rw [Finset.mul_sum]
                _ = common * ((4 * (N : ℚ) / 25) *
                      ∑ t ∈ Finset.range P,
                        (if t = 0 then 0 else farTailFactorialGas m (t+1))) := by
                    rw [show (∑ t ∈ Finset.range P,
                        ((4 * (N : ℚ) / 25) *
                          (if t = 0 then 0 else farTailFactorialGas m (t+1))))
                        = (4 * (N : ℚ) / 25) *
                            ∑ t ∈ Finset.range P,
                              (if t = 0 then 0 else farTailFactorialGas m (t+1)) by
                      rw [Finset.mul_sum]]
              _ = common * ((4 * (N : ℚ) / 25) *
                    ∑ k ∈ Finset.Icc 2 P, farTailFactorialGas m k) := by
                    rw [farTail_range_if_gas_sum_eq m P (by omega : 1 ≤ P)]
          have hweighted :
              (4 * (N : ℚ) / 25) *
                  (∑ k ∈ Finset.Icc 2 P, farTailFactorialGas m k)
                ≤ (P : ℚ) :=
            farTailFactorialGas_weighted_sum_le
              (N := N) (m := m) (p := P) hN40 hm hP2 hPpm
          have hcommon_nonneg : 0 ≤ common := by
            dsimp [common, farTailExpUpper]
            positivity
          have hmul :
              (P : ℚ) * |expCoeff L P| ≤ (P : ℚ) * common := by
            calc
              (P : ℚ) * |expCoeff L P|
                = |(P : ℚ) * expCoeff L P| := by
                    rw [abs_mul, abs_of_pos hPpos]
              _ = |∑ t ∈ Finset.range P,
                    ((t+1 : Nat) : ℚ) * L (t+1) *
                      Eminus (N : ℚ) (P-(t+1))| := by
                    rw [hrecE]
              _ ≤ ∑ t ∈ Finset.range P,
                    |((t+1 : Nat) : ℚ) * L (t+1) *
                      Eminus (N : ℚ) (P-(t+1))| :=
                    Finset.abs_sum_le_sum_abs _ _
              _ ≤ common * ((4 * (N : ℚ) / 25) *
                    ∑ k ∈ Finset.Icc 2 P, farTailFactorialGas m k) := hsum_abs
              _ ≤ common * (P : ℚ) :=
                    mul_le_mul_of_nonneg_left hweighted hcommon_nonneg
              _ = (P : ℚ) * common := by ring
          have hmain : |expCoeff L P| ≤ common :=
            le_of_mul_le_mul_left hmul hPpos
          simpa [Eminus, L, P, common] using hmain

private theorem exp_tail_term_from_le (y : ℚ) (hy : 0 ≤ y) (L j : Nat)
    (hL : 1 ≤ L) :
    y^(L+j) / ((L+j).factorial : ℚ)
      ≤ (y^L / (L.factorial : ℚ)) * (y/(L:ℚ))^j := by
  have hNat : L.factorial * L^j ≤ (L+j).factorial :=
    le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) j))
      Nat.factorial_mul_pow_le_factorial
  have hden : (0:ℚ) < (L.factorial : ℚ) * (L:ℚ)^j := by
    have h1 : (0:ℚ) < (L.factorial : ℚ) := by
      exact_mod_cast L.factorial_pos
    have h2 : (0:ℚ) < (L:ℚ)^j := by
      have : (0:ℚ) < (L:ℚ) := by exact_mod_cast (by omega : 0 < L)
      positivity
    positivity
  rw [pow_add, div_pow, div_mul_div_comm]
  apply div_le_div_of_nonneg_left (by positivity) hden
  exact_mod_cast hNat

private theorem poisson_tail_Ico_le_first_mul_inv
    (y : ℚ) (hy : 0 ≤ y) {L M : Nat} (hL : 1 ≤ L) (hyL : y < (L : ℚ)) :
    ∑ s ∈ Finset.Ico L M, y^s / (s.factorial : ℚ)
      ≤ (y^L / (L.factorial : ℚ)) * (1 / (1 - y/(L:ℚ))) := by
  have hLpos : (0:ℚ) < (L:ℚ) := by exact_mod_cast (by omega : 0 < L)
  have hq0 : 0 ≤ y/(L:ℚ) := div_nonneg hy hLpos.le
  have hq1 : y/(L:ℚ) < 1 := by
    rw [div_lt_one hLpos]
    exact hyL
  have hfirst_nonneg : 0 ≤ y^L / (L.factorial : ℚ) := by positivity
  rw [Finset.sum_Ico_eq_sum_range]
  calc
    ∑ j ∈ Finset.range (M - L), y^(L+j) / ((L+j).factorial : ℚ)
        ≤ ∑ j ∈ Finset.range (M - L),
            (y^L / (L.factorial : ℚ)) * (y/(L:ℚ))^j := by
          exact Finset.sum_le_sum fun j _ => exp_tail_term_from_le y hy L j hL
    _ = (y^L / (L.factorial : ℚ))
          * ∑ j ∈ Finset.range (M - L), (y/(L:ℚ))^j := by
          rw [Finset.mul_sum]
    _ ≤ (y^L / (L.factorial : ℚ)) * (1 / (1 - y/(L:ℚ))) := by
          exact mul_le_mul_of_nonneg_left
            (geom_sum_le_inv_one_sub _ hq0 hq1 _) hfirst_nonneg

/-- The finite Poisson tail beginning at `m/3+1` is much smaller than the
paper's `2.04` first-omitted-term allowance. -/
theorem zetaQ_tail_Ico_le_first
    {N m : Nat} (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ)) (hm : 361 ≤ m) :
    ∑ s ∈ Finset.Ico (m/3 + 1) (m+1),
        (zetaQ N m)^s / (s.factorial : ℚ)
      ≤ farTailPoissonFactor
          * ((zetaQ N m)^(m/3 + 1)
              / (((m/3 + 1).factorial : Nat) : ℚ)) := by
  let L : Nat := m/3 + 1
  have hL121 : 121 ≤ L := by
    dsimp [L]
    omega
  have hL : 1 ≤ L := by omega
  have hLpos : (0:ℚ) < (L:ℚ) := by exact_mod_cast (by omega : 0 < L)
  have hLQ : (121 : ℚ) ≤ (L : ℚ) := by exact_mod_cast hL121
  have hy0 : 0 ≤ zetaQ N m := zetaQ_nonneg N m
  have hymax : zetaQ N m ≤ zetaMax :=
    zetaQ_le_zetaMax (by omega : 1 ≤ m) hN40
  have hy50 : zetaQ N m ≤ 50/27 := by simpa [zetaMax] using hymax
  have hyL : zetaQ N m < (L : ℚ) := by
    calc
      zetaQ N m ≤ 50/27 := hy50
      _ < 121 := by norm_num
      _ ≤ (L : ℚ) := hLQ
  have htail := poisson_tail_Ico_le_first_mul_inv
    (zetaQ N m) hy0 (L := L) (M := m+1) hL hyL
  have hratio_half : zetaQ N m / (L : ℚ) ≤ 1/2 := by
    have hhalfL : (50/27 : ℚ) ≤ (L : ℚ) / 2 := by
      calc
        (50/27 : ℚ) ≤ 121 / 2 := by norm_num
        _ ≤ (L : ℚ) / 2 := by linarith
    have hy_halfL : zetaQ N m ≤ (L : ℚ) / 2 := hy50.trans hhalfL
    rw [div_le_iff₀ hLpos]
    linarith
  have hlow : (1/2 : ℚ) ≤ 1 - zetaQ N m / (L : ℚ) := by
    linarith
  have hinv_le : 1 / (1 - zetaQ N m / (L : ℚ)) ≤ farTailPoissonFactor := by
    calc
      1 / (1 - zetaQ N m / (L : ℚ)) ≤ 1 / (1/2 : ℚ) :=
        one_div_le_one_div_of_le (by norm_num) hlow
      _ ≤ farTailPoissonFactor := by
        norm_num [farTailPoissonFactor]
  have hfirst_nonneg :
      0 ≤ (zetaQ N m)^L / (L.factorial : ℚ) := by positivity
  calc
    ∑ s ∈ Finset.Ico (m/3 + 1) (m+1),
        (zetaQ N m)^s / (s.factorial : ℚ)
      = ∑ s ∈ Finset.Ico L (m+1),
          (zetaQ N m)^s / (s.factorial : ℚ) := by rfl
    _ ≤ (zetaQ N m)^L / (L.factorial : ℚ)
          * (1 / (1 - zetaQ N m / (L : ℚ))) := htail
    _ ≤ (zetaQ N m)^L / (L.factorial : ℚ) * farTailPoissonFactor :=
          mul_le_mul_of_nonneg_left hinv_le hfirst_nonneg
    _ = farTailPoissonFactor
          * ((zetaQ N m)^(m/3 + 1)
              / (((m/3 + 1).factorial : Nat) : ℚ)) := by
          dsimp [L]
          ring

private theorem farTail_summand_saddle_rewrite
    {N m s : Nat} (hN : 1 ≤ N) (hm : 1 ≤ m) (hs : s ≤ m) :
    (((N : ℚ) * c 1)^s / (s.factorial : ℚ)) *
      (farTailExpUpper * (6 * (m : ℚ))^(m-s)) /
        ((N : ℚ) * ((5/36) * ((6:ℚ)^m * ((m-1).factorial : ℚ))))
      =
    ((36 * farTailExpUpper) / (5 * (N : ℚ))) *
      ((m : ℚ)^m / (((m-1).factorial : Nat) : ℚ)) *
      ((zetaQ N m)^s / (s.factorial : ℚ)) := by
  have hNq : ((N : ℚ) ≠ 0) := by exact_mod_cast (by omega : N ≠ 0)
  have hmq : ((m : ℚ) ≠ 0) := by exact_mod_cast (by omega : m ≠ 0)
  have hsf : ((s.factorial : ℚ) ≠ 0) := by positivity
  have hmf : ((((m-1).factorial : Nat) : ℚ) ≠ 0) := by positivity
  have hm_decomp : m = (m-s) + s := by omega
  have hmpow0 : (m : ℚ)^m = (m : ℚ)^((m-s)+s) :=
    congrArg (fun n : Nat => (m : ℚ)^n) hm_decomp
  have hmpow : (m : ℚ)^m = (m : ℚ)^(m-s) * (m : ℚ)^s := by
    rw [hmpow0, pow_add]
  have h6pow0 : (6 : ℚ)^m = (6 : ℚ)^((m-s)+s) :=
    congrArg (fun n : Nat => (6 : ℚ)^n) hm_decomp
  have h6pow : (6 : ℚ)^m = (6 : ℚ)^(m-s) * (6 : ℚ)^s := by
    rw [h6pow0, pow_add]
  have hm_cancel : (m : ℚ)^s * ((m : ℚ)⁻¹)^s = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hmq, one_pow]
  have hzpow : ((N : ℚ) * 5 / ((m : ℚ) * 36))^s
      = (N : ℚ)^s * (5/36 : ℚ)^s * ((m : ℚ)⁻¹)^s := by
    rw [show (N : ℚ) * 5 / ((m : ℚ) * 36)
        = (N : ℚ) * (5/36) * (m : ℚ)⁻¹ by
      field_simp [hmq]]
    rw [mul_pow, mul_pow]
  have hleftpow :
      (((N : ℚ) * 5 / 6)^s) = (N : ℚ)^s * (5/6 : ℚ)^s := by
    rw [show (N : ℚ) * 5 / 6 = (N : ℚ) * (5/6) by ring, mul_pow]
  have hfive : ((5/6 : ℚ)^s) = (5/36 : ℚ)^s * (6:ℚ)^s := by
    rw [← mul_pow]
    norm_num
  rw [c_one]
  unfold zetaQ farTailExpUpper
  rw [hmpow, h6pow]
  field_simp [hNq, hmq, hsf, hmf]
  rw [mul_pow (6:ℚ) (m:ℚ) (m-s)]
  rw [hleftpow, hzpow, hfive]
  rw [show (6:ℚ) ^ (m - s) * (6:ℚ) ^ s * (m:ℚ) ^ (m - s)
      * (m:ℚ)^s * ((N:ℚ)^s * (5/36:ℚ)^s * ((m:ℚ)⁻¹)^s)
        =
      (N:ℚ)^s * (5/36:ℚ)^s * (6:ℚ)^s * (6:ℚ)^(m-s)
        * ((m:ℚ)^s * ((m:ℚ)⁻¹)^s) * (m:ℚ)^(m-s) by ring]
  rw [hm_cancel]
  ring

/-- Algebraic reduction of the omitted actual tail to the displayed
saddle/Stirling scalar, conditional on the coefficient bound for `E^-_p` in
the range `p ≤ 2m/3`.  The unconditional wrapper
`signLockFarTail_le_saddleScalar` supplies this coefficient input from the
finite recurrence proof above; this conditional theorem isolates the Poisson
tail and normalization algebra. -/
theorem signLockFarTail_le_saddleScalar_of_Eminus_bound
    {N m : Nat} (hN : 1 ≤ N)
    (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ)) (hm : 361 ≤ m)
    (hE : ∀ p, 3*p ≤ 2*m →
      |Eminus (N : ℚ) p| ≤ farTailExpUpper * (6 * (m : ℚ))^p) :
    signLockFarTail N m ≤ signLockFarTailScalar N m := by
  have hNpos : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  have hcm_pos : 0 < c m := c_pos m (by omega : 1 ≤ m)
  have hden_pos : 0 < (N : ℚ) * c m := mul_pos hNpos hcm_pos
  have hpoint :
      signLockFarTail N m
        ≤ ∑ s ∈ Finset.Ico (m/3 + 1) (m+1),
            ((36 * farTailExpUpper) / (5 * (N : ℚ))) *
              ((m : ℚ)^m / (((m-1).factorial : Nat) : ℚ)) *
              ((zetaQ N m)^s / (s.factorial : ℚ)) := by
    unfold signLockFarTail
    refine Finset.sum_le_sum fun s hs => ?_
    obtain ⟨hslo, hshi⟩ := Finset.mem_Ico.mp hs
    have hsle : s ≤ m := by omega
    have hpcond : 3*(m-s) ≤ 2*m := by omega
    have hE_s := hE (m-s) hpcond
    have hweight_nonneg :
        0 ≤ (((N : ℚ) * c 1)^s / (s.factorial : ℚ)) := by
      rw [c_one]
      positivity
    have hbounded_num_nonneg :
        0 ≤ (((N : ℚ) * c 1)^s / (s.factorial : ℚ))
            * (farTailExpUpper * (6 * (m : ℚ))^(m-s)) := by
      exact mul_nonneg hweight_nonneg (by unfold farTailExpUpper; positivity)
    have hden_lb_pos :
        0 < (N : ℚ) * ((5/36) * ((6:ℚ)^m * ((m-1).factorial : ℚ))) := by
      positivity
    have hden_lb_le :
        (N : ℚ) * ((5/36) * ((6:ℚ)^m * ((m-1).factorial : ℚ)))
          ≤ (N : ℚ) * c m := by
      exact mul_le_mul_of_nonneg_left (c_lb m (by omega : 1 ≤ m)) hNpos.le
    calc
      (((N : ℚ) * c 1)^s / (s.factorial : ℚ))
          * |Eminus (N : ℚ) (m-s)| / ((N : ℚ) * c m)
        ≤ (((N : ℚ) * c 1)^s / (s.factorial : ℚ))
            * (farTailExpUpper * (6 * (m : ℚ))^(m-s)) / ((N : ℚ) * c m) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hE_s hweight_nonneg) hden_pos.le
      _ ≤ (((N : ℚ) * c 1)^s / (s.factorial : ℚ))
            * (farTailExpUpper * (6 * (m : ℚ))^(m-s))
              / ((N : ℚ) * ((5/36) * ((6:ℚ)^m * ((m-1).factorial : ℚ)))) := by
          exact div_le_div_of_nonneg_left hbounded_num_nonneg
            hden_lb_pos hden_lb_le
      _ =
          ((36 * farTailExpUpper) / (5 * (N : ℚ))) *
            ((m : ℚ)^m / (((m-1).factorial : Nat) : ℚ)) *
            ((zetaQ N m)^s / (s.factorial : ℚ)) :=
          farTail_summand_saddle_rewrite hN (by omega : 1 ≤ m) hsle
  let K : ℚ :=
    ((36 * farTailExpUpper) / (5 * (N : ℚ))) *
      ((m : ℚ)^m / (((m-1).factorial : Nat) : ℚ))
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    have hcoef : 0 ≤ (36 * farTailExpUpper) / (5 * (N : ℚ)) := by
      exact div_nonneg (by norm_num [farTailExpUpper]) (by positivity)
    have hpowfac :
        0 ≤ (m : ℚ)^m / (((m-1).factorial : Nat) : ℚ) := by
      positivity
    exact mul_nonneg hcoef hpowfac
  have hpois := zetaQ_tail_Ico_le_first (N := N) (m := m) hN40 hm
  calc
    signLockFarTail N m
      ≤ ∑ s ∈ Finset.Ico (m/3 + 1) (m+1),
          K * ((zetaQ N m)^s / (s.factorial : ℚ)) := by
        simpa [K] using hpoint
    _ = K * ∑ s ∈ Finset.Ico (m/3 + 1) (m+1),
          (zetaQ N m)^s / (s.factorial : ℚ) := by
        rw [Finset.mul_sum]
      _ ≤ K * (farTailPoissonFactor
            * ((zetaQ N m)^(m/3 + 1)
                / (((m/3 + 1).factorial : Nat) : ℚ))) :=
          by
            exact mul_le_mul_of_nonneg_left hpois hK_nonneg
      _ = signLockFarTailScalar N m := by
          unfold signLockFarTailScalar
          dsimp [K]
          ring

/-- Unconditional far-tail reduction to the displayed saddle/Stirling scalar.

This is the formal replacement for the TeX sentence invoking the truncated
saddle inequality for `E^-_p`: rather than evaluating an analytic truncation,
Lean uses `abs_Eminus_le_farTailExpUpper_mul`, proved from the finite
coefficient recurrence and the rational factorial-gas estimate. -/
theorem signLockFarTail_le_saddleScalar
    {N m : Nat} (hN : 1 ≤ N)
    (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ)) (hm : 361 ≤ m) :
    signLockFarTail N m ≤ signLockFarTailScalar N m :=
  signLockFarTail_le_saddleScalar_of_Eminus_bound
    (N := N) (m := m) hN hN40 hm
    (fun p hp =>
      abs_Eminus_le_farTailExpUpper_mul
        (N := N) (m := m) (p := p) hN hN40 hm hp)

theorem signLockFarTail_le_one_over_m_sq_of_saddleScalar
    {N m : Nat} (hN : 1 ≤ N)
    (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ)) (hm : 361 ≤ m)
    (hscalar : signLockFarTailScalar N m ≤ 1 / (m : ℚ)^2) :
    signLockFarTail N m ≤ 1 / (m : ℚ)^2 :=
  (signLockFarTail_le_saddleScalar
    (N := N) (m := m) hN hN40 hm).trans hscalar

theorem signLockFarTail_le_one_over_m_sq
    {N m : Nat} (hN : 1 ≤ N)
    (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ)) (hm : 361 ≤ m) :
    signLockFarTail N m ≤ 1 / (m : ℚ)^2 :=
  signLockFarTail_le_one_over_m_sq_of_saddleScalar
    (N := N) (m := m) hN hN40 hm
    (signLockFarTailScalar_le_one_over_m_sq
      (N := N) (m := m) hN hN40 hm)

/-- Near-range `w_s` audit plus the separate far-tail allowance gives the
paper's `2215/m²` error budget. -/
theorem signLock_error_budget_zetaMax_of_farTail
    {N m : Nat} (hN : 1 ≤ N)
    (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ)) (hm : 361 ≤ m)
    (hfar : signLockFarTail N m ≤ 1 / (m : ℚ)^2) :
    (∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) * |signLockErrorW N m s|)
      + signLockFarTail N m
      ≤ 2215 / (m : ℚ)^2 := by
  have hnear := signLock_near_error_budget_zetaMax
    (N := N) (m := m) hN hN40 hm
  calc
    (∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) * |signLockErrorW N m s|)
        + signLockFarTail N m
        ≤ 2214 / (m : ℚ)^2 + 1 / (m : ℚ)^2 := by
          exact add_le_add hnear hfar
      _ = 2215 / (m : ℚ)^2 := by ring_nf

/-- Near-range audit plus the proved far-tail reduction, leaving only the
explicit saddle/Stirling scalar certificate. -/
theorem signLock_error_budget_zetaMax_of_saddleScalar
    {N m : Nat} (hN : 1 ≤ N)
    (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ)) (hm : 361 ≤ m)
    (hscalar : signLockFarTailScalar N m ≤ 1 / (m : ℚ)^2) :
    (∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) * |signLockErrorW N m s|)
      + signLockFarTail N m
      ≤ 2215 / (m : ℚ)^2 :=
  signLock_error_budget_zetaMax_of_farTail
    (N := N) (m := m) hN hN40 hm
    (signLockFarTail_le_one_over_m_sq_of_saddleScalar
      (N := N) (m := m) hN hN40 hm hscalar)

theorem signLock_error_budget_zetaMax
    {N m : Nat} (hN : 1 ≤ N)
    (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ)) (hm : 361 ≤ m) :
    (∑ s ∈ Finset.range (m/3 + 1),
        (zetaMax^s / (s.factorial : ℚ)) * |signLockErrorW N m s|)
      + signLockFarTail N m
      ≤ 2215 / (m : ℚ)^2 :=
  signLock_error_budget_zetaMax_of_farTail
    (N := N) (m := m) hN hN40 hm
    (signLockFarTail_le_one_over_m_sq
      (N := N) (m := m) hN hN40 hm)

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
