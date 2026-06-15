/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# The rational Δ-envelope scaffold (paper Lemma 4.1)

This file starts the formal Layer C envelope.  The paper's displayed
`Δ(p,N)` uses the analytic upper bound `c_j ≤ (1/6)·6^j(j-1)!`.  The Lean
development has already rationalized that input to
`c_j ≤ (4/25)·6^j(j-1)!`, so the coefficient is replaced here by the
equivalent rationalized form `(36/5)·(4/25)^r·4^(r-1)`.

The main result in this file is not yet the final numerical estimate
`Δ ≤ 13.2/m`; it is the bridge from the already-proved residual bound for
`Eminus` to this explicit finite Δ-sum.  The remaining numerical work can now
target `DeltaRat` directly.
-/

import Prop51.HPow

namespace Prop51

/-! ## The rationalized Δ sum -/

/-- The `r`th rationalized Δ block:

`(36/5) * (4/25)^r * 4^(r-1) * N^(r-1) / r! *
(p-2r+1)!/(p-1)!`.

It is consumed under the side condition `2*r ≤ p`; outside that range the
composition block vanishes, so no value is needed. -/
def DeltaRatTerm (p : Nat) (N : ℚ) (r : Nat) : ℚ :=
  (36/5) * (4/25)^r * 4^(r-1) * N^(r-1)
    * ((p - 2*r + 1).factorial : ℚ)
    / ((r.factorial : ℚ) * ((p-1).factorial : ℚ))

/-- The rationalized Δ envelope for `Eminus`, summed over the only possible
block counts. -/
def DeltaRat (p : Nat) (N : ℚ) : ℚ :=
  ∑ r ∈ Finset.Icc 2 (p/2), DeltaRatTerm p N r

/-- The residual block appearing on the right side of `Eminus_residual_le`. -/
def EminusResidualBlock (p : Nat) (N : ℚ) (r : Nat) : ℚ :=
  (N*(4/25))^r * 6^p * Gcomp r p / (r.factorial : ℚ)

/-- Exact ratio multiplying the `r`th Δ block to get the `(r+1)`st block. -/
def DeltaRatStepRatio (p : Nat) (N : ℚ) (r : Nat) : ℚ :=
  ((16/25) * N)
    / (((r+1 : Nat) : ℚ)
      * ((p - 2*r : Nat) : ℚ)
      * ((p - 2*r + 1 : Nat) : ℚ))

/-- Geometric-ratio upper bound used for the near range `r ≥ 2`, replacing
`r+1` by `3` in the denominator. -/
def DeltaRatStepRatioBound (p : Nat) (N : ℚ) (r : Nat) : ℚ :=
  ((16/25) * N)
    / (3 * ((p - 2*r : Nat) : ℚ) * ((p - 2*r + 1 : Nat) : ℚ))

theorem DeltaRatTerm_nonneg (p r : Nat) {N : ℚ} (hN : 0 ≤ N) :
    0 ≤ DeltaRatTerm p N r := by
  unfold DeltaRatTerm
  positivity

theorem DeltaRat_nonneg (p : Nat) {N : ℚ} (hN : 0 ≤ N) :
    0 ≤ DeltaRat p N := by
  unfold DeltaRat
  exact Finset.sum_nonneg fun r _ => DeltaRatTerm_nonneg p r hN

theorem EminusResidualBlock_nonneg (p r : Nat) {N : ℚ} (hN : 0 ≤ N) :
    0 ≤ EminusResidualBlock p N r := by
  unfold EminusResidualBlock
  apply div_nonneg
  · exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) (Gcomp_nonneg r p)
  · positivity

/-! ## Exact Δ-block algebra -/

/-- The leading two-block term of the rationalized Δ envelope. -/
theorem DeltaRatTerm_two (p : Nat) (N : ℚ) (hp : 4 ≤ p) :
    DeltaRatTerm p N 2
      = (1152/3125) * N / (((p-1 : Nat) : ℚ) * ((p-2 : Nat) : ℚ)) := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 4 := ⟨p-4, by omega⟩
  simp only [DeltaRatTerm]
  norm_num [Nat.factorial_succ]
  have hk2 : (2 + (k:ℚ)) ≠ 0 := by positivity
  ring_nf
  field_simp [hk2]
  ring

/-- Exact ratio of consecutive rationalized Δ blocks. -/
theorem DeltaRatTerm_succ (p : Nat) (N : ℚ) (r : Nat)
    (hr : 1 ≤ r) (hrp : 2*(r+1) ≤ p) :
    DeltaRatTerm p N (r+1)
      =
    DeltaRatTerm p N r
      * DeltaRatStepRatio p N r := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r-1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, p = 2*((s+1)+1) + k := ⟨p - 2*((s+1)+1), by omega⟩
  simp only [DeltaRatTerm, DeltaRatStepRatio]
  rw [show 2 * ((s+1)+1) + k - 2 * ((s+1)+1) + 1 = k + 1 by omega,
      show 2 * ((s+1)+1) + k - 2 * (s+1) + 1 = k + 3 by omega,
      show 2 * ((s+1)+1) + k - 2 * (s+1) = k + 2 by omega]
  norm_num [Nat.factorial_succ]
  field_simp
  ring_nf

theorem DeltaRatStepRatio_le_bound (p : Nat) {N : ℚ} (r : Nat)
    (hN : 0 ≤ N) (hr : 2 ≤ r) (hrp : 2*(r+1) ≤ p) :
    DeltaRatStepRatio p N r ≤ DeltaRatStepRatioBound p N r := by
  unfold DeltaRatStepRatio DeltaRatStepRatioBound
  have hnum : 0 ≤ (16/25) * N := by positivity
  have hApos : (0:ℚ) < ((p - 2*r : Nat) : ℚ) := by
    exact_mod_cast (by omega : 0 < p - 2*r)
  have hBpos : (0:ℚ) < ((p - 2*r + 1 : Nat) : ℚ) := by positivity
  have hdenpos :
      (0:ℚ) < 3 * ((p - 2*r : Nat) : ℚ) * ((p - 2*r + 1 : Nat) : ℚ) := by
    positivity
  have hrq : (3:ℚ) ≤ ((r+1 : Nat) : ℚ) := by
    exact_mod_cast (by omega : 3 ≤ r+1)
  have hden_le :
      3 * ((p - 2*r : Nat) : ℚ) * ((p - 2*r + 1 : Nat) : ℚ)
        ≤ ((r+1 : Nat) : ℚ) * ((p - 2*r : Nat) : ℚ)
          * ((p - 2*r + 1 : Nat) : ℚ) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hrq hApos.le) hBpos.le
  exact div_le_div_of_nonneg_left hnum hdenpos hden_le

theorem DeltaRatTerm_succ_le (p : Nat) {N : ℚ} (r : Nat)
    (hN : 0 ≤ N) (hr : 2 ≤ r) (hrp : 2*(r+1) ≤ p) :
    DeltaRatTerm p N (r+1)
      ≤ DeltaRatTerm p N r * DeltaRatStepRatioBound p N r := by
  rw [DeltaRatTerm_succ p N r (by omega : 1 ≤ r) hrp]
  exact mul_le_mul_of_nonneg_left
    (DeltaRatStepRatio_le_bound p r hN hr hrp)
    (DeltaRatTerm_nonneg p r hN)

/-- If `r > p/2`, the corresponding residual block is zero: `p` cannot be
written as a sum of `r` parts all at least two. -/
theorem EminusResidualBlock_eq_zero_of_half_lt {p r : Nat} (hr : 1 ≤ r)
    (hpr : p/2 < r) : EminusResidualBlock p N r = 0 := by
  have hp_lt : p < 2*r := by
    have hnot : ¬ r ≤ p/2 := Nat.not_le.mpr hpr
    rw [Nat.le_div_two_iff_mul_two_le] at hnot
    omega
  unfold EminusResidualBlock
  rw [Gcomp_eq_zero r p hr hp_lt]
  simp

/-- One residual block is dominated by the corresponding rationalized Δ
block after multiplying back by `N c_p`. -/
theorem EminusResidualBlock_le_Nc_mul_DeltaRatTerm
    {p r : Nat} {N : ℚ} (hN : 0 ≤ N) (hp : 2 ≤ p) (hr : 1 ≤ r)
    (hrp : 2*r ≤ p) :
    EminusResidualBlock p N r ≤ N * c p * DeltaRatTerm p N r := by
  have hG := Gcomp_le r hr p hrp
  have hfact_pos : (0:ℚ) < (r.factorial : ℚ) := by
    exact_mod_cast r.factorial_pos
  have hleft :
      EminusResidualBlock p N r
        ≤ (N*(4/25))^r * 6^p
            * (4^(r-1) * ((p - 2*r + 1).factorial : ℚ))
            / (r.factorial : ℚ) := by
    unfold EminusResidualBlock
    apply div_le_div_of_nonneg_right ?_ hfact_pos.le
    exact mul_le_mul_of_nonneg_left hG (by positivity)
  have hc := c_lb p (by omega : 1 ≤ p)
  have hc' : (5/36) * (6:ℚ)^p * ((p-1).factorial : ℚ) ≤ c p := by
    simpa [mul_assoc] using hc
  have hterm_nonneg : 0 ≤ DeltaRatTerm p N r :=
    DeltaRatTerm_nonneg p r hN
  have hNc :
      N * ((5/36) * (6:ℚ)^p * ((p-1).factorial : ℚ)) * DeltaRatTerm p N r
        ≤ N * c p * DeltaRatTerm p N r := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hc' hN) hterm_nonneg
  have halg :
      (N*(4/25))^r * 6^p
            * (4^(r-1) * ((p - 2*r + 1).factorial : ℚ))
            / (r.factorial : ℚ)
        =
      N * ((5/36) * (6:ℚ)^p * ((p-1).factorial : ℚ))
        * DeltaRatTerm p N r := by
    have hrf : ((r.factorial : ℕ) : ℚ) ≠ 0 := by positivity
    have hpf : (((p-1).factorial : ℕ) : ℚ) ≠ 0 := by positivity
    have hpowN : N^r = N * N^(r-1) := by
      cases r with
      | zero => omega
      | succ k => simp [pow_succ, mul_comm]
    unfold DeltaRatTerm
    rw [mul_pow, hpowN]
    field_simp [hrf, hpf]
  exact hleft.trans (by rw [halg]; exact hNc)

/-- The full residual majorant from `Eminus_residual_le` is bounded by
`N c_p Δ(p,N)`. -/
theorem Eminus_residual_sum_le_Nc_mul_DeltaRat
    {p : Nat} {N : ℚ} (hN : 0 ≤ N) (hp : 2 ≤ p) :
    (∑ r ∈ Finset.Icc 2 p, EminusResidualBlock p N r)
      ≤ N * c p * DeltaRat p N := by
  have htrunc :
      (∑ r ∈ Finset.Icc 2 p, EminusResidualBlock p N r)
        = ∑ r ∈ Finset.Icc 2 (p/2), EminusResidualBlock p N r := by
    symm
    apply Finset.sum_subset
    · intro r hr
      obtain ⟨hr2, hrhalf⟩ := Finset.mem_Icc.mp hr
      exact Finset.mem_Icc.mpr ⟨hr2, by omega⟩
    · intro r hr hnot
      obtain ⟨hr2, _hrp⟩ := Finset.mem_Icc.mp hr
      have hhalf : p/2 < r := by
        by_contra hle
        exact hnot (Finset.mem_Icc.mpr ⟨hr2, by omega⟩)
      exact EminusResidualBlock_eq_zero_of_half_lt (by omega : 1 ≤ r) hhalf
  rw [htrunc, DeltaRat, Finset.mul_sum]
  refine Finset.sum_le_sum fun r hr => ?_
  obtain ⟨hr2, hrhalf⟩ := Finset.mem_Icc.mp hr
  have hrp : 2*r ≤ p := by
    have hInt : (r : ℤ) * 2 ≤ (p : ℤ) :=
      Nat.le_div_two_iff_mul_two_le.mp hrhalf
    omega
  exact EminusResidualBlock_le_Nc_mul_DeltaRatTerm hN hp (by omega : 1 ≤ r) hrp

/-- Normalized `Eminus` residual bound in terms of the rationalized Δ sum. -/
theorem Eminus_normalized_residual_le_DeltaRat
    {p : Nat} {N : ℚ} (hN : 0 < N) (hp : 2 ≤ p) :
    |Eminus N p / (-N * c p) - 1| ≤ DeltaRat p N := by
  have hN0 : 0 ≤ N := hN.le
  have hcpos : 0 < c p := c_pos p (by omega : 1 ≤ p)
  have hdenpos : 0 < N * c p := mul_pos hN hcpos
  have hdenpos_ne : N * c p ≠ 0 := ne_of_gt hdenpos
  have habs :
      |Eminus N p / (-N * c p) - 1|
        = |Eminus N p + N * c p| / (N * c p) := by
    have hneg : -N * c p = -(N * c p) := by ring
    rw [hneg]
    calc
      |Eminus N p / (-(N * c p)) - 1|
          = |-(Eminus N p + N * c p) / (N * c p)| := by
              field_simp [hdenpos_ne]
              ring_nf
      _ = |Eminus N p + N * c p| / (N * c p) := by
              rw [abs_div, abs_neg, abs_of_pos hdenpos]
  rw [habs]
  have hres := Eminus_residual_le N hN0 p hp
  have hsum :
      (∑ r ∈ Finset.Icc 2 p,
          (N*(4/25))^r * 6^p * Gcomp r p / (r.factorial : ℚ))
        ≤ N * c p * DeltaRat p N :=
    Eminus_residual_sum_le_Nc_mul_DeltaRat hN0 hp
  have hmain :
      |Eminus N p + N * c p| ≤ N * c p * DeltaRat p N :=
    hres.trans hsum
  rw [div_le_iff₀ hdenpos]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmain

end Prop51
