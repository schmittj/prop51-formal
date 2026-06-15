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
import Prop51.ExpBounds

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

/-- Uniform near-range ratio bound when `N ≤ R p`. -/
def DeltaNearRatio (p : Nat) (R : ℚ) : ℚ :=
  (64*R)/(75*(p:ℚ))

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

/-- Concrete near-range ratio bound.  If `N ≤ R p` and `4r ≤ p`, then the
geometric ratio is bounded by `(64R)/(75p)`. -/
theorem DeltaRatStepRatioBound_le_near (p r : Nat) {N R : ℚ}
    (hR : 0 ≤ R) (hNp : N ≤ R * (p:ℚ))
    (hp : 1 ≤ p) (hrnear : 4*r ≤ p) :
    DeltaRatStepRatioBound p N r ≤ DeltaNearRatio p R := by
  unfold DeltaRatStepRatioBound
  have hpQ : (0:ℚ) < p := by exact_mod_cast hp
  have h2rle : 2*r ≤ p := by omega
  have h4rq : (4:ℚ) * r ≤ p := by exact_mod_cast hrnear
  have hA_lower : (p:ℚ)/2 ≤ ((p - 2*r : Nat) : ℚ) := by
    rw [Nat.cast_sub h2rle]
    norm_num
    nlinarith
  have hA_nonneg : (0:ℚ) ≤ ((p - 2*r : Nat) : ℚ) :=
    le_trans (by positivity : (0:ℚ) ≤ (p:ℚ)/2) hA_lower
  have hA_pos : (0:ℚ) < ((p - 2*r : Nat) : ℚ) := by
    exact_mod_cast (by omega : 0 < p - 2*r)
  have hB_lower : (p:ℚ)/2 ≤ ((p - 2*r + 1 : Nat) : ℚ) := by
    exact le_trans hA_lower (by norm_num)
  have hB_pos : (0:ℚ) < ((p - 2*r + 1 : Nat) : ℚ) := by positivity
  have hprod :
      ((p:ℚ)/2) * ((p:ℚ)/2)
        ≤ ((p - 2*r : Nat) : ℚ) * ((p - 2*r + 1 : Nat) : ℚ) := by
    exact mul_le_mul hA_lower hB_lower (by positivity) hA_nonneg
  have hden_lower :
      3 * ((p:ℚ)/2) * ((p:ℚ)/2)
        ≤ 3 * ((p - 2*r : Nat) : ℚ) * ((p - 2*r + 1 : Nat) : ℚ) := by
    nlinarith [hprod]
  have hden_pos :
      (0:ℚ) < 3 * ((p - 2*r : Nat) : ℚ) * ((p - 2*r + 1 : Nat) : ℚ) := by
    positivity
  have hden0_pos : (0:ℚ) < 3 * ((p:ℚ)/2) * ((p:ℚ)/2) := by
    positivity
  have hnum_le : (16/25) * N ≤ (16/25) * (R * (p:ℚ)) := by
    exact mul_le_mul_of_nonneg_left hNp (by norm_num)
  have hnum_nonneg : 0 ≤ (16/25) * (R * (p:ℚ)) := by positivity
  calc ((16/25) * N)
        / (3 * ((p - 2*r : Nat) : ℚ) * ((p - 2*r + 1 : Nat) : ℚ))
      ≤ ((16/25) * (R * (p:ℚ)))
        / (3 * ((p - 2*r : Nat) : ℚ) * ((p - 2*r + 1 : Nat) : ℚ)) := by
          exact div_le_div_of_nonneg_right hnum_le hden_pos.le
    _ ≤ ((16/25) * (R * (p:ℚ))) / (3 * ((p:ℚ)/2) * ((p:ℚ)/2)) := by
          exact div_le_div_of_nonneg_left hnum_nonneg hden0_pos hden_lower
    _ = DeltaNearRatio p R := by
          unfold DeltaNearRatio
          field_simp [ne_of_gt hpQ]
          ring

theorem DeltaNearRatio_nonneg (p : Nat) {R : ℚ} (hR : 0 ≤ R) (hp : 1 ≤ p) :
    0 ≤ DeltaNearRatio p R := by
  unfold DeltaNearRatio
  positivity

/-- In the paper's used range `R ≤ 20`, the near-range ratio is already
strictly below `1` for `p ≥ 18` (hence certainly for `p ≥ 100`). -/
theorem DeltaNearRatio_lt_one_of_le_20 (p : Nat) {R : ℚ}
    (hR20 : R ≤ 20) (hp : 18 ≤ p) :
    DeltaNearRatio p R < 1 := by
  unfold DeltaNearRatio
  have hpQ : (0:ℚ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp18Q : (18:ℚ) ≤ p := by exact_mod_cast hp
  have hden : (0:ℚ) < 75 * (p:ℚ) := by positivity
  rw [div_lt_iff₀ hden]
  nlinarith

/-! ## Finite geometric domination for the near range -/

private theorem geom_chain_bound_upto (F : Nat → ℚ) {q : ℚ} (hq0 : 0 ≤ q)
    {K : Nat} (hstep : ∀ j, j + 1 < K → F (j+3) ≤ F (j+2) * q) :
    ∀ j, j < K → F (j+2) ≤ F 2 * q^j := by
  intro j hj
  induction j with
  | zero =>
      simp
  | succ j ih =>
      calc F (j.succ + 2)
          = F (j + 3) := rfl
        _ ≤ F (j+2) * q := hstep j (by omega)
        _ ≤ (F 2 * q^j) * q := by
            exact mul_le_mul_of_nonneg_right (ih (by omega)) hq0
        _ = F 2 * q^(j.succ) := by
            rw [pow_succ]
            ring

private theorem geom_chain_sum_le (F : Nat → ℚ) {q : ℚ} (hq0 : 0 ≤ q)
    {K : Nat} (hstep : ∀ j, j + 1 < K → F (j+3) ≤ F (j+2) * q) :
    ∑ j ∈ Finset.range K, F (j+2)
      ≤ F 2 * ∑ j ∈ Finset.range K, q^j := by
  calc ∑ j ∈ Finset.range K, F (j+2)
      ≤ ∑ j ∈ Finset.range K, F 2 * q^j := by
          refine Finset.sum_le_sum fun j hj => ?_
          exact geom_chain_bound_upto F hq0 hstep j (Finset.mem_range.mp hj)
    _ = F 2 * ∑ j ∈ Finset.range K, q^j := by
          rw [Finset.mul_sum]

/-- Shifted near-range Δ terms are bounded by the corresponding finite
geometric progression whenever all successor ratios are bounded by `q`. -/
theorem DeltaRatTerm_shifted_sum_le_geom (p K : Nat) {N q : ℚ}
    (hN : 0 ≤ N) (hq0 : 0 ≤ q)
    (hratio : ∀ j, j + 1 < K → DeltaRatStepRatioBound p N (j+2) ≤ q)
    (hpstep : ∀ j, j + 1 < K → 2*((j+2)+1) ≤ p) :
    ∑ j ∈ Finset.range K, DeltaRatTerm p N (j+2)
      ≤ DeltaRatTerm p N 2 * ∑ j ∈ Finset.range K, q^j := by
  refine geom_chain_sum_le (fun r => DeltaRatTerm p N r) hq0 ?_
  intro j hj
  calc DeltaRatTerm p N (j+3)
      ≤ DeltaRatTerm p N (j+2) * DeltaRatStepRatioBound p N (j+2) := by
          exact DeltaRatTerm_succ_le p (j+2) hN (by omega) (hpstep j hj)
    _ ≤ DeltaRatTerm p N (j+2) * q := by
          exact mul_le_mul_of_nonneg_left (hratio j hj)
            (DeltaRatTerm_nonneg p (j+2) hN)

/-- Infinite-tail version of `DeltaRatTerm_shifted_sum_le_geom`, using the
rational geometric bound from `ExpBounds.lean`. -/
theorem DeltaRatTerm_shifted_sum_le_inv_one_sub (p K : Nat) {N q : ℚ}
    (hN : 0 ≤ N) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hratio : ∀ j, j + 1 < K → DeltaRatStepRatioBound p N (j+2) ≤ q)
    (hpstep : ∀ j, j + 1 < K → 2*((j+2)+1) ≤ p) :
    ∑ j ∈ Finset.range K, DeltaRatTerm p N (j+2)
      ≤ DeltaRatTerm p N 2 * (1/(1-q)) := by
  have hgeom :=
    DeltaRatTerm_shifted_sum_le_geom p K hN hq0 hratio hpstep
  exact hgeom.trans
    (mul_le_mul_of_nonneg_left
      (geom_sum_le_inv_one_sub q hq0 hq1 K)
      (DeltaRatTerm_nonneg p 2 hN))

private theorem sum_Icc_two_eq_shift (F : Nat → ℚ) (M : Nat) (hM : 2 ≤ M) :
    ∑ r ∈ Finset.Icc 2 M, F r = ∑ j ∈ Finset.range (M-1), F (j+2) := by
  have hIccIco : Finset.Icc 2 M = Finset.Ico 2 (M+1) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIccIco, Finset.sum_Ico_eq_sum_range,
      show M + 1 - 2 = M - 1 by omega]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Nat.add_comm]

/-- `Icc 2 M` version of the finite near-range geometric bound. -/
theorem DeltaRatTerm_Icc_sum_le_geom (p M : Nat) {N q : ℚ}
    (hM : 2 ≤ M) (hN : 0 ≤ N) (hq0 : 0 ≤ q)
    (hratio : ∀ r, 2 ≤ r → r < M → DeltaRatStepRatioBound p N r ≤ q)
    (hpstep : ∀ r, 2 ≤ r → r < M → 2*(r+1) ≤ p) :
    ∑ r ∈ Finset.Icc 2 M, DeltaRatTerm p N r
      ≤ DeltaRatTerm p N 2 * ∑ j ∈ Finset.range (M-1), q^j := by
  rw [sum_Icc_two_eq_shift (fun r => DeltaRatTerm p N r) M hM]
  exact DeltaRatTerm_shifted_sum_le_geom p (M-1) hN hq0
    (fun j hj => hratio (j+2) (by omega) (by omega))
    (fun j hj => hpstep (j+2) (by omega) (by omega))

/-- Infinite-tail `Icc 2 M` version of the near-range geometric bound. -/
theorem DeltaRatTerm_Icc_sum_le_inv_one_sub (p M : Nat) {N q : ℚ}
    (hM : 2 ≤ M) (hN : 0 ≤ N) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hratio : ∀ r, 2 ≤ r → r < M → DeltaRatStepRatioBound p N r ≤ q)
    (hpstep : ∀ r, 2 ≤ r → r < M → 2*(r+1) ≤ p) :
    ∑ r ∈ Finset.Icc 2 M, DeltaRatTerm p N r
      ≤ DeltaRatTerm p N 2 * (1/(1-q)) := by
  rw [sum_Icc_two_eq_shift (fun r => DeltaRatTerm p N r) M hM]
  exact DeltaRatTerm_shifted_sum_le_inv_one_sub p (M-1) hN hq0 hq1
    (fun j hj => hratio (j+2) (by omega) (by omega))
    (fun j hj => hpstep (j+2) (by omega) (by omega))

/-- Concrete near-range finite geometric bound for `Icc 2 M`, under
`N ≤ R p` and `4r ≤ p` throughout the slice. -/
theorem DeltaRatTerm_Icc_sum_le_near_geom (p M : Nat) {N R : ℚ}
    (hM : 2 ≤ M) (hN : 0 ≤ N) (hR : 0 ≤ R) (hNp : N ≤ R * (p:ℚ))
    (hp : 1 ≤ p) (hnear : ∀ r, 2 ≤ r → r < M → 4*r ≤ p) :
    ∑ r ∈ Finset.Icc 2 M, DeltaRatTerm p N r
      ≤ DeltaRatTerm p N 2 * ∑ j ∈ Finset.range (M-1), (DeltaNearRatio p R)^j := by
  refine DeltaRatTerm_Icc_sum_le_geom p M hM hN
    (DeltaNearRatio_nonneg p hR hp) ?_ ?_
  · intro r hr2 hrM
    exact DeltaRatStepRatioBound_le_near p r hR hNp hp (hnear r hr2 hrM)
  · intro r hr2 hrM
    have h4 := hnear r hr2 hrM
    omega

/-- Concrete near-range infinite-tail bound for `Icc 2 M`. -/
theorem DeltaRatTerm_Icc_sum_le_near_inv_one_sub (p M : Nat) {N R : ℚ}
    (hM : 2 ≤ M) (hN : 0 ≤ N) (hR : 0 ≤ R) (hNp : N ≤ R * (p:ℚ))
    (hp : 1 ≤ p) (hq1 : DeltaNearRatio p R < 1)
    (hnear : ∀ r, 2 ≤ r → r < M → 4*r ≤ p) :
    ∑ r ∈ Finset.Icc 2 M, DeltaRatTerm p N r
      ≤ DeltaRatTerm p N 2 * (1/(1 - DeltaNearRatio p R)) := by
  refine DeltaRatTerm_Icc_sum_le_inv_one_sub p M hM hN
    (DeltaNearRatio_nonneg p hR hp) hq1 ?_ ?_
  · intro r hr2 hrM
    exact DeltaRatStepRatioBound_le_near p r hR hNp hp (hnear r hr2 hrM)
  · intro r hr2 hrM
    have h4 := hnear r hr2 hrM
    omega

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
