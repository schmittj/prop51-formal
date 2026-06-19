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

/-- Near part of `DeltaRat`, up to the paper's cutoff `r ≤ p/4`. -/
def DeltaRatNear (p : Nat) (N : ℚ) : ℚ :=
  ∑ r ∈ Finset.Icc 2 (p/4), DeltaRatTerm p N r

/-- Far part of `DeltaRat`, beyond the paper's cutoff `r > p/4`. -/
def DeltaRatFar (p : Nat) (N : ℚ) : ℚ :=
  ∑ r ∈ Finset.Icc (p/4 + 1) (p/2), DeltaRatTerm p N r

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

/-- Closed-form geometric majorant for the near-range Δ terms. -/
def DeltaNearGeomBound (p : Nat) (R : ℚ) : ℚ :=
  ((1152/3125) * R * (p:ℚ)
      / (((p-1 : Nat) : ℚ) * ((p-2 : Nat) : ℚ)))
    * (1/(1 - DeltaNearRatio p R))

/-- A `p`-independent far-range majorant for a single Δ block, valid once
`N ≤ 20p` and `r > p/4`.  The factorials in the denominator are left in place;
the next layer applies `factorial_lb` to this term. -/
def DeltaRatFarTermBound (r : Nat) : ℚ :=
  (9/5) * (16/25)^r * (80*(r:ℚ))^(r-1)
    / ((r.factorial : ℚ) * (((2*r - 1 : Nat).factorial : ℚ)))

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

/-- Closed-form version of the near-range geometric bound. -/
theorem DeltaRatTerm_Icc_sum_le_near_closed (p M : Nat) {N R : ℚ}
    (hM : 2 ≤ M) (hN : 0 ≤ N) (hR : 0 ≤ R) (hNp : N ≤ R * (p:ℚ))
    (hp : 4 ≤ p) (hq1 : DeltaNearRatio p R < 1)
    (hnear : ∀ r, 2 ≤ r → r < M → 4*r ≤ p) :
    ∑ r ∈ Finset.Icc 2 M, DeltaRatTerm p N r
      ≤ DeltaNearGeomBound p R := by
  have hslice := DeltaRatTerm_Icc_sum_le_near_inv_one_sub
    p M hM hN hR hNp (by omega : 1 ≤ p) hq1 hnear
  have hterm2 :
      DeltaRatTerm p N 2
        ≤ (1152/3125) * (R * (p:ℚ))
          / (((p-1 : Nat) : ℚ) * ((p-2 : Nat) : ℚ)) := by
    rw [DeltaRatTerm_two p N hp]
    have hden_pos :
        (0:ℚ) < ((p-1 : Nat) : ℚ) * ((p-2 : Nat) : ℚ) := by
      have h1 : (0:ℚ) < ((p-1 : Nat) : ℚ) := by
        exact_mod_cast (by omega : 0 < p-1)
      have h2 : (0:ℚ) < ((p-2 : Nat) : ℚ) := by
        exact_mod_cast (by omega : 0 < p-2)
      positivity
    have hnum_le : (1152/3125) * N ≤ (1152/3125) * (R * (p:ℚ)) := by
      exact mul_le_mul_of_nonneg_left hNp (by norm_num)
    exact div_le_div_of_nonneg_right hnum_le hden_pos.le
  have htail_nonneg : 0 ≤ 1/(1 - DeltaNearRatio p R) := by
    have hpos : (0:ℚ) < 1 - DeltaNearRatio p R := by linarith
    positivity
  have hclosed :
      DeltaRatTerm p N 2 * (1/(1 - DeltaNearRatio p R))
        ≤ DeltaNearGeomBound p R := by
    unfold DeltaNearGeomBound
    calc DeltaRatTerm p N 2 * (1/(1 - DeltaNearRatio p R))
        ≤ ((1152/3125) * (R * (p:ℚ))
            / (((p-1 : Nat) : ℚ) * ((p-2 : Nat) : ℚ)))
            * (1/(1 - DeltaNearRatio p R)) := by
              exact mul_le_mul_of_nonneg_right hterm2 htail_nonneg
      _ = ((1152/3125) * R * (p:ℚ)
            / (((p-1 : Nat) : ℚ) * ((p-2 : Nat) : ℚ)))
            * (1/(1 - DeltaNearRatio p R)) := by
              ring
  exact hslice.trans hclosed

/-- The near part of `DeltaRat`, cut off at `r ≤ p/4`, is bounded by the
closed-form near geometric majorant. -/
theorem DeltaRatNear_le_geomBound (p : Nat) {N R : ℚ}
    (hN : 0 ≤ N) (hR : 0 ≤ R) (hNp : N ≤ R * (p:ℚ))
    (hp : 8 ≤ p) (hq1 : DeltaNearRatio p R < 1) :
    DeltaRatNear p N ≤ DeltaNearGeomBound p R := by
  unfold DeltaRatNear
  refine DeltaRatTerm_Icc_sum_le_near_closed p (p/4) (by omega) hN hR hNp
    (by omega) hq1 ?_
  intro r _hr2 hr
  omega

/-- Split `DeltaRat` at the paper's cutoff `r = p/4`. -/
theorem DeltaRat_eq_near_add_far (p : Nat) (N : ℚ) (hp : 4 ≤ p) :
    DeltaRat p N = DeltaRatNear p N + DeltaRatFar p N := by
  unfold DeltaRat DeltaRatNear DeltaRatFar
  have hsplit :
      Finset.Icc 2 (p/2)
        = Finset.Icc 2 (p/4) ∪ Finset.Icc (p/4 + 1) (p/2) := by
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
      Disjoint (Finset.Icc 2 (p/4)) (Finset.Icc (p/4 + 1) (p/2)) := by
    rw [Finset.disjoint_left]
    intro r hnear hfar
    simp only [Finset.mem_Icc] at hnear hfar
    omega
  rw [hsplit, Finset.sum_union hdisj]

/-- After the near/far split, the near part may be replaced by its closed
geometric majorant. -/
theorem DeltaRat_le_nearGeomBound_add_far (p : Nat) {N R : ℚ}
    (hN : 0 ≤ N) (hR : 0 ≤ R) (hNp : N ≤ R * (p:ℚ))
    (hp : 8 ≤ p) (hq1 : DeltaNearRatio p R < 1) :
    DeltaRat p N ≤ DeltaNearGeomBound p R + DeltaRatFar p N := by
  have hnear : DeltaRatNear p N ≤ DeltaNearGeomBound p R :=
    DeltaRatNear_le_geomBound p hN hR hNp hp hq1
  calc DeltaRat p N
      = DeltaRatNear p N + DeltaRatFar p N :=
          DeltaRat_eq_near_add_far p N (by omega)
    _ ≤ DeltaNearGeomBound p R + DeltaRatFar p N :=
          add_le_add hnear le_rfl

/-! ## Far-range factorial compression -/

private theorem factorial_mul_factorial_le_far {p r : Nat}
    (hr : 1 ≤ r) (hrp : 2*r ≤ p) :
    (p - 2*r + 1).factorial * (2*r - 1).factorial
      ≤ (p-1).factorial := by
  have hleft_len : 2*r - 2 ≤ 2*r - 1 := by omega
  have hright_len : 2*r - 2 ≤ p - 1 := by omega
  have hbase : 2*r - 1 ≤ p - 1 := by omega
  have hdesc_le :
      (2*r - 1).descFactorial (2*r - 2)
        ≤ (p - 1).descFactorial (2*r - 2) :=
    Nat.descFactorial_le (2*r - 2) hbase
  have hleft_eq :
      (2*r - 1).descFactorial (2*r - 2) = (2*r - 1).factorial := by
    have hmul := Nat.factorial_mul_descFactorial hleft_len
    have hdiff : (2*r - 1) - (2*r - 2) = 1 := by omega
    rw [hdiff] at hmul
    norm_num at hmul
    exact hmul
  have hright_eq :
      (p - 2*r + 1).factorial * (p - 1).descFactorial (2*r - 2)
        = (p - 1).factorial := by
    have hmul := Nat.factorial_mul_descFactorial hright_len
    have hdiff : (p - 1) - (2*r - 2) = p - 2*r + 1 := by omega
    rw [hdiff] at hmul
    exact hmul
  calc
    (p - 2*r + 1).factorial * (2*r - 1).factorial
        = (p - 2*r + 1).factorial
            * (2*r - 1).descFactorial (2*r - 2) := by rw [hleft_eq]
    _ ≤ (p - 2*r + 1).factorial
            * (p - 1).descFactorial (2*r - 2) :=
          Nat.mul_le_mul_left _ hdesc_le
    _ = (p-1).factorial := hright_eq

private theorem far_factorial_ratio_le_inv (p r : Nat)
    (hr : 1 ≤ r) (hrp : 2*r ≤ p) :
    ((p - 2*r + 1).factorial : ℚ) / ((p-1).factorial : ℚ)
      ≤ 1 / (((2*r - 1 : Nat).factorial : ℚ)) := by
  have hNat := factorial_mul_factorial_le_far (p := p) (r := r) hr hrp
  have hcast :
      ((p - 2*r + 1).factorial : ℚ)
        * (((2*r - 1 : Nat).factorial : ℚ))
          ≤ ((p-1).factorial : ℚ) := by
    exact_mod_cast hNat
  have hFpos : (0:ℚ) < (((2*r - 1 : Nat).factorial : ℚ)) := by
    exact_mod_cast (Nat.factorial_pos (2*r - 1))
  have hPpos : (0:ℚ) < ((p-1).factorial : ℚ) := by
    exact_mod_cast (Nat.factorial_pos (p-1))
  have hdiv :
      ((p - 2*r + 1).factorial : ℚ)
        ≤ ((p-1).factorial : ℚ) / (((2*r - 1 : Nat).factorial : ℚ)) := by
    rw [le_div_iff₀ hFpos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcast
  calc
    ((p - 2*r + 1).factorial : ℚ) / ((p-1).factorial : ℚ)
        ≤ (((p-1).factorial : ℚ) / (((2*r - 1 : Nat).factorial : ℚ)))
            / ((p-1).factorial : ℚ) :=
          div_le_div_of_nonneg_right hdiv hPpos.le
    _ = 1 / (((2*r - 1 : Nat).factorial : ℚ)) := by
          field_simp [ne_of_gt hFpos, ne_of_gt hPpos]

private theorem DeltaRatTerm_far_coeff (r : Nat) (hr : 1 ≤ r) :
    (36/5) * (4/25)^r * 4^(r-1) = (9/5) * (16/25)^r := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r-1, by omega⟩
  norm_num

/-- Very coarse all-range Δ-block estimate.

This is intentionally much weaker than the paper's near/far envelope.  It is
useful in the final deep-low solo tail, where the surrounding factorial and
power decay leaves enormous slack and a one-line `N^p` majorant is preferable
to another thresholded Δ split. -/
theorem DeltaRatTerm_le_two_pow (p r : Nat) {N : ℚ}
    (hN1 : 1 ≤ N) (hr : 2 ≤ r) (hrp : 2*r ≤ p) :
    DeltaRatTerm p N r ≤ 2 * N^p := by
  have hN0 : 0 ≤ N := le_trans zero_le_one hN1
  have hpow_le : N^(r-1) ≤ N^p :=
    pow_le_pow_right₀ hN1 (by omega : r - 1 ≤ p)
  have hcoef_eq :
      (36/5 : ℚ) * (4/25)^r * 4^(r-1) = (9/5) * (16/25)^r :=
    by
      obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r-1, by omega⟩
      norm_num
      ring_nf
      rw [← mul_pow]
      norm_num
  have hcoef_pow_le_one : (16 / 25 : ℚ)^r ≤ 1 :=
    pow_le_one₀ (by norm_num : (0 : ℚ) ≤ 16 / 25)
      (by norm_num : (16 / 25 : ℚ) ≤ 1)
  have hcoef_le : (9 / 5 : ℚ) * (16 / 25 : ℚ)^r ≤ 2 := by
    nlinarith
  have hfacNat :
      (p - 2*r + 1).factorial ≤ (p - 1).factorial :=
    Nat.factorial_le (by omega : p - 2*r + 1 ≤ p - 1)
  have hfac :
      (((p - 2*r + 1).factorial : Nat) : ℚ)
        ≤ (((p - 1).factorial : Nat) : ℚ) := by
    exact_mod_cast hfacNat
  have hrfac_ge_one : (1 : ℚ) ≤ (r.factorial : ℚ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos r))
  have hpfac_nonneg : 0 ≤ (((p - 1).factorial : Nat) : ℚ) := by
    positivity
  have hden_ge :
      (((p - 1).factorial : Nat) : ℚ)
        ≤ (r.factorial : ℚ) * (((p - 1).factorial : Nat) : ℚ) := by
    calc
      (((p - 1).factorial : Nat) : ℚ)
          = (1 : ℚ) * (((p - 1).factorial : Nat) : ℚ) := by ring
      _ ≤ (r.factorial : ℚ) * (((p - 1).factorial : Nat) : ℚ) :=
          mul_le_mul_of_nonneg_right hrfac_ge_one hpfac_nonneg
  have hden_pos :
      0 < (r.factorial : ℚ) * (((p - 1).factorial : Nat) : ℚ) := by
    positivity
  have hratio_le :
      (((p - 2*r + 1).factorial : Nat) : ℚ) /
          ((r.factorial : ℚ) * (((p - 1).factorial : Nat) : ℚ))
        ≤ 1 := by
    rw [div_le_one₀ hden_pos]
    exact hfac.trans hden_ge
  have hratio_nonneg :
      0 ≤ (((p - 2*r + 1).factorial : Nat) : ℚ) /
          ((r.factorial : ℚ) * (((p - 1).factorial : Nat) : ℚ)) := by
    positivity
  have hbase_le :
      (9 / 5 : ℚ) * (16 / 25 : ℚ)^r * N^(r-1) ≤ 2 * N^p := by
    have hpow_nonneg : 0 ≤ N^(r-1) := pow_nonneg hN0 (r-1)
    have hcoef_scaled :
        (9 / 5 : ℚ) * (16 / 25 : ℚ)^r * N^(r-1)
          ≤ 2 * N^(r-1) :=
      mul_le_mul_of_nonneg_right hcoef_le hpow_nonneg
    have hpow_scaled : 2 * N^(r-1) ≤ 2 * N^p :=
      mul_le_mul_of_nonneg_left hpow_le (by norm_num)
    exact hcoef_scaled.trans hpow_scaled
  have hbound_nonneg : 0 ≤ 2 * N^p := by
    exact mul_nonneg (by norm_num) (pow_nonneg hN0 p)
  have hterm_rewrite :
      DeltaRatTerm p N r =
        ((9 / 5 : ℚ) * (16 / 25 : ℚ)^r * N^(r-1)) *
          ((((p - 2*r + 1).factorial : Nat) : ℚ) /
            ((r.factorial : ℚ) * (((p - 1).factorial : Nat) : ℚ))) := by
    unfold DeltaRatTerm
    rw [hcoef_eq]
    ring
  rw [hterm_rewrite]
  calc
    ((9 / 5 : ℚ) * (16 / 25 : ℚ)^r * N^(r-1)) *
        ((((p - 2*r + 1).factorial : Nat) : ℚ) /
          ((r.factorial : ℚ) * (((p - 1).factorial : Nat) : ℚ)))
        ≤ (2 * N^p) * 1 :=
          mul_le_mul hbase_le hratio_le hratio_nonneg hbound_nonneg
    _ = 2 * N^p := by ring

/-- Coarse all-range Δ estimate used by the final deep-low solo tail. -/
theorem DeltaRat_le_two_count_mul_pow (p : Nat) {N : ℚ} (hN1 : 1 ≤ N) :
    DeltaRat p N ≤ 2 * (((p + 1 : Nat) : ℚ) * N^p) := by
  have hN0 : 0 ≤ N := le_trans zero_le_one hN1
  have hterm :
      ∀ r ∈ Finset.Icc 2 (p/2), DeltaRatTerm p N r ≤ 2 * N^p := by
    intro r hrmem
    obtain ⟨hr2, hrhi⟩ := Finset.mem_Icc.mp hrmem
    have hrp : 2*r ≤ p := by
      have hInt : (r : ℤ) * 2 ≤ (p : ℤ) :=
        Nat.le_div_two_iff_mul_two_le.mp hrhi
      omega
    exact DeltaRatTerm_le_two_pow p r hN1 hr2 hrp
  have hsubset : Finset.Icc 2 (p/2) ⊆ Finset.range (p + 1) := by
    intro r hrmem
    obtain ⟨_hr2, hrhi⟩ := Finset.mem_Icc.mp hrmem
    have hrp : 2*r ≤ p := by
      have hInt : (r : ℤ) * 2 ≤ (p : ℤ) :=
        Nat.le_div_two_iff_mul_two_le.mp hrhi
      omega
    simp only [Finset.mem_range]
    omega
  have hcardNat : (Finset.Icc 2 (p/2)).card ≤ p + 1 := by
    simpa using Finset.card_le_card hsubset
  have hcard : (((Finset.Icc 2 (p/2)).card : Nat) : ℚ)
      ≤ ((p + 1 : Nat) : ℚ) := by
    exact_mod_cast hcardNat
  have hconst_nonneg : 0 ≤ 2 * N^p := by
    exact mul_nonneg (by norm_num) (pow_nonneg hN0 p)
  unfold DeltaRat
  calc
    (∑ r ∈ Finset.Icc 2 (p/2), DeltaRatTerm p N r)
        ≤ ∑ _r ∈ Finset.Icc 2 (p/2), 2 * N^p :=
          Finset.sum_le_sum hterm
    _ = (((Finset.Icc 2 (p/2)).card : Nat) : ℚ) * (2 * N^p) := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((p + 1 : Nat) : ℚ) * (2 * N^p) :=
          mul_le_mul_of_nonneg_right hcard hconst_nonneg
    _ = 2 * (((p + 1 : Nat) : ℚ) * N^p) := by ring

theorem DeltaRatTerm_le_farTermBound (p r : Nat) {N : ℚ}
    (hN : 0 ≤ N) (hN20 : N ≤ 20 * (p:ℚ))
    (hrfar : p/4 < r) (hrp : 2*r ≤ p) :
    DeltaRatTerm p N r ≤ DeltaRatFarTermBound r := by
  have hr : 1 ≤ r := by omega
  have hp_lt : p < 4*r := by omega
  have hN80 : N ≤ 80 * (r:ℚ) := by
    have hp_le : (p:ℚ) ≤ 4 * (r:ℚ) := by
      exact_mod_cast (Nat.le_of_lt hp_lt)
    nlinarith
  have hpow :
      N^(r-1) ≤ (80*(r:ℚ))^(r-1) :=
    pow_le_pow_left₀ hN hN80 (r-1)
  have hcoef_nonneg : 0 ≤ (9/5:ℚ) * (16/25)^r := by positivity
  have hrf_pos : (0:ℚ) < (r.factorial : ℚ) := by
    exact_mod_cast r.factorial_pos
  have hpf_pos : (0:ℚ) < ((p-1).factorial : ℚ) := by
    exact_mod_cast (p-1).factorial_pos
  have hfarf_pos : (0:ℚ) < (((2*r - 1 : Nat).factorial : ℚ)) := by
    exact_mod_cast (2*r - 1).factorial_pos
  have hratio_nonneg :
      0 ≤ ((p - 2*r + 1).factorial : ℚ) / ((p-1).factorial : ℚ) := by
    positivity
  have hbase_nonneg :
      0 ≤ ((9/5:ℚ) * (16/25)^r * (80*(r:ℚ))^(r-1)) / (r.factorial : ℚ) := by
    positivity
  have hpow_part :
      ((9/5:ℚ) * (16/25)^r * N^(r-1)) / (r.factorial : ℚ)
        ≤ ((9/5:ℚ) * (16/25)^r * (80*(r:ℚ))^(r-1))
            / (r.factorial : ℚ) := by
    have hnum :
        (9/5:ℚ) * (16/25)^r * N^(r-1)
          ≤ (9/5:ℚ) * (16/25)^r * (80*(r:ℚ))^(r-1) := by
      exact mul_le_mul_of_nonneg_left hpow hcoef_nonneg
    exact div_le_div_of_nonneg_right hnum hrf_pos.le
  have hfact := far_factorial_ratio_le_inv p r hr hrp
  have hterm_rewrite :
      DeltaRatTerm p N r
        =
      ((9/5:ℚ) * (16/25)^r * N^(r-1)) / (r.factorial : ℚ)
        * (((p - 2*r + 1).factorial : ℚ) / ((p-1).factorial : ℚ)) := by
    have hcoef' :
        (36:ℚ) * (4/25)^r * 4^(r-1) = 9 * (16/25)^r := by
      obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r-1, by omega⟩
      norm_num
      ring_nf
      rw [← mul_pow]
      norm_num
    unfold DeltaRatTerm
    field_simp [ne_of_gt hrf_pos, ne_of_gt hpf_pos]
    rw [hcoef']
    ring
  have hbound_rewrite :
      DeltaRatFarTermBound r
        =
      ((9/5:ℚ) * (16/25)^r * (80*(r:ℚ))^(r-1)) / (r.factorial : ℚ)
        * (1 / (((2*r - 1 : Nat).factorial : ℚ))) := by
    unfold DeltaRatFarTermBound
    field_simp [ne_of_gt hrf_pos, ne_of_gt hfarf_pos]
  rw [hterm_rewrite, hbound_rewrite]
  exact mul_le_mul hpow_part hfact hratio_nonneg hbase_nonneg

theorem DeltaRatFar_le_termBound (p : Nat) {N : ℚ}
    (hN : 0 ≤ N) (hN20 : N ≤ 20 * (p:ℚ)) :
    DeltaRatFar p N
      ≤ ∑ r ∈ Finset.Icc (p/4 + 1) (p/2), DeltaRatFarTermBound r := by
  unfold DeltaRatFar
  refine Finset.sum_le_sum fun r hrmem => ?_
  obtain ⟨hrlo, hrhi⟩ := Finset.mem_Icc.mp hrmem
  have hrfar : p/4 < r := by omega
  have hrp : 2*r ≤ p := by
    have hInt : (r : ℤ) * 2 ≤ (p : ℤ) :=
      Nat.le_div_two_iff_mul_two_le.mp hrhi
    omega
  exact DeltaRatTerm_le_farTermBound p r hN hN20 hrfar hrp

theorem DeltaRatFarTermBound_nonneg (r : Nat) :
    0 ≤ DeltaRatFarTermBound r := by
  unfold DeltaRatFarTermBound
  positivity

private theorem DeltaRatFarTermBound_succ_ratio (r : Nat) (hr : 1 ≤ r) :
    DeltaRatFarTermBound (r+1)
      =
    DeltaRatFarTermBound r
      * (((256/5) * ((((r+1 : Nat) : ℚ)/(r:ℚ))^(r-1)))
          / (((2*r : Nat) : ℚ) * (((2*r + 1 : Nat) : ℚ)))) := by
  have hrQ : (0:ℚ) < r := by exact_mod_cast (by omega : 0 < r)
  have hrf : ((r.factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have h2rf : ((((2*r - 1 : Nat).factorial : ℕ) : ℚ)) ≠ 0 := by positivity
  have h2rQ : (((2*r : Nat) : ℚ)) ≠ 0 := by
    exact_mod_cast (by omega : 2*r ≠ 0)
  have h2r1Q : (((2*r + 1 : Nat) : ℚ)) ≠ 0 := by positivity
  have hfact_r :
      (((r+1).factorial : ℕ) : ℚ) = ((r:ℚ)+1) * (r.factorial : ℚ) := by
    push_cast [Nat.factorial_succ]
    ring
  have hfact_2r :
      ((((2*(r+1) - 1 : Nat).factorial : ℕ) : ℚ))
        = (((2*r + 1 : Nat) : ℚ)) * (((2*r : Nat) : ℚ))
            * (((2*r - 1 : Nat).factorial : ℚ)) := by
    have hnat :
        (2*(r+1) - 1).factorial
          = (2*r + 1) * (2*r) * (2*r - 1).factorial := by
      rw [show 2*(r+1) - 1 = 2*r + 1 by omega,
          show 2*r + 1 = (2*r) + 1 by omega, Nat.factorial_succ,
          show 2*r = (2*r - 1) + 1 by omega, Nat.factorial_succ]
      simp
      ring_nf
    exact_mod_cast hnat
  have hpow_cancel :
      (r:ℚ)^(r-1) * ((r:ℚ)⁻¹)^(r-1) = 1 := by
    rw [← mul_pow]
    field_simp [ne_of_gt hrQ]
    simp
  have hpow_cancel_pref (P : ℚ) :
      P * (r:ℚ) * (r:ℚ)^(r-1) * ((r:ℚ)⁻¹)^(r-1) = P * (r:ℚ) := by
    calc
      P * (r:ℚ) * (r:ℚ)^(r-1) * ((r:ℚ)⁻¹)^(r-1)
          = P * ((r:ℚ) * ((r:ℚ)^(r-1) * ((r:ℚ)⁻¹)^(r-1))) := by ring
      _ = P * ((r:ℚ) * 1) := by rw [hpow_cancel]
      _ = P * (r:ℚ) := by ring
  have hpow_cancel_pref0 (P : ℚ) :
      P * (r:ℚ)^(r-1) * ((r:ℚ)⁻¹)^(r-1) = P := by
    rw [mul_assoc, hpow_cancel, mul_one]
  unfold DeltaRatFarTermBound
  rw [hfact_r, hfact_2r]
  field_simp [ne_of_gt hrQ, hrf, h2rf, h2rQ, h2r1Q]
  ring_nf
  rw [hpow_cancel_pref ((((1 + r : Nat) : ℚ))^(r-1))]
  rw [hpow_cancel_pref0 ((((1 + r : Nat) : ℚ))^(r-1))]
  conv_lhs =>
    rw [show 1 + r - 1 = (r - 1) + 1 by omega]
    rw [pow_succ]
    rw [pow_succ]
  push_cast
  ring_nf

theorem DeltaRatFarTermBound_succ_le_half (r : Nat) (hr : 34 ≤ r) :
    DeltaRatFarTermBound (r+1) ≤ DeltaRatFarTermBound r * (1/2) := by
  have hr1 : 1 ≤ r := by omega
  have hrQ : (0:ℚ) < r := by exact_mod_cast (by omega : 0 < r)
  have hbase_one : (1:ℚ) ≤ 1 + 1/(r:ℚ) := by
    have hinv_nonneg : (0:ℚ) ≤ 1/(r:ℚ) := by positivity
    linarith
  have hpow_mono :
      (1 + 1/(r:ℚ))^(r-1) ≤ (1 + 1/(r:ℚ))^r :=
    pow_right_mono₀ hbase_one (by omega)
  have hpow_le : (1 + 1/(r:ℚ))^(r-1) ≤ 68/25 :=
    hpow_mono.trans (one_add_inv_pow_le r hr1)
  have hratio_base :
      (((r+1 : Nat) : ℚ)/(r:ℚ)) = 1 + 1/(r:ℚ) := by
    have hcast : (((r+1 : Nat) : ℚ)) = (r:ℚ) + 1 := by
      push_cast
      ring
    rw [hcast]
    field_simp [ne_of_gt hrQ]
  have hden_pos :
      (0:ℚ) < ((2*r : Nat) : ℚ) * (((2*r + 1 : Nat) : ℚ)) := by positivity
  have hratio :
      (((256/5) * ((((r+1 : Nat) : ℚ)/(r:ℚ))^(r-1)))
          / (((2*r : Nat) : ℚ) * (((2*r + 1 : Nat) : ℚ)))) ≤ 1/2 := by
    rw [hratio_base]
    rw [div_le_iff₀ hden_pos]
    have hr34 : (34:ℚ) ≤ r := by exact_mod_cast hr
    have hden_cast :
        (((2*r : Nat) : ℚ) * (((2*r + 1 : Nat) : ℚ))
          = (2*(r:ℚ)) * (2*(r:ℚ)+1)) := by
      push_cast
      ring
    rw [hden_cast]
    nlinarith
  rw [DeltaRatFarTermBound_succ_ratio r hr1]
  exact mul_le_mul_of_nonneg_left hratio (DeltaRatFarTermBound_nonneg r)

private theorem geom_chain_bound_from (F : Nat → ℚ) {q : ℚ} (hq0 : 0 ≤ q)
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

private theorem geom_chain_sum_from_le (F : Nat → ℚ) {q : ℚ} (hq0 : 0 ≤ q)
    {a K : Nat} (hstep : ∀ j, j + 1 < K → F (a+j+1) ≤ F (a+j) * q) :
    ∑ j ∈ Finset.range K, F (a+j)
      ≤ F a * ∑ j ∈ Finset.range K, q^j := by
  calc ∑ j ∈ Finset.range K, F (a+j)
      ≤ ∑ j ∈ Finset.range K, F a * q^j := by
          refine Finset.sum_le_sum fun j hj => ?_
          exact geom_chain_bound_from F hq0 hstep j (Finset.mem_range.mp hj)
    _ = F a * ∑ j ∈ Finset.range K, q^j := by
          rw [Finset.mul_sum]

private theorem sum_Icc_eq_shift_from (F : Nat → ℚ) (a b : Nat) :
    ∑ r ∈ Finset.Icc a b, F r = ∑ j ∈ Finset.range (b+1-a), F (a+j) := by
  have hIccIco : Finset.Icc a b = Finset.Ico a (b+1) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIccIco, Finset.sum_Ico_eq_sum_range]

theorem DeltaRatFarTermBound_Icc_sum_le_two_first (a b : Nat) (ha : 34 ≤ a) :
    ∑ r ∈ Finset.Icc a b, DeltaRatFarTermBound r
      ≤ 2 * DeltaRatFarTermBound a := by
  by_cases hab : a ≤ b
  · rw [sum_Icc_eq_shift_from (fun r => DeltaRatFarTermBound r) a b]
    have hgeom :
        ∑ j ∈ Finset.range (b+1-a), DeltaRatFarTermBound (a+j)
          ≤ DeltaRatFarTermBound a
              * ∑ j ∈ Finset.range (b+1-a), (1/2:ℚ)^j := by
      refine geom_chain_sum_from_le (fun r => DeltaRatFarTermBound r)
        (by norm_num : (0:ℚ) ≤ 1/2) ?_
      intro j hj
      exact DeltaRatFarTermBound_succ_le_half (a+j) (by omega)
    calc
      ∑ j ∈ Finset.range (b+1-a), DeltaRatFarTermBound (a+j)
          ≤ DeltaRatFarTermBound a
              * ∑ j ∈ Finset.range (b+1-a), (1/2:ℚ)^j := hgeom
      _ ≤ DeltaRatFarTermBound a * (1/(1-(1/2:ℚ))) := by
            exact mul_le_mul_of_nonneg_left
              (geom_sum_le_inv_one_sub (1/2) (by norm_num) (by norm_num) _)
              (DeltaRatFarTermBound_nonneg a)
      _ = 2 * DeltaRatFarTermBound a := by ring
  · have hzero :
        ∑ r ∈ Finset.Icc a b, DeltaRatFarTermBound r = 0 := by
      apply Finset.sum_eq_zero
      intro r hrmem
      obtain ⟨hrlo, hrhi⟩ := Finset.mem_Icc.mp hrmem
      omega
    rw [hzero]
    exact mul_nonneg (by norm_num) (DeltaRatFarTermBound_nonneg a)

theorem DeltaRatFar_le_two_first (p : Nat) {N : ℚ}
    (hN : 0 ≤ N) (hN20 : N ≤ 20 * (p:ℚ)) (hp : 132 ≤ p) :
    DeltaRatFar p N ≤ 2 * DeltaRatFarTermBound (p/4 + 1) := by
  have hfar := DeltaRatFar_le_termBound p hN hN20
  have hsum :=
    DeltaRatFarTermBound_Icc_sum_le_two_first (p/4 + 1) (p/2) (by omega)
  exact hfar.trans hsum

private theorem DeltaRatFarTermBound_34_le_inv_two_thousand :
    DeltaRatFarTermBound 34 ≤ 1 / 2000 := by
  native_decide

theorem DeltaRatFar_le_one_thousand_of_ge_134 (p : Nat) {N : ℚ}
    (hN : 0 ≤ N) (hN20 : N ≤ 20 * (p:ℚ)) (hp : 134 ≤ p) :
    DeltaRatFar p N ≤ 1 / 1000 := by
  have hfar := DeltaRatFar_le_termBound p hN hN20
  have hsubset :
      ∑ r ∈ Finset.Icc (p/4 + 1) (p/2), DeltaRatFarTermBound r
        ≤ ∑ r ∈ Finset.Icc 34 (p/2), DeltaRatFarTermBound r := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro r hr
      obtain ⟨hrlo, hrhi⟩ := Finset.mem_Icc.mp hr
      exact Finset.mem_Icc.mpr ⟨by omega, hrhi⟩
    · intro r _hrBig _hrSmall
      exact DeltaRatFarTermBound_nonneg r
  have hsum :
      ∑ r ∈ Finset.Icc 34 (p/2), DeltaRatFarTermBound r
        ≤ 2 * DeltaRatFarTermBound 34 :=
    DeltaRatFarTermBound_Icc_sum_le_two_first 34 (p/2) (by omega)
  calc
    DeltaRatFar p N
        ≤ ∑ r ∈ Finset.Icc (p/4 + 1) (p/2),
            DeltaRatFarTermBound r := hfar
    _ ≤ ∑ r ∈ Finset.Icc 34 (p/2), DeltaRatFarTermBound r := hsubset
    _ ≤ 2 * DeltaRatFarTermBound 34 := hsum
    _ ≤ 2 * (1 / 2000 : ℚ) := by
          exact mul_le_mul_of_nonneg_left
            DeltaRatFarTermBound_34_le_inv_two_thousand (by norm_num)
    _ = 1 / 1000 := by norm_num

theorem DeltaNearGeomBound_le_59_1000_of_ge_134 (p : Nat)
    (hp : 134 ≤ p) :
    DeltaNearGeomBound p 18 ≤ 59 / 1000 := by
  have hpQ : (0:ℚ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp134Q : (134:ℚ) ≤ p := by exact_mod_cast hp
  have htail :
      1 / (1 - DeltaNearRatio p 18) ≤ 17/15 := by
    have hqle : DeltaNearRatio p 18 ≤ 2/17 := by
      unfold DeltaNearRatio
      have hden : (0:ℚ) < 75 * (p:ℚ) := by positivity
      rw [div_le_iff₀ hden]
      nlinarith
    have hlow : (15/17:ℚ) ≤ 1 - DeltaNearRatio p 18 := by linarith
    calc
      1 / (1 - DeltaNearRatio p 18) ≤ 1 / (15/17:ℚ) :=
        one_div_le_one_div_of_le (by norm_num) hlow
      _ = 17/15 := by norm_num
  have htail_nonneg : 0 ≤ 1 / (1 - DeltaNearRatio p 18) := by
    have hq1 := DeltaNearRatio_lt_one_of_le_20 p (R := (18:ℚ))
      (by norm_num) (by omega)
    have hpos : (0:ℚ) < 1 - DeltaNearRatio p 18 := by linarith
    exact one_div_nonneg.mpr hpos.le
  have hmain :
      ((1152/3125) * (18:ℚ) * (p:ℚ)
          / ((((p-1 : Nat) : ℚ) * ((p-2 : Nat) : ℚ))))
        ≤ 13 / 250 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p),
      Nat.cast_sub (by omega : 2 ≤ p)]
    change
      (1152 / 3125 : ℚ) * 18 * (p:ℚ) /
          (((p:ℚ) - 1) * ((p:ℚ) - 2)) ≤ 13 / 250
    have hden' : (0:ℚ) < ((p:ℚ)-1) * ((p:ℚ)-2) := by nlinarith
    rw [div_le_iff₀ hden']
    nlinarith
  unfold DeltaNearGeomBound
  calc
    ((1152/3125) * (18:ℚ) * (p:ℚ)
        / ((((p-1 : Nat) : ℚ) * ((p-2 : Nat) : ℚ)))
      * (1 / (1 - DeltaNearRatio p 18)))
      ≤ (13 / 250) * (17/15) :=
        mul_le_mul hmain htail htail_nonneg (by norm_num)
    _ ≤ 59 / 1000 := by norm_num

theorem DeltaRat_le_three_fiftieth_of_le_eighteen
    (p : Nat) {N : ℚ} (hN : 0 ≤ N)
    (hN18 : N ≤ 18 * (p:ℚ)) (hp : 134 ≤ p) :
    DeltaRat p N ≤ 3 / 50 := by
  have hN20 : N ≤ 20 * (p:ℚ) := by
    have hp_nonneg : 0 ≤ (p:ℚ) := Nat.cast_nonneg p
    exact hN18.trans (by nlinarith)
  have hsplit := DeltaRat_le_nearGeomBound_add_far p
    hN (by norm_num : (0:ℚ) ≤ 18) hN18 (by omega : 8 ≤ p)
    (DeltaNearRatio_lt_one_of_le_20 p (R := (18:ℚ)) (by norm_num) (by omega))
  have hnear := DeltaNearGeomBound_le_59_1000_of_ge_134 p hp
  have hfar := DeltaRatFar_le_one_thousand_of_ge_134 p hN hN20 hp
  calc
    DeltaRat p N ≤ DeltaNearGeomBound p 18 + DeltaRatFar p N := hsplit
    _ ≤ 59 / 1000 + 1 / 1000 := add_le_add hnear hfar
    _ = 3 / 50 := by norm_num

private theorem DeltaRatFarTermBound_61_le_inv_linear :
    DeltaRatFarTermBound 61 ≤ 1 / (12000 * (61:ℚ)) := by
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
    ≤ 1 / (12000 * (61:ℚ))
  calc
    (9/5:ℚ) * (16/25)^61 * (80*(61:ℚ))^60
        / (((61).factorial : ℚ) * ((121).factorial : ℚ))
        ≤ (9/5:ℚ) * (16/25)^61 * (80*(61:ℚ))^60
            / (((25*(61:ℚ))/68)^61 * ((25*(121:ℚ))/68)^121) := by
          exact div_le_div_of_nonneg_left hnum_nonneg hden_pos hden_lb
    _ ≤ 1 / (12000 * (61:ℚ)) := by norm_num

theorem DeltaRatFarTermBound_le_inv_linear (r : Nat) (hr : 61 ≤ r) :
    DeltaRatFarTermBound r ≤ 1 / (12000 * (r:ℚ)) := by
  suffices h : ∀ k : Nat,
      DeltaRatFarTermBound (61+k) ≤ 1 / (12000 * ((61+k : Nat) : ℚ)) by
    obtain ⟨k, rfl⟩ : ∃ k, r = 61 + k := ⟨r - 61, by omega⟩
    exact h k
  intro k
  induction k with
  | zero =>
      simpa using DeltaRatFarTermBound_61_le_inv_linear
  | succ k ih =>
      have hstep := DeltaRatFarTermBound_succ_le_half (61+k) (by omega : 34 ≤ 61+k)
      have hden₁ : (0:ℚ) < 12000 * ((61+k : Nat) : ℚ) := by positivity
      have hden₂ : (0:ℚ) < 12000 * ((61+(k+1) : Nat) : ℚ) := by positivity
      calc
        DeltaRatFarTermBound (61 + (k+1))
            = DeltaRatFarTermBound ((61+k)+1) := by rw [Nat.add_assoc]
        _ ≤ DeltaRatFarTermBound (61+k) * (1/2) := hstep
        _ ≤ (1 / (12000 * ((61+k : Nat) : ℚ))) * (1/2) := by
              exact mul_le_mul_of_nonneg_right ih (by norm_num)
        _ ≤ 1 / (12000 * ((61+(k+1) : Nat) : ℚ)) := by
              field_simp [ne_of_gt hden₁, ne_of_gt hden₂]
              norm_num
              have hk0 : (0:ℚ) ≤ k := by exact_mod_cast Nat.zero_le k
              nlinarith

theorem DeltaRatFar_le_inv_start (p : Nat) {N : ℚ}
    (hN : 0 ≤ N) (hN20 : N ≤ 20 * (p:ℚ)) (hp : 240 ≤ p) :
    DeltaRatFar p N ≤ 1 / (6000 * ((p/4 + 1 : Nat) : ℚ)) := by
  have htwo := DeltaRatFar_le_two_first p hN hN20 (by omega : 132 ≤ p)
  have hfirst := DeltaRatFarTermBound_le_inv_linear (p/4 + 1) (by omega)
  have hden : (0:ℚ) < 12000 * ((p/4 + 1 : Nat) : ℚ) := by positivity
  calc
    DeltaRatFar p N ≤ 2 * DeltaRatFarTermBound (p/4 + 1) := htwo
    _ ≤ 2 * (1 / (12000 * ((p/4 + 1 : Nat) : ℚ))) := by
          exact mul_le_mul_of_nonneg_left hfirst (by norm_num)
    _ = 1 / (6000 * ((p/4 + 1 : Nat) : ℚ)) := by
          field_simp [ne_of_gt hden]
          ring

theorem DeltaRatFar_le_inv_m (p m : Nat) {N : ℚ}
    (hN : 0 ≤ N) (hN20 : N ≤ 20 * (p:ℚ))
    (hm : 361 ≤ m) (hpm : 2*m ≤ 3*p) :
    DeltaRatFar p N ≤ 1 / (1000 * (m:ℚ)) := by
  have hp : 240 ≤ p := by omega
  have hstart := DeltaRatFar_le_inv_start p hN hN20 hp
  have hmle : m ≤ 6 * (p/4 + 1) := by omega
  have hden_le :
      1000 * (m:ℚ) ≤ 6000 * ((p/4 + 1 : Nat) : ℚ) := by
    have hnat : 1000 * m ≤ 6000 * (p/4 + 1) := by omega
    exact_mod_cast hnat
  have hden_pos : (0:ℚ) < 1000 * (m:ℚ) := by positivity
  exact hstart.trans (one_div_le_one_div_of_le hden_pos hden_le)

theorem DeltaNearGeomBound_le_final_range (p m : Nat)
    (hm : 361 ≤ m) (hpm : 2*m ≤ 3*p) :
    DeltaNearGeomBound p 20 ≤ (196416/15625) / (m:ℚ) := by
  have hp241 : 241 ≤ p := by omega
  have hpQ : (0:ℚ) < p := by exact_mod_cast (by omega : 0 < p)
  have hmQ : (0:ℚ) < m := by exact_mod_cast (by omega : 0 < m)
  have hp241Q : (241:ℚ) ≤ p := by exact_mod_cast hp241
  have hpmQ : (2:ℚ) * m ≤ 3 * (p:ℚ) := by exact_mod_cast hpm
  have hprod :
      20 * (m:ℚ) * (p:ℚ) ≤ 31 * ((p:ℚ)-1) * ((p:ℚ)-2) := by
    have hmle : (m:ℚ) ≤ (3/2) * (p:ℚ) := by nlinarith
    have hleft : 20 * (m:ℚ) * (p:ℚ) ≤ 30 * (p:ℚ) * (p:ℚ) := by
      have hcoeff : 20 * (m:ℚ) ≤ 30 * (p:ℚ) := by nlinarith
      exact mul_le_mul_of_nonneg_right hcoeff (le_of_lt hpQ)
    have hp93 : (93:ℚ) ≤ p := by nlinarith
    have hpoly_nonneg : 0 ≤ (p:ℚ) * ((p:ℚ) - 93) := by
      exact mul_nonneg (le_of_lt hpQ) (by linarith)
    have hright : 30 * (p:ℚ) * (p:ℚ)
        ≤ 31 * ((p:ℚ)-1) * ((p:ℚ)-2) := by
      nlinarith
    exact hleft.trans hright
  have hpden :
      (p:ℚ) / ((((p-1 : Nat) : ℚ) * ((p-2 : Nat) : ℚ)))
        ≤ 31 / (20 * (m:ℚ)) := by
    have hden_pos :
        (0:ℚ) < ((p:ℚ)-1) * ((p:ℚ)-2) := by
      nlinarith
    have hmden_pos : (0:ℚ) < 20 * (m:ℚ) := by positivity
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_sub (by omega : 2 ≤ p)]
    change (p:ℚ) / (((p:ℚ)-1) * ((p:ℚ)-2)) ≤ 31 / (20 * (m:ℚ))
    rw [div_le_div_iff₀ hden_pos hmden_pos]
    nlinarith
  have htail :
      1 / (1 - DeltaNearRatio p 20) ≤ 11/10 := by
    have hqle : DeltaNearRatio p 20 ≤ 1/11 := by
      unfold DeltaNearRatio
      have hden_pos : (0:ℚ) < 75 * (p:ℚ) := by positivity
      rw [div_le_iff₀ hden_pos]
      nlinarith
    have hlow : (10/11:ℚ) ≤ 1 - DeltaNearRatio p 20 := by linarith
    calc
      1 / (1 - DeltaNearRatio p 20) ≤ 1 / (10/11:ℚ) :=
        one_div_le_one_div_of_le (by norm_num) hlow
      _ = 11/10 := by norm_num
  have htail_nonneg : 0 ≤ 1 / (1 - DeltaNearRatio p 20) := by
    have hq1 := DeltaNearRatio_lt_one_of_le_20 p (R := (20:ℚ)) (by norm_num) (by omega)
    have hpos : (0:ℚ) < 1 - DeltaNearRatio p 20 := by linarith
    exact one_div_nonneg.mpr hpos.le
  have hmain :
      ((1152/3125) * (20:ℚ) * (p:ℚ)
          / ((((p-1 : Nat) : ℚ) * ((p-2 : Nat) : ℚ))))
        ≤ ((1152/3125) * (20:ℚ)) * (31 / (20 * (m:ℚ))) := by
    calc
      ((1152/3125) * (20:ℚ) * (p:ℚ)
          / ((((p-1 : Nat) : ℚ) * ((p-2 : Nat) : ℚ))))
          = ((1152/3125) * (20:ℚ))
              * ((p:ℚ) / ((((p-1 : Nat) : ℚ) * ((p-2 : Nat) : ℚ)))) := by ring
      _ ≤ ((1152/3125) * (20:ℚ)) * (31 / (20 * (m:ℚ))) := by
          exact mul_le_mul_of_nonneg_left hpden (by norm_num)
  have hmain_nonneg :
      0 ≤ ((1152/3125) * (20:ℚ)) * (31 / (20 * (m:ℚ))) := by
    positivity
  unfold DeltaNearGeomBound
  calc
    ((1152/3125) * (20:ℚ) * (p:ℚ)
        / ((((p-1 : Nat) : ℚ) * ((p-2 : Nat) : ℚ)))
      * (1 / (1 - DeltaNearRatio p 20)))
        ≤ (((1152/3125) * (20:ℚ)) * (31 / (20 * (m:ℚ)))) * (11/10) := by
          exact mul_le_mul hmain htail htail_nonneg hmain_nonneg
    _ = (196416/15625) / (m:ℚ) := by
          field_simp [ne_of_gt hmQ]
          ring

theorem DeltaRat_le_final_envelope (p m : Nat) {N : ℚ}
    (hN : 0 ≤ N) (hN40 : N ≤ (40/3) * (m:ℚ))
    (hm : 361 ≤ m) (hpm : 2*m ≤ 3*p) :
    DeltaRat p N ≤ (66/5) / (m:ℚ) := by
  have hp : 241 ≤ p := by omega
  have hN20 : N ≤ 20 * (p:ℚ) := by
    have hpmQ : (40/3:ℚ) * (m:ℚ) ≤ 20 * (p:ℚ) := by
      have hpmQ' : (2:ℚ) * m ≤ 3 * (p:ℚ) := by exact_mod_cast hpm
      nlinarith
    exact hN40.trans hpmQ
  have hsplit := DeltaRat_le_nearGeomBound_add_far p
    hN (by norm_num : (0:ℚ) ≤ 20) hN20 (by omega : 8 ≤ p)
    (DeltaNearRatio_lt_one_of_le_20 p (R := (20:ℚ)) (by norm_num) (by omega))
  have hnear := DeltaNearGeomBound_le_final_range p m hm hpm
  have hfar := DeltaRatFar_le_inv_m p m hN hN20 hm hpm
  calc
    DeltaRat p N ≤ DeltaNearGeomBound p 20 + DeltaRatFar p N := hsplit
    _ ≤ (196416/15625) / (m:ℚ) + 1 / (1000 * (m:ℚ)) :=
          add_le_add hnear hfar
    _ ≤ (66/5) / (m:ℚ) := by
          have hmQ : (0:ℚ) < m := by exact_mod_cast (by omega : 0 < m)
          field_simp [ne_of_gt hmQ]
          norm_num

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

/-- Closed factorial version of one residual block is dominated by the
corresponding rationalized Δ block after multiplying back by `N c_p`.

This is the closed-composition part of
`EminusResidualBlock_le_Nc_mul_DeltaRatTerm`, exposed separately so later
large-tail estimates can reuse the factorial block without routing through
`Gcomp`. -/
theorem EminusResidualClosedBlock_le_Nc_mul_DeltaRatTerm
    {p r : Nat} {N : ℚ} (hN : 0 ≤ N) (hp : 2 ≤ p) (hr : 1 ≤ r)
    (_hrp : 2*r ≤ p) :
    (N*(4/25))^r * 6^p
        * (4^(r-1) * ((p - 2*r + 1).factorial : ℚ))
        / (r.factorial : ℚ)
      ≤ N * c p * DeltaRatTerm p N r := by
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
  have hrf : ((r.factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have hpf : (((p-1).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have hpowN : N^r = N * N^(r-1) := by
    cases r with
    | zero => omega
    | succ k => simp [pow_succ, mul_comm]
  have halg :
      (N*(4/25))^r * 6^p
            * (4^(r-1) * ((p - 2*r + 1).factorial : ℚ))
            / (r.factorial : ℚ)
        =
      N * ((5/36) * (6:ℚ)^p * ((p-1).factorial : ℚ))
        * DeltaRatTerm p N r := by
    unfold DeltaRatTerm
    rw [mul_pow, hpowN]
    field_simp [hrf, hpf]
  rw [halg]
  exact hNc

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

/-- Final rationalized `Eminus` envelope in the sign-lock range:
`66/5 = 13.2`. -/
theorem Eminus_normalized_residual_le_final
    {p m : Nat} {N : ℚ} (hN : 0 < N)
    (hN40 : N ≤ (40/3) * (m:ℚ))
    (hm : 361 ≤ m) (hpm : 2*m ≤ 3*p) :
    |Eminus N p / (-N * c p) - 1| ≤ (66/5) / (m:ℚ) := by
  have hp : 2 ≤ p := by omega
  exact (Eminus_normalized_residual_le_DeltaRat hN hp).trans
    (DeltaRat_le_final_envelope p m hN.le hN40 hm hpm)

end Prop51
