/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Powers of `H` and the exponential formula (paper §§3–4 machinery)

Let `H(t) = Σ_{j≥2} c_j t^j` be the nonlinear part of `log C`.  This file
provides the bridge between the recurrence world (`expCoeff`) and the
block decomposition of the paper:

* the **exponential formula** (`expCoeff_eq_sum_pow`): for `L 0 = 0`,
  `expCoeff L p = Σ_{r=0}^{p} [t^p]((Σ L_j t^j)^r) / r!` — a finite
  identity, proved from the `θ`-recurrence;
* the **power bound** (`abs_coeff_pow_le`): if `L` is supported on degrees
  `≥ 2` with `|L_j| ≤ M·6^j (j-1)!`, then
  `|[t^p](Σ L_j t^j)^r| ≤ M^r 6^p G_r(p)` — the ordered-composition
  estimate of `Prop51/Composition.lean` in its consumed form;
* the specialization to `H` (`hpow`, `abs_hpow_le`) and the exact
  **block split** of `E⁻_p(N) = [t^p] exp(-N·H)`
  (`Eminus_split`): `E⁻_p = -N c_p + Σ_{r=2}^{p} (-N)^r [t^p]H^r / r!`,
  with the residual bounded by `Σ_{r≥2} (4N/25)^r 6^p G_r(p)/r!`
  (`Eminus_residual_le`).  The numeric Δ-envelope (paper Lemma 4.1) is
  derived from these in `Prop51/Envelope.lean`.
-/

import Prop51.DNorm
import Prop51.Composition

namespace Prop51

open PowerSeries

/-! ## The power rule for `θ` -/

theorem theta_pow_succ (G : ℚ⟦X⟧) : ∀ r : Nat,
    theta (G ^ (r+1)) = (PowerSeries.C ((r+1 : Nat) : ℚ)) * (G ^ r * theta G)
  | 0 => by
      simp [pow_one]
  | (r+1) => by
      rw [pow_succ, theta_mul, theta_pow_succ G r,
          show ((r+1+1 : Nat) : ℚ) = ((r+1 : Nat) : ℚ) + 1 by push_cast; ring,
          map_add, map_one]
      ring

/-! ## Coefficients of powers: vanishing and the `θ`-recurrence -/

/-- Powers of a series with zero constant term have vanishing low
coefficients: `[t^p] G^r = 0` for `p < r`. -/
theorem coeff_pow_eq_zero (L : Nat → ℚ) (hL0 : L 0 = 0) :
    ∀ r p : Nat, p < r → coeff p ((mk L : ℚ⟦X⟧) ^ r) = 0 := by
  intro r
  induction r with
  | zero => intro p h; omega
  | succ r ih =>
      intro p h
      rw [pow_succ', coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      refine Finset.sum_eq_zero fun k hk => ?_
      have hkp : k ≤ p := by
        have := Finset.mem_range.mp hk
        omega
      rcases Nat.eq_zero_or_pos k with rfl | hk1
      · simp [hL0]
      · rw [ih (p-k) (by omega), mul_zero]

/-- The `θ`-recurrence for coefficients of powers:
`p·[t^p]G^{r+1} = (r+1)·Σ_k (k L_k)·[t^{p-k}]G^r`. -/
theorem coeff_pow_succ_mul (L : Nat → ℚ) (r p : Nat) :
    (p : ℚ) * coeff p ((mk L : ℚ⟦X⟧) ^ (r+1))
      = ((r+1 : Nat) : ℚ) * ∑ k ∈ Finset.range (p+1),
          ((k : ℚ) * L k) * coeff (p-k) ((mk L : ℚ⟦X⟧) ^ r) := by
  have h : coeff p (theta ((mk L : ℚ⟦X⟧) ^ (r+1)))
      = coeff p ((PowerSeries.C ((r+1 : Nat) : ℚ))
          * (theta (mk L) * (mk L : ℚ⟦X⟧) ^ r)) := by
    rw [theta_pow_succ (mk L) r, mul_comm ((mk L : ℚ⟦X⟧) ^ r) (theta (mk L))]
  rw [coeff_theta, coeff_C_mul, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp only [coeff_theta, coeff_mk] at h
  exact h

/-! ## The exponential formula -/

/-- **The exponential formula** as a finite coefficient identity: for
`L 0 = 0`,
`expCoeff L p = Σ_{r=0}^{p} [t^p]((mk L)^r)/r!`. -/
theorem expCoeff_eq_sum_pow (L : Nat → ℚ) (hL0 : L 0 = 0) (p : Nat) :
    expCoeff L p
      = ∑ r ∈ Finset.range (p+1),
          coeff p ((mk L : ℚ⟦X⟧) ^ r) / (r.factorial : ℚ) := by
  induction p using Nat.strong_induction_on with
  | _ p ih =>
      match p with
      | 0 =>
          rw [expCoeff_zero, Finset.sum_range_one, pow_zero, coeff_one]
          norm_num [show Nat.factorial 0 = 1 from rfl]
      | (n+1) =>
          have hne : ((n+1 : Nat) : ℚ) ≠ 0 := by
            exact_mod_cast Nat.succ_ne_zero n
          apply mul_left_cancel₀ hne
          rw [expCoeff_succ_mul]
          -- truncated partial sums equal `expCoeff` below `n+1`
          have htrunc : ∀ t : Nat, t < n+1 →
              ∑ r ∈ Finset.range (n+1),
                  coeff (n-t) ((mk L : ℚ⟦X⟧) ^ r) / (r.factorial : ℚ)
                = expCoeff L (n-t) := by
            intro t ht
            rw [ih (n-t) (by omega)]
            symm
            apply Finset.sum_subset
            · intro x hx
              rw [Finset.mem_range] at hx ⊢
              omega
            · intro r hr hnot
              rw [Finset.mem_range] at hr
              rw [Finset.mem_range] at hnot
              rw [coeff_pow_eq_zero L hL0 r (n-t) (by omega), zero_div]
          -- the `r = 0` term vanishes at degree `n+1`
          have e0 : coeff (n+1) ((mk L : ℚ⟦X⟧) ^ 0) = 0 := by
            rw [pow_zero, coeff_one]
            simp
          calc ∑ t ∈ Finset.range (n+1),
                ((t+1 : Nat) : ℚ) * L (t+1) * expCoeff L (n-t)
              = ∑ t ∈ Finset.range (n+1), ((t+1 : Nat) : ℚ) * L (t+1)
                  * ∑ r ∈ Finset.range (n+1),
                      coeff (n-t) ((mk L : ℚ⟦X⟧) ^ r) / (r.factorial : ℚ) := by
                refine Finset.sum_congr rfl fun t ht => ?_
                rw [htrunc t (Finset.mem_range.mp ht)]
            _ = ∑ t ∈ Finset.range (n+1), ∑ r ∈ Finset.range (n+1),
                  ((t+1 : Nat) : ℚ) * L (t+1)
                    * (coeff (n-t) ((mk L : ℚ⟦X⟧) ^ r) / (r.factorial : ℚ)) := by
                refine Finset.sum_congr rfl fun t _ => ?_
                rw [Finset.mul_sum]
            _ = ∑ r ∈ Finset.range (n+1), ∑ t ∈ Finset.range (n+1),
                  ((t+1 : Nat) : ℚ) * L (t+1)
                    * (coeff (n-t) ((mk L : ℚ⟦X⟧) ^ r) / (r.factorial : ℚ)) :=
                Finset.sum_comm
            _ = ∑ r ∈ Finset.range (n+1),
                  ((n+1 : Nat) : ℚ) * coeff (n+1) ((mk L : ℚ⟦X⟧) ^ (r+1))
                    / ((r+1).factorial : ℚ) := by
                refine Finset.sum_congr rfl fun r _ => ?_
                rw [coeff_pow_succ_mul]
                -- (r+1)·Σ_k (k L_k)·coeff_{n+1-k}(G^r) / (r+1)!
                -- = Σ_t ((t+1) L_{t+1})·coeff_{n-t}(G^r)/r!
                conv_rhs => rw [Finset.sum_range_succ']
                simp only [Nat.cast_zero, zero_mul, add_zero]
                have hfac : ((r+1).factorial : ℚ)
                    = ((r+1 : Nat) : ℚ) * (r.factorial : ℚ) := by
                  push_cast [Nat.factorial_succ]
                  ring
                rw [Finset.mul_sum, hfac, Finset.sum_div]
                refine Finset.sum_congr rfl fun t _ => ?_
                rw [show n+1-(t+1) = n-t by omega]
                have hrne : ((r+1 : Nat) : ℚ) ≠ 0 := by
                  exact_mod_cast Nat.succ_ne_zero r
                have hfne : (r.factorial : ℚ) ≠ 0 := by
                  exact_mod_cast r.factorial_pos.ne'
                field_simp
            _ = ((n+1 : Nat) : ℚ) * ∑ r ∈ Finset.range (n+2),
                  coeff (n+1) ((mk L : ℚ⟦X⟧) ^ r) / (r.factorial : ℚ) := by
                rw [Finset.mul_sum]
                conv_rhs => rw [Finset.sum_range_succ']
                rw [e0]
                simp only [zero_div, mul_zero, add_zero]
                refine Finset.sum_congr rfl fun r _ => ?_
                ring

/-! ## The power bound through `Gcomp` -/

/-- Base-parameterized composition bound for powers.

If `L` vanishes below degree 2 and
`|L_j| ≤ M * B^j * (j-1)!` for a positive base `B`, then the coefficient of
`(Σ L_j t^j)^r` is bounded by `M^r * B^p * Gcomp r p`.  The public
`abs_coeff_pow_le` below is the specialization `B = 6`; the sharp solo route
uses this version with `B = 3`. -/
theorem abs_coeff_pow_le_base (L : Nat → ℚ) (M B : ℚ) (hB : 0 < B)
    (hL0 : ∀ j, j < 2 → L j = 0)
    (hLb : ∀ j, 2 ≤ j → |L j| ≤ M * (B^j * ((j-1).factorial : ℚ))) :
    ∀ r p : Nat, |coeff p ((mk L : ℚ⟦X⟧) ^ r)| ≤ M^r * B^p * Gcomp r p := by
  have hM : 0 ≤ M := by
    have h2 := hLb 2 le_rfl
    rw [show (2:ℕ)-1 = 1 from rfl, show Nat.factorial 1 = 1 from rfl] at h2
    norm_num at h2
    have habs : (0:ℚ) ≤ |L 2| := abs_nonneg _
    have hB2 : 0 < B^2 := by positivity
    nlinarith [h2, habs, hB2]
  intro r
  induction r with
  | zero =>
      intro p
      simp only [pow_zero, one_mul]
      match p with
      | 0 => simp [Gcomp]
      | (q+1) =>
          rw [coeff_one]
          simp only [Gcomp]
          norm_num
  | succ r ih =>
      intro p
      rw [pow_succ', coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      have habs : |∑ k ∈ Finset.range (p+1),
            coeff k (mk L : ℚ⟦X⟧) * coeff (p-k) ((mk L : ℚ⟦X⟧) ^ r)|
          ≤ ∑ k ∈ Finset.range (p+1),
              |L k| * |coeff (p-k) ((mk L : ℚ⟦X⟧) ^ r)| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [coeff_mk, abs_mul]
      refine habs.trans ?_
      have hdrop : ∑ k ∈ Finset.range (p+1),
            |L k| * |coeff (p-k) ((mk L : ℚ⟦X⟧) ^ r)|
          = ∑ k ∈ Finset.Icc 2 p,
              |L k| * |coeff (p-k) ((mk L : ℚ⟦X⟧) ^ r)| := by
        symm
        apply Finset.sum_subset
        · intro x hx
          rw [Finset.mem_Icc] at hx
          rw [Finset.mem_range]
          omega
        · intro k hk hnot
          rw [Finset.mem_Icc] at hnot
          rw [Finset.mem_range] at hk
          have : L k = 0 := hL0 k (by omega)
          rw [this, abs_zero, zero_mul]
      rw [hdrop]
      have hterm : ∀ k ∈ Finset.Icc 2 p,
          |L k| * |coeff (p-k) ((mk L : ℚ⟦X⟧) ^ r)|
            ≤ (M * (B^k * ((k-1).factorial : ℚ)))
              * (M^r * B^(p-k) * Gcomp r (p-k)) := by
        intro k hk
        obtain ⟨h2, _hkp⟩ := Finset.mem_Icc.mp hk
        exact mul_le_mul (hLb k h2) (ih (p-k)) (abs_nonneg _)
          (by positivity)
      refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
      have hsplit : ∀ k ∈ Finset.Icc 2 p,
          (M * (B^k * ((k-1).factorial : ℚ)))
              * (M^r * B^(p-k) * Gcomp r (p-k))
            = M^(r+1) * B^p * (((k-1).factorial : ℚ) * Gcomp r (p-k)) := by
        intro k hk
        obtain ⟨_h2, hkp⟩ := Finset.mem_Icc.mp hk
        have hpow : B^k * B^(p-k) = B^p := by
          rw [← pow_add]
          congr 1
          omega
        rw [← hpow]
        ring
      rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum]
      have : Gcomp (r+1) p = ∑ k ∈ Finset.Icc 2 p,
          ((k-1).factorial : ℚ) * Gcomp r (p-k) := by
        simp only [Gcomp]
      rw [this]

/-- **The composition bound for powers**: if `L` vanishes below degree 2
and `|L_j| ≤ M·6^j (j-1)!`, then `|[t^p]G^r| ≤ M^r·6^p·G_r(p)`. -/
theorem abs_coeff_pow_le (L : Nat → ℚ) (M : ℚ)
    (hL0 : ∀ j, j < 2 → L j = 0)
    (hLb : ∀ j, 2 ≤ j → |L j| ≤ M * (6^j * ((j-1).factorial : ℚ))) :
    ∀ r p : Nat, |coeff p ((mk L : ℚ⟦X⟧) ^ r)| ≤ M^r * 6^p * Gcomp r p := by
  have hM : 0 ≤ M := by
    have h2 := hLb 2 le_rfl
    rw [show (2:ℕ)-1 = 1 from rfl, show Nat.factorial 1 = 1 from rfl] at h2
    norm_num at h2
    have habs : (0:ℚ) ≤ |L 2| := abs_nonneg _
    nlinarith [h2, habs]
  intro r
  induction r with
  | zero =>
      intro p
      simp only [pow_zero, one_mul]
      match p with
      | 0 => simp [Gcomp]
      | (q+1) =>
          rw [coeff_one]
          simp only [Gcomp]
          norm_num
  | succ r ih =>
      intro p
      rw [pow_succ', coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      have habs : |∑ k ∈ Finset.range (p+1),
            coeff k (mk L : ℚ⟦X⟧) * coeff (p-k) ((mk L : ℚ⟦X⟧) ^ r)|
          ≤ ∑ k ∈ Finset.range (p+1),
              |L k| * |coeff (p-k) ((mk L : ℚ⟦X⟧) ^ r)| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [coeff_mk, abs_mul]
      refine habs.trans ?_
      have hdrop : ∑ k ∈ Finset.range (p+1),
            |L k| * |coeff (p-k) ((mk L : ℚ⟦X⟧) ^ r)|
          = ∑ k ∈ Finset.Icc 2 p,
              |L k| * |coeff (p-k) ((mk L : ℚ⟦X⟧) ^ r)| := by
        symm
        apply Finset.sum_subset
        · intro x hx
          rw [Finset.mem_Icc] at hx
          rw [Finset.mem_range]
          omega
        · intro k hk hnot
          rw [Finset.mem_Icc] at hnot
          rw [Finset.mem_range] at hk
          have : L k = 0 := hL0 k (by omega)
          rw [this, abs_zero, zero_mul]
      rw [hdrop]
      have hterm : ∀ k ∈ Finset.Icc 2 p,
          |L k| * |coeff (p-k) ((mk L : ℚ⟦X⟧) ^ r)|
            ≤ (M * (6^k * ((k-1).factorial : ℚ)))
              * (M^r * 6^(p-k) * Gcomp r (p-k)) := by
        intro k hk
        obtain ⟨h2, hkp⟩ := Finset.mem_Icc.mp hk
        exact mul_le_mul (hLb k h2) (ih (p-k)) (abs_nonneg _)
          (by positivity)
      refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
      have hsplit : ∀ k ∈ Finset.Icc 2 p,
          (M * (6^k * ((k-1).factorial : ℚ)))
              * (M^r * 6^(p-k) * Gcomp r (p-k))
            = M^(r+1) * 6^p * (((k-1).factorial : ℚ) * Gcomp r (p-k)) := by
        intro k hk
        obtain ⟨h2, hkp⟩ := Finset.mem_Icc.mp hk
        have hpow : (6:ℚ)^k * (6:ℚ)^(p-k) = 6^p := by
          rw [← pow_add]
          congr 1
          omega
        rw [← hpow]
        ring
      rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum]
      have : Gcomp (r+1) p = ∑ k ∈ Finset.Icc 2 p,
          ((k-1).factorial : ℚ) * Gcomp r (p-k) := by
        simp only [Gcomp]
      rw [this]

/-! ## Specialization to `H = Σ_{j≥2} c_j t^j` -/

/-- The coefficients of the nonlinear part `H` of `log C`. -/
def Hcoef : Nat → ℚ := fun r => if 2 ≤ r then c r else 0

@[simp] theorem Hcoef_of_lt_two {r : Nat} (hr : r < 2) : Hcoef r = 0 := by
  rw [Hcoef, if_neg (by omega)]

theorem Hcoef_of_ge_two {r : Nat} (hr : 2 ≤ r) : Hcoef r = c r := by
  rw [Hcoef, if_pos hr]

/-- `hpow r p = [t^p] H(t)^r`. -/
noncomputable def hpow (r p : Nat) : ℚ := coeff p ((mk Hcoef : ℚ⟦X⟧) ^ r)

/-- The non-endpoint part of `[t^p]H(t)^2`, i.e. the terms with
`3 ≤ j ≤ p-3`. -/
def hpowTwoMiddle (p : Nat) : ℚ :=
  ∑ j ∈ Finset.Ico 3 (p-2), c j * c (p-j)

theorem hpowTwoMiddle_nonneg (p : Nat) : 0 ≤ hpowTwoMiddle p := by
  unfold hpowTwoMiddle
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (c_nonneg j) (c_nonneg (p-j))

theorem hpow_one (p : Nat) (hp : 2 ≤ p) : hpow 1 p = c p := by
  rw [hpow, pow_one, coeff_mk, Hcoef, if_pos hp]

/-- The two-block coefficient is the ordinary finite convolution of the
coefficients of `H`. -/
theorem hpow_two_eq_sum_range (p : Nat) :
    hpow 2 p = ∑ j ∈ Finset.range (p+1), Hcoef j * Hcoef (p-j) := by
  rw [hpow, pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [coeff_mk]

/-- Exact extraction of the two endpoint products in `[t^p]H(t)^2`.
For `p ≥ 5`, the endpoint pairs are distinct and the middle sum is over
`3 ≤ j ≤ p-3`, written as `Ico 3 (p-2)`.  This is the coefficient-level
form of the endpoint extraction used in the sign-lock recentering. -/
theorem hpow_two_eq_endpoints_add_middle (p : Nat) (hp : 5 ≤ p) :
    hpow 2 p =
      2 * c 2 * c (p-2) + hpowTwoMiddle p := by
  rw [hpow_two_eq_sum_range]
  have hdrop :
      (∑ j ∈ Finset.range (p+1), Hcoef j * Hcoef (p-j))
        = ∑ j ∈ Finset.Icc 2 (p-2), Hcoef j * Hcoef (p-j) := by
    symm
    apply Finset.sum_subset
    · intro j hj
      rw [Finset.mem_Icc] at hj
      rw [Finset.mem_range]
      omega
    · intro j hj hnot
      rw [Finset.mem_range] at hj
      rw [Finset.mem_Icc] at hnot
      by_cases hlt : j < 2
      · rw [Hcoef_of_lt_two hlt, zero_mul]
      · have htail : p - j < 2 := by omega
        rw [Hcoef_of_lt_two htail, mul_zero]
  rw [hdrop]
  have hIccIco : Finset.Icc 2 (p-2) = Finset.Ico 2 (p-1) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIccIco]
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 2 < p-1)]
  rw [show p-1 = (p-2)+1 by omega]
  rw [Finset.sum_Ico_succ_top (by omega : 3 ≤ p-2)]
  simp only [Hcoef_of_ge_two (by omega : 2 ≤ 2),
    Hcoef_of_ge_two (by omega : 2 ≤ p-2)]
  have hmiddle : ∀ j ∈ Finset.Ico 3 (p-2),
      Hcoef j * Hcoef (p-j) = c j * c (p-j) := by
    intro j hj
    obtain ⟨hj3, hjlt⟩ := Finset.mem_Ico.mp hj
    rw [Hcoef_of_ge_two (by omega : 2 ≤ j),
      Hcoef_of_ge_two (by omega : 2 ≤ p-j)]
  rw [Finset.sum_congr rfl hmiddle]
  rw [show p - (p - 2) = 2 by omega]
  rw [Hcoef_of_ge_two (by omega : 2 ≤ 2)]
  unfold hpowTwoMiddle
  ring_nf

theorem abs_hpow_le (r p : Nat) :
    |hpow r p| ≤ (4/25)^r * 6^p * Gcomp r p := by
  apply abs_coeff_pow_le Hcoef (4/25)
  · intro j hj
    rw [Hcoef, if_neg (by omega)]
  · intro j hj
    rw [Hcoef, if_pos hj, abs_of_nonneg (c_nonneg j)]
    have := c_ub j (by omega)
    linarith

/-- `[t^p]H^r = 0` for `p < 2r` (each block has degree ≥ 2). -/
theorem hpow_eq_zero {r p : Nat} (hr : 1 ≤ r) (hp : p < 2*r) :
    hpow r p = 0 := by
  have h := abs_hpow_le r p
  rw [Gcomp_eq_zero r p hr hp, mul_zero] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

/-! ## The block split of `E⁻` -/

/-- `E⁻_p(N) = [t^p] exp(-N H(t))`, as an `expCoeff`. -/
def Eminus (N : ℚ) (p : Nat) : ℚ := expCoeff (fun r => -N * Hcoef r) p

private theorem mk_neg_smul (N : ℚ) :
    (mk (fun r => -N * Hcoef r) : ℚ⟦X⟧)
      = PowerSeries.C (-N) * mk Hcoef := by
  ext n
  rw [coeff_mk, coeff_C_mul, coeff_mk]

/-- Coefficients of powers of the scaled series. -/
private theorem coeff_pow_scaled (N : ℚ) (r p : Nat) :
    coeff p ((mk (fun r => -N * Hcoef r) : ℚ⟦X⟧) ^ r)
      = (-N)^r * hpow r p := by
  rw [mk_neg_smul, mul_pow, ← map_pow, coeff_C_mul, hpow]

/-- **The exact block split** (paper eq. 17 territory): for `p ≥ 2`,
`E⁻_p(N) = -N c_p + Σ_{r=2}^{p} (-N)^r [t^p]H^r / r!`. -/
theorem Eminus_split (N : ℚ) (p : Nat) (hp : 2 ≤ p) :
    Eminus N p
      = -N * c p
        + ∑ r ∈ Finset.Icc 2 p, (-N)^r * hpow r p / (r.factorial : ℚ) := by
  have hL0 : (fun r => -N * Hcoef r) 0 = 0 := by
    simp only [Hcoef]
    rw [if_neg (by omega)]
    ring
  rw [Eminus, expCoeff_eq_sum_pow _ hL0 p]
  have hIcc : Finset.Icc 2 p = Finset.Ico 2 (p+1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [Finset.range_eq_Ico,
      Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < p+1),
      Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < p+1), hIcc]
  have h0 : coeff p ((mk (fun r => -N * Hcoef r) : ℚ⟦X⟧) ^ 0)
      / ((0).factorial : ℚ) = 0 := by
    rw [pow_zero, coeff_one, if_neg (by omega : ¬ p = 0)]
    simp
  have h1 : coeff p ((mk (fun r => -N * Hcoef r) : ℚ⟦X⟧) ^ 1)
      / ((1).factorial : ℚ) = -N * c p := by
    rw [coeff_pow_scaled, hpow_one p hp]
    simp [Nat.factorial]
  rw [h0, h1, zero_add]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [coeff_pow_scaled]

/-- **The residual bound**: for `N ≥ 0`, `p ≥ 2`,
`|E⁻_p(N) + N c_p| ≤ Σ_{r=2}^{p} (4N/25)^r 6^p G_r(p)/r!`. -/
theorem Eminus_residual_le (N : ℚ) (hN : 0 ≤ N) (p : Nat) (hp : 2 ≤ p) :
    |Eminus N p + N * c p|
      ≤ ∑ r ∈ Finset.Icc 2 p,
          (N*(4/25))^r * 6^p * Gcomp r p / (r.factorial : ℚ) := by
  rw [Eminus_split N p hp, show -N * c p
      + (∑ r ∈ Finset.Icc 2 p, (-N)^r * hpow r p / (r.factorial : ℚ))
      + N * c p
      = ∑ r ∈ Finset.Icc 2 p, (-N)^r * hpow r p / (r.factorial : ℚ) by ring]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro r _
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_of_nonneg hN,
      abs_of_nonneg (by positivity : (0:ℚ) ≤ ((r.factorial : ℕ) : ℚ))]
  have hfpos : (0:ℚ) < ((r.factorial : ℕ) : ℚ) := by
    exact_mod_cast r.factorial_pos
  apply div_le_div_of_nonneg_right ?_ hfpos.le
  calc N^r * |hpow r p| ≤ N^r * ((4/25)^r * 6^p * Gcomp r p) := by
        apply mul_le_mul_of_nonneg_left (abs_hpow_le r p) (by positivity)
    _ = (N*(4/25))^r * 6^p * Gcomp r p := by
        rw [mul_pow]
        ring

end Prop51
