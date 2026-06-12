/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Ordered factorial compositions (paper Lemma 3.1)

`G_r(p) = Σ_{j_1+⋯+j_r = p, j_i ≥ 2} Π_i (j_i - 1)!`, defined here in
recursive convolution form (which is also how it is consumed: the
coefficients of `H(t)^r`, `H = Σ_{j≥2} c_j t^j`, satisfy the same
recursion).  The bound

  `G_r(p) ≤ 4^{r-1} (p - 2r + 1)!`   (`p ≥ 2r`)

is the engine of the nonlinear-block estimates: each extra block costs a
factor `4/(p·…)` rather than a factorial.  The induction step reduces to
`Σ_{i=1}^{t-1} i! (t-i)! ≤ 4 (t-1)!`, which is the reciprocal-binomial
bound of `Prop51/BinomRecip.lean` in disguise.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import Prop51.BinomRecip

namespace Prop51

/-- Ordered factorial compositions, in convolution form:
`Gcomp 0 p = [p = 0]`, and
`Gcomp (r+1) p = Σ_{j=2}^{p} (j-1)! · Gcomp r (p-j)`. -/
def Gcomp : Nat → Nat → ℚ
  | 0, p => if p = 0 then 1 else 0
  | (r+1), p => ∑ j ∈ Finset.Icc 2 p, ((j-1).factorial : ℚ) * Gcomp r (p-j)

theorem Gcomp_nonneg (r : Nat) : ∀ p : Nat, 0 ≤ Gcomp r p := by
  induction r with
  | zero =>
      intro p
      simp only [Gcomp]
      split <;> norm_num
  | succ r ih =>
      intro p
      simp only [Gcomp]
      exact Finset.sum_nonneg fun j _ =>
        mul_nonneg (Nat.cast_nonneg _) (ih (p-j))

/-- Compositions of `p < 2r` into `r` parts `≥ 2` do not exist. -/
theorem Gcomp_eq_zero (r : Nat) : ∀ p : Nat, 1 ≤ r → p < 2*r →
    Gcomp r p = 0 := by
  induction r with
  | zero => intro p h _; omega
  | succ r ih =>
      intro p _ hp
      simp only [Gcomp]
      rcases Nat.eq_zero_or_pos r with rfl | hr1
      · have hempty : Finset.Icc 2 p = ∅ := Finset.Icc_eq_empty (by omega)
        rw [hempty, Finset.sum_empty]
      · refine Finset.sum_eq_zero fun j hj => ?_
        obtain ⟨h2, hjp⟩ := Finset.mem_Icc.mp hj
        rw [ih (p-j) hr1 (by omega), mul_zero]

/-- One block: `Gcomp 1 p = (p-1)!` for `p ≥ 2` (only `j = p` survives). -/
theorem Gcomp_one (p : Nat) (hp : 2 ≤ p) :
    Gcomp 1 p = ((p-1).factorial : ℚ) := by
  simp only [Gcomp]
  have h0 : ∀ j ∈ Finset.Icc 2 p, j ≠ p →
      ((j-1).factorial : ℚ) * (if p-j = 0 then (1:ℚ) else 0) = 0 := by
    intro j hj hne
    obtain ⟨h2, hjp⟩ := Finset.mem_Icc.mp hj
    rw [if_neg (by omega : ¬ p - j = 0), mul_zero]
  rw [Finset.sum_eq_single_of_mem p (Finset.mem_Icc.mpr ⟨hp, le_rfl⟩) h0,
      Nat.sub_self, if_pos rfl, mul_one]

/-- The factorial-pair sum: `Σ_{i=1}^{t-1} i!(t-i)! ≤ 4(t-1)!` for `t ≥ 2`
(termwise `i!(t-i)! = t!/C(t,i)`, then the reciprocal-binomial bound). -/
theorem sum_factorial_mul_factorial_le (t : Nat) (ht : 2 ≤ t) :
    ∑ i ∈ Finset.Ico 1 t, (i.factorial : ℚ) * ((t-i).factorial : ℚ)
      ≤ 4 * ((t-1).factorial : ℚ) := by
  have hconv : ∀ i ∈ Finset.Ico 1 t,
      (i.factorial : ℚ) * ((t-i).factorial : ℚ)
        = (t.factorial : ℚ) * ((1:ℚ)/(t.choose i)) := by
    intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hi
    have hC : ((t.choose i : ℕ):ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega : i ≤ t)).ne'
    have hcf : ((t.choose i : ℕ):ℚ) * (i.factorial : ℚ) * ((t-i).factorial : ℚ)
        = (t.factorial : ℚ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by omega : i ≤ t)
    rw [mul_one_div, eq_div_iff hC]
    linear_combination hcf
  rw [Finset.sum_congr rfl hconv, ← Finset.mul_sum]
  have hft : (0:ℚ) ≤ (t.factorial : ℚ) := Nat.cast_nonneg _
  have htf : (t.factorial : ℚ) = (t:ℚ) * ((t-1).factorial : ℚ) := by
    exact_mod_cast (Nat.mul_factorial_pred (by omega : t ≠ 0)).symm
  have htne : (t:ℚ) ≠ 0 := by
    exact_mod_cast (by omega : t ≠ 0)
  calc (t.factorial : ℚ) * ∑ i ∈ Finset.Ico 1 t, (1:ℚ)/(t.choose i)
      ≤ (t.factorial : ℚ) * (4/(t:ℚ)) :=
        mul_le_mul_of_nonneg_left (sum_choose_recip_le t ht) hft
    _ = 4 * ((t-1).factorial : ℚ) := by
        rw [htf]
        field_simp

/-- **Paper Lemma 3.1**: `G_r(p) ≤ 4^{r-1} (p-2r+1)!` for `p ≥ 2r`, `r ≥ 1`. -/
theorem Gcomp_le (r : Nat) (hr : 1 ≤ r) : ∀ p : Nat, 2*r ≤ p →
    Gcomp r p ≤ 4^(r-1) * ((p - 2*r + 1).factorial : ℚ) := by
  induction r, hr using Nat.le_induction with
  | base =>
      intro p hp
      rw [Gcomp_one p (by omega), show p - 2*1 + 1 = p-1 by omega]
      norm_num
  | succ r hr1 ih =>
      intro p hp
      have ht2 : 2 ≤ p - 2*r := by omega
      have htrunc : Gcomp (r+1) p
          = ∑ j ∈ Finset.Icc 2 (p - 2*r),
              ((j-1).factorial : ℚ) * Gcomp r (p-j) := by
        simp only [Gcomp]
        symm
        apply Finset.sum_subset
        · intro j hj
          obtain ⟨h2, hle⟩ := Finset.mem_Icc.mp hj
          exact Finset.mem_Icc.mpr ⟨h2, by omega⟩
        · intro j hj hnot
          obtain ⟨h2, hjp⟩ := Finset.mem_Icc.mp hj
          have hgt : p - 2*r < j := by
            by_contra hle
            exact hnot (Finset.mem_Icc.mpr ⟨h2, by omega⟩)
          rw [Gcomp_eq_zero r (p-j) hr1 (by omega), mul_zero]
      have hterm : ∀ j ∈ Finset.Icc 2 (p - 2*r),
          ((j-1).factorial : ℚ) * Gcomp r (p-j)
            ≤ ((j-1).factorial : ℚ)
              * (4^(r-1) * ((p-j - 2*r + 1).factorial : ℚ)) := by
        intro j hj
        obtain ⟨h2, hle⟩ := Finset.mem_Icc.mp hj
        exact mul_le_mul_of_nonneg_left (ih (p-j) (by omega))
          (Nat.cast_nonneg _)
      have hreindex : ∑ j ∈ Finset.Icc 2 (p - 2*r),
          ((j-1).factorial : ℚ) * ((p-j - 2*r + 1).factorial : ℚ)
          = ∑ i ∈ Finset.Ico 1 (p - 2*r),
              (i.factorial : ℚ) * (((p - 2*r) - i).factorial : ℚ) := by
        have hIccIco : Finset.Icc 2 (p - 2*r) = Finset.Ico 2 (p - 2*r + 1) := by
          ext x
          simp only [Finset.mem_Icc, Finset.mem_Ico]
          omega
        rw [hIccIco, Finset.sum_Ico_eq_sum_range,
            Finset.sum_Ico_eq_sum_range,
            show p - 2*r + 1 - 2 = p - 2*r - 1 by omega]
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k < p - 2*r - 1 := Finset.mem_range.mp hk
        rw [show 2+k-1 = 1+k by omega,
            show p-(2+k) - 2*r + 1 = (p - 2*r) - (1+k) by omega]
      have hpow : (4:ℚ)^(r-1) * 4 = 4^r := by
        rw [← pow_succ, show r-1+1 = r by omega]
      calc Gcomp (r+1) p
          = ∑ j ∈ Finset.Icc 2 (p - 2*r),
              ((j-1).factorial : ℚ) * Gcomp r (p-j) := htrunc
        _ ≤ ∑ j ∈ Finset.Icc 2 (p - 2*r),
              ((j-1).factorial : ℚ)
                * (4^(r-1) * ((p-j - 2*r + 1).factorial : ℚ)) :=
            Finset.sum_le_sum hterm
        _ = 4^(r-1) * ∑ j ∈ Finset.Icc 2 (p - 2*r),
              ((j-1).factorial : ℚ) * ((p-j - 2*r + 1).factorial : ℚ) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = 4^(r-1) * ∑ i ∈ Finset.Ico 1 (p - 2*r),
              (i.factorial : ℚ) * (((p - 2*r) - i).factorial : ℚ) := by
            rw [hreindex]
        _ ≤ 4^(r-1) * (4 * ((p - 2*r - 1).factorial : ℚ)) := by
            apply mul_le_mul_of_nonneg_left
              (sum_factorial_mul_factorial_le (p - 2*r) ht2) (by positivity)
        _ = 4^((r+1)-1) * ((p - 2*(r+1) + 1).factorial : ℚ) := by
            rw [show (r+1)-1 = r by omega,
                show p - 2*(r+1) + 1 = p - 2*r - 1 by omega, ← hpow]
            ring

end Prop51
