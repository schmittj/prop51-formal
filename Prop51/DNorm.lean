/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# The `d`-normalization of the logarithmic coefficients (paper §2)

Write `c_r = 6^r (r-1)! d_r` (paper eq. 13).  This file proves the
rationalized form of the paper's Lemma 2.1:

* the recurrence `d_r = d_{r-1} + (1/r) Σ_{i} d_i d_{r-1-i} / C(r-1,i)`
  (`d_succ_succ`), hence `d` is *nondecreasing* with `d_1 = d_2 = 5/36`;
* the two-sided bound `5/36 ≤ d_r ≤ 4/25` (`d_lb`, `d_ub`);
* increment control `d_{r} - d_{r-1} ≤ (64/625)/(r(r-1))` (`d_increment`)
  and its telescoped ratio form
  `1 - (2304/3125)·s/(m(m-s)) ≤ d_{m-s}/d_m ≤ 1` (`d_ratio_lb`, `d_mono`).

## Rationalization

The paper bounds `d_r ≤ 1/(2π)` via Γ-reflection.  We avoid `π` (and all of
real analysis): with `F_r = A_r/(6^r (r-1)!)` the exact ratio
`F_{r+1}/F_r = 1 + 5/(36 r(r+1))` (from `Aseq_succ`) gives, for `r ≥ 3`,

  `F_r ≤ F_3 / (1 - (5/36)(1/3 - 1/r)) ≤ F_3·(108/103) = 0.15934… ≤ 4/25`

by a Weierstrass-type product bound proved by induction, and `d_r ≤ F_r`
since `c_r ≤ A_r` (`c_le_Aseq`).  All constants downstream (Layer C) are
re-audited against `4/25` in place of `1/(2π)` and `64/625` in place of
`1/π²`; the sign-lock budget has an order of magnitude of slack.
-/

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Field
import Prop51.Majorant
import Prop51.BinomRecip

namespace Prop51

/-! ## Definition and first values -/

/-- The `d`-normalization `d r = c r / (6^r (r-1)!)` (paper eq. 13).
`d 0 = 0` by convention (`c 0 = 0`); all lemmas assume `1 ≤ r`. -/
def d (r : Nat) : ℚ := c r / (6^r * ((r-1).factorial : ℚ))

@[simp] theorem d_zero : d 0 = 0 := by simp [d]

theorem c_two : c 2 = 5 := by
  have h := c_succ_succ 0
  norm_num [List.range_one] at h
  exact h

theorem d_one : d 1 = 5/36 := by
  norm_num [d, Nat.factorial]

theorem d_two : d 2 = 5/36 := by
  norm_num [d, c_two, Nat.factorial]

private theorem factorial_cast_ne (k : Nat) : ((k.factorial : ℕ) : ℚ) ≠ 0 := by
  exact_mod_cast k.factorial_pos.ne'

private theorem factorial_cast_pos (k : Nat) : (0:ℚ) < ((k.factorial : ℕ) : ℚ) := by
  exact_mod_cast k.factorial_pos

/-- `c r = 6^r (r-1)! · d r`, valid for every `r` (at `r = 0` both sides
vanish). -/
theorem c_eq_d (r : Nat) : c r = (6^r * ((r-1).factorial : ℚ)) * d r := by
  have hden : (6:ℚ)^r * ((r-1).factorial : ℚ) ≠ 0 :=
    mul_ne_zero (by positivity) (factorial_cast_ne (r-1))
  rw [d, mul_comm]
  exact (div_mul_cancel₀ _ hden).symm

theorem d_pos (r : Nat) (hr : 1 ≤ r) : 0 < d r :=
  div_pos (c_pos r hr) (mul_pos (by positivity) (factorial_cast_pos (r-1)))

theorem d_nonneg (r : Nat) : 0 ≤ d r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · exact (d_pos r hr).le

/-! ## The `d`-recurrence (paper eq. 14) -/

/-- The convolution appearing in the `d`-recurrence:
`dconv p = Σ_{i<p} d_i d_{p-i} / C(p,i)` (the `i = 0` term vanishes). -/
def dconv (p : Nat) : ℚ :=
  ∑ i ∈ Finset.range p, d i * d (p - i) / ((p.choose i : ℕ) : ℚ)

theorem dconv_nonneg (p : Nat) : 0 ≤ dconv p :=
  Finset.sum_nonneg fun i _ =>
    div_nonneg (mul_nonneg (d_nonneg i) (d_nonneg (p - i))) (Nat.cast_nonneg _)

/-- `dconv` with the binomial cleared: a single uniform denominator `p!`. -/
theorem dconv_eq (p : Nat) :
    dconv p = (∑ i ∈ Finset.range p,
        d i * d (p-i) * (i.factorial : ℚ) * ((p-i).factorial : ℚ))
      / (p.factorial : ℚ) := by
  rw [dconv, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hip : i < p := Finset.mem_range.mp hi
  have hC : ((p.choose i : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (le_of_lt hip)).ne'
  rw [div_eq_div_iff hC (factorial_cast_ne p)]
  have hq : ((p.choose i : ℕ) : ℚ) * (i.factorial : ℚ) * ((p-i).factorial : ℚ)
      = (p.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial (le_of_lt hip)
  linear_combination (d i * d (p - i)) * hq.symm

/-- **The `d`-recurrence** (paper eq. 14):
`d_{r} = d_{r-1} + (1/r) Σ_{i=1}^{r-2} d_i d_{r-1-i}/C(r-1,i)` at `r = n+2`. -/
theorem d_succ_succ (n : Nat) :
    d (n+2) = d (n+1) + dconv (n+1) / ((n+2 : Nat) : ℚ) := by
  have hterm : ∀ i ∈ Finset.range (n+1),
      (i : ℚ) * ((n+1-i : Nat) : ℚ) * c i * c (n+1-i)
        = 6^(n+1) * (d i * d (n+1-i) * (i.factorial : ℚ)
            * ((n+1-i).factorial : ℚ)) := by
    intro i hi
    have hip : i < n+1 := Finset.mem_range.mp hi
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · simp
    · have h1 : c i = (6^i * ((i-1).factorial : ℚ)) * d i := c_eq_d i
      have h2 : c (n+1-i)
          = (6^(n+1-i) * ((n+1-i-1).factorial : ℚ)) * d (n+1-i) :=
        c_eq_d (n+1-i)
      rw [show n+1-i-1 = n-i by omega] at h2
      have hif : (i:ℚ) * ((i-1).factorial : ℚ) = (i.factorial : ℚ) := by
        exact_mod_cast Nat.mul_factorial_pred (by omega : i ≠ 0)
      have hjf : ((n+1-i : Nat):ℚ) * ((n-i).factorial : ℚ)
          = ((n+1-i).factorial : ℚ) := by
        have h := Nat.mul_factorial_pred (show n+1-i ≠ 0 by omega)
        rw [show n+1-i-1 = n-i by omega] at h
        exact_mod_cast h
      have hpow : (6:ℚ)^i * (6:ℚ)^(n+1-i) = 6^(n+1) := by
        rw [← pow_add]
        congr 1
        omega
      rw [h1, h2, ← hif, ← hjf, ← hpow]
      ring
  have hsum : ((List.range (n+1)).map fun (i : Nat) =>
      (i : ℚ) * ((n+1-i : Nat) : ℚ) * c i * c (n+1-i)).sum
      = 6^(n+1) * ∑ i ∈ Finset.range (n+1),
          d i * d (n+1-i) * (i.factorial : ℚ) * ((n+1-i).factorial : ℚ) := by
    rw [list_range_map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  have hc2 := c_succ_succ n
  rw [hsum] at hc2
  have hfs : ((n+1).factorial : ℚ) = ((n+1 : Nat) : ℚ) * (n.factorial : ℚ) := by
    exact_mod_cast Nat.factorial_succ n
  have hne1 : ((n:ℚ)+1) ≠ 0 := by positivity
  have hne2 : ((n:ℚ)+2) ≠ 0 := by positivity
  have hnef : (n.factorial : ℚ) ≠ 0 := factorial_cast_ne n
  have hne6 : (6:ℚ)^(n+1) ≠ 0 := by positivity
  have hne6' : (6:ℚ)^(n+2) ≠ 0 := by positivity
  show c (n+2) / (6^(n+2) * ((n+2-1).factorial : ℚ))
      = c (n+1) / (6^(n+1) * ((n+1-1).factorial : ℚ)) + _
  rw [show n+2-1 = n+1 by omega, show n+1-1 = n by omega, hc2, dconv_eq,
      hfs, c_eq_d (n+1), show n+1-1 = n by omega]
  push_cast
  field_simp
  ring

/-! ## Monotonicity and the lower bound `5/36 ≤ d` -/

theorem d_le_d_succ (n : Nat) : d (n+1) ≤ d (n+2) := by
  rw [d_succ_succ n]
  have h := div_nonneg (dconv_nonneg (n+1))
    (by positivity : (0:ℚ) ≤ ((n+2 : Nat) : ℚ))
  linarith

theorem d_mono {r s : Nat} (hrs : r ≤ s) : d r ≤ d s := by
  induction s, hrs using Nat.le_induction with
  | base => exact le_rfl
  | succ s hs ih =>
      rcases Nat.eq_zero_or_pos s with rfl | hspos
      · interval_cases r
        · simp [d_nonneg 1]
      · obtain ⟨k, rfl⟩ : ∃ k, s = k+1 := ⟨s-1, by omega⟩
        exact ih.trans (d_le_d_succ k)

theorem d_lb (r : Nat) (hr : 1 ≤ r) : 5/36 ≤ d r := by
  rw [← d_one]
  exact d_mono hr

/-! ## The upper bound `d ≤ 4/25` via the `F`-ratio -/

/-- `F_r = A_r / (6^r (r-1)!)` — the same normalization applied to the
ordinary coefficients of `C`. -/
def Fseq (r : Nat) : ℚ := Aseq r / (6^r * ((r-1).factorial : ℚ))

theorem Aseq_pos (k : Nat) : 0 < Aseq k := by
  rw [Aseq]
  have h1 := factorial_cast_pos (6*k)
  have h2 := factorial_cast_pos (3*k)
  have h3 := factorial_cast_pos (2*k)
  have h4 : (0:ℚ) < 72^k := by positivity
  exact div_pos h1 (mul_pos (mul_pos h2 h3) h4)

theorem Fseq_pos (r : Nat) : 0 < Fseq r :=
  div_pos (Aseq_pos r) (mul_pos (by positivity) (factorial_cast_pos (r-1)))

theorem d_le_Fseq (r : Nat) : d r ≤ Fseq r := by
  have hD : (0:ℚ) < 6^r * ((r-1).factorial : ℚ) :=
    mul_pos (by positivity) (factorial_cast_pos (r-1))
  rw [d, Fseq, div_le_div_iff₀ hD hD]
  exact mul_le_mul_of_nonneg_right (c_le_Aseq r) hD.le

/-- The exact ratio: `F_{r+1} = F_r (1 + 5/(36 r(r+1)))` (from
`Aseq_succ`; this is `(r+1/6)(r+5/6)/(r(r+1))`). -/
theorem Fseq_succ (r : Nat) (hr : 1 ≤ r) :
    Fseq (r+1) = Fseq r * (1 + 5/(36*(r:ℚ)*((r:ℚ)+1))) := by
  have hA := Aseq_succ r
  push_cast at hA
  have hA' : Aseq (r+1) = (6*(r:ℚ)+1)*(6*(r:ℚ)+5)*Aseq r / (6*((r:ℚ)+1)) := by
    rw [eq_div_iff (by positivity : (6:ℚ)*((r:ℚ)+1) ≠ 0)]
    linear_combination hA
  have hrf : (r.factorial : ℚ) = (r:ℚ) * ((r-1).factorial : ℚ) := by
    exact_mod_cast (Nat.mul_factorial_pred (by omega : r ≠ 0)).symm
  have hne : ((r:ℚ)) ≠ 0 := by
    exact_mod_cast (by omega : r ≠ 0)
  have hne1 : ((r:ℚ)+1) ≠ 0 := by positivity
  have hnef : ((r-1).factorial : ℚ) ≠ 0 := factorial_cast_ne (r-1)
  have hne6 : (6:ℚ)^r ≠ 0 := by positivity
  show Aseq (r+1) / (6^(r+1) * ((r+1-1).factorial : ℚ)) = _
  rw [show r+1-1 = r by omega, hA', hrf, Fseq]
  field_simp
  ring

/-- Weierstrass-type product bound, by induction along `Fseq_succ`:
for `r ≥ 3`, `F_r ≤ F_3 / (1 - (5/36)(1/3 - 1/r))`. -/
theorem Fseq_le_of_three {r : Nat} (hr : 3 ≤ r) :
    Fseq r ≤ Fseq 3 / (1 - (5/36) * (1/3 - 1/(r:ℚ))) := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr3 ih =>
      have hrpos : (0:ℚ) < (r:ℚ) := by
        exact_mod_cast (by omega : 0 < r)
      have hr1pos : (0:ℚ) < (r:ℚ)+1 := by positivity
      have hne : (r:ℚ) ≠ 0 := hrpos.ne'
      have hne1 : ((r:ℚ)+1) ≠ 0 := hr1pos.ne'
      rw [show ((r+1 : Nat) : ℚ) = (r:ℚ)+1 by push_cast; ring]
      have hrecip : (1:ℚ)/(r:ℚ) ≤ 1/3 := by
        rw [div_le_div_iff₀ hrpos (by norm_num : (0:ℚ) < 3)]
        have : (3:ℚ) ≤ (r:ℚ) := by exact_mod_cast hr3
        linarith
      have hrecip1 : (0:ℚ) < 1/((r:ℚ)+1) := by positivity
      set S : ℚ := (5/36) * (1/3 - 1/(r:ℚ)) with hS
      set x : ℚ := 5/(36*(r:ℚ)*((r:ℚ)+1)) with hx
      have hxpos : 0 < x := by rw [hx]; positivity
      have hSnn : 0 ≤ S := by rw [hS]; linarith
      have htel : S + x = (5/36) * (1/3 - 1/((r:ℚ)+1)) := by
        rw [hS, hx]
        field_simp
        ring
      have hS108 : S + x ≤ 5/108 := by rw [htel]; linarith
      have hden1 : (0:ℚ) < 1 - S := by linarith
      have hden2 : (0:ℚ) < 1 - S - x := by linarith
      have hF3 : (0:ℚ) < Fseq 3 := Fseq_pos 3
      calc Fseq (r+1) = Fseq r * (1+x) := by rw [Fseq_succ r (by omega), hx]
        _ ≤ (Fseq 3 / (1 - S)) * (1+x) :=
            mul_le_mul_of_nonneg_right ih (by linarith)
        _ ≤ Fseq 3 / (1 - S - x) := by
            rw [div_mul_eq_mul_div, div_le_div_iff₀ hden1 hden2]
            nlinarith [mul_nonneg (mul_nonneg hF3.le hxpos.le) hSnn,
              mul_nonneg (mul_nonneg hF3.le hxpos.le) hxpos.le]
        _ = Fseq 3 / (1 - (5/36) * (1/3 - 1/((r:ℚ)+1))) := by rw [← htel]; ring_nf

theorem Fseq_three : Fseq 3 = 85085/559872 := by
  have h18 : Nat.factorial 18 = 6402373705728000 := rfl
  have h9 : Nat.factorial 9 = 362880 := rfl
  have h6 : Nat.factorial 6 = 720 := rfl
  have h2 : Nat.factorial 2 = 2 := rfl
  norm_num [Fseq, Aseq, h18, h9, h6, h2]

/-- **The rational upper bound** (paper: `d_r ≤ 1/(2π)`; rationalized to
`4/25 = 0.16`, with `F_3 · 108/103 = 0.15934…` doing the work). -/
theorem d_ub (r : Nat) (hr : 1 ≤ r) : d r ≤ 4/25 := by
  rcases (by omega : r = 1 ∨ r = 2 ∨ 3 ≤ r) with rfl | rfl | h3
  · rw [d_one]; norm_num
  · rw [d_two]; norm_num
  · have h1 := d_le_Fseq r
    have h2 := Fseq_le_of_three h3
    have hrpos : (0:ℚ) < (r:ℚ) := by exact_mod_cast (by omega : 0 < r)
    have hrecip : (0:ℚ) < 1/(r:ℚ) := by positivity
    have hden : (0:ℚ) < 1 - (5/36) * (1/3 - 1/(r:ℚ)) := by nlinarith
    have h3' : Fseq 3 / (1 - (5/36) * (1/3 - 1/(r:ℚ)))
        ≤ Fseq 3 / (1 - 5/108) := by
      apply div_le_div_of_nonneg_left (Fseq_pos 3).le (by norm_num)
      nlinarith
    have h4 : Fseq 3 / (1 - 5/108) ≤ 4/25 := by
      rw [Fseq_three]
      norm_num
    linarith

/-! ## The workhorse bounds on `c` itself -/

/-- `c_r ≥ (5/36)·6^r (r-1)!`. -/
theorem c_lb (r : Nat) (hr : 1 ≤ r) :
    5/36 * (6^r * ((r-1).factorial : ℚ)) ≤ c r := by
  have hD : (0:ℚ) < 6^r * ((r-1).factorial : ℚ) :=
    mul_pos (by positivity) (factorial_cast_pos (r-1))
  calc 5/36 * (6^r * ((r-1).factorial : ℚ))
      ≤ d r * (6^r * ((r-1).factorial : ℚ)) :=
        mul_le_mul_of_nonneg_right (d_lb r hr) hD.le
    _ = c r := by rw [c_eq_d r]; ring

/-- `c_r ≤ (4/25)·6^r (r-1)!` (the paper uses the weaker `(1/6)·6^r (r-1)!`). -/
theorem c_ub (r : Nat) (hr : 1 ≤ r) :
    c r ≤ 4/25 * (6^r * ((r-1).factorial : ℚ)) := by
  have hD : (0:ℚ) < 6^r * ((r-1).factorial : ℚ) :=
    mul_pos (by positivity) (factorial_cast_pos (r-1))
  calc c r = d r * (6^r * ((r-1).factorial : ℚ)) := by rw [c_eq_d r]; ring
    _ ≤ 4/25 * (6^r * ((r-1).factorial : ℚ)) :=
        mul_le_mul_of_nonneg_right (d_ub r hr) hD.le

/-! ## Increment control (paper Lemma 2.1, rationalized) -/

/-- `dconv p ≤ (16/625)·(4/p) = (64/625)/p` for `p ≥ 2`, via the
reciprocal-binomial bound. -/
theorem dconv_le (p : Nat) (hp : 2 ≤ p) : dconv p ≤ (64/625) / (p:ℚ) := by
  have hsplit : dconv p
      = d 0 * d (p-0) / ((p.choose 0 : ℕ):ℚ)
        + ∑ i ∈ Finset.Ico 1 p, d i * d (p-i) / ((p.choose i : ℕ):ℚ) := by
    rw [dconv, Finset.range_eq_Ico,
        Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < p)]
  rw [hsplit]
  simp only [d_zero, zero_mul, zero_div, zero_add]
  have hterm : ∀ i ∈ Finset.Ico 1 p,
      d i * d (p-i) / ((p.choose i : ℕ):ℚ)
        ≤ (16/625) * ((1:ℚ)/(p.choose i)) := by
    intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hi
    have hC : (0:ℚ) < ((p.choose i : ℕ):ℚ) := by
      exact_mod_cast Nat.choose_pos (by omega : i ≤ p)
    have hbound : d i * d (p-i) ≤ 16/625 := by
      calc d i * d (p-i) ≤ (4/25) * (4/25) :=
            mul_le_mul (d_ub i (by omega)) (d_ub (p-i) (by omega))
              (d_nonneg (p-i)) (by norm_num)
        _ = 16/625 := by norm_num
    rw [mul_one_div, div_le_div_iff₀ hC hC]
    exact mul_le_mul_of_nonneg_right hbound hC.le
  calc ∑ i ∈ Finset.Ico 1 p, d i * d (p-i) / ((p.choose i : ℕ):ℚ)
      ≤ ∑ i ∈ Finset.Ico 1 p, (16/625) * ((1:ℚ)/(p.choose i)) :=
        Finset.sum_le_sum hterm
    _ = (16/625) * ∑ i ∈ Finset.Ico 1 p, (1:ℚ)/(p.choose i) := by
        rw [Finset.mul_sum]
    _ ≤ (16/625) * (4/(p:ℚ)) :=
        mul_le_mul_of_nonneg_left (sum_choose_recip_le p hp) (by norm_num)
    _ = (64/625)/(p:ℚ) := by ring

/-- **Increment control** (paper eq. 15, rationalized):
`d_{r} - d_{r-1} ≤ (64/625)/(r(r-1))` at `r = n+2`. -/
theorem d_increment (n : Nat) :
    d (n+2) - d (n+1) ≤ (64/625) / (((n:ℚ)+2) * ((n:ℚ)+1)) := by
  have hcast : ((n+2 : Nat) : ℚ) = (n:ℚ)+2 := by push_cast; ring
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : dconv 1 = 0 := by
      rw [dconv]
      simp
    rw [d_succ_succ 0, h1]
    norm_num
  · have h2 := dconv_le (n+1) (by omega)
    have hp2 : (0:ℚ) < (n:ℚ)+2 := by positivity
    have hp1 : (0:ℚ) < ((n+1 : Nat):ℚ) := by
      exact_mod_cast (by omega : 0 < n+1)
    rw [d_succ_succ n, hcast]
    have h3 : dconv (n+1) / ((n:ℚ)+2)
        ≤ ((64/625)/((n+1 : Nat):ℚ)) / ((n:ℚ)+2) := by
      rw [div_le_div_iff₀ hp2 hp2]
      exact mul_le_mul_of_nonneg_right h2 hp2.le
    have hcast1 : ((n+1 : Nat) : ℚ) = (n:ℚ)+1 := by push_cast; ring
    rw [hcast1] at h3
    calc d (n+1) + dconv (n+1)/((n:ℚ)+2) - d (n+1)
        = dconv (n+1)/((n:ℚ)+2) := by ring
      _ ≤ ((64/625)/((n:ℚ)+1))/((n:ℚ)+2) := h3
      _ = (64/625) / (((n:ℚ)+2) * ((n:ℚ)+1)) := by
          rw [div_div]
          ring_nf

/-- Telescoped increment control: `d_m - d_{m-s} ≤ (64/625)(1/(m-s) - 1/m)`. -/
theorem d_sub_le (m : Nat) : ∀ s : Nat, s < m →
    d m - d (m - s) ≤ (64/625) * (1/((m-s : Nat):ℚ) - 1/(m:ℚ)) := by
  intro s
  induction s with
  | zero => intro _; simp
  | succ s ih =>
      intro h
      have ihs := ih (by omega)
      obtain ⟨k, hk⟩ : ∃ k, m - s = k+2 := ⟨m-s-2, by omega⟩
      have hstep : d (m-s) - d (m-s-1)
          ≤ (64/625)/(((k:ℚ)+2)*((k:ℚ)+1)) := by
        rw [hk, show k+2-1 = k+1 by omega]
        exact d_increment k
      have hcast2 : ((m-s : Nat):ℚ) = (k:ℚ)+2 := by rw [hk]; push_cast; ring
      have hcast1 : ((m-s-1 : Nat):ℚ) = (k:ℚ)+1 := by
        rw [show m-s-1 = k+1 by omega]
        push_cast
        ring
      have hne2 : ((k:ℚ)+2) ≠ 0 := by positivity
      have hne1 : ((k:ℚ)+1) ≠ 0 := by positivity
      have key : (1:ℚ)/((m-s-1 : Nat):ℚ) - 1/(m:ℚ)
          = (1/((m-s : Nat):ℚ) - 1/(m:ℚ)) + 1/(((k:ℚ)+2)*((k:ℚ)+1)) := by
        rw [hcast1, hcast2]
        field_simp
        ring
      rw [show m-(s+1) = m-s-1 by omega, key]
      have hsplit : d m - d (m-s-1)
          = (d m - d (m-s)) + (d (m-s) - d (m-s-1)) := by ring
      rw [hsplit]
      have hfin : d (m-s) - d (m-s-1)
          ≤ (64/625) * (1/(((k:ℚ)+2)*((k:ℚ)+1))) := by
        calc d (m-s) - d (m-s-1) ≤ (64/625)/(((k:ℚ)+2)*((k:ℚ)+1)) := hstep
          _ = (64/625) * (1/(((k:ℚ)+2)*((k:ℚ)+1))) := by ring
      linarith [ihs, hfin]

/-- **Ratio control** (paper eq. 16, rationalized): for `s < m`,
`1 - (2304/3125)·s/(m(m-s)) ≤ d_{m-s}/d_m` (and `≤ 1` by monotonicity:
`d_mono`). -/
theorem d_ratio_lb (m s : Nat) (hs : s < m) :
    1 - (2304/3125) * ((s:ℚ) / ((m:ℚ) * ((m-s : Nat):ℚ))) ≤ d (m-s) / d m := by
  have hm1 : 1 ≤ m := by omega
  have hdm := d_pos m hm1
  have hdmlb := d_lb m hm1
  have hsub := d_sub_le m s hs
  have hmpos : (0:ℚ) < (m:ℚ) := by exact_mod_cast (by omega : 0 < m)
  have hmspos : (0:ℚ) < ((m-s : Nat):ℚ) := by
    exact_mod_cast (by omega : 0 < m-s)
  have hcast : (1:ℚ)/((m-s : Nat):ℚ) - 1/(m:ℚ)
      = (s:ℚ)/((m:ℚ)*((m-s : Nat):ℚ)) := by
    have hms : ((m-s : Nat):ℚ) = (m:ℚ) - (s:ℚ) := by
      rw [Nat.cast_sub hs.le]
    rw [hms]
    have h1 : (m:ℚ) ≠ 0 := hmpos.ne'
    have h2 : (m:ℚ) - (s:ℚ) ≠ 0 := by rw [← hms]; exact hmspos.ne'
    field_simp
    ring
  rw [le_div_iff₀ hdm]
  set q : ℚ := (s:ℚ)/((m:ℚ)*((m-s : Nat):ℚ)) with hqdef
  have hq : (0:ℚ) ≤ q :=
    div_nonneg (Nat.cast_nonneg s) (by positivity)
  have h1 : d m - d (m-s) ≤ (64/625) * q := by
    calc d m - d (m-s) ≤ (64/625)*(1/((m-s : Nat):ℚ) - 1/(m:ℚ)) := hsub
      _ = (64/625) * q := by rw [hcast]
  have h3 := mul_nonneg (sub_nonneg.mpr hdmlb) hq
  nlinarith [h1, h3]

end Prop51
