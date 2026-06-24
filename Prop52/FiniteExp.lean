/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Finite-support exponential series bridge

This file contains analytic lemmas for evaluating the formal powers which
occur in `Prop51.expCoeff_eq_sum_pow`.  The statements are intentionally
generic: if a rational coefficient sequence `L` is supported in degrees
`<= P`, then the real series of coefficients of `(mk L)^q` sums to the
ordinary `q`th power of the finite polynomial evaluation of `L`.
-/

import Prop52.Printed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential

namespace Prop52

open PowerSeries

/-- If `L` is supported in degrees `<= P`, then `(mk L)^q` is supported in
degrees `<= q*P`. -/
theorem coeff_mk_pow_eq_zero_of_gt_mul
    {L : Nat → ℚ} {P : Nat}
    (hsupp : ∀ r : Nat, P < r → L r = 0) :
    ∀ q n : Nat, q * P < n →
      coeff n ((mk L : ℚ⟦X⟧)^q) = 0
  | 0, n, hn => by
      rw [pow_zero, coeff_one]
      have hn0 : n ≠ 0 := by omega
      simp [hn0]
  | q + 1, n, hn => by
      rw [pow_succ]
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp only [coeff_mk]
      refine Finset.sum_eq_zero fun k hk => ?_
      have hk_le_n : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      by_cases hkbig : q * P < k
      · rw [coeff_mk_pow_eq_zero_of_gt_mul hsupp q k hkbig, zero_mul]
      · have hk_le_qP : k ≤ q * P := Nat.le_of_not_gt hkbig
        have htail : P < n - k := by
          by_contra hnot
          have htail_le : n - k ≤ P := Nat.le_of_not_gt hnot
          have hn_le : n ≤ q * P + P := by
            calc
              n = k + (n - k) := (Nat.add_sub_of_le hk_le_n).symm
              _ ≤ q * P + P := Nat.add_le_add hk_le_qP htail_le
          have hn_le_succ : n ≤ (q + 1) * P := by
            rw [Nat.succ_mul]
            exact hn_le
          exact (not_lt_of_ge hn_le_succ) hn
        rw [hsupp (n - k) htail, mul_zero]

theorem summable_norm_coeff_mk_pow_eval_of_support
    {L : Nat → ℚ} {P : Nat}
    (hsupp : ∀ r : Nat, P < r → L r = 0) (q : Nat) (t : ℝ) :
    Summable fun n : Nat =>
      ‖((coeff n ((mk L : ℚ⟦X⟧)^q) : ℚ) : ℝ) * t^n‖ := by
  refine summable_of_ne_finset_zero (s := Finset.range (q * P + 1)) ?_
  intro n hn
  have hgt : q * P < n := by
    rw [Finset.mem_range] at hn
    omega
  rw [coeff_mk_pow_eq_zero_of_gt_mul hsupp q n hgt]
  norm_num

theorem hasSum_mk_eval_of_support
    {L : Nat → ℚ} {P : Nat}
    (hsupp : ∀ r : Nat, P < r → L r = 0) (t : ℝ) :
    HasSum (fun n : Nat => (L n : ℝ) * t^n)
      (∑ n ∈ Finset.range (P + 1), (L n : ℝ) * t^n) := by
  refine hasSum_sum_of_ne_finset_zero ?_
  intro n hn
  have hgt : P < n := by
    rw [Finset.mem_range] at hn
    omega
  rw [hsupp n hgt]
  norm_num

/-- Evaluation of finite-support formal powers as ordinary real powers. -/
theorem hasSum_coeff_mk_pow_eval_of_support
    {L : Nat → ℚ} {P : Nat}
    (hsupp : ∀ r : Nat, P < r → L r = 0) (t : ℝ) :
    ∀ q : Nat,
      HasSum
        (fun n : Nat => ((coeff n ((mk L : ℚ⟦X⟧)^q) : ℚ) : ℝ) * t^n)
        ((∑ n ∈ Finset.range (P + 1), (L n : ℝ) * t^n)^q)
  | 0 => by
      have hbase :
          HasSum
            (fun n : Nat => ((coeff n ((mk L : ℚ⟦X⟧)^0) : ℚ) : ℝ) * t^n)
            (∑ n ∈ Finset.range 1,
              ((coeff n ((mk L : ℚ⟦X⟧)^0) : ℚ) : ℝ) * t^n) := by
        refine hasSum_sum_of_ne_finset_zero (s := Finset.range 1) ?_
        intro n hn
        have hgt : 0 < n := by
          rw [Finset.mem_range] at hn
          omega
        rw [pow_zero, coeff_one]
        simp [Nat.ne_of_gt hgt]
      simpa using hbase
  | q + 1 => by
      let Fq : Nat → ℝ := fun n =>
        ((coeff n ((mk L : ℚ⟦X⟧)^q) : ℚ) : ℝ) * t^n
      let G : Nat → ℝ := fun n => (L n : ℝ) * t^n
      have hq :
          HasSum Fq
            ((∑ n ∈ Finset.range (P + 1), (L n : ℝ) * t^n)^q) := by
        simpa [Fq] using hasSum_coeff_mk_pow_eval_of_support hsupp t q
      have hG :
          HasSum G (∑ n ∈ Finset.range (P + 1), (L n : ℝ) * t^n) := by
        simpa [G] using hasSum_mk_eval_of_support hsupp t
      have hf : Summable fun n => ‖Fq n‖ := by
        simpa [Fq] using summable_norm_coeff_mk_pow_eval_of_support hsupp q t
      have hg : Summable fun n => ‖G n‖ := by
        refine summable_of_ne_finset_zero (s := Finset.range (P + 1)) ?_
        intro n hn
        have hgt : P < n := by
          rw [Finset.mem_range] at hn
          omega
        simp [G, hsupp n hgt]
      have hconv := hasSum_sum_range_mul_of_summable_norm (R := ℝ) hf hg
      rw [hq.tsum_eq, hG.tsum_eq] at hconv
      have hseq :
          (fun n : Nat => ∑ k ∈ Finset.range (n + 1), Fq k * G (n - k)) =
          (fun n : Nat =>
            ((coeff n ((mk L : ℚ⟦X⟧)^(q + 1)) : ℚ) : ℝ) * t^n) := by
        funext n
        dsimp [Fq, G]
        rw [pow_succ]
        rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        simp only [coeff_mk]
        rw [Rat.cast_sum]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk_le_n : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        rw [Rat.cast_mul]
        have hpow : t^k * t^(n-k) = t^n := by
          rw [← pow_add, Nat.add_sub_of_le hk_le_n]
        calc
          ↑((coeff k) (mk L ^ q)) * t ^ k *
              (↑(L (n - k)) * t ^ (n - k))
              = (↑((coeff k) (mk L ^ q)) * ↑(L (n - k))) *
                  (t^k * t^(n-k)) := by ring
          _ = ↑((coeff k) (mk L ^ q)) * ↑(L (n - k)) * t^n := by
              rw [hpow]
      rw [hseq] at hconv
      simpa [pow_succ] using hconv

theorem coeff_mk_pow_nonneg {L : Nat → ℚ}
    (hL : ∀ r : Nat, 0 ≤ L r) :
    ∀ q n : Nat, 0 ≤ coeff n ((mk L : ℚ⟦X⟧)^q)
  | 0, n => by
      rw [pow_zero, coeff_one]
      by_cases hn : n = 0 <;> simp [hn]
  | q + 1, n => by
      rw [pow_succ]
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp only [coeff_mk]
      refine Finset.sum_nonneg fun k _hk => ?_
      exact mul_nonneg (coeff_mk_pow_nonneg hL q k) (hL (n-k))

theorem abs_coeff_mk_pow_le_abs (L : Nat → ℚ) :
    ∀ q n : Nat,
      |coeff n ((mk L : ℚ⟦X⟧)^q)| ≤
        coeff n ((mk (fun r : Nat => |L r|) : ℚ⟦X⟧)^q)
  | 0, n => by
      by_cases hn : n = 0 <;> simp [hn]
  | q + 1, n => by
      rw [pow_succ, pow_succ]
      rw [coeff_mul, coeff_mul]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp only [coeff_mk]
      calc
        |∑ k ∈ Finset.range (n + 1),
            coeff k ((mk L : ℚ⟦X⟧)^q) * L (n - k)|
            ≤ ∑ k ∈ Finset.range (n + 1),
                |coeff k ((mk L : ℚ⟦X⟧)^q) * L (n - k)| := by
              exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.range (n + 1),
                coeff k ((mk (fun r : Nat => |L r|) : ℚ⟦X⟧)^q) *
                  |L (n-k)| := by
              refine Finset.sum_le_sum fun k _hk => ?_
              rw [abs_mul]
              exact mul_le_mul
                (abs_coeff_mk_pow_le_abs L q k)
                le_rfl
                (abs_nonneg (L (n-k)))
                (coeff_mk_pow_nonneg (fun r => abs_nonneg (L r)) q k)

/-- Analytic evaluation of the recurrence-defined formal exponential for a
finite-support rational input.

This is the main generic bridge from `Prop51.expCoeff_eq_sum_pow` to the
ordinary real exponential.  The proof uses the finite-power evaluation above,
an absolute-value double-series majorant, and Mathlib's real exponential
series. -/
theorem hasSum_expCoeff_eval_of_support
    {L : Nat → ℚ} {P : Nat}
    (hL0 : L 0 = 0)
    (hsupp : ∀ r : Nat, P < r → L r = 0) (t : ℝ) :
    HasSum (fun n : Nat => (Prop51.expCoeff L n : ℝ) * t^n)
      (Real.exp (∑ n ∈ Finset.range (P + 1), (L n : ℝ) * t^n)) := by
  let Gval : ℝ := ∑ n ∈ Finset.range (P + 1), (L n : ℝ) * t^n
  let Labs : Nat → ℚ := fun r => |L r|
  let Gabs : ℝ := ∑ n ∈ Finset.range (P + 1), (Labs n : ℝ) * |t|^n
  let Aσ : (Σ _q : Nat, Nat) → ℝ := fun x =>
    (((coeff x.2 ((mk L : ℚ⟦X⟧)^x.1) : ℚ) : ℝ) * t^x.2) /
      (x.1.factorial : ℝ)
  let Bσ : (Σ _q : Nat, Nat) → ℝ := fun x =>
    (((coeff x.2 ((mk Labs : ℚ⟦X⟧)^x.1) : ℚ) : ℝ) * |t|^x.2) /
      (x.1.factorial : ℝ)
  have hLabs_supp : ∀ r : Nat, P < r → Labs r = 0 := by
    intro r hr
    simp [Labs, hsupp r hr]
  have hB_nonneg : ∀ x, 0 ≤ Bσ x := by
    intro x
    dsimp [Bσ, Labs]
    have hcQ :
        0 ≤ coeff x.2 ((mk (fun r : Nat => |L r|) : ℚ⟦X⟧)^x.1) :=
      coeff_mk_pow_nonneg (fun r => abs_nonneg (L r)) x.1 x.2
    have hcR :
        0 ≤ ((coeff x.2
          ((mk (fun r : Nat => |L r|) : ℚ⟦X⟧)^x.1) : ℚ) : ℝ) := by
      exact_mod_cast hcQ
    exact div_nonneg (mul_nonneg hcR (pow_nonneg (abs_nonneg t) x.2))
      (by positivity)
  have hB_inner :
      ∀ q : Nat, HasSum (fun n : Nat => Bσ ⟨q, n⟩)
        (Gabs^q / (q.factorial : ℝ)) := by
    intro q
    have hpow := hasSum_coeff_mk_pow_eval_of_support
      (L := Labs) (P := P) hLabs_supp |t| q
    dsimp [Bσ, Gabs]
    simpa [Labs] using hpow.div_const (q.factorial : ℝ)
  have hB_outer_summable :
      Summable fun q : Nat => tsum (fun n : Nat => Bσ ⟨q, n⟩) := by
    have hexp := (NormedSpace.expSeries_div_hasSum_exp (x := Gabs)).summable
    exact hexp.congr fun q => (hB_inner q).tsum_eq.symm
  have hB_summable : Summable Bσ := by
    exact (summable_sigma_of_nonneg hB_nonneg).2
      ⟨fun q => (hB_inner q).summable, hB_outer_summable⟩
  have hA_le_B : ∀ x, ‖Aσ x‖ ≤ Bσ x := by
    intro x
    rcases x with ⟨q, n⟩
    dsimp [Aσ, Bσ, Labs]
    have hcoeffQ :
        |coeff n ((mk L : ℚ⟦X⟧)^q)| ≤
          coeff n ((mk (fun r : Nat => |L r|) : ℚ⟦X⟧)^q) :=
      abs_coeff_mk_pow_le_abs L q n
    have hcoeffR :
        |((coeff n ((mk L : ℚ⟦X⟧)^q) : ℚ) : ℝ)| ≤
          ((coeff n ((mk (fun r : Nat => |L r|) : ℚ⟦X⟧)^q) : ℚ) : ℝ) := by
      exact_mod_cast hcoeffQ
    have hnum :
        ‖((coeff n ((mk L : ℚ⟦X⟧)^q) : ℚ) : ℝ) * t^n‖ ≤
          ((coeff n ((mk (fun r : Nat => |L r|) : ℚ⟦X⟧)^q) : ℚ) : ℝ) *
            |t|^n := by
      rw [norm_mul, Real.norm_eq_abs, norm_pow, Real.norm_eq_abs]
      exact mul_le_mul hcoeffR le_rfl (pow_nonneg (abs_nonneg t) n)
        (by
          exact_mod_cast
            coeff_mk_pow_nonneg (fun r => abs_nonneg (L r)) q n)
    have hfac_nonneg : 0 ≤ (q.factorial : ℝ) := by positivity
    calc
      ‖(((coeff n ((mk L : ℚ⟦X⟧)^q) : ℚ) : ℝ) * t^n) /
          (q.factorial : ℝ)‖
          = ‖(((coeff n ((mk L : ℚ⟦X⟧)^q) : ℚ) : ℝ) * t^n)‖ /
              (q.factorial : ℝ) := by
            rw [norm_div, Real.norm_of_nonneg hfac_nonneg]
      _ ≤ (((coeff n ((mk (fun r : Nat => |L r|) : ℚ⟦X⟧)^q) : ℚ) : ℝ) *
            |t|^n) / (q.factorial : ℝ) := by
            exact div_le_div_of_nonneg_right hnum hfac_nonneg
  have hA_summable : Summable Aσ :=
    Summable.of_norm_bounded hB_summable hA_le_B
  have hA_inner :
      ∀ q : Nat, HasSum (fun n : Nat => Aσ ⟨q, n⟩)
        (Gval^q / (q.factorial : ℝ)) := by
    intro q
    have hpow := hasSum_coeff_mk_pow_eval_of_support
      (L := L) (P := P) hsupp t q
    dsimp [Aσ, Gval]
    simpa using hpow.div_const (q.factorial : ℝ)
  have hA_outer :
      HasSum (fun q : Nat => Gval^q / (q.factorial : ℝ))
        (NormedSpace.exp Gval) :=
    NormedSpace.expSeries_div_hasSum_exp (x := Gval)
  have hA_sigma : HasSum Aσ (NormedSpace.exp Gval) :=
    hA_outer.sigma_of_hasSum hA_inner hA_summable
  let swapSigma : Nat × Nat ≃ (Σ _q : Nat, Nat) :=
    (Equiv.prodComm Nat Nat).trans (Equiv.sigmaEquivProd Nat Nat).symm
  have hA_prod :
      HasSum (fun p : Nat × Nat => Aσ (swapSigma p))
        (NormedSpace.exp Gval) :=
    (Equiv.hasSum_iff swapSigma).2 hA_sigma
  have hrows :
      ∀ n : Nat,
        HasSum (fun q : Nat => Aσ (swapSigma (n, q)))
          (∑ q ∈ Finset.range (n + 1), Aσ (swapSigma (n, q))) := by
    intro n
    refine hasSum_sum_of_ne_finset_zero (s := Finset.range (n + 1)) ?_
    intro q hqnot
    have hnq : n < q := by
      rw [Finset.mem_range] at hqnot
      omega
    dsimp [swapSigma, Aσ]
    rw [Prop51.coeff_pow_eq_zero L hL0 q n hnq]
    norm_num
  have hrowSum :
      HasSum
        (fun n : Nat => ∑ q ∈ Finset.range (n + 1), Aσ (swapSigma (n, q)))
        (NormedSpace.exp Gval) :=
    hA_prod.prod_fiberwise hrows
  have hrow_eq :
      (fun n : Nat => ∑ q ∈ Finset.range (n + 1), Aσ (swapSigma (n, q))) =
      (fun n : Nat => (Prop51.expCoeff L n : ℝ) * t^n) := by
    funext n
    dsimp [Aσ, swapSigma]
    rw [Prop51.expCoeff_eq_sum_pow L hL0 n]
    rw [Rat.cast_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _hq => ?_
    rw [Rat.cast_div, Rat.cast_natCast]
    ring
  rw [hrow_eq] at hrowSum
  simpa [Gval, Real.exp_eq_exp_ℝ] using hrowSum

end Prop52
