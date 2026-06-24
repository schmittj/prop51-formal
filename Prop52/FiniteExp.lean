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
import Mathlib.Analysis.Normed.Ring.InfiniteSum

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

end Prop52
