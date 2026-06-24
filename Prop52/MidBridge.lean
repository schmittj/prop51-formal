/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Bridge from the Prop52 mid upper bound to printed negativity

The finite certificate in `Prop52.MidCertificateAll` proves negativity of the
one-parameter upper bound `midUNormFast a (N μ)` for `14 <= a <= 149`.
This file isolates the remaining analytic/formal bridge: the coefficientwise
upper bound from the printed coefficient to that one-parameter expression.
-/

import Prop52.Printed
import Prop52.MidCertificateAll
import Prop52.MidNormalization

namespace Prop52

open PowerSeries

/-! ## Exact `B_N * A_μ` decomposition -/

/-- The auxiliary series `A_μ(t)=P_μ(t)(1-K_μ(t))` used in the mid proof. -/
noncomputable def printedMidASeries (μ : List Nat) : ℚ⟦X⟧ :=
  Prop51.prodSeries μ * (1 - printedFullKSeries μ)

/-- Coefficients of `A_μ(t)=P_μ(t)(1-K_μ(t))`. -/
noncomputable def printedMidACoeff (μ : List Nat) (r : Nat) : ℚ :=
  coeff r (printedMidASeries μ)

theorem coeff_printedMidASeries (μ : List Nat) (r : Nat) :
    coeff r (printedMidASeries μ) = printedMidACoeff μ r := by
  rfl

theorem printedFullFSeries_eq_bSeries (μ : List Nat) :
    printedFullFSeries μ = Prop51.bSeries μ := by
  ext r
  rw [coeff_printedFullFSeries]
  rw [← bCoeff_eq_fCoeff μ r]
  rw [Prop51.bSeries, coeff_mk]

theorem printedFullFSeries_eq_B_mul_prod (μ : List Nat) :
    printedFullFSeries μ = Prop51.BSeriesQ (N μ) * Prop51.prodSeries μ := by
  rw [printedFullFSeries_eq_bSeries, Prop51.bSeries_eq_B_mul_prod]
  rfl

theorem coeff_printedMidASeries_zero (μ : List Nat) :
    printedMidACoeff μ 0 = 1 := by
  unfold printedMidACoeff printedMidASeries
  rw [coeff_zero_eq_constantCoeff, map_mul, Prop51.constantCoeff_prodSeries]
  have hK0 : constantCoeff (printedFullKSeries μ) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_printedFullKSeries]
    rfl
  rw [map_sub, map_one, hK0]
  ring

/-- Coefficient convolution for `P_μ(t) K_μ(t)`. -/
theorem coeff_prodSeries_mul_printedFullKSeries (μ : List Nat) (r : Nat) :
    coeff r (Prop51.prodSeries μ * printedFullKSeries μ) =
      ∑ j ∈ Finset.range r,
        kCoeff μ (j + 1) * coeff (r - (j + 1)) (Prop51.prodSeries μ) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_printedFullKSeries]
  rw [Finset.sum_range_succ]
  rw [Nat.sub_self]
  change (∑ x ∈ Finset.range r,
      coeff x (Prop51.prodSeries μ) * kCoeff μ (r - x)) +
      coeff r (Prop51.prodSeries μ) * kCoeff μ 0 =
    ∑ j ∈ Finset.range r,
      kCoeff μ (j + 1) * coeff (r - (j + 1)) (Prop51.prodSeries μ)
  rw [show kCoeff μ 0 = 0 by rfl, mul_zero, add_zero]
  rw [← Finset.sum_range_reflect (fun x : Nat =>
    coeff x (Prop51.prodSeries μ) * kCoeff μ (r - x)) r]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjlt : j < r := Finset.mem_range.mp hj
  have hsub : r - (r - 1 - j) = j + 1 := by omega
  have hsub' : r - (j + 1) = r - 1 - j := by omega
  rw [hsub, hsub']
  ring

/-- Coefficient form of `A_μ=P_μ(1-K_μ)`. -/
theorem printedMidACoeff_eq_prod_sub_convolution (μ : List Nat) (r : Nat) :
    printedMidACoeff μ r =
      coeff r (Prop51.prodSeries μ) -
        ∑ j ∈ Finset.range r,
          kCoeff μ (j + 1) * coeff (r - (j + 1)) (Prop51.prodSeries μ) := by
  unfold printedMidACoeff printedMidASeries
  rw [mul_sub, mul_one, map_sub, coeff_prodSeries_mul_printedFullKSeries]

theorem sPower_nonneg (μ : List Nat) (r : Nat) :
    0 ≤ sPower μ r := by
  unfold sPower
  refine List.sum_nonneg fun x hx => ?_
  simp only [List.mem_map] at hx
  obtain ⟨mi, _hmi, rfl⟩ := hx
  positivity

theorem prodSeries_eq_expSeries_sPower (μ : List Nat) :
    Prop51.prodSeries μ =
      Prop51.expSeries (fun r => Prop51.c r * sPower μ r) := by
  rw [Prop51.prodSeries_eq_expSeries']
  congr 1
  funext r
  unfold sPower
  rw [mul_comm]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun mi _hmi => ?_)
  simp [Prop51.qq, one_div, inv_pow]

/-- The exponential recurrence gives `P_r <= Σ (c_j s_j) P_{r-j}` for
positive `r`. -/
theorem coeff_prodSeries_le_log_sum (μ : List Nat) (r : Nat) (hr : 1 ≤ r) :
    coeff r (Prop51.prodSeries μ) ≤
      ∑ j ∈ Finset.range r,
        (Prop51.c (j + 1) * sPower μ (j + 1)) *
          coeff (r - (j + 1)) (Prop51.prodSeries μ) := by
  obtain ⟨n, rfl⟩ : ∃ n : Nat, r = n + 1 := ⟨r - 1, by omega⟩
  rw [prodSeries_eq_expSeries_sPower]
  simp only [Prop51.coeff_expSeries]
  let L : Nat → ℚ := fun r => Prop51.c r * sPower μ r
  change Prop51.expCoeff L (n + 1) ≤
      ∑ j ∈ Finset.range (n + 1),
        L (j + 1) * Prop51.expCoeff L (n + 1 - (j + 1))
  have hrec := Prop51.expCoeff_succ_mul L n
  have hL_nonneg : ∀ r : Nat, 0 ≤ L r := by
    intro r
    exact mul_nonneg (Prop51.c_nonneg r) (sPower_nonneg μ r)
  have hsum_bound :
      ∑ t ∈ Finset.range (n + 1),
          ((t + 1 : Nat) : ℚ) * L (t + 1) * Prop51.expCoeff L (n - t)
        ≤
      ((n + 1 : Nat) : ℚ) *
        ∑ t ∈ Finset.range (n + 1),
          L (t + 1) * Prop51.expCoeff L (n - t) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun t ht => ?_
    have htlt : t < n + 1 := Finset.mem_range.mp ht
    have hcoef_nonneg : 0 ≤ L (t + 1) * Prop51.expCoeff L (n - t) :=
      mul_nonneg (hL_nonneg (t + 1))
        (Prop51.expCoeff_nonneg hL_nonneg (n - t))
    have hcast : ((t + 1 : Nat) : ℚ) ≤ ((n + 1 : Nat) : ℚ) := by
      exact_mod_cast Nat.succ_le_of_lt htlt
    calc
      ((t + 1 : Nat) : ℚ) * L (t + 1) * Prop51.expCoeff L (n - t)
          = ((t + 1 : Nat) : ℚ) *
              (L (t + 1) * Prop51.expCoeff L (n - t)) := by ring
      _ ≤ ((n + 1 : Nat) : ℚ) *
              (L (t + 1) * Prop51.expCoeff L (n - t)) :=
            mul_le_mul_of_nonneg_right hcast hcoef_nonneg
  rw [← hrec] at hsum_bound
  have hpos : (0 : ℚ) < (n + 1 : Nat) := by positivity
  have hsum_reindex :
      (∑ t ∈ Finset.range (n + 1),
          L (t + 1) * Prop51.expCoeff L (n - t)) =
        ∑ j ∈ Finset.range (n + 1),
          L (j + 1) * Prop51.expCoeff L (n + 1 - (j + 1)) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjlt : j < n + 1 := Finset.mem_range.mp hj
    have hsub : n - j = n + 1 - (j + 1) := by omega
    rw [hsub]
  rw [hsum_reindex] at hsum_bound
  nlinarith

/-- Positive-degree `A_μ` coefficients are nonpositive once the marked
coefficients dominate the logarithmic coefficients of `P_μ`. -/
theorem printedMidACoeff_nonpos_of_kCoeff_ge_logCoeff (μ : List Nat) (r : Nat)
    (hr : 1 ≤ r)
    (hK : ∀ j : Nat, 1 ≤ j → j ≤ r →
      Prop51.c j * sPower μ j ≤ kCoeff μ j) :
    printedMidACoeff μ r ≤ 0 := by
  rw [printedMidACoeff_eq_prod_sub_convolution]
  have hP_le := coeff_prodSeries_le_log_sum μ r hr
  have hlog_le_K :
      (∑ j ∈ Finset.range r,
          (Prop51.c (j + 1) * sPower μ (j + 1)) *
            coeff (r - (j + 1)) (Prop51.prodSeries μ)) ≤
        ∑ j ∈ Finset.range r,
          kCoeff μ (j + 1) *
            coeff (r - (j + 1)) (Prop51.prodSeries μ) := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hjlt : j < r := Finset.mem_range.mp hj
    have hKj := hK (j + 1) (by omega) (by omega)
    have hPnonneg :
        0 ≤ coeff (r - (j + 1)) (Prop51.prodSeries μ) :=
      Prop51.coeff_prodSeries_nonneg μ (r - (j + 1))
    exact mul_le_mul_of_nonneg_right hKj hPnonneg
  linarith

theorem sPower_le_markedWeight_of_positive (μ : List Nat)
    (hpos : ∀ m ∈ μ, 1 ≤ m) (r : Nat) :
    sPower μ r ≤ markedWeight μ r := by
  induction μ with
  | nil =>
      simp [sPower, markedWeight]
  | cons mi μ ih =>
      have hmi_nat : 1 ≤ mi := hpos mi (by simp)
      have htail : ∀ m ∈ μ, 1 ≤ m := by
        intro m hm
        exact hpos m (by simp [hm])
      have ih' := ih htail
      unfold sPower markedWeight at ih' ⊢
      simp only [List.map_cons, List.sum_cons]
      have hmi : (1 : ℚ) ≤ (mi : ℚ) := by exact_mod_cast hmi_nat
      have hterm :
          1 / (((mi : ℚ) + 1)^r) ≤ (mi : ℚ) / (((mi : ℚ) + 1)^r) :=
        div_le_div_of_nonneg_right hmi (by positivity)
      have hterm' :
          1 / (((mi + 1 : Nat) : ℚ)^r) ≤
            (mi : ℚ) / (((mi + 1 : Nat) : ℚ)^r) := by
        simpa [Nat.cast_add, Nat.cast_one] using hterm
      exact add_le_add hterm' ih'

theorem c_le_phiCoeff_of_two_le (r : Nat) (hr : 2 ≤ r) :
    Prop51.c r ≤ phiCoeff r := by
  obtain ⟨n, rfl⟩ : ∃ n : Nat, r = n + 2 := ⟨r - 2, by omega⟩
  have hdub : Prop51.d (n + 2) ≤ 4 / 25 :=
    Prop51.d_ub (n + 2) (by omega)
  have hdlb : 5 / 36 ≤ Prop51.d (n + 1) :=
    Prop51.d_lb (n + 1) (by omega)
  have hd2 : Prop51.d (n + 2) ≤ 2 * Prop51.d (n + 1) := by
    nlinarith
  let A : ℚ := (6 : ℚ)^(n + 1) * ((n.factorial : Nat) : ℚ)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hfactor_nonneg : 0 ≤ 6 * ((n + 1 : Nat) : ℚ) * A := by
    positivity
  calc
    Prop51.c (n + 2)
        = (6 * ((n + 1 : Nat) : ℚ) * A) * Prop51.d (n + 2) := by
          rw [Prop51.c_eq_d (n + 2)]
          dsimp [A]
          rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
          rw [show (n + 1).factorial = (n + 1) * n.factorial by
            rw [Nat.factorial_succ]]
          push_cast
          ring
    _ ≤ (6 * ((n + 1 : Nat) : ℚ) * A) * (2 * Prop51.d (n + 1)) :=
          mul_le_mul_of_nonneg_left hd2 hfactor_nonneg
    _ = phiCoeff (n + 2) := by
          simp [phiCoeff]
          rw [Prop51.c_eq_d (n + 1)]
          dsimp [A]
          ring

theorem kCoeff_ge_logCoeff_of_positive (μ : List Nat)
    (hpos : ∀ m ∈ μ, 1 ≤ m) (r : Nat) (hr : 1 ≤ r) :
    Prop51.c r * sPower μ r ≤ kCoeff μ r := by
  rcases r with _ | r
  · omega
  rcases r with _ | r
  · simp [kCoeff, Prop51.c_one]
    have hsle := sPower_le_markedWeight_of_positive μ hpos 1
    have hs_nonneg := sPower_nonneg μ 1
    have hmw_nonneg := markedWeight_nonneg_of_coeffs μ 1
    nlinarith
  · have hsle := sPower_le_markedWeight_of_positive μ hpos (r + 2)
    have hphi : Prop51.c (r + 2) ≤
        12 * ((r + 1 : Nat) : ℚ) * Prop51.c (r + 1) := by
      simpa [phiCoeff] using c_le_phiCoeff_of_two_le (r + 2) (by omega)
    have hs_nonneg := sPower_nonneg μ (r + 2)
    have hmw_nonneg := markedWeight_nonneg_of_coeffs μ (r + 2)
    have hphi_nonneg :
        0 ≤ 12 * ((r + 1 : Nat) : ℚ) * Prop51.c (r + 1) := by
      exact mul_nonneg (mul_nonneg (by norm_num) (by positivity))
        (Prop51.c_nonneg (r + 1))
    simp [kCoeff]
    calc
      Prop51.c (r + 2) * sPower μ (r + 2)
          ≤ (12 * ((r + 1 : Nat) : ℚ) * Prop51.c (r + 1)) *
              sPower μ (r + 2) :=
            mul_le_mul_of_nonneg_right hphi hs_nonneg
      _ ≤ (12 * ((r + 1 : Nat) : ℚ) * Prop51.c (r + 1)) *
              markedWeight μ (r + 2) :=
            mul_le_mul_of_nonneg_left hsle hphi_nonneg
      _ = 12 * ((r : ℚ) + 1) * Prop51.c (r + 1) *
              markedWeight μ (r + 2) := by
            norm_num [Nat.cast_add, Nat.cast_one]

theorem printedMidACoeff_nonpos_of_positive (μ : List Nat)
    (hpos : ∀ m ∈ μ, 1 ≤ m) (r : Nat) (hr : 1 ≤ r) :
    printedMidACoeff μ r ≤ 0 :=
  printedMidACoeff_nonpos_of_kCoeff_ge_logCoeff μ r hr
    (fun j hj _hjr => kCoeff_ge_logCoeff_of_positive μ hpos j hj)

theorem printedMidACoeff_nonpos_of_partition {a : Nat} {μ : List Nat}
    (hμ : Prop51.IsPartitionOf μ (M a)) (r : Nat) (hr : 1 ≤ r) :
    printedMidACoeff μ r ≤ 0 := by
  exact printedMidACoeff_nonpos_of_positive μ hμ.2 r hr

/--
Exact convolution form of the printed coefficient after the `A_μ` rewrite.

This is the formal target behind the mid-range upper bound: the remaining
coefficientwise work is to prove that positive-degree coefficients of
`A_μ` are nonpositive and bounded in size by the one-parameter `midS` sequence.
-/
theorem printedCoeff_eq_B_mul_A_coeff (μ : List Nat) (a : Nat) :
    printedCoeff μ a =
      ∑ k ∈ Finset.range (a + 1),
        Prop51.Bq (N μ) k * printedMidACoeff μ (a - k) := by
  rw [← coeff_printedFullSeries_eq_printedCoeff μ a]
  rw [printedFullFSeries_eq_B_mul_prod]
  have hseries :
      Prop51.BSeriesQ (N μ) * Prop51.prodSeries μ * (1 - printedFullKSeries μ) =
        Prop51.BSeriesQ (N μ) * printedMidASeries μ := by
    unfold printedMidASeries
    ring
  rw [hseries]
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Prop51.coeff_BSeriesQ, coeff_printedMidASeries]

/-! ## Raw one-parameter upper-bound bookkeeping -/

/-- The all-simple partition of weight `M`. -/
def simpleParts (M : Nat) : List Nat :=
  List.replicate M 1

theorem sPower_simpleParts (M r : Nat) :
    sPower (simpleParts M) r = (M : ℚ) / (2 : ℚ)^r := by
  unfold sPower simpleParts
  simp [List.sum_replicate, div_eq_mul_inv]
  ring_nf
  exact Or.inl trivial

theorem markedWeight_simpleParts (M r : Nat) :
    markedWeight (simpleParts M) r = (M : ℚ) / (2 : ℚ)^r := by
  unfold markedWeight simpleParts
  simp [List.sum_replicate, div_eq_mul_inv]
  ring_nf
  exact Or.inl trivial

theorem kCoeff_simpleParts (M r : Nat) :
    kCoeff (simpleParts M) r = (M : ℚ) * phiCoeff r / (2 : ℚ)^r := by
  rw [kCoeff_eq_markedCoeff]
  unfold markedCoeff
  rw [markedWeight_simpleParts]
  ring

theorem coeff_prodSeries_simpleParts (M r : Nat) :
    coeff r (Prop51.prodSeries (simpleParts M)) = midQCoeff M r := by
  rw [prodSeries_eq_expSeries_sPower]
  simp only [Prop51.coeff_expSeries]
  unfold midQCoeff
  congr 1
  funext s
  rw [sPower_simpleParts]
  ring

theorem simpleK_convolution_eq_Q (M r : Nat) (hr : 1 ≤ r) :
    (∑ j ∈ Finset.range r,
        kCoeff (simpleParts M) (j + 1) * midQCoeff M (r - (j + 1))) =
      ((M : ℚ) + 6 * (r : ℚ) - 6) * midQCoeff M (r - 1) := by
  rcases r with _ | r
  · omega
  rcases r with _ | n
  · simp [kCoeff_simpleParts, phiCoeff]
  let F : Nat → ℚ := fun j =>
    kCoeff (simpleParts M) (j + 1) * midQCoeff M (n + 2 - (j + 1))
  change (∑ j ∈ Finset.range (n + 2), F j) =
    ((M : ℚ) + 6 * ((n + 2 : Nat) : ℚ) - 6) * midQCoeff M (n + 2 - 1)
  have hsplit :
      (∑ j ∈ Finset.range (n + 2), F j) =
        (∑ j ∈ Finset.range (n + 1), F (j + 1)) + F 0 := by
    simpa [show n + 2 = n + 1 + 1 by omega] using
      (Finset.sum_range_succ' F (n + 1))
  rw [hsplit]
  have hF0 : F 0 = (M : ℚ) * midQCoeff M (n + 1) := by
    dsimp [F]
    simp [kCoeff_simpleParts, phiCoeff]
  have hrec :
      (∑ j ∈ Finset.range (n + 1),
        ((j + 1 : Nat) : ℚ) *
          ((M : ℚ) * Prop51.c (j + 1) / (2 : ℚ)^(j + 1)) *
          midQCoeff M (n - j)) =
        ((n + 1 : Nat) : ℚ) * midQCoeff M (n + 1) := by
    rw [midQCoeff_succ M n]
    have hden : ((n + 1 : Nat) : ℚ) ≠ 0 := by
      exact_mod_cast (by omega : (n + 1 : Nat) ≠ 0)
    field_simp [hden]
    refine Finset.sum_congr rfl fun x hx => ?_
    ring
  have hshift :
      (∑ j ∈ Finset.range (n + 1), F (j + 1)) =
        6 * ((n + 1 : Nat) : ℚ) * midQCoeff M (n + 1) := by
    calc
      (∑ j ∈ Finset.range (n + 1), F (j + 1))
          =
        6 * (∑ j ∈ Finset.range (n + 1),
          ((j + 1 : Nat) : ℚ) *
            ((M : ℚ) * Prop51.c (j + 1) / (2 : ℚ)^(j + 1)) *
            midQCoeff M (n - j)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hjlt : j < n + 1 := Finset.mem_range.mp hj
          dsimp [F]
          rw [kCoeff_simpleParts]
          simp [phiCoeff]
          have hpow : (2 : ℚ)^(j + 2) =
              (2 : ℚ) * (2 : ℚ)^(j + 1) := by
            rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
            ring
          rw [hpow]
          field_simp [(by positivity : (2 : ℚ)^(j + 1) ≠ 0)]
          ring
      _ = 6 * ((n + 1 : Nat) : ℚ) * midQCoeff M (n + 1) := by
          rw [hrec]
          ring
  rw [hF0, hshift]
  have hsub_top : n + 2 - 1 = n + 1 := by omega
  rw [hsub_top]
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

/-- Coefficients of the all-simple marked numerator. -/
noncomputable def printedMidSimpleACoeff (M r : Nat) : ℚ :=
  printedMidACoeff (simpleParts M) r

/-- `R_r(M)=-[t^r]A_M^{simp}` in the printed proof. -/
noncomputable def printedMidRCoeff (M r : Nat) : ℚ :=
  -printedMidSimpleACoeff M r

theorem printedMidSimpleACoeff_eq_midQ_sub_simpleK (M r : Nat) :
    printedMidSimpleACoeff M r =
      midQCoeff M r -
        ∑ j ∈ Finset.range r,
          kCoeff (simpleParts M) (j + 1) * midQCoeff M (r - (j + 1)) := by
  unfold printedMidSimpleACoeff
  rw [printedMidACoeff_eq_prod_sub_convolution]
  rw [coeff_prodSeries_simpleParts]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [coeff_prodSeries_simpleParts]

/-- The raw all-simple remainder coefficient is the scaled certificate `S`. -/
theorem printedMidRCoeff_eq_midS_scaled (M r : Nat) (hr : 1 ≤ r) :
    printedMidRCoeff M r =
      (((M : ℚ) * Prop51.c r) / (2 : ℚ)^r) * midS M r := by
  unfold printedMidRCoeff
  rw [printedMidSimpleACoeff_eq_midQ_sub_simpleK]
  rw [simpleK_convolution_eq_Q M r hr]
  have hS := midS_scaled_eq_Q M r hr
  linarith

/-- The unnormalized one-parameter upper bound before identifying it with
`midUNormFast`. -/
noncomputable def printedMidRawUpper (M N a : Nat) : ℚ :=
  Prop51.Bq N a +
    ∑ k ∈ Finset.range a,
      if 1 ≤ k ∧ Prop51.Bq N k < 0 then
        (-Prop51.Bq N k) * printedMidRCoeff M (a - k)
      else 0

/--
Convolution/sign bookkeeping for the mid majorant.

The two nontrivial analytic inputs are kept explicit:
positive-degree coefficients of `A_μ` are nonpositive, and `A_μ` dominates the
all-simple marked numerator coefficientwise.
-/
theorem printedCoeff_le_rawUpper_of_A_bounds (μ : List Nat) (a M Ntot : Nat)
    (hN : Ntot = N μ)
    (hAnonpos : ∀ r : Nat, 1 ≤ r → printedMidACoeff μ r ≤ 0)
    (hAcomp : ∀ r : Nat, printedMidSimpleACoeff M r ≤ printedMidACoeff μ r) :
    printedCoeff μ a ≤ printedMidRawUpper M Ntot a := by
  classical
  rw [printedCoeff_eq_B_mul_A_coeff]
  subst Ntot
  unfold printedMidRawUpper
  rw [Finset.sum_range_succ]
  have hlast :
      Prop51.Bq (N μ) a * printedMidACoeff μ (a - a) = Prop51.Bq (N μ) a := by
    rw [Nat.sub_self, coeff_printedMidASeries_zero]
    ring
  rw [hlast]
  have hsum_le :
      (∑ x ∈ Finset.range a,
          Prop51.Bq (N μ) x * printedMidACoeff μ (a - x)) ≤
        ∑ k ∈ Finset.range a,
          if 1 ≤ k ∧ Prop51.Bq (N μ) k < 0 then
            (-Prop51.Bq (N μ) k) * printedMidRCoeff M (a - k)
          else 0 := by
    refine Finset.sum_le_sum fun k hk => ?_
    have hklt : k < a := Finset.mem_range.mp hk
    have hdeg : 1 ≤ a - k := by omega
    by_cases hkpos : 1 ≤ k
    · by_cases hBneg : Prop51.Bq (N μ) k < 0
      · rw [if_pos ⟨hkpos, hBneg⟩]
        have hcomp := hAcomp (a - k)
        have hmul :
            Prop51.Bq (N μ) k * printedMidACoeff μ (a - k) ≤
              Prop51.Bq (N μ) k * printedMidSimpleACoeff M (a - k) :=
          mul_le_mul_of_nonpos_left hcomp (le_of_lt hBneg)
        unfold printedMidRCoeff at hmul ⊢
        linarith
      · rw [if_neg (by exact fun h => hBneg h.2)]
        have hA := hAnonpos (a - k) hdeg
        have hBnonneg : 0 ≤ Prop51.Bq (N μ) k := le_of_not_gt hBneg
        exact mul_nonpos_of_nonneg_of_nonpos hBnonneg hA
    · have hk0 : k = 0 := by omega
      subst k
      rw [if_neg (by omega)]
      have hA := hAnonpos a (by omega)
      have hB0 : Prop51.Bq (N μ) 0 = 1 := by
        simp [Prop51.Bq]
      rw [hB0, one_mul]
      exact hA
  linarith

theorem printedCoeff_le_rawUpper_of_Acomparison {a : Nat} {μ : List Nat}
    (hμ : Prop51.IsPartitionOf μ (M a))
    (hAcomp : ∀ r : Nat, printedMidSimpleACoeff (M a) r ≤ printedMidACoeff μ r) :
    printedCoeff μ a ≤ printedMidRawUpper (M a) (N μ) a :=
  printedCoeff_le_rawUpper_of_A_bounds μ a (M a) (N μ) rfl
    (fun r hr => printedMidACoeff_nonpos_of_partition hμ r hr)
    hAcomp

/--
Remaining mid-range bridge target.

For every partition in the mid range, the printed coefficient is bounded above
by the certified one-parameter quantity, after undoing the normalization by
`N c_a`.
-/
def PrintedMidUpperBound : Prop :=
  ∀ a : Nat, 14 ≤ a → a ≤ 149 →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      printedCoeff μ a ≤ (((N μ : Nat) : ℚ) * Prop51.c a) *
        midUNormFast a (N μ)

/-- The all-simple comparison target from the printed proof. -/
def PrintedMidSimpleComparison : Prop :=
  ∀ a : Nat, 14 ≤ a → a ≤ 149 →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      ∀ r : Nat, printedMidSimpleACoeff (M a) r ≤ printedMidACoeff μ r

/-- Identification of the raw `B/R` bound with the normalized certificate
kernel, after undoing the factor `N c_a`. -/
def PrintedMidRawToNormBound : Prop :=
  ∀ a : Nat, 14 ≤ a → a ≤ 149 →
    ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
      printedMidRawUpper (M a) (N μ) a ≤
        (((N μ : Nat) : ℚ) * Prop51.c a) * midUNormFast a (N μ)

theorem printedMidUpperBound_of_simpleComparison_rawToNorm
    (hcomp : PrintedMidSimpleComparison)
    (hraw : PrintedMidRawToNormBound) :
    PrintedMidUpperBound := by
  intro a ha_lo ha_hi μ hμ
  exact (printedCoeff_le_rawUpper_of_Acomparison hμ
    (hcomp a ha_lo ha_hi μ hμ)).trans (hraw a ha_lo ha_hi μ hμ)

private theorem mid_N_pos_of_partition {a : Nat} {μ : List Nat}
    (ha : 14 ≤ a) (hμ : Prop51.IsPartitionOf μ (M a)) :
    0 < N μ := by
  obtain ⟨hsum, _hpos⟩ := hμ
  unfold N
  rw [Prop51.sum_map_add_one]
  unfold M at hsum
  omega

private theorem mid_den_pos_of_partition {a : Nat} {μ : List Nat}
    (ha : 14 ≤ a) (hμ : Prop51.IsPartitionOf μ (M a)) :
    0 < (((N μ : Nat) : ℚ) * Prop51.c a) := by
  have hN : (0 : ℚ) < ((N μ : Nat) : ℚ) := by
    exact_mod_cast mid_N_pos_of_partition (a := a) (μ := μ) ha hμ
  have hc : 0 < Prop51.c a := Prop51.c_pos a (by omega)
  exact mul_pos hN hc

/--
Closing the printed mid-range sign from the coefficientwise bridge and the
native interval certificates.
-/
theorem printedCoeffNegativityMid_of_upperBound
    (hbound : PrintedMidUpperBound) :
    PrintedCoeffNegativityMid := by
  intro a ha_lo ha_hi μ hμ
  have hU : midUNormFast a (N μ) < 0 :=
    midUNormFast_neg_rows_14_149_of_partition a μ ha_lo ha_hi hμ
  have hden : 0 < (((N μ : Nat) : ℚ) * Prop51.c a) :=
    mid_den_pos_of_partition (a := a) (μ := μ) ha_lo hμ
  have hscaled :
      (((N μ : Nat) : ℚ) * Prop51.c a) * midUNormFast a (N μ) < 0 :=
    mul_neg_of_pos_of_neg hden hU
  exact lt_of_le_of_lt (hbound a ha_lo ha_hi μ hμ) hscaled

end Prop52
