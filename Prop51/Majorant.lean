/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# The majorant inequality (Layer A, part 3)

This file closes Layer A: for every positive partition `μ` (all parts ≥ 1)
with `N = Σ (m_i + 1)` and `a ≥ 1`,

  `bCoeff μ a ≤ N·c_a · Unorm a N`    (`bCoeff_le_unorm`)

and consequently `Unorm a N < 0 → bCoeff μ a < 0` (`bCoeff_neg_of_unorm`).
This is eq. (8) of the paper.  Main ingredients:

* `c_nonneg`/`c_pos` — positivity of the log-coefficients (induction on the
  Riccati recurrence);
* `expCoeff_nonneg`, `expCoeff_mono` — the exp-recurrence preserves
  nonnegativity and is monotone in the exponent sequence;
* `expSeries_mul/pow`, `rescale_expSeries` — exp-algebra, by
  `logDeriv_unique`; hence `prodSeries μ` is itself an `expSeries`
  (`prodSeries_eq_expSeries'`), so the paper's domination
  `P_k(μ) ≤ Q_k(N)` reduces to `expCoeff_mono` plus the scalar inequality
  `Σ_i q_i^{-r} ≤ (N/2)·2^{-r}`;
* sign bookkeeping: terms with `B_k ≤ 0` are dropped, the rest compared.

Everything here uses only the standard three axioms.
-/
import Prop51.BCoeffSeries

namespace Prop51

open PowerSeries

/-! ## Positivity of `c` -/

theorem c_nonneg : ∀ r, 0 ≤ c r := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
      match r with
      | 0 => simp
      | 1 => norm_num [c_one]
      | (n+2) =>
          rw [c_succ_succ]
          have h1 : 0 ≤ 6*(((n+2 : Nat) : ℚ) - 1) * c (n+1) := by
            have hc := ih (n+1) (by omega)
            have hn : (0:ℚ) ≤ ((n+2 : Nat) : ℚ) - 1 := by push_cast; linarith
            exact mul_nonneg (mul_nonneg (by norm_num) hn) hc
          have h2 : 0 ≤ ((List.range (n+1)).map fun (i : Nat) =>
              (i : ℚ) * ((n+1-i : Nat) : ℚ) * c i * c (n+1-i)).sum := by
            refine List.sum_nonneg fun x hx => ?_
            simp only [List.mem_map, List.mem_range] at hx
            obtain ⟨i, hi, rfl⟩ := hx
            have hci := ih i (by omega)
            have hci' := ih (n+1-i) (by omega)
            positivity
          have h3 : (0:ℚ) ≤ 6/((n+2 : Nat) : ℚ) :=
            div_nonneg (by norm_num) (Nat.cast_nonneg _)
          nlinarith

theorem c_pos : ∀ r, 1 ≤ r → 0 < c r := by
  intro r hr
  match r, hr with
  | 1, _ => norm_num [c_one]
  | (n+2), _ =>
      rw [c_succ_succ]
      have h1 : 0 < 6*(((n+2 : Nat) : ℚ) - 1) * c (n+1) := by
        have hc := c_pos (n+1) (by omega)
        have hn : (0:ℚ) < ((n+2 : Nat) : ℚ) - 1 := by push_cast; linarith
        exact mul_pos (mul_pos (by norm_num) hn) hc
      have h2 : 0 ≤ ((List.range (n+1)).map fun (i : Nat) =>
          (i : ℚ) * ((n+1-i : Nat) : ℚ) * c i * c (n+1-i)).sum := by
        refine List.sum_nonneg fun x hx => ?_
        simp only [List.mem_map, List.mem_range] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        have hci := c_nonneg i
        have hci' := c_nonneg (n+1-i)
        positivity
      have h3 : (0:ℚ) ≤ 6/((n+2 : Nat) : ℚ) :=
        div_nonneg (by norm_num) (Nat.cast_nonneg _)
      nlinarith

/-- `c_r ≤ A_r` — the log-coefficients are dominated by the coefficients
(positivity of the disconnected part), via the bridge identity. -/
theorem c_le_Aseq (n : Nat) : c n ≤ Aseq n := by
  match n with
  | 0 => simp [c_zero]
  | (n+1) =>
      have h := bridge_identity n
      have hterm : ((n+1 : Nat) : ℚ) * c (n+1)
          ≤ ∑ t ∈ Finset.range (n+1),
              ((t+1 : Nat) : ℚ) * c (t+1) * Aseq (n-t) := by
        have hmem : n ∈ Finset.range (n+1) := by simp
        have hle := Finset.single_le_sum
          (f := fun t => ((t+1 : Nat) : ℚ) * c (t+1) * Aseq (n-t))
          (fun t _ => by
            have h1 := c_nonneg (t+1)
            have h2 : 0 ≤ Aseq (n-t) := by
              unfold Aseq
              exact div_nonneg (Nat.cast_nonneg _) (by positivity)
            positivity) hmem
        simpa using hle
      rw [← h] at hterm
      have hpos : (0:ℚ) < ((n+1 : Nat) : ℚ) := by positivity
      nlinarith

/-! ## Monotonicity of the exp-recurrence -/

theorem expCoeff_nonneg {L : Nat → ℚ} (hL : ∀ r, 0 ≤ L r) :
    ∀ n, 0 ≤ expCoeff L n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      match n with
      | 0 => norm_num
      | (n+1) =>
          have h := expCoeff_succ_mul L n
          have hS : 0 ≤ ∑ t ∈ Finset.range (n+1),
              ((t+1 : Nat) : ℚ) * L (t+1) * expCoeff L (n-t) := by
            refine Finset.sum_nonneg fun t ht => ?_
            have h1 := hL (t+1)
            have h2 := ih (n-t) (by omega)
            positivity
          have hpos : (0:ℚ) < ((n+1 : Nat) : ℚ) := by positivity
          nlinarith

theorem expCoeff_mono {L M : Nat → ℚ} (hL : ∀ r, 0 ≤ L r)
    (hLM : ∀ r, L r ≤ M r) : ∀ n, expCoeff L n ≤ expCoeff M n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      match n with
      | 0 => norm_num
      | (n+1) =>
          have hML := expCoeff_succ_mul L n
          have hMM := expCoeff_succ_mul M n
          have hS : ∑ t ∈ Finset.range (n+1),
                ((t+1 : Nat) : ℚ) * L (t+1) * expCoeff L (n-t)
              ≤ ∑ t ∈ Finset.range (n+1),
                ((t+1 : Nat) : ℚ) * M (t+1) * expCoeff M (n-t) := by
            refine Finset.sum_le_sum fun t ht => ?_
            have h1 : ((t+1 : Nat) : ℚ) * L (t+1) ≤ ((t+1 : Nat) : ℚ) * M (t+1) :=
              mul_le_mul_of_nonneg_left (hLM (t+1)) (by positivity)
            have h2 : expCoeff L (n-t) ≤ expCoeff M (n-t) := ih (n-t) (by omega)
            have h3 : 0 ≤ expCoeff L (n-t) := expCoeff_nonneg hL (n-t)
            have h4 : (0:ℚ) ≤ ((t+1 : Nat) : ℚ) * M (t+1) :=
              mul_nonneg (by positivity) (le_trans (hL (t+1)) (hLM (t+1)))
            exact mul_le_mul h1 h2 h3 h4
          have hpos : (0:ℚ) < ((n+1 : Nat) : ℚ) := by positivity
          nlinarith

/-! ## Exp-algebra: products, powers, rescaling -/

theorem expSeries_mul (L M : Nat → ℚ) :
    expSeries L * expSeries M = expSeries (fun r => L r + M r) := by
  apply logDeriv_unique (u := mk fun r => (r : ℚ) * (L r + M r))
  · rw [← coeff_zero_eq_constantCoeff, coeff_mk]; simp
  · rw [map_mul, constantCoeff_expSeries, constantCoeff_expSeries, one_mul]
  · exact constantCoeff_expSeries _
  · rw [theta_mul, theta_expSeries, theta_expSeries]
    have : (mk fun r => (r : ℚ) * (L r + M r))
        = (mk fun r => (r : ℚ) * L r) + (mk fun r => (r : ℚ) * M r) := by
      ext n
      rw [map_add, coeff_mk, coeff_mk, coeff_mk]
      ring
    rw [this]
    ring
  · exact theta_expSeries _

theorem expSeries_zero : expSeries (fun _ => 0) = 1 := by
  apply logDeriv_unique (u := 0)
  · simp
  · exact constantCoeff_expSeries _
  · simp
  · rw [theta_expSeries]
    have : (mk fun r => (r : ℚ) * 0) = 0 := by
      ext n; simp
    rw [this, zero_mul]
  · rw [theta_one, zero_mul]

theorem expSeries_pow (L : Nat → ℚ) : ∀ n : Nat,
    (expSeries L) ^ n = expSeries (fun r => (n : ℚ) * L r)
  | 0 => by
      rw [pow_zero]
      have : (fun r => ((0 : Nat) : ℚ) * L r) = fun _ => (0:ℚ) := by
        funext r; simp
      rw [this, expSeries_zero]
  | (n+1) => by
      rw [pow_succ, expSeries_pow L n, expSeries_mul]
      congr 1
      funext r
      push_cast
      ring

theorem rescale_expSeries (q : ℚ) (L : Nat → ℚ) :
    rescale q (expSeries L) = expSeries (fun r => q^r * L r) := by
  apply logDeriv_unique (u := mk fun r => (r : ℚ) * (q^r * L r))
  · rw [← coeff_zero_eq_constantCoeff, coeff_mk]; simp
  · rw [← coeff_zero_eq_constantCoeff, coeff_rescale]
    simp
  · exact constantCoeff_expSeries _
  · have h1 : theta (rescale q (expSeries L))
        = rescale q (theta (expSeries L)) := theta_rescale q _
    rw [h1, theta_expSeries, map_mul]
    have h2 : rescale q (mk fun r => (r : ℚ) * L r)
        = mk fun r => (r : ℚ) * (q^r * L r) := by
      ext n
      rw [coeff_rescale, coeff_mk, coeff_mk]
      ring
    rw [h2]
  · exact theta_expSeries _

/-- `prodSeries μ` is itself an `expSeries`: its exponent sequence is
`(Σ_i q_i^{-r})·c_r`. -/
theorem prodSeries_eq_expSeries' : ∀ μ : List Nat,
    prodSeries μ
      = expSeries (fun r => (μ.map fun mi => ((qq mi)⁻¹)^r).sum * c r)
  | [] => by
      show (1 : ℚ⟦X⟧) = _
      have : (fun r => ((List.map (fun mi => ((qq mi)⁻¹)^r) ([] : List Nat)).sum * c r))
          = fun _ => (0:ℚ) := by
        funext r; simp
      rw [this, expSeries_zero]
  | (mi :: μ) => by
      show rescale (qq mi)⁻¹ Cseries * prodSeries μ = _
      rw [Cseries_eq_expSeries_c, rescale_expSeries,
        prodSeries_eq_expSeries' μ, expSeries_mul]
      congr 1
      funext r
      simp only [List.map_cons, List.sum_cons]
      ring

/-! ## The coefficient bounds `0 ≤ P_j` and `P_j ≤ Q_j` -/

private theorem sum_map_const (l : List Nat) (x : ℚ) :
    (l.map fun _ => x).sum = (l.length : ℚ) * x := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      push_cast
      ring

private theorem two_mul_length_le (μ : List Nat) (hμ : ∀ m ∈ μ, 1 ≤ m) :
    2 * μ.length ≤ (μ.map (· + 1)).sum := by
  induction μ with
  | nil => simp
  | cons m μ ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have h1 := hμ m (by simp)
      have h2 := ih (fun x hx => hμ x (by simp [hx]))
      omega

/-- The exponent sequence of `prodSeries` is nonneg. -/
private theorem prodL_nonneg (μ : List Nat) (r : Nat) :
    0 ≤ (μ.map fun mi => ((qq mi)⁻¹)^r).sum * c r := by
  have h1 : 0 ≤ (μ.map fun mi => ((qq mi)⁻¹)^r).sum := by
    refine List.sum_nonneg fun x hx => ?_
    simp only [List.mem_map] at hx
    obtain ⟨mi, -, rfl⟩ := hx
    have h0 : (0:ℚ) < qq mi := by
      unfold qq
      exact_mod_cast Nat.succ_pos mi
    exact pow_nonneg (inv_nonneg.mpr (le_of_lt h0)) r
  exact mul_nonneg h1 (c_nonneg r)

theorem coeff_prodSeries_nonneg (μ : List Nat) (j : Nat) :
    0 ≤ coeff j (prodSeries μ) := by
  rw [prodSeries_eq_expSeries', coeff_expSeries]
  exact expCoeff_nonneg (prodL_nonneg μ) j

/-- The domination `P_j(μ) ≤ Q_j(N)` (paper eq. 7), reduced to
`expCoeff_mono` and `Σ_i q_i^{-r} ≤ (N/2)·2^{-r}`. -/
theorem coeff_prodSeries_le (μ : List Nat) (hμ : ∀ m ∈ μ, 1 ≤ m) (j : Nat) :
    coeff j (prodSeries μ)
      ≤ expCoeff (fun r => ((((μ.map (· + 1)).sum : Nat) : ℚ))/2 * c r / 2^r) j := by
  rw [prodSeries_eq_expSeries', coeff_expSeries]
  refine expCoeff_mono (prodL_nonneg μ) (fun r => ?_) j
  have hscalar : (μ.map fun mi => ((qq mi)⁻¹)^r).sum
      ≤ ((((μ.map (· + 1)).sum : Nat) : ℚ))/2 * (2⁻¹:ℚ)^r := by
    have step1 : (μ.map fun mi => ((qq mi)⁻¹)^r).sum
        ≤ (μ.map fun _ => (2⁻¹:ℚ)^r).sum := by
      refine List.sum_le_sum fun mi hmi => ?_
      have h2q : (2:ℚ) ≤ qq mi := by
        have h1 := hμ mi hmi
        have h1' : (1:ℚ) ≤ (mi : ℚ) := by exact_mod_cast h1
        unfold qq
        push_cast
        linarith
      have hq0 : (0:ℚ) < qq mi := by linarith
      refine pow_le_pow_left₀ (inv_nonneg.mpr (le_of_lt hq0)) ?_ r
      have hcancel := mul_inv_cancel₀ (ne_of_gt hq0)
      have hip : (0:ℚ) < (qq mi)⁻¹ := inv_pos.mpr hq0
      nlinarith [hcancel, h2q, hip]
    have step2 : (μ.map fun _ => (2⁻¹:ℚ)^r).sum
        ≤ ((((μ.map (· + 1)).sum : Nat) : ℚ))/2 * (2⁻¹:ℚ)^r := by
      rw [sum_map_const]
      have hlen := two_mul_length_le μ hμ
      have : (μ.length : ℚ) ≤ ((((μ.map (· + 1)).sum : Nat) : ℚ))/2 := by
        rw [le_div_iff₀ (by norm_num : (0:ℚ) < 2)]
        exact_mod_cast by omega
      exact mul_le_mul_of_nonneg_right this (by positivity)
    linarith
  calc (μ.map fun mi => ((qq mi)⁻¹)^r).sum * c r
      ≤ (((((μ.map (· + 1)).sum : Nat) : ℚ))/2 * (2⁻¹:ℚ)^r) * c r := by
        exact mul_le_mul_of_nonneg_right hscalar (c_nonneg r)
    _ = ((((μ.map (· + 1)).sum : Nat) : ℚ))/2 * c r / 2^r := by
        rw [inv_pow]
        ring

/-! ## `C^N · B = 1` and the convolution form of `b` -/

/-- The official series `C(X)^{-N}`, as an `expSeries`. -/
noncomputable def BSeriesQ (N : Nat) : ℚ⟦X⟧ :=
  expSeries (fun r => -(N : ℚ) * c r)

theorem Cpow_mul_BSeriesQ (N : Nat) : Cseries ^ N * BSeriesQ N = 1 := by
  apply logDeriv_unique (u := 0)
  · simp
  · rw [map_mul, map_pow, constantCoeff_Cseries, one_pow, one_mul]
    exact constantCoeff_expSeries _
  · simp
  · rw [theta_mul, theta_pow theta_Cseries N, BSeriesQ, theta_expSeries]
    have hbal : PowerSeries.C (N:ℚ) * uSeries
        + (mk fun r => (r : ℚ) * (-(N : ℚ) * c r)) = 0 := by
      ext n
      rw [map_add, coeff_C_mul, coeff_uSeries, coeff_mk, map_zero]
      ring
    have expand : PowerSeries.C (N:ℚ) * uSeries * Cseries ^ N * expSeries (fun r => -(N : ℚ) * c r)
        + Cseries ^ N * ((mk fun r => (r : ℚ) * (-(N : ℚ) * c r)) * expSeries (fun r => -(N : ℚ) * c r))
        = (PowerSeries.C (N:ℚ) * uSeries
            + (mk fun r => (r : ℚ) * (-(N : ℚ) * c r)))
          * (Cseries ^ N * expSeries (fun r => -(N : ℚ) * c r)) := by
      ring
    rw [expand, hbal, zero_mul]
  · rw [theta_one, zero_mul]

/-- Convolution form: `bSeries μ = B(N) · P(μ)`. -/
theorem bSeries_eq_B_mul_prod (μ : List Nat) :
    bSeries μ = BSeriesQ ((μ.map (· + 1)).sum) * prodSeries μ := by
  have h1 := bSeries_official μ
  have h2 := Cpow_mul_BSeriesQ ((μ.map (· + 1)).sum)
  calc bSeries μ
      = (Cseries ^ ((μ.map (· + 1)).sum) * BSeriesQ ((μ.map (· + 1)).sum))
        * bSeries μ := by rw [h2, one_mul]
    _ = BSeriesQ ((μ.map (· + 1)).sum)
        * (Cseries ^ ((μ.map (· + 1)).sum) * bSeries μ) := by ring
    _ = _ := by rw [h1]



/-! ## The official majorant coefficients -/

/-- `B_k(N) = [X^k] C(X)^{-N}` (official; cf. `coeff_BSeriesQ`). -/
def Bq (N k : Nat) : ℚ := expCoeff (fun r => -(N : ℚ) * c r) k

/-- `Q_j(N) = [X^j] C(X/2)^{N/2}` (official; see `QSeriesQ_sq`). -/
def Qq (N j : Nat) : ℚ := expCoeff (fun r => (N : ℚ)/2 * c r / 2^r) j

theorem coeff_BSeriesQ (N k : Nat) : coeff k (BSeriesQ N) = Bq N k :=
  coeff_expSeries k _

/-- The square of `Σ_j Q_j(N) X^j` is `C(X/2)^N` — the official sense in
which it is "`C(X/2)^{N/2}`". -/
theorem QSeriesQ_sq (N : Nat) :
    (expSeries (fun r => (N : ℚ)/2 * c r / 2^r)) ^ 2
      = rescale (2⁻¹ : ℚ) Cseries ^ N := by
  rw [Cseries_eq_expSeries_c, rescale_expSeries, expSeries_pow,
    expSeries_pow]
  congr 1
  funext r
  rw [inv_pow]
  push_cast
  field_simp

/-! ## The majorant inequality (paper eq. 8) -/

theorem bCoeff_le_U (μ : List Nat) (hμ : ∀ m ∈ μ, 1 ≤ m) (m : Nat) :
    bCoeff μ (m+1)
      ≤ Bq ((μ.map (· + 1)).sum) (m+1) + Qq ((μ.map (· + 1)).sum) (m+1)
        + ∑ k ∈ Finset.range (m+1),
            (if 1 ≤ k ∧ 0 < Bq ((μ.map (· + 1)).sum) k
             then Bq ((μ.map (· + 1)).sum) k * Qq ((μ.map (· + 1)).sum) ((m+1)-k)
             else 0) := by
  classical
  have hb : bCoeff μ (m+1)
      = ∑ k ∈ Finset.range (m+2),
          Bq ((μ.map (· + 1)).sum) k * coeff ((m+1)-k) (prodSeries μ) := by
    have h0 : bCoeff μ (m+1) = coeff (m+1) (bSeries μ) := (coeff_mk _ _).symm
    rw [h0, bSeries_eq_B_mul_prod, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    exact Finset.sum_congr rfl fun k hk => by rw [coeff_BSeriesQ]
  rw [hb, Finset.sum_range_succ, Finset.sum_range_succ']
  have hP0 : coeff ((m+1)-(m+1)) (prodSeries μ) = 1 := by
    rw [Nat.sub_self, coeff_zero_eq_constantCoeff, constantCoeff_prodSeries]
  have hB0 : Bq ((μ.map (· + 1)).sum) 0 = 1 := expCoeff_zero _
  have hPa : coeff ((m+1)-0) (prodSeries μ) ≤ Qq ((μ.map (· + 1)).sum) (m+1) :=
    coeff_prodSeries_le μ hμ (m+1)
  have hmid : ∑ i ∈ Finset.range m,
        Bq ((μ.map (· + 1)).sum) (i+1) * coeff ((m+1)-(i+1)) (prodSeries μ)
      ≤ ∑ i ∈ Finset.range m,
        (if 0 < Bq ((μ.map (· + 1)).sum) (i+1)
         then Bq ((μ.map (· + 1)).sum) (i+1) * Qq ((μ.map (· + 1)).sum) ((m+1)-(i+1))
         else 0) := by
    refine Finset.sum_le_sum fun i hi => ?_
    by_cases hpos : 0 < Bq ((μ.map (· + 1)).sum) (i+1)
    · rw [if_pos hpos]
      exact mul_le_mul_of_nonneg_left
        (coeff_prodSeries_le μ hμ ((m+1)-(i+1))) (le_of_lt hpos)
    · rw [if_neg hpos]
      push_neg at hpos
      have hPnn := coeff_prodSeries_nonneg μ ((m+1)-(i+1))
      nlinarith
  have hT : ∑ k ∈ Finset.range (m+1),
        (if 1 ≤ k ∧ 0 < Bq ((μ.map (· + 1)).sum) k
         then Bq ((μ.map (· + 1)).sum) k * Qq ((μ.map (· + 1)).sum) ((m+1)-k)
         else 0)
      = ∑ i ∈ Finset.range m,
        (if 0 < Bq ((μ.map (· + 1)).sum) (i+1)
         then Bq ((μ.map (· + 1)).sum) (i+1) * Qq ((μ.map (· + 1)).sum) ((m+1)-(i+1))
         else 0) := by
    rw [Finset.sum_range_succ']
    have hzero : (if 1 ≤ 0 ∧ 0 < Bq ((μ.map (· + 1)).sum) 0
        then Bq ((μ.map (· + 1)).sum) 0 * Qq ((μ.map (· + 1)).sum) ((m+1)-0)
        else 0) = 0 := by
      rw [if_neg]
      rintro ⟨h1, -⟩
      omega
    rw [hzero, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : (1:ℕ) ≤ i+1 := by omega
    rw [if_congr (and_iff_right h1) rfl rfl]
  rw [hP0, mul_one, hB0, one_mul, hT]
  linarith

/-! ## Bridge to the computational `Unorm` -/

theorem BListQ_getD_eq (N a k : Nat) (hk : k ≤ a) :
    (BListQ (cList a) N a).getD k 0 = Bq N k := by
  unfold BListQ Bq
  rw [expList_getD_eq _ k a hk]
  exact expCoeff_congr_le k fun r hr => by
    rw [cList_getD_eq r a (le_trans hr hk)]

theorem QListQ_getD_eq (N a k : Nat) (hk : k ≤ a) :
    (QListQ (cList a) N a).getD k 0 = Qq N k := by
  unfold QListQ Qq
  rw [expList_getD_eq _ k a hk]
  exact expCoeff_congr_le k fun r hr => by
    rw [cList_getD_eq r a (le_trans hr hk)]

theorem Unorm_eq (a N : Nat) :
    Unorm a N
      = (Bq N a + Qq N a
          + ∑ k ∈ Finset.range a,
              (if 1 ≤ k ∧ 0 < Bq N k then Bq N k * Qq N (a-k) else 0))
        / ((N : ℚ) * c a) := by
  show (((BListQ (cList a) N a).getD a 0 + (QListQ (cList a) N a).getD a 0
      + ((List.range a).map fun (k : Nat) =>
          if 1 ≤ k ∧ 0 < (BListQ (cList a) N a).getD k 0
          then (BListQ (cList a) N a).getD k 0
            * (QListQ (cList a) N a).getD (a-k) 0
          else 0).sum)
      / ((N : ℚ) * (cList a).getD a 0)) = _
  rw [list_range_map_sum, BListQ_getD_eq N a a le_rfl,
    QListQ_getD_eq N a a le_rfl]
  have hc : (cList a).getD a 0 = c a := rfl
  rw [hc]
  congr 2
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ a := le_of_lt (Finset.mem_range.mp hk)
  rw [BListQ_getD_eq N a k hk', QListQ_getD_eq N a (a-k) (by omega)]

/-- Negativity transfer: if the (computational, certified) majorant is
negative, so is the Chen–Larson coefficient. -/
theorem bCoeff_neg_of_unorm (μ : List Nat) (a N : Nat)
    (hμ : ∀ m ∈ μ, 1 ≤ m) (hN : N = (μ.map (· + 1)).sum)
    (ha : 1 ≤ a) (hN1 : 1 ≤ N) (hU : Unorm a N < 0) :
    bCoeff μ a < 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, a = m+1 := ⟨a-1, by omega⟩
  have hb := bCoeff_le_U μ hμ m
  rw [← hN] at hb
  have hden : (0:ℚ) < (N : ℚ) * c (m+1) := by
    have h1 : (0:ℚ) < (N : ℚ) := by exact_mod_cast hN1
    exact mul_pos h1 (c_pos (m+1) (by omega))
  rw [Unorm_eq] at hU
  have hnum := mul_neg_of_neg_of_pos hU hden
  rw [div_mul_cancel₀ _ (ne_of_gt hden)] at hnum
  linarith

/-! ## List arithmetic helpers for the capstone -/

theorem sum_map_add_one (μ : List Nat) :
    (μ.map (· + 1)).sum = μ.sum + μ.length := by
  induction μ with
  | nil => simp
  | cons m μ ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      omega

theorem length_le_sum (μ : List Nat) (h : ∀ m ∈ μ, 1 ≤ m) :
    μ.length ≤ μ.sum := by
  induction μ with
  | nil => simp
  | cons m μ ih =>
      simp only [List.length_cons, List.sum_cons]
      have h1 := h m (by simp)
      have h2 := ih fun x hx => h x (by simp [hx])
      omega

end Prop51
