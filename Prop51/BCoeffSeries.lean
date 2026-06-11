/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Official characterization of `bCoeff` (Layer A, part 2)

The Chen–Larson coefficient `b_a(μ)` was *defined* in `Prop51.Defs` through
the exp-recurrence.  Here we prove it is the coefficient sequence officially
attached to the partition `μ`: with `q_i = m_i + 1` and `N = Σ q_i`,

  `Cseries ^ N * (Σ_a b_a(μ) X^a) = Π_i rescale (q_i⁻¹) Cseries`,

i.e. `Σ_a b_a(μ) X^a = Π_i C(q_i⁻¹ X) / C(X)^N` — multiplication form, no
inverse needed (`C^N` is a unit, so this determines the series uniquely).

Proof: both sides have constant coefficient 1 and the same logarithmic
derivative; conclude by `logDeriv_unique`.  The log-derivative computation
uses `N - D_r = Σ_i q_i^{-r}` — the defining identity of `D_r`.
-/
import Prop51.Bridge

namespace Prop51

open PowerSeries

/-! ## `expCoeff` only depends on an initial segment of `L` -/

theorem expList_congr_le {L L' : Nat → ℚ} : ∀ n, (∀ r ≤ n, L r = L' r) →
    expList L n = expList L' n
  | 0, _ => rfl
  | (n+1), h => by
      have ih := expList_congr_le n (fun r hr => h r (by omega))
      have hstep : (((List.range (n+1)).map fun (t : Nat) =>
            ((t+1 : Nat) : ℚ) * L (t+1) * (expList L n).getD (n-t) 0).sum)
          = (((List.range (n+1)).map fun (t : Nat) =>
            ((t+1 : Nat) : ℚ) * L' (t+1) * (expList L' n).getD (n-t) 0).sum) := by
        rw [ih]
        refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
        have ht' : t < n+1 := List.mem_range.mp ht
        rw [h (t+1) (by omega)]
      simp only [expList]
      rw [hstep, ih]

theorem expCoeff_congr_le {L L' : Nat → ℚ} (a : Nat)
    (h : ∀ r ≤ a, L r = L' r) : expCoeff L a = expCoeff L' a := by
  unfold expCoeff
  rw [expList_congr_le a h]

/-- `bCoeff μ` is `expCoeff` of the *untruncated* sequence `-D_r c_r`. -/
theorem bCoeff_eq_expCoeff (μ : List Nat) (a : Nat) :
    bCoeff μ a = expCoeff (fun r => -(Dr μ r) * c r) a := by
  unfold bCoeff
  exact expCoeff_congr_le a fun r hr => by rw [cList_getD_eq r a hr]

/-- The generating series `Σ_a b_a(μ) X^a`. -/
noncomputable def bSeries (μ : List Nat) : ℚ⟦X⟧ := mk fun a => bCoeff μ a

theorem bSeries_eq_expSeries (μ : List Nat) :
    bSeries μ = expSeries (fun r => -(Dr μ r) * c r) := by
  ext n
  rw [bSeries, coeff_mk, coeff_expSeries, bCoeff_eq_expCoeff]

/-! ## Logarithmic-derivative toolkit -/

theorem theta_one : theta (1 : ℚ⟦X⟧) = 0 := by
  rw [theta, derivativeFun_one, mul_zero]

theorem theta_Cseries : theta Cseries = uSeries * Cseries := by
  rw [Cseries_eq_expSeries_c]
  exact theta_expSeries c

theorem theta_rescale (a : ℚ) (F : ℚ⟦X⟧) :
    theta (rescale a F) = rescale a (theta F) := by
  ext n
  rw [coeff_theta, coeff_rescale, coeff_rescale, coeff_theta]
  ring

theorem theta_pow {F u : ℚ⟦X⟧} (h : theta F = u * F) :
    ∀ n : Nat, theta (F ^ n) = (PowerSeries.C (n : ℚ)) * u * F ^ n
  | 0 => by simp [theta_one]
  | (n+1) => by
      rw [pow_succ, theta_mul, theta_pow h n, h, Nat.cast_succ, map_add,
        map_one]
      ring

/-! ## The log derivatives of both sides agree -/

/-- `q i` as a rational: `q_i = m_i + 1`. -/
def qq (mi : Nat) : ℚ := ((mi + 1 : Nat) : ℚ)

theorem qq_ne_zero (mi : Nat) : qq mi ≠ 0 := by
  unfold qq; positivity

/-- The right-hand side: `Π_i C(q_i⁻¹ X)`. -/
noncomputable def prodSeries (μ : List Nat) : ℚ⟦X⟧ :=
  (μ.map fun mi => rescale (qq mi)⁻¹ Cseries).prod

theorem constantCoeff_prodSeries (μ : List Nat) :
    constantCoeff (prodSeries μ) = 1 := by
  rw [prodSeries, map_list_prod]
  refine List.prod_eq_one fun x hx => ?_
  simp only [List.map_map, List.mem_map] at hx
  obtain ⟨mi, -, rfl⟩ := hx
  show constantCoeff (rescale (qq mi)⁻¹ Cseries) = 1
  rw [← coeff_zero_eq_constantCoeff, coeff_rescale]
  simp

theorem theta_prodSeries : ∀ μ : List Nat,
    theta (prodSeries μ)
      = (μ.map fun mi => rescale (qq mi)⁻¹ uSeries).sum * prodSeries μ
  | [] => by simp [prodSeries, theta_one]
  | (mi :: μ) => by
      have ih := theta_prodSeries μ
      show theta (rescale (qq mi)⁻¹ Cseries * prodSeries μ) = _
      rw [theta_mul, ih, theta_rescale, theta_Cseries, map_mul]
      show _ = (rescale (qq mi)⁻¹ uSeries
          + (μ.map fun mi => rescale (qq mi)⁻¹ uSeries).sum)
        * (rescale (qq mi)⁻¹ Cseries * prodSeries μ)
      ring

private theorem list_sum_mul_right (l : List Nat) (f : Nat → ℚ) (s : ℚ) :
    (l.map fun mi => f mi * s).sum = (l.map f).sum * s := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring

private theorem Dr_eq (μ : List Nat) (n : Nat) :
    Dr μ n = (((μ.map (· + 1)).sum : Nat) : ℚ)
      - (μ.map fun mi => ((qq mi)⁻¹)^n).sum := by
  induction μ with
  | nil => simp [Dr]
  | cons mi μ ih =>
      simp only [Dr, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      unfold qq
      push_cast
      rw [inv_pow]
      ring

/-- The `D_r` identity, series form: `N·u + u_b = Σ_i rescale (q_i⁻¹) u`,
where `u_b` is the log-derivative numerator of `bSeries μ`. -/
theorem logDeriv_balance (μ : List Nat) :
    PowerSeries.C (((μ.map (· + 1)).sum : Nat) : ℚ) * uSeries
      + (mk fun r => (r : ℚ) * (-(Dr μ r) * c r))
      = (μ.map fun mi => rescale (qq mi)⁻¹ uSeries).sum := by
  ext n
  rw [map_add, coeff_C_mul, coeff_mk, coeff_uSeries, map_list_sum]
  rw [List.map_map]
  have hcoeff : ∀ mi : Nat,
      (coeff n ∘ fun mi => rescale (qq mi)⁻¹ uSeries) mi
        = ((qq mi)⁻¹)^n * ((n : ℚ) * c n) := fun mi => by
    show coeff n (rescale (qq mi)⁻¹ uSeries) = _
    rw [coeff_rescale, coeff_uSeries]
  rw [List.map_congr_left fun mi _ => hcoeff mi,
      list_sum_mul_right μ (fun mi => ((qq mi)⁻¹)^n) ((n : ℚ) * c n),
      Dr_eq μ n]
  ring

theorem constantCoeff_rescaled_u_sum (μ : List Nat) :
    constantCoeff ((μ.map fun mi => rescale (qq mi)⁻¹ uSeries).sum) = 0 := by
  rw [map_list_sum, List.map_map]
  refine List.sum_eq_zero fun x hx => ?_
  simp only [List.mem_map] at hx
  obtain ⟨mi, -, rfl⟩ := hx
  show constantCoeff (rescale (qq mi)⁻¹ uSeries) = 0
  rw [← coeff_zero_eq_constantCoeff, coeff_rescale]
  simp

/-! ## The main characterization -/

/-- **Official characterization of `bCoeff`** (multiplication form):
with `q_i = m_i + 1` and `N = Σ_i q_i`,
`C(X)^N · (Σ_a b_a(μ) X^a) = Π_i C(q_i⁻¹ X)`.
Since `C^N` is a unit (constant coefficient 1), this says exactly
`Σ_a b_a(μ) X^a = Π_i C(X/q_i) / C(X)^N`, which is the series of
Chen–Larson Proposition 5.1. -/
theorem bSeries_official (μ : List Nat) :
    Cseries ^ ((μ.map (· + 1)).sum) * bSeries μ = prodSeries μ := by
  -- both sides satisfy θF = w·F with constant coefficient 1,
  -- for w = Σ_i rescale (q_i⁻¹) uSeries
  apply logDeriv_unique
      (u := (μ.map fun mi => rescale (qq mi)⁻¹ uSeries).sum)
      (constantCoeff_rescaled_u_sum μ)
  · rw [map_mul, map_pow, constantCoeff_Cseries, one_pow, one_mul,
      bSeries_eq_expSeries]
    exact constantCoeff_expSeries _
  · exact constantCoeff_prodSeries μ
  · rw [theta_mul, theta_pow theta_Cseries _, bSeries_eq_expSeries,
      theta_expSeries, ← logDeriv_balance μ]
    ring
  · exact theta_prodSeries μ

/-- Coefficient form: `b_a(μ)` is determined by the official series identity. -/
theorem coeff_official (μ : List Nat) (a : Nat) :
    coeff a (Cseries ^ ((μ.map (· + 1)).sum) * bSeries μ)
      = coeff a (prodSeries μ) := by
  rw [bSeries_official]

end Prop51
