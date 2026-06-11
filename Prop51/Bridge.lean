/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# The bridge: `c` really is `log C` (Layer A centerpiece)

`Cseries = Σ_k A_k Xᵏ` with `A_k = (6k)!/((3k)!(2k)!·72^k)` is the
hypergeometric series of the paper.  This file proves

  `Cseries_eq_expSeries_c : Cseries = expSeries c`,

i.e. the Riccati-recurrence sequence `c` of `Prop51.Defs` is the sequence of
logarithmic coefficients of `C`.  Route (all coefficient identities over ℚ):

1. `Aseq_succ` — the hypergeometric ratio
   `6(k+1)·A_{k+1} = (6k+1)(6k+5)·A_k` (a factorial computation);
2. `satOde Cseries` — hence `C` satisfies the ODE
   `θC = X·(6θ²C + 6θC + (5/6)C)`;
3. `riccati_u` — the Riccati recurrence for `c` says exactly
   `u = X·(6θu + 6u² + 6u + 5/6)` for `u = Σ r·c_r Xʳ`;
4. `satOde_expSeries_c` — by the Leibniz rule, `θF = uF` and the Riccati
   identity force `expSeries c` to satisfy the same ODE (pure ring algebra);
5. `satOde_unique` — the ODE has a unique solution with constant term 1.
-/
import Prop51.ExpSeries
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

namespace Prop51

open PowerSeries

/-! ## The hypergeometric coefficients -/

/-- `A k = (6k)!/((3k)!(2k)!·72^k)`, the coefficients of `C(t)`. -/
def Aseq (k : Nat) : ℚ :=
  (Nat.factorial (6*k) : ℚ)
    / ((Nat.factorial (3*k) : ℚ) * (Nat.factorial (2*k) : ℚ) * 72^k)

/-- The series `C` of Chen–Larson Proposition 5.1. -/
noncomputable def Cseries : ℚ⟦X⟧ := mk Aseq

@[simp] theorem coeff_Cseries (n : Nat) : coeff n Cseries = Aseq n :=
  coeff_mk n _

@[simp] theorem Aseq_zero : Aseq 0 = 1 := by
  simp [Aseq]

@[simp] theorem constantCoeff_Cseries : constantCoeff Cseries = 1 := by
  rw [← coeff_zero_eq_constantCoeff, coeff_Cseries, Aseq_zero]

private theorem factorial_cast_ne (m : Nat) : ((Nat.factorial m : Nat) : ℚ) ≠ 0 := by
  exact_mod_cast (Nat.factorial_pos m).ne'

/-- The hypergeometric ratio identity, integer-cleared:
`6(k+1)·A_{k+1} = (6k+1)(6k+5)·A_k`. -/
theorem Aseq_succ (k : Nat) :
    6 * ((k+1 : Nat) : ℚ) * Aseq (k+1)
      = ((6*k+1 : Nat) : ℚ) * ((6*k+5 : Nat) : ℚ) * Aseq k := by
  have f6 : (Nat.factorial (6*(k+1)) : ℚ)
      = ((6*k+6 : Nat) : ℚ) * ((6*k+5 : Nat) : ℚ) * ((6*k+4 : Nat) : ℚ)
        * ((6*k+3 : Nat) : ℚ) * ((6*k+2 : Nat) : ℚ) * ((6*k+1 : Nat) : ℚ)
        * (Nat.factorial (6*k) : ℚ) := by
    rw [show 6*(k+1) = (6*k+5)+1 from by omega, Nat.factorial_succ,
        show (6*k+5) = (6*k+4)+1 from by omega, Nat.factorial_succ,
        show (6*k+4) = (6*k+3)+1 from by omega, Nat.factorial_succ,
        show (6*k+3) = (6*k+2)+1 from by omega, Nat.factorial_succ,
        show (6*k+2) = (6*k+1)+1 from by omega, Nat.factorial_succ,
        show (6*k+1) = (6*k)+1 from by omega, Nat.factorial_succ]
    push_cast
    ring
  have f3 : (Nat.factorial (3*(k+1)) : ℚ)
      = ((3*k+3 : Nat) : ℚ) * ((3*k+2 : Nat) : ℚ) * ((3*k+1 : Nat) : ℚ)
        * (Nat.factorial (3*k) : ℚ) := by
    rw [show 3*(k+1) = (3*k+2)+1 from by omega, Nat.factorial_succ,
        show (3*k+2) = (3*k+1)+1 from by omega, Nat.factorial_succ,
        show (3*k+1) = (3*k)+1 from by omega, Nat.factorial_succ]
    push_cast
    ring
  have f2 : (Nat.factorial (2*(k+1)) : ℚ)
      = ((2*k+2 : Nat) : ℚ) * ((2*k+1 : Nat) : ℚ) * (Nat.factorial (2*k) : ℚ) := by
    rw [show 2*(k+1) = (2*k+1)+1 from by omega, Nat.factorial_succ,
        show (2*k+1) = (2*k)+1 from by omega, Nat.factorial_succ]
    push_cast
    ring
  unfold Aseq
  rw [f6, f3, f2]
  have n6 := factorial_cast_ne (6*k)
  have n3 := factorial_cast_ne (3*k)
  have n2 := factorial_cast_ne (2*k)
  have n72 : (72 : ℚ)^k ≠ 0 := by positivity
  field_simp
  push_cast
  ring

/-! ## The ODE `θG = X·(6θ²G + 6θG + (5/6)G)` -/

/-- The hypergeometric ODE satisfied by `C`, in `θ`-form. -/
def SatOde (G : ℚ⟦X⟧) : Prop :=
  theta G = X * (PowerSeries.C (6:ℚ) * theta (theta G)
    + PowerSeries.C (6:ℚ) * theta G + PowerSeries.C ((5:ℚ)/6) * G)

theorem satOde_Cseries : SatOde Cseries := by
  unfold SatOde
  ext n
  cases n with
  | zero =>
      simp [constantCoeff_theta]
  | succ n =>
      simp only [coeff_theta, coeff_succ_X_mul, map_add, coeff_C_mul,
        coeff_Cseries]
      have h := Aseq_succ n
      push_cast at h ⊢
      linear_combination h / 6

/-- Uniqueness for the ODE among series with constant coefficient 1. -/
theorem satOde_unique {F G : ℚ⟦X⟧}
    (hF0 : constantCoeff F = 1) (hG0 : constantCoeff G = 1)
    (hF : SatOde F) (hG : SatOde G) : F = G := by
  ext n
  induction n with
  | zero => rw [coeff_zero_eq_constantCoeff, hF0, hG0]
  | succ n ih =>
      have key : ∀ H : ℚ⟦X⟧, SatOde H →
          ((n+1 : Nat) : ℚ) * coeff (n+1) H
            = (6*(n:ℚ)*(n:ℚ) + 6*(n:ℚ) + 5/6) * coeff n H := by
        intro H hH
        have h1 := congrArg (coeff (n+1)) hH
        simp only [coeff_theta, coeff_succ_X_mul, map_add, coeff_C_mul] at h1
        push_cast at h1 ⊢
        linear_combination h1
      have hFn := key F hF
      have hGn := key G hG
      rw [ih] at hFn
      have : ((n+1 : Nat) : ℚ) * coeff (n+1) F = ((n+1 : Nat) : ℚ) * coeff (n+1) G := by
        rw [hFn, hGn]
      exact mul_left_cancel₀ (by positivity : ((n+1 : Nat) : ℚ) ≠ 0) this

/-! ## The Riccati identity for `u = Σ r·c_r·Xʳ` -/

/-- `u = θ log C` as a power series: `u = Σ_r r·c_r·Xʳ`. -/
noncomputable def uSeries : ℚ⟦X⟧ := mk fun r => (r : ℚ) * c r

@[simp] theorem coeff_uSeries (n : Nat) : coeff n uSeries = (n : ℚ) * c n :=
  coeff_mk n _

theorem constantCoeff_uSeries : constantCoeff uSeries = 0 := by
  rw [← coeff_zero_eq_constantCoeff, coeff_uSeries]
  simp

/-- The Riccati identity: the recurrence defining `c` says exactly
`u = X·(6θu + 6u² + 6u + 5/6)`. -/
theorem riccati_u :
    uSeries = X * (PowerSeries.C (6:ℚ) * theta uSeries
      + PowerSeries.C (6:ℚ) * (uSeries * uSeries)
      + PowerSeries.C (6:ℚ) * uSeries + PowerSeries.C ((5:ℚ)/6) * 1) := by
  ext n
  match n with
  | 0 =>
      simp [constantCoeff_uSeries]
  | 1 =>
      rw [coeff_succ_X_mul]
      simp [constantCoeff_theta, constantCoeff_uSeries, c_one]
  | (m+2) =>
      simp only [coeff_uSeries, coeff_succ_X_mul, map_add, coeff_C_mul,
        coeff_theta, coeff_one]
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
          Finset.sum_range_succ]
      simp only [coeff_uSeries, Nat.sub_self, Nat.cast_zero, zero_mul,
        mul_zero, add_zero]
      have hsum : ∑ i ∈ Finset.range (m+1),
            ((i : ℚ) * c i) * ((((m+1-i : Nat)) : ℚ) * c (m+1-i))
          = ((List.range (m+1)).map fun (i : Nat) =>
              (i : ℚ) * ((m+1-i : Nat) : ℚ) * c i * c (m+1-i)).sum := by
        rw [list_range_map_sum]
        exact Finset.sum_congr rfl fun i hi => by ring
      have hrec := c_succ_succ m
      have hm2 : ((m+2 : Nat) : ℚ) ≠ 0 := by positivity
      have hrec' : ((m+2 : Nat) : ℚ) * c (m+2)
          = 6*(((m+2 : Nat) : ℚ) - 1) * ((m+2 : Nat) : ℚ) * c (m+1)
            + 6 * ((List.range (m+1)).map fun (i : Nat) =>
                (i : ℚ) * ((m+1-i : Nat) : ℚ) * c i * c (m+1-i)).sum := by
        rw [hrec]
        field_simp
      rw [hsum, hrec']
      push_cast
      have e1 : (m+1+1 : ℚ) ≠ 0 := by positivity
      field_simp
      ring

/-! ## `expSeries c` satisfies the same ODE -/

theorem theta_expSeries_c :
    theta (expSeries c) = uSeries * expSeries c :=
  theta_expSeries c

theorem satOde_expSeries_c : SatOde (expSeries c) := by
  have hF : theta (expSeries c) = uSeries * expSeries c := theta_expSeries_c
  have hθθ : theta (theta (expSeries c))
      = theta uSeries * expSeries c + uSeries * (uSeries * expSeries c) := by
    rw [hF, theta_mul, hF]
  unfold SatOde
  rw [hθθ, hF]
  calc uSeries * expSeries c
      = (X * (PowerSeries.C (6:ℚ) * theta uSeries
          + PowerSeries.C (6:ℚ) * (uSeries * uSeries)
          + PowerSeries.C (6:ℚ) * uSeries + PowerSeries.C ((5:ℚ)/6) * 1))
        * expSeries c := by rw [← riccati_u]
    _ = X * (PowerSeries.C (6:ℚ)
            * (theta uSeries * expSeries c + uSeries * (uSeries * expSeries c))
          + PowerSeries.C (6:ℚ) * (uSeries * expSeries c)
          + PowerSeries.C ((5:ℚ)/6) * expSeries c) := by ring

/-! ## The bridge -/

/-- **The bridge theorem**: the hypergeometric series `C` is the exponential
of `Σ_r c_r Xʳ` — i.e. the Riccati sequence `c` of `Prop51.Defs` is the
sequence of logarithmic coefficients of `C`. -/
theorem Cseries_eq_expSeries_c : Cseries = expSeries c :=
  satOde_unique constantCoeff_Cseries (constantCoeff_expSeries c)
    satOde_Cseries satOde_expSeries_c

/-- Coefficient form of the bridge: `A_n = expCoeff c n`. -/
theorem Aseq_eq_expCoeff (n : Nat) : Aseq n = expCoeff c n := by
  have := congrArg (fun F => coeff n F) Cseries_eq_expSeries_c
  simpa using this

/-- The classical log-derivative identity `n·A_n = Σ_{j≤n} j·c_j·A_{n-j}`,
for the record (used in the paper as the "bridge identity"). -/
theorem bridge_identity (n : Nat) :
    ((n+1 : Nat) : ℚ) * Aseq (n+1)
      = ∑ t ∈ Finset.range (n+1),
          ((t+1 : Nat) : ℚ) * c (t+1) * Aseq (n-t) := by
  have h := expCoeff_succ_mul c n
  rw [← Aseq_eq_expCoeff] at h
  rw [h]
  exact Finset.sum_congr rfl fun t ht => by rw [← Aseq_eq_expCoeff]

end Prop51
