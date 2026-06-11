/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Exp-characterized power series (Layer A machinery)

`expCoeff L` (from `Prop51.Defs`) implements the coefficients of
`exp (Σ_{r≥1} L r · Xʳ)` through the recurrence `n·E_n = Σ_j j·L_j·E_{n-j}`.
This file makes that official, through the *logarithmic-derivative*
characterization, using the operator `θ = X · d/dX`:

* `theta` — the operator `θ`, with `coeff (n+1) (θ F) = (n+1)·coeff (n+1) F`;
* `theta_mul` — Leibniz rule;
* `expSeries L := PowerSeries.mk (expCoeff L)` satisfies
  `θ (expSeries L) = (mk fun r => r·L r) * expSeries L` (`theta_expSeries`);
* `logDeriv_unique` — two series with constant coefficient 1 and the same
  log-derivative relation `θF = u·F` (where `u` has zero constant term)
  are equal.

Everything is over `ℚ`; no analysis, only coefficient identities.
-/
import Prop51.Defs
import Mathlib.RingTheory.PowerSeries.Derivative

namespace Prop51

open PowerSeries

/-! ## List-range sums as Finset sums -/

theorem list_range_map_sum (f : Nat → ℚ) (n : Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append,
      Finset.sum_range_succ, ih]; simp

/-! ## Spec lemmas for `expList`/`expCoeff` -/

theorem expList_succ_append (L : Nat → ℚ) (n : Nat) :
    ∃ x : ℚ, expList L (n+1) = expList L n ++ [x] :=
  ⟨_, rfl⟩

theorem expList_length (L : Nat → ℚ) : ∀ n, (expList L n).length = n + 1
  | 0 => rfl
  | (n+1) => by
      obtain ⟨x, hx⟩ := expList_succ_append L n
      rw [hx, List.length_append, expList_length L n]
      rfl

theorem expList_getD_eq (L : Nat → ℚ) (r m : Nat) (h : r ≤ m) :
    (expList L m).getD r 0 = expCoeff L r := by
  induction m with
  | zero =>
      have : r = 0 := by omega
      subst this; rfl
  | succ m ih =>
      rcases Nat.lt_or_ge r (m+1) with hlt | hge
      · obtain ⟨x, hx⟩ := expList_succ_append L m
        rw [hx, List.getD_eq_getElem?_getD,
            List.getElem?_append_left (by rw [expList_length]; omega),
            ← List.getD_eq_getElem?_getD]
        exact ih (by omega)
      · have : r = m+1 := le_antisymm h hge
        subst this; rfl

@[simp] theorem expCoeff_zero (L : Nat → ℚ) : expCoeff L 0 = 1 := rfl

/-- The defining recurrence of `expCoeff`, in multiplied-out form:
`(n+1)·E_{n+1} = Σ_{j=1}^{n+1} j·L_j·E_{n+1-j}` (as a `Finset.range` sum over
`j = t+1`, `t < n+1`). -/
theorem expCoeff_succ_mul (L : Nat → ℚ) (n : Nat) :
    ((n+1 : Nat) : ℚ) * expCoeff L (n+1)
      = ∑ t ∈ Finset.range (n+1),
          ((t+1 : Nat) : ℚ) * L (t+1) * expCoeff L (n-t) := by
  have hgetD : ∀ i, i ≤ n → (expList L n).getD i 0 = expCoeff L i := fun i hi =>
    expList_getD_eq L i n hi
  have hx : expList L (n+1) = expList L n ++
      [(((List.range (n+1)).map fun (t : Nat) =>
          ((t+1 : Nat) : ℚ) * L (t+1) * (expList L n).getD (n-t) 0).sum)
        / ((n+1 : Nat) : ℚ)] := rfl
  have hcoeff : expCoeff L (n+1)
      = (((List.range (n+1)).map fun (t : Nat) =>
          ((t+1 : Nat) : ℚ) * L (t+1) * (expList L n).getD (n-t) 0).sum)
        / ((n+1 : Nat) : ℚ) := by
    show (expList L (n+1)).getD (n+1) 0 = _
    rw [hx, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by rw [expList_length] : (expList L n).length ≤ n+1),
        expList_length]
    simp
  rw [hcoeff, mul_div_cancel₀ _ (by positivity : ((n+1 : Nat) : ℚ) ≠ 0),
      list_range_map_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [hgetD (n-t) (by omega)]

/-! ## The operator `θ = X · d/dX` -/

/-- `θ F = X * F'`; satisfies `coeff n (θ F) = n · coeff n F`. -/
noncomputable def theta (F : ℚ⟦X⟧) : ℚ⟦X⟧ := X * derivativeFun F

@[simp] theorem coeff_theta (n : Nat) (F : ℚ⟦X⟧) :
    coeff n (theta F) = (n : ℚ) * coeff n F := by
  cases n with
  | zero => simp [theta]
  | succ n =>
      rw [theta, coeff_succ_X_mul, coeff_derivativeFun]
      push_cast
      ring

theorem constantCoeff_theta (F : ℚ⟦X⟧) : constantCoeff (theta F) = 0 := by
  rw [← coeff_zero_eq_constantCoeff, coeff_theta]
  simp

/-- Leibniz rule for `θ`. -/
theorem theta_mul (F G : ℚ⟦X⟧) :
    theta (F * G) = theta F * G + F * theta G := by
  rw [theta, derivativeFun_mul, smul_eq_mul, smul_eq_mul, theta, theta]
  ring

/-! ## `expSeries` and its logarithmic derivative -/

/-- The official power series `exp (Σ_{r≥1} L r · Xʳ)`, via `expCoeff`. -/
noncomputable def expSeries (L : Nat → ℚ) : ℚ⟦X⟧ := mk (expCoeff L)

@[simp] theorem coeff_expSeries (n : Nat) (L : Nat → ℚ) :
    coeff n (expSeries L) = expCoeff L n := coeff_mk n _

@[simp] theorem constantCoeff_expSeries (L : Nat → ℚ) :
    constantCoeff (expSeries L) = 1 := by
  rw [← coeff_zero_eq_constantCoeff, coeff_expSeries, expCoeff_zero]

/-- The log-derivative relation: `θ (expSeries L) = (Σ_r r·L_r·Xʳ) · expSeries L`. -/
theorem theta_expSeries (L : Nat → ℚ) :
    theta (expSeries L) = (mk fun r => (r : ℚ) * L r) * expSeries L := by
  ext n
  rw [coeff_theta, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  cases n with
  | zero => simp
  | succ n =>
      rw [coeff_expSeries, expCoeff_succ_mul]
      conv_rhs => rw [Finset.sum_range_succ']
      simp only [coeff_mk, coeff_expSeries, Nat.cast_zero, zero_mul, add_zero]
      refine Finset.sum_congr rfl fun t ht => ?_
      have e : n + 1 - (t + 1) = n - t := by omega
      rw [e]

/-- Uniqueness of solutions of the log-derivative relation `θF = u·F`
with `constantCoeff u = 0` and `constantCoeff F = 1`. -/
theorem logDeriv_unique {u F G : ℚ⟦X⟧}
    (hu : constantCoeff u = 0)
    (hF0 : constantCoeff F = 1) (hG0 : constantCoeff G = 1)
    (hF : theta F = u * F) (hG : theta G = u * G) : F = G := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      match n with
      | 0 => rw [coeff_zero_eq_constantCoeff, hF0, hG0]
      | (n+1) =>
          have key : ∀ H : ℚ⟦X⟧, theta H = u * H →
              ((n+1 : Nat) : ℚ) * coeff (n+1) H
                = ∑ t ∈ Finset.range (n+1),
                    coeff (t+1) u * coeff (n-t) H := by
            intro H hH
            have h1 : coeff (n+1) (theta H) = coeff (n+1) (u * H) := by rw [hH]
            rw [coeff_theta, coeff_mul,
                Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
                Finset.sum_range_succ'] at h1
            rw [← coeff_zero_eq_constantCoeff] at hu
            simpa [hu] using h1
          have hFn := key F hF
          have hGn := key G hG
          have hsum : ∑ t ∈ Finset.range (n+1), coeff (t+1) u * coeff (n-t) F
              = ∑ t ∈ Finset.range (n+1), coeff (t+1) u * coeff (n-t) G := by
            refine Finset.sum_congr rfl fun t ht => ?_
            rw [ih (n-t) (by omega)]
          have : ((n+1 : Nat) : ℚ) * coeff (n+1) F
              = ((n+1 : Nat) : ℚ) * coeff (n+1) G := by
            rw [hFn, hGn, hsum]
          exact mul_left_cancel₀ (by positivity : ((n+1 : Nat) : ℚ) ≠ 0) this

end Prop51
