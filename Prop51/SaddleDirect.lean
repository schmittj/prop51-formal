import Prop51.Majorant
import Prop51.ExpBounds
import Prop51.HPow

namespace Prop51

open PowerSeries

/-!
Direct saddle toolkit for the corrected product route.

The older exact upper-edge split-product route loses the dyadic gain in the
`Y` factor and cannot close the large-tail product certificate.  The direct
route works with finite exponential prefixes until the final `sum_exp_le`
step, avoiding products of independent `partialExpUpper` shells.
-/

theorem expCoeff_scale (rho : ℚ) (L : Nat → ℚ) :
    ∀ m : Nat,
      expCoeff (fun r => rho^r * L r) m = rho^m * expCoeff L m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      cases m with
      | zero =>
          simp
      | succ n =>
          have hscaled := expCoeff_succ_mul (fun r => rho^r * L r) n
          have hbase := expCoeff_succ_mul L n
          have hsum :
              (∑ t ∈ Finset.range (n + 1),
                ((t + 1 : Nat) : ℚ) * (rho^(t + 1) * L (t + 1)) *
                  expCoeff (fun r => rho^r * L r) (n - t))
                =
              rho^(n + 1) *
                ∑ t ∈ Finset.range (n + 1),
                  ((t + 1 : Nat) : ℚ) * L (t + 1) *
                    expCoeff L (n - t) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun t ht => ?_
            have ht_le : t ≤ n := by
              have ht' := Finset.mem_range.mp ht
              omega
            have hpow : rho^(t + 1) * rho^(n - t) = rho^(n + 1) := by
              rw [← pow_add]
              congr 1
              omega
            rw [ih (n - t) (by omega)]
            calc
              ((t + 1 : Nat) : ℚ) * (rho^(t + 1) * L (t + 1)) *
                  (rho^(n - t) * expCoeff L (n - t))
                  = rho^(t + 1) * rho^(n - t) *
                      (((t + 1 : Nat) : ℚ) * L (t + 1) *
                        expCoeff L (n - t)) := by
                    ring
              _ = rho^(n + 1) *
                      (((t + 1 : Nat) : ℚ) * L (t + 1) *
                        expCoeff L (n - t)) := by
                    rw [hpow]
          have hmul :
              ((n + 1 : Nat) : ℚ) *
                  expCoeff (fun r => rho^r * L r) (n + 1)
                =
              ((n + 1 : Nat) : ℚ) *
                  (rho^(n + 1) * expCoeff L (n + 1)) := by
            rw [hscaled, hsum, ← hbase]
            ring
          exact mul_left_cancel₀ (by positivity : ((n + 1 : Nat) : ℚ) ≠ 0) hmul

/-- Inclusive finite exponential prefix:
`P_m(x) = sum_{0 <= r <= m} x^r/r!`. -/
def expPrefix (x : ℚ) (m : Nat) : ℚ :=
  ∑ r ∈ Finset.range (m + 1), x^r / (r.factorial : ℚ)

/-- Coefficients of a power are bounded by the corresponding finite gas.

This is the composition-free bound used by the direct saddle route: if all
coefficients `M_r` are nonnegative, then every coefficient of `G(t)^q` up to
degree `p` is bounded by `(M_0 + ... + M_p)^q`. -/
theorem coeff_pow_le_gas_pow {M : Nat → ℚ} (hM : ∀ r, 0 ≤ M r) :
    ∀ p q : Nat,
      coeff p ((mk M : ℚ⟦X⟧)^q)
        ≤ (∑ r ∈ Finset.range (p + 1), M r)^q := by
  intro p q
  revert p
  induction q with
  | zero =>
      intro p
      by_cases hp : p = 0
      · subst p
        simp
      · simp [hp]
  | succ q ih =>
      intro p
      let Gp : ℚ := ∑ r ∈ Finset.range (p + 1), M r
      have hGp : 0 ≤ Gp := by
        dsimp [Gp]
        exact Finset.sum_nonneg fun r _ => hM r
      have hcoeff :
          coeff p ((mk M : ℚ⟦X⟧)^(q + 1))
            =
          ∑ t ∈ Finset.range (p + 1),
            coeff t ((mk M : ℚ⟦X⟧)^q) * M (p - t) := by
        rw [pow_succ, coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        simp [coeff_mk]
      rw [hcoeff]
      calc
        ∑ t ∈ Finset.range (p + 1),
            coeff t ((mk M : ℚ⟦X⟧)^q) * M (p - t)
            ≤ ∑ t ∈ Finset.range (p + 1), Gp^q * M (p - t) := by
              refine Finset.sum_le_sum fun t ht => ?_
              have ht_le : t ≤ p := by
                have ht' := Finset.mem_range.mp ht
                omega
              have hGt_nonneg :
                  0 ≤ ∑ r ∈ Finset.range (t + 1), M r := by
                exact Finset.sum_nonneg fun r _ => hM r
              have hGt_le :
                  (∑ r ∈ Finset.range (t + 1), M r) ≤ Gp := by
                dsimp [Gp]
                exact
                  Finset.sum_le_sum_of_subset_of_nonneg
                    (fun r hr => by
                      exact Finset.mem_range.mpr (by
                        have hr' := Finset.mem_range.mp hr
                        omega))
                    (fun r _ _ => hM r)
              have hpow :
                  (∑ r ∈ Finset.range (t + 1), M r)^q ≤ Gp^q :=
                pow_le_pow_left₀ hGt_nonneg hGt_le q
              have hct : coeff t ((mk M : ℚ⟦X⟧)^q) ≤ Gp^q :=
                (ih t).trans hpow
              exact mul_le_mul_of_nonneg_right hct (hM (p - t))
        _ = Gp^q * ∑ t ∈ Finset.range (p + 1), M (p - t) := by
              rw [Finset.mul_sum]
        _ = Gp^q * Gp := by
              dsimp [Gp]
              rw [← Finset.sum_range_reflect M (p + 1)]
              simp
        _ = Gp^(q + 1) := by
              rw [pow_succ]

theorem coeff_pow_le_total_gas_pow {M : Nat → ℚ} (hM : ∀ r, 0 ≤ M r)
    {p m q : Nat} (hpm : p ≤ m) :
    coeff p ((mk M : ℚ⟦X⟧)^q)
      ≤ (∑ r ∈ Finset.range (m + 1), M r)^q := by
  have hbase := coeff_pow_le_gas_pow hM p q
  have hpGas_nonneg :
      0 ≤ ∑ r ∈ Finset.range (p + 1), M r :=
    Finset.sum_nonneg fun r _ => hM r
  have hgas_le :
      (∑ r ∈ Finset.range (p + 1), M r)
        ≤ ∑ r ∈ Finset.range (m + 1), M r :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun r hr => by
        exact Finset.mem_range.mpr (by
          have hr' := Finset.mem_range.mp hr
          omega))
      (fun r _ _ => hM r)
  exact hbase.trans (pow_le_pow_left₀ hpGas_nonneg hgas_le q)

/-- Direct saddle bound without scaling. -/
theorem expCoeff_le_expPrefix_gas {L : Nat → ℚ}
    (hL0 : L 0 = 0) (hL : ∀ r, 0 ≤ L r) (m : Nat) :
    expCoeff L m
      ≤ expPrefix (∑ r ∈ Finset.range (m + 1), L r) m := by
  rw [expCoeff_eq_sum_pow L hL0 m]
  unfold expPrefix
  refine Finset.sum_le_sum fun q hq => ?_
  have hcoeff :
      coeff m ((mk L : ℚ⟦X⟧)^q)
        ≤ (∑ r ∈ Finset.range (m + 1), L r)^q :=
    coeff_pow_le_total_gas_pow hL (p := m) (m := m) (q := q) le_rfl
  have hfpos : (0 : ℚ) < (q.factorial : ℚ) := by
    exact_mod_cast q.factorial_pos
  exact div_le_div_of_nonneg_right hcoeff hfpos.le

/-- Direct saddle bound after introducing a nonnegative radius `rho`. -/
theorem expCoeff_saddle {rho : ℚ} (hrho : 0 ≤ rho) {L : Nat → ℚ}
    (hL0 : L 0 = 0) (hL : ∀ r, 0 ≤ L r) (m : Nat) :
    rho^m * expCoeff L m
      ≤ expPrefix (∑ r ∈ Finset.range (m + 1), rho^r * L r) m := by
  have hscaled0 : (fun r => rho^r * L r) 0 = 0 := by
    simp [hL0]
  have hscaled_nonneg : ∀ r, 0 ≤ rho^r * L r := by
    intro r
    exact mul_nonneg (pow_nonneg hrho r) (hL r)
  have h :=
    expCoeff_le_expPrefix_gas hscaled0 hscaled_nonneg m
  simpa [expCoeff_scale] using h

@[simp] theorem expPrefix_zero (x : ℚ) : expPrefix x 0 = 1 := by
  simp [expPrefix]

theorem expPrefix_nonneg {x : ℚ} (hx : 0 ≤ x) (m : Nat) :
    0 ≤ expPrefix x m := by
  unfold expPrefix
  exact Finset.sum_nonneg fun r _ => by
    positivity

theorem expPrefix_mono_index {x : ℚ} (hx : 0 ≤ x) {m n : Nat}
    (hmn : m ≤ n) :
    expPrefix x m ≤ expPrefix x n := by
  unfold expPrefix
  exact
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun r hr => by
        exact Finset.mem_range.mpr (by
          have hr' := Finset.mem_range.mp hr
          omega))
      (fun r _ _ => by
        positivity)

theorem expPrefix_mono_arg {x y : ℚ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (m : Nat) :
    expPrefix x m ≤ expPrefix y m := by
  have hy : 0 ≤ y := hx.trans hxy
  unfold expPrefix
  refine Finset.sum_le_sum fun r _ => ?_
  have hpow : x^r ≤ y^r := pow_le_pow_left₀ hx hxy r
  exact div_le_div_of_nonneg_right hpow (by positivity)

/-- Final conversion from the finite prefix to the rational exponential shell.

This keeps `SaddleDirect` independent of the later `partialExpUpper`
definition: the right hand side is exactly that shell's defining expression.
-/
theorem expPrefix_le_partialExpUpperExpr
    {x : ℚ} {T₀ : Nat} (hx : 0 ≤ x) (hxT : x < (T₀ : ℚ)) (m : Nat) :
    expPrefix x m
      ≤ (∑ t ∈ Finset.range T₀, x^t / (t.factorial : ℚ))
        + (x^T₀ / (T₀.factorial : ℚ)) * (1 / (1 - x/(T₀ : ℚ))) := by
  change
    (∑ r ∈ Finset.range (m + 1), x^r / (r.factorial : ℚ))
      ≤ (∑ t ∈ Finset.range T₀, x^t / (t.factorial : ℚ))
        + (x^T₀ / (T₀.factorial : ℚ)) * (1 / (1 - x/(T₀ : ℚ)))
  exact sum_exp_le x T₀ hx hxT (m + 1)

/-- A single monomial is bounded by the inclusive prefix containing it. -/
theorem monomial_le_expPrefix {x : ℚ} (hx : 0 ≤ x) {r m : Nat}
    (hrm : r ≤ m) :
    x^r / (r.factorial : ℚ) ≤ expPrefix x m := by
  have htop : x^r / (r.factorial : ℚ) ≤ expPrefix x r := by
    unfold expPrefix
    rw [Finset.sum_range_succ]
    have hsum : 0 ≤ ∑ s ∈ Finset.range r, x^s / (s.factorial : ℚ) :=
      Finset.sum_nonneg fun s _ => by
        have hs : 0 ≤ x^s := pow_nonneg hx s
        have hfac : 0 ≤ (s.factorial : ℚ) := by
          exact_mod_cast (Nat.factorial_pos s).le
        exact div_nonneg hs hfac
    linarith
  exact htop.trans (expPrefix_mono_index hx hrm)

theorem expPrefix_one (x : ℚ) : expPrefix x 1 = 1 + x := by
  norm_num [expPrefix, Finset.sum_range_succ]

theorem five_thirds_eq_expPrefix_two_thirds_one :
    expPrefix (2 / 3 : ℚ) 1 = 5 / 3 := by
  norm_num [expPrefix, Finset.sum_range_succ]

theorem five_thirds_le_expPrefix_two_thirds_one :
    (5 / 3 : ℚ) ≤ expPrefix (2 / 3 : ℚ) 1 := by
  rw [five_thirds_eq_expPrefix_two_thirds_one]

theorem one_add_le_expPrefix {x : ℚ} (hx : 0 ≤ x) {m : Nat}
    (hm : 1 ≤ m) :
    1 + x ≤ expPrefix x m := by
  rw [← expPrefix_one x]
  exact expPrefix_mono_index hx hm

/-- Elementary absorption used by the product normalization:
`(1+d)^n <= P_n(n*d)`. -/
theorem one_add_pow_le_expPrefix {d : ℚ} (hd : 0 ≤ d) (n : Nat) :
    (1 + d)^n ≤ expPrefix ((n : ℚ) * d) n := by
  rcases n with _ | n
  · simp [expPrefix]
  · have hnpos : (0 : ℚ) < ((n + 1 : Nat) : ℚ) := by positivity
    have hterm :
        ∀ m ∈ Finset.range (n + 1 + 1),
          d^m * 1^(n + 1 - m) * ((n + 1).choose m : ℚ)
            ≤ (((n + 1 : Nat) : ℚ) * d)^m / (m.factorial : ℚ) := by
      intro m hm
      have hmle : m ≤ n + 1 := by
        have hm' := Finset.mem_range.mp hm
        omega
      have hNat : (n + 1).choose m * m.factorial ≤ (n + 1)^m := by
        calc
          (n + 1).choose m * m.factorial
              = m.factorial * (n + 1).choose m := Nat.mul_comm _ _
          _ = (n + 1).descFactorial m :=
              (Nat.descFactorial_eq_factorial_mul_choose (n + 1) m).symm
          _ ≤ (n + 1)^m := Nat.descFactorial_le_pow (n + 1) m
      have hChooseFac :
          (((n + 1).choose m : Nat) : ℚ) * (m.factorial : ℚ)
            ≤ (((n + 1 : Nat) : ℚ))^m := by
        exact_mod_cast hNat
      have hdm : 0 ≤ d^m := pow_nonneg hd m
      have hmul :=
        mul_le_mul_of_nonneg_left hChooseFac hdm
      have hfac : (0 : ℚ) < (m.factorial : ℚ) := by
        exact_mod_cast m.factorial_pos
      rw [one_pow, mul_one, mul_pow, le_div_iff₀ hfac]
      nlinarith [hmul]
    calc
      (1 + d)^(n + 1)
          = (d + 1)^(n + 1) := by ring_nf
      _ = ∑ m ∈ Finset.range (n + 1 + 1),
            d^m * 1^(n + 1 - m) * ((n + 1).choose m : ℚ) := by
            exact add_pow d 1 (n + 1)
      _ ≤ ∑ m ∈ Finset.range (n + 1 + 1),
            (((n + 1 : Nat) : ℚ) * d)^m / (m.factorial : ℚ) :=
            Finset.sum_le_sum hterm
      _ = expPrefix (((n + 1 : Nat) : ℚ) * d) (n + 1) := by
            simp [expPrefix]

end Prop51
