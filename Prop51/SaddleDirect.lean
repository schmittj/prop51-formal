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

theorem expTerm_add_eq_antidiagonal (x y : ℚ) (t : Nat) :
    (x + y)^t / (t.factorial : ℚ)
      =
    ∑ ij ∈ Finset.antidiagonal t,
      x^ij.1 / (ij.1.factorial : ℚ) *
        (y^ij.2 / (ij.2.factorial : ℚ)) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [add_pow, Finset.sum_div]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpt : p ≤ t := by
    have hp' := Finset.mem_range.mp hp
    omega
  have hchoose :
      (((t.choose p : Nat) : ℚ) * (p.factorial : ℚ)) *
          ((t - p).factorial : ℚ) = (t.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hpt
  have hchoose_pos : (0 : ℚ) < (t.choose p : ℚ) := by
    exact_mod_cast Nat.choose_pos hpt
  have hpfac : (0 : ℚ) < (p.factorial : ℚ) := by
    exact_mod_cast p.factorial_pos
  have htpfac : (0 : ℚ) < ((t - p).factorial : ℚ) := by
    exact_mod_cast (t - p).factorial_pos
  have htfac : (0 : ℚ) < (t.factorial : ℚ) := by
    exact_mod_cast t.factorial_pos
  rw [← hchoose]
  field_simp [hchoose_pos.ne', hpfac.ne', htpfac.ne', htfac.ne']

/-- Product term attached to a pair of exponents. -/
def expPairTerm (x y : ℚ) (ij : Nat × Nat) : ℚ :=
  x^ij.1 / (ij.1.factorial : ℚ) *
    (y^ij.2 / (ij.2.factorial : ℚ))

/-- All exponent pairs with total degree at most `N`, presented as a disjoint
union of antidiagonals. -/
def expTrianglePairs (N : Nat) : Finset (Nat × Nat) :=
  (Finset.range (N + 1)).biUnion fun t => Finset.antidiagonal t

theorem mem_expTrianglePairs {N : Nat} {ij : Nat × Nat} :
    ij ∈ expTrianglePairs N ↔ ij.1 + ij.2 ≤ N := by
  unfold expTrianglePairs
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨t, ht, hij⟩
    have htN := Finset.mem_range.mp ht
    have hijsum := Finset.mem_antidiagonal.mp hij
    omega
  · intro hijN
    refine ⟨ij.1 + ij.2, Finset.mem_range.mpr (by omega), ?_⟩
    exact Finset.mem_antidiagonal.mpr rfl

private theorem antidiagonal_pairwiseDisjoint (N : Nat) :
    Set.PairwiseDisjoint (↑(Finset.range (N + 1)) : Set Nat)
      (fun t => Finset.antidiagonal t) := by
  intro a _ha b _hb hab
  exact Finset.disjoint_left.mpr (by
    intro ij hia hib
    have hia' := Finset.mem_antidiagonal.mp hia
    have hib' := Finset.mem_antidiagonal.mp hib
    exact hab (by omega))

theorem expPrefix_add_eq_triangle_sum (x y : ℚ) (N : Nat) :
    expPrefix (x + y) N
      = ∑ ij ∈ expTrianglePairs N, expPairTerm x y ij := by
  unfold expPrefix
  calc
    ∑ t ∈ Finset.range (N + 1), (x + y)^t / (t.factorial : ℚ)
        =
      ∑ t ∈ Finset.range (N + 1),
        ∑ ij ∈ Finset.antidiagonal t, expPairTerm x y ij := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [expTerm_add_eq_antidiagonal]
          rfl
    _ = ∑ ij ∈ expTrianglePairs N, expPairTerm x y ij := by
          unfold expTrianglePairs
          rw [Finset.sum_biUnion (antidiagonal_pairwiseDisjoint N)]

theorem expPrefix_mul_eq_rect_sum (x y : ℚ) (m n : Nat) :
    expPrefix x m * expPrefix y n
      =
    ∑ ij ∈ (Finset.range (m + 1)) ×ˢ (Finset.range (n + 1)),
      expPairTerm x y ij := by
  unfold expPrefix expPairTerm
  rw [Finset.sum_product]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]

theorem expPairTerm_nonneg {x y : ℚ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (ij : Nat × Nat) :
    0 ≤ expPairTerm x y ij := by
  unfold expPairTerm
  have hxpow : 0 ≤ x^ij.1 := pow_nonneg hx ij.1
  have hypow : 0 ≤ y^ij.2 := pow_nonneg hy ij.2
  have hxfac : 0 ≤ (ij.1.factorial : ℚ) := by
    exact_mod_cast (Nat.factorial_pos ij.1).le
  have hyfac : 0 ≤ (ij.2.factorial : ℚ) := by
    exact_mod_cast (Nat.factorial_pos ij.2).le
  exact mul_nonneg (div_nonneg hxpow hxfac) (div_nonneg hypow hyfac)

theorem expPrefix_mul_le {x y : ℚ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (m n : Nat) :
    expPrefix x m * expPrefix y n ≤ expPrefix (x + y) (m + n) := by
  rw [expPrefix_mul_eq_rect_sum, expPrefix_add_eq_triangle_sum]
  refine
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun ij hij => ?_)
      (fun ij _ _ => expPairTerm_nonneg hx hy ij)
  have hij' := Finset.mem_product.mp hij
  rw [mem_expTrianglePairs]
  have hi := Finset.mem_range.mp hij'.1
  have hj := Finset.mem_range.mp hij'.2
  omega

/-! ## Factorial gas estimates -/

/-- Small-branch factorial gas term `(r-1)! / s^r`. -/
def smallFactorialGasTerm (s r : Nat) : ℚ :=
  ((r - 1).factorial : ℚ) / (s : ℚ)^r

def smallFactorialGas (s k : Nat) : ℚ :=
  ∑ r ∈ Finset.Icc 2 k, smallFactorialGasTerm s r

theorem smallFactorialGasTerm_nonneg (s r : Nat) :
    0 ≤ smallFactorialGasTerm s r := by
  unfold smallFactorialGasTerm
  positivity

theorem smallFactorialGasTerm_succ_le
    {s r : Nat} (hs : 1 ≤ s) (hr : 1 ≤ r) (hrs : r ≤ s) :
    smallFactorialGasTerm s (r + 1) ≤ smallFactorialGasTerm s r := by
  have hspos : (0 : ℚ) < (s : ℚ) := by
    exact_mod_cast (by omega : 0 < s)
  have hratio : (r : ℚ) / (s : ℚ) ≤ 1 := by
    rw [div_le_one hspos]
    exact_mod_cast hrs
  have hrewrite :
      smallFactorialGasTerm s (r + 1)
        = smallFactorialGasTerm s r * ((r : ℚ) / (s : ℚ)) := by
    unfold smallFactorialGasTerm
    have hfac :
        (((r + 1 - 1).factorial : Nat) : ℚ)
          = (r : ℚ) * ((r - 1).factorial : ℚ) := by
      rw [show r + 1 - 1 = r by omega]
      rw [show r = (r - 1) + 1 by omega, Nat.factorial_succ]
      norm_num
    rw [hfac, pow_succ]
    field_simp [hspos.ne']
  rw [hrewrite]
  calc
    smallFactorialGasTerm s r * ((r : ℚ) / (s : ℚ))
        ≤ smallFactorialGasTerm s r * 1 :=
          mul_le_mul_of_nonneg_left hratio (smallFactorialGasTerm_nonneg s r)
    _ = smallFactorialGasTerm s r := by ring

theorem smallFactorialGasTerm_le_four
    {s r : Nat} (h4 : 4 ≤ r) (hrs : r ≤ s) :
    smallFactorialGasTerm s r ≤ smallFactorialGasTerm s 4 := by
  induction r, h4 using Nat.le_induction with
  | base =>
      rfl
  | succ r h4r ih =>
      have hrs_prev : r ≤ s := by omega
      have hs1 : 1 ≤ s := by omega
      have hr1 : 1 ≤ r := by omega
      exact
        (smallFactorialGasTerm_succ_le (s := s) (r := r) hs1 hr1 hrs_prev).trans
          (ih hrs_prev)

theorem smallFactorialGasTerm_two (s : Nat) :
    smallFactorialGasTerm s 2 = 1 / (s : ℚ)^2 := by
  norm_num [smallFactorialGasTerm]

theorem smallFactorialGasTerm_three (s : Nat) :
    smallFactorialGasTerm s 3 = 2 / (s : ℚ)^3 := by
  norm_num [smallFactorialGasTerm]

theorem smallFactorialGasTerm_four (s : Nat) :
    smallFactorialGasTerm s 4 = 6 / (s : ℚ)^4 := by
  norm_num [smallFactorialGasTerm, Nat.factorial]

private theorem smallFactorialGas_sum_Icc_two_eq
    (F : Nat → ℚ) {k : Nat} (hk : 3 ≤ k) :
    ∑ r ∈ Finset.Icc 2 k, F r
      = F 2 + F 3 + ∑ r ∈ Finset.Icc 4 k, F r := by
  have hIcc2 : Finset.Icc 2 k = Finset.Ico 2 (k + 1) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hIcc3 : Finset.Icc 3 k = Finset.Ico 3 (k + 1) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hIcc4 : Finset.Icc 4 k = Finset.Ico 4 (k + 1) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hsplit3 :
      ∑ r ∈ Finset.Icc 3 k, F r = F 3 + ∑ r ∈ Finset.Icc 4 k, F r := by
    rw [hIcc3, Finset.sum_eq_sum_Ico_succ_bot (by omega : 3 < k + 1)]
    rw [← hIcc4]
  rw [hIcc2, Finset.sum_eq_sum_Ico_succ_bot (by omega : 2 < k + 1)]
  rw [← hIcc3, hsplit3]
  ring

private theorem sum_range_zero_one_Icc_two_eq
    (F : Nat → ℚ) {k : Nat} (hk : 2 ≤ k) :
    ∑ r ∈ Finset.range (k + 1), F r
      = F 0 + F 1 + ∑ r ∈ Finset.Icc 2 k, F r := by
  have hRange : Finset.range (k + 1) = Finset.Ico 0 (k + 1) := by
    ext r
    simp only [Finset.mem_range, Finset.mem_Ico]
    omega
  have hIcc1 : Finset.Icc 1 k = Finset.Ico 1 (k + 1) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hIcc2 : Finset.Icc 2 k = Finset.Ico 2 (k + 1) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hsplit1 :
      ∑ r ∈ Finset.Icc 1 k, F r = F 1 + ∑ r ∈ Finset.Icc 2 k, F r := by
    rw [hIcc1, Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < k + 1)]
    rw [← hIcc2]
  rw [hRange, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < k + 1)]
  rw [← hIcc1, hsplit1]
  ring

theorem smallFactorialGas_tail_ge_four_le
    {s k : Nat} (hs : 4 ≤ s) (hks : k ≤ s) :
    ∑ r ∈ Finset.Icc 4 k, smallFactorialGasTerm s r
      ≤ (s : ℚ) * (6 / (s : ℚ)^4) := by
  have hspos : (0 : ℚ) < (s : ℚ) := by
    exact_mod_cast (by omega : 0 < s)
  have hterm :
      ∀ r ∈ Finset.Icc 4 k,
        smallFactorialGasTerm s r ≤ 6 / (s : ℚ)^4 := by
    intro r hr
    have hr' := Finset.mem_Icc.mp hr
    calc
      smallFactorialGasTerm s r
          ≤ smallFactorialGasTerm s 4 :=
            smallFactorialGasTerm_le_four hr'.1 (hr'.2.trans hks)
      _ = 6 / (s : ℚ)^4 := smallFactorialGasTerm_four s
  have hcard : (Finset.Icc 4 k).card ≤ s := by
    have hsubset : Finset.Icc 4 k ⊆ Finset.Ico 1 (s + 1) := by
      intro r hr
      have hr' := Finset.mem_Icc.mp hr
      exact Finset.mem_Ico.mpr (by omega)
    calc
      (Finset.Icc 4 k).card ≤ (Finset.Ico 1 (s + 1)).card :=
        Finset.card_le_card hsubset
      _ = s := by
        simp
  calc
    ∑ r ∈ Finset.Icc 4 k, smallFactorialGasTerm s r
        ≤ ∑ _r ∈ Finset.Icc 4 k, 6 / (s : ℚ)^4 :=
          Finset.sum_le_sum hterm
    _ = ((Finset.Icc 4 k).card : ℚ) * (6 / (s : ℚ)^4) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (s : ℚ) * (6 / (s : ℚ)^4) := by
          exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast hcard)
            (by positivity : 0 ≤ 6 / (s : ℚ)^4)

private theorem smallFactorialGas_main_expr_eq {x : ℚ} (hx : x ≠ 0) :
    1 / x^2 + 2 / x^3 + x * (6 / x^4) = 1 / x^2 + 8 / x^3 := by
  field_simp [hx]
  ring

private theorem smallFactorialGas_main_numeric_le {x : ℚ}
    (hxpos : 0 < x) (hx32 : 32 ≤ x) :
    1 / x^2 + 8 / x^3 ≤ 5 / (4 * x^2) := by
  field_simp [hxpos.ne']
  nlinarith

private theorem smallFactorialGas_le_main_terms
    {s k : Nat} (hs4 : 4 ≤ s) (hk : 3 ≤ k) (hks : k ≤ s) :
    smallFactorialGas s k ≤ 1 / (s : ℚ)^2 + 8 / (s : ℚ)^3 := by
  have hspos : (0 : ℚ) < (s : ℚ) := by
    exact_mod_cast (by omega : 0 < s)
  unfold smallFactorialGas
  rw [smallFactorialGas_sum_Icc_two_eq (fun r => smallFactorialGasTerm s r) hk]
  calc
    smallFactorialGasTerm s 2 + smallFactorialGasTerm s 3 +
        ∑ r ∈ Finset.Icc 4 k, smallFactorialGasTerm s r
        ≤ 1 / (s : ℚ)^2 + 2 / (s : ℚ)^3 +
            (s : ℚ) * (6 / (s : ℚ)^4) := by
          have htail := smallFactorialGas_tail_ge_four_le hs4 hks
          rw [smallFactorialGasTerm_two, smallFactorialGasTerm_three]
          simpa [add_assoc, add_comm, add_left_comm] using
            add_le_add_right htail (1 / (s : ℚ)^2 + 2 / (s : ℚ)^3)
    _ = 1 / (s : ℚ)^2 + 8 / (s : ℚ)^3 := by
          exact smallFactorialGas_main_expr_eq hspos.ne'

private theorem smallFactorialGas_main_terms_le
    {s : Nat} (hs : 32 ≤ s) :
    1 / (s : ℚ)^2 + 8 / (s : ℚ)^3 ≤ 5 / (4 * (s : ℚ)^2) := by
  have hspos : (0 : ℚ) < (s : ℚ) := by
    exact_mod_cast (by omega : 0 < s)
  have hs32 : (32 : ℚ) ≤ (s : ℚ) := by exact_mod_cast hs
  exact smallFactorialGas_main_numeric_le hspos hs32

theorem smallFactorialGas_le_of_ge_three
    {s k : Nat} (hs : 32 ≤ s) (hk : 3 ≤ k) (hks : k ≤ s) :
    smallFactorialGas s k ≤ 5 / (4 * (s : ℚ)^2) := by
  exact
    (smallFactorialGas_le_main_terms (s := s) (k := k) (by omega) hk hks).trans
      (smallFactorialGas_main_terms_le (s := s) hs)

theorem smallFactorialGas_le
    {s k : Nat} (hs : 32 ≤ s) (hk : 2 ≤ k) (hks : k ≤ s) :
    smallFactorialGas s k ≤ 5 / (4 * (s : ℚ)^2) := by
  by_cases hk3 : 3 ≤ k
  · exact smallFactorialGas_le_of_ge_three hs hk3 hks
  · have hk2eq : k = 2 := by omega
    subst k
    have hspos : (0 : ℚ) < (s : ℚ) := by
      exact_mod_cast (by omega : 0 < s)
    unfold smallFactorialGas
    simp [smallFactorialGasTerm_two]
    field_simp [hspos.ne']
    norm_num

theorem Bplusq_small_weightedGas_le
    {N s k : Nat} (hs : 32 ≤ s) (hk : 2 ≤ k) (hks : k ≤ s)
    (hNs : N ≤ s * s) :
    ∑ r ∈ Finset.range (k + 1),
        (1 / ((6 : ℚ) * (s : ℚ)))^r * ((N : ℚ) * c r)
      ≤ 5 * (s : ℚ) / 36 + 1 / 5 := by
  have hspos : (0 : ℚ) < (s : ℚ) := by
    exact_mod_cast (by omega : 0 < s)
  have hN_nonneg : 0 ≤ (N : ℚ) := Nat.cast_nonneg N
  have hNs_rat : (N : ℚ) ≤ (s : ℚ)^2 := by
    have hcast : (N : ℚ) ≤ ((s * s : Nat) : ℚ) := by
      exact_mod_cast hNs
    simpa [pow_two] using hcast
  let F : Nat → ℚ :=
    fun r => (1 / ((6 : ℚ) * (s : ℚ)))^r * ((N : ℚ) * c r)
  have hzero : F 0 = 0 := by
    dsimp [F]
    simp
  have hone : F 1 = 5 * (N : ℚ) / (36 * (s : ℚ)) := by
    dsimp [F]
    field_simp [hspos.ne']
    ring_nf
  have htail :
      ∑ r ∈ Finset.Icc 2 k, F r
        ≤ (N : ℚ) / (5 * (s : ℚ)^2) := by
    have hterm :
        ∀ r ∈ Finset.Icc 2 k,
          F r ≤ ((4 * (N : ℚ)) / 25) * smallFactorialGasTerm s r := by
      intro r hr
      have hr' := Finset.mem_Icc.mp hr
      have hc := c_ub r (by omega : 1 ≤ r)
      have hscale_nonneg :
          0 ≤ (1 / ((6 : ℚ) * (s : ℚ)))^r * (N : ℚ) := by
        positivity
      calc
        F r
            = ((1 / ((6 : ℚ) * (s : ℚ)))^r * (N : ℚ)) * c r := by
              dsimp [F]
              ring
        _ ≤ ((1 / ((6 : ℚ) * (s : ℚ)))^r * (N : ℚ)) *
              ((4 / 25 : ℚ) * (6^r * ((r - 1).factorial : ℚ))) :=
              mul_le_mul_of_nonneg_left hc hscale_nonneg
        _ = ((4 * (N : ℚ)) / 25) * smallFactorialGasTerm s r := by
              have hcancel :
                  (1 / ((6 : ℚ) * (s : ℚ)))^r *
                      (6 : ℚ)^r * (s : ℚ)^r = 1 := by
                rw [← mul_pow, ← mul_pow]
                field_simp [hspos.ne']
                simp
              unfold smallFactorialGasTerm
              field_simp [hspos.ne']
              calc
                (1 / (6 * (s : ℚ))) ^ r * (N : ℚ) * 6 ^ r * (s : ℚ)^r
                    = (N : ℚ) *
                        ((1 / (6 * (s : ℚ))) ^ r * 6 ^ r * (s : ℚ)^r) := by
                      ring
                _ = (N : ℚ) * 1 := by rw [hcancel]
                _ = (N : ℚ) := by ring
    calc
      ∑ r ∈ Finset.Icc 2 k, F r
          ≤ ∑ r ∈ Finset.Icc 2 k,
              ((4 * (N : ℚ)) / 25) * smallFactorialGasTerm s r :=
            Finset.sum_le_sum hterm
      _ = ((4 * (N : ℚ)) / 25) * smallFactorialGas s k := by
            unfold smallFactorialGas
            rw [Finset.mul_sum]
      _ ≤ ((4 * (N : ℚ)) / 25) * (5 / (4 * (s : ℚ)^2)) :=
            mul_le_mul_of_nonneg_left
              (smallFactorialGas_le hs hk hks)
              (by positivity : 0 ≤ (4 * (N : ℚ)) / 25)
      _ = (N : ℚ) / (5 * (s : ℚ)^2) := by
            field_simp [hspos.ne']
            ring
  have hlin :
      5 * (N : ℚ) / (36 * (s : ℚ)) ≤ 5 * (s : ℚ) / 36 := by
    field_simp [hspos.ne']
    nlinarith
  have hquad :
      (N : ℚ) / (5 * (s : ℚ)^2) ≤ 1 / 5 := by
    field_simp [hspos.ne']
    nlinarith
  calc
    ∑ r ∈ Finset.range (k + 1), F r
        = F 0 + F 1 + ∑ r ∈ Finset.Icc 2 k, F r :=
          sum_range_zero_one_Icc_two_eq F hk
    _ = 0 + 5 * (N : ℚ) / (36 * (s : ℚ)) +
          ∑ r ∈ Finset.Icc 2 k, F r := by
          rw [hzero, hone]
    _ ≤ 0 + 5 * (s : ℚ) / 36 + (1 / 5) := by
          have hlin0 :
              0 + 5 * (N : ℚ) / (36 * (s : ℚ)) ≤
                0 + 5 * (s : ℚ) / 36 := by
            linarith
          exact add_le_add hlin0 (htail.trans hquad)
    _ = 5 * (s : ℚ) / 36 + 1 / 5 := by ring

theorem Bplusq_le_small_saddle
    {N s k : Nat} (hs : 32 ≤ s) (hk : 2 ≤ k) (hks : k ≤ s)
    (hNs : N ≤ s * s) :
    Bplusq N k
      ≤ ((6 : ℚ) * (s : ℚ))^k *
          expPrefix (5 * (s : ℚ) / 36 + 1 / 5) k := by
  let rho : ℚ := 1 / ((6 : ℚ) * (s : ℚ))
  let gas : ℚ :=
    ∑ r ∈ Finset.range (k + 1), rho^r * ((N : ℚ) * c r)
  let G : ℚ := 5 * (s : ℚ) / 36 + 1 / 5
  have hspos : (0 : ℚ) < (s : ℚ) := by
    exact_mod_cast (by omega : 0 < s)
  have hrho_pos : 0 < rho := by
    dsimp [rho]
    positivity
  have hgas_nonneg : 0 ≤ gas := by
    dsimp [gas, rho]
    exact Finset.sum_nonneg fun r _ => by
      exact mul_nonneg (pow_nonneg (le_of_lt hrho_pos) r)
        (mul_nonneg (Nat.cast_nonneg N) (c_nonneg r))
  have hgas_le : gas ≤ G := by
    dsimp [gas, G, rho]
    exact Bplusq_small_weightedGas_le hs hk hks hNs
  have hsaddle :
      rho^k * Bplusq N k ≤ expPrefix gas k := by
    have hraw :=
      expCoeff_saddle (rho := rho) (L := fun r => (N : ℚ) * c r)
        (le_of_lt hrho_pos)
        (by
          dsimp
          simp)
        (fun r => mul_nonneg (Nat.cast_nonneg N) (c_nonneg r))
        k
    simpa [Bplusq, gas] using hraw
  have hprefix : expPrefix gas k ≤ expPrefix G k :=
    expPrefix_mono_arg hgas_nonneg hgas_le k
  have hscaled : rho^k * Bplusq N k ≤ expPrefix G k :=
    hsaddle.trans hprefix
  have hrhopow_pos : 0 < rho^k := pow_pos hrho_pos k
  have hdiv : Bplusq N k ≤ expPrefix G k / rho^k := by
    rw [le_div_iff₀ hrhopow_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
  have hdiv_eq :
      expPrefix G k / rho^k =
        ((6 : ℚ) * (s : ℚ))^k * expPrefix G k := by
    have hcancel : ((6 : ℚ) * (s : ℚ))^k * rho^k = 1 := by
      dsimp [rho]
      rw [← mul_pow]
      field_simp [hspos.ne']
      simp
    rw [div_eq_iff hrhopow_pos.ne']
    symm
    calc
      ((6 : ℚ) * (s : ℚ))^k * expPrefix G k * rho^k
          = expPrefix G k * (((6 : ℚ) * (s : ℚ))^k * rho^k) := by
            rw [mul_comm (((6 : ℚ) * (s : ℚ))^k) (expPrefix G k)]
            rw [mul_assoc]
      _ = expPrefix G k * 1 := by rw [hcancel]
      _ = expPrefix G k := by ring
  calc
    Bplusq N k ≤ expPrefix G k / rho^k := hdiv
    _ = ((6 : ℚ) * (s : ℚ))^k * expPrefix G k := hdiv_eq

/-- The common radius used by the tempered `B+` and `Q` coefficient bounds. -/
def saddleBeta : ℚ := 34 / 15

/-- Uniform tempered factorial gas term
`beta^r (r-1)! / n^r`, with `beta = 34/15`. -/
def temperedFactorialGasTerm (n r : Nat) : ℚ :=
  saddleBeta^r * ((r - 1).factorial : ℚ) / (n : ℚ)^r

def temperedFactorialGas (n : Nat) : ℚ :=
  ∑ r ∈ Finset.Icc 2 n, temperedFactorialGasTerm n r

theorem temperedFactorialGasTerm_nonneg (n r : Nat) :
    0 ≤ temperedFactorialGasTerm n r := by
  unfold temperedFactorialGasTerm saddleBeta
  positivity

theorem temperedFactorialGasTerm_succ_eq
    {n r : Nat} (hn : 1 ≤ n) (hr : 1 ≤ r) :
    temperedFactorialGasTerm n (r + 1)
      = temperedFactorialGasTerm n r *
          (((34 : ℚ) * (r : ℚ)) / ((15 : ℚ) * (n : ℚ))) := by
  have hnpos : (0 : ℚ) < (n : ℚ) := by
    exact_mod_cast (by omega : 0 < n)
  unfold temperedFactorialGasTerm saddleBeta
  have hfac :
      (((r + 1 - 1).factorial : Nat) : ℚ)
        = (r : ℚ) * ((r - 1).factorial : ℚ) := by
    rw [show r + 1 - 1 = r by omega]
    rw [show r = (r - 1) + 1 by omega, Nat.factorial_succ]
    norm_num
  rw [hfac, pow_succ (34 / 15 : ℚ), pow_succ (n : ℚ)]
  field_simp [hnpos.ne']

theorem temperedFactorialGasTerm_succ_le
    {n r : Nat} (hn : 1 ≤ n) (hr : 1 ≤ r) (hleft : 34 * r ≤ 15 * n) :
    temperedFactorialGasTerm n (r + 1) ≤ temperedFactorialGasTerm n r := by
  have hnpos : (0 : ℚ) < (n : ℚ) := by
    exact_mod_cast (by omega : 0 < n)
  have hratio :
      ((34 : ℚ) * (r : ℚ)) / ((15 : ℚ) * (n : ℚ)) ≤ 1 := by
    rw [div_le_one (by positivity : (0 : ℚ) < (15 : ℚ) * (n : ℚ))]
    exact_mod_cast hleft
  rw [temperedFactorialGasTerm_succ_eq hn hr]
  calc
    temperedFactorialGasTerm n r *
        (((34 : ℚ) * (r : ℚ)) / ((15 : ℚ) * (n : ℚ)))
        ≤ temperedFactorialGasTerm n r * 1 :=
          mul_le_mul_of_nonneg_left hratio (temperedFactorialGasTerm_nonneg n r)
    _ = temperedFactorialGasTerm n r := by ring

theorem temperedFactorialGasTerm_le_succ
    {n r : Nat} (hn : 1 ≤ n) (hr : 1 ≤ r) (hright : 15 * n ≤ 34 * r) :
    temperedFactorialGasTerm n r ≤ temperedFactorialGasTerm n (r + 1) := by
  have hratio :
      1 ≤ ((34 : ℚ) * (r : ℚ)) / ((15 : ℚ) * (n : ℚ)) := by
    rw [le_div_iff₀ (by positivity : (0 : ℚ) < (15 : ℚ) * (n : ℚ))]
    simpa [one_mul] using
      (show (15 : ℚ) * (n : ℚ) ≤ (34 : ℚ) * (r : ℚ) by
        exact_mod_cast hright)
  rw [temperedFactorialGasTerm_succ_eq hn hr]
  calc
    temperedFactorialGasTerm n r
        = temperedFactorialGasTerm n r * 1 := by ring
    _ ≤ temperedFactorialGasTerm n r *
        (((34 : ℚ) * (r : ℚ)) / ((15 : ℚ) * (n : ℚ))) :=
          mul_le_mul_of_nonneg_left hratio (temperedFactorialGasTerm_nonneg n r)

theorem temperedFactorialGasTerm_two (n : Nat) :
    temperedFactorialGasTerm n 2 = saddleBeta^2 / (n : ℚ)^2 := by
  norm_num [temperedFactorialGasTerm]

theorem temperedFactorialGasTerm_three (n : Nat) :
    temperedFactorialGasTerm n 3 = 2 * saddleBeta^3 / (n : ℚ)^3 := by
  norm_num [temperedFactorialGasTerm]
  ring

theorem temperedFactorialGasTerm_four (n : Nat) :
    temperedFactorialGasTerm n 4 = 6 * saddleBeta^4 / (n : ℚ)^4 := by
  norm_num [temperedFactorialGasTerm, Nat.factorial]
  ring

/-- Endpoint envelope `W_n = n^2 u_{n,n}` in factorial form. -/
def temperedEndpointW (n : Nat) : ℚ :=
  saddleBeta^n * (n.factorial : ℚ) / (n : ℚ)^(n - 1)

theorem temperedEndpointW_nonneg (n : Nat) :
    0 ≤ temperedEndpointW n := by
  unfold temperedEndpointW saddleBeta
  positivity

private theorem temperedEndpointW_forty_le_half :
    temperedEndpointW 40 ≤ 1 / 2 := by
  norm_num [temperedEndpointW, saddleBeta, Nat.factorial]

theorem temperedEndpointW_eq_scaled_last_term
    {n : Nat} (hn : 1 ≤ n) :
    (n : ℚ)^2 * temperedFactorialGasTerm n n = temperedEndpointW n := by
  have hnpos : (0 : ℚ) < (n : ℚ) := by
    exact_mod_cast (by omega : 0 < n)
  unfold temperedEndpointW temperedFactorialGasTerm
  have hfac :
      (n.factorial : ℚ) = (n : ℚ) * ((n - 1).factorial : ℚ) := by
    rw [show n = (n - 1) + 1 by omega, Nat.factorial_succ]
    norm_num
  have hpow : (n : ℚ)^n = (n : ℚ)^(n - 1) * (n : ℚ) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
    rw [show n - 1 + 1 = n by omega]
  rw [hfac]
  field_simp [hnpos.ne']
  rw [hpow]
  ring

private theorem saddleBeta_le_one_add_inv_pow_pred
    {n : Nat} (hn : 40 ≤ n) :
    saddleBeta ≤ (1 + 1 / (n : ℚ))^(n - 1) := by
  have hnpos : (0 : ℚ) < (n : ℚ) := by
    exact_mod_cast (by omega : 0 < n)
  have hmono :
      (64 / 27 : ℚ) ≤ (1 + 1 / (n : ℚ))^n := by
    have h :=
      one_add_inv_pow_mono (n := 3) (m := n) (by norm_num) (by omega)
    norm_num at h
    simpa using h
  let A : ℚ := (1 + 1 / (n : ℚ))^(n - 1)
  let B : ℚ := 1 + 1 / (n : ℚ)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB_le : B ≤ 41 / 40 := by
    have hinv : 1 / (n : ℚ) ≤ 1 / 40 := by
      field_simp [hnpos.ne']
      exact_mod_cast hn
    dsimp [B]
    linarith
  have hsplit : (1 + 1 / (n : ℚ))^n = A * B := by
    dsimp [A, B]
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
    rw [show n - 1 + 1 = n by omega]
  have hprod_le : (1 + 1 / (n : ℚ))^n ≤ A * (41 / 40) := by
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left hB_le hA_nonneg
  have hA_lb : (64 / 27 : ℚ) / (41 / 40) ≤ A := by
    rw [div_le_iff₀ (by norm_num : (0 : ℚ) < 41 / 40)]
    exact hmono.trans hprod_le
  have hbeta : saddleBeta ≤ (64 / 27 : ℚ) / (41 / 40) := by
    norm_num [saddleBeta]
  exact hbeta.trans hA_lb

private theorem temperedEndpointW_succ_eq {n : Nat} (hn : 1 ≤ n) :
    temperedEndpointW (n + 1)
      = temperedEndpointW n *
          (saddleBeta / (1 + 1 / (n : ℚ))^(n - 1)) := by
  have hnpos : (0 : ℚ) < (n : ℚ) := by
    exact_mod_cast (by omega : 0 < n)
  have hbasepos : (0 : ℚ) < 1 + 1 / (n : ℚ) := by positivity
  have hone :
      1 + 1 / (n : ℚ) = ((n + 1 : Nat) : ℚ) / (n : ℚ) := by
    field_simp [hnpos.ne']
    push_cast
    ring
  unfold temperedEndpointW
  rw [Nat.factorial_succ]
  rw [hone, div_pow]
  norm_num
  field_simp [hnpos.ne', show (((n + 1 : Nat) : ℚ) ≠ 0) by positivity]
  have hpow :
      ((n : ℚ) + 1)^n = ((n : ℚ) + 1)^(n - 1) * ((n : ℚ) + 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
    rw [show n - 1 + 1 = n by omega]
  rw [hpow]
  ring

private theorem temperedEndpointW_succ_le
    {n : Nat} (hn : 40 ≤ n) :
    temperedEndpointW (n + 1) ≤ temperedEndpointW n := by
  have hdenpos : (0 : ℚ) < (1 + 1 / (n : ℚ))^(n - 1) := by
    positivity
  have hratio :
      saddleBeta / (1 + 1 / (n : ℚ))^(n - 1) ≤ 1 := by
    rw [div_le_one hdenpos]
    exact saddleBeta_le_one_add_inv_pow_pred hn
  rw [temperedEndpointW_succ_eq (by omega : 1 ≤ n)]
  calc
    temperedEndpointW n *
        (saddleBeta / (1 + 1 / (n : ℚ))^(n - 1))
        ≤ temperedEndpointW n * 1 :=
          mul_le_mul_of_nonneg_left hratio (temperedEndpointW_nonneg n)
    _ = temperedEndpointW n := by ring

theorem temperedEndpointW_le_half {n : Nat} (hn : 40 ≤ n) :
    temperedEndpointW n ≤ 1 / 2 := by
  exact Nat.le_induction
    (m := 40)
    (P := fun n _ => temperedEndpointW n ≤ 1 / 2)
    temperedEndpointW_forty_le_half
    (fun n hn ih => (temperedEndpointW_succ_le hn).trans ih)
    n hn

theorem temperedFactorialGasTerm_le_four_add_last
    {n r : Nat} (hn : 40 ≤ n) (hr4 : 4 ≤ r) (hrn : r ≤ n) :
    temperedFactorialGasTerm n r
      ≤ temperedFactorialGasTerm n 4 + temperedFactorialGasTerm n n := by
  by_cases hleft : 34 * r ≤ 15 * n
  · have hle_four :
        temperedFactorialGasTerm n r ≤ temperedFactorialGasTerm n 4 := by
      have hmono :
          ∀ t : Nat, 4 ≤ t → t ≤ r →
            temperedFactorialGasTerm n t ≤ temperedFactorialGasTerm n 4 := by
        intro t ht4
        induction t, ht4 using Nat.le_induction with
        | base =>
            intro _htr
            rfl
        | succ t ht4t ih =>
            intro hsucc_le
            have ht1 : 1 ≤ t := by omega
            have hcond : 34 * t ≤ 15 * n := by omega
            exact
              (temperedFactorialGasTerm_succ_le
                  (n := n) (r := t) (by omega) ht1 hcond).trans
                (ih (by omega))
      exact hmono r hr4 le_rfl
    exact hle_four.trans
      (le_add_of_nonneg_right (temperedFactorialGasTerm_nonneg n n))
  · have hright : 15 * n ≤ 34 * r := by omega
    have hle_last :
        temperedFactorialGasTerm n r ≤ temperedFactorialGasTerm n n := by
      have hmono :
          ∀ t : Nat, r ≤ t →
            temperedFactorialGasTerm n r ≤ temperedFactorialGasTerm n t := by
        intro t hrt
        induction t, hrt using Nat.le_induction with
        | base =>
            rfl
        | succ t hrt ih =>
            have ht1 : 1 ≤ t := by omega
            have hcond : 15 * n ≤ 34 * t := by omega
            exact ih.trans
              (temperedFactorialGasTerm_le_succ
                (n := n) (r := t) (by omega) ht1 hcond)
      exact hmono n hrn
    exact hle_last.trans
      (le_add_of_nonneg_left (temperedFactorialGasTerm_nonneg n 4))

private theorem temperedFactorialGas_low_scaled_le
    {n : Nat} (hn : 40 ≤ n) :
    (n : ℚ) *
        (temperedFactorialGasTerm n 2 + temperedFactorialGasTerm n 3)
      ≤ 1 / 6 := by
  have hnpos : (0 : ℚ) < (n : ℚ) := by
    exact_mod_cast (by omega : 0 < n)
  have hn40 : (40 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  rw [temperedFactorialGasTerm_two, temperedFactorialGasTerm_three]
  unfold saddleBeta
  field_simp [hnpos.ne']
  nlinarith

private theorem temperedFactorialGas_four_scaled_le
    {n : Nat} (hn : 40 ≤ n) :
    (n : ℚ)^2 * temperedFactorialGasTerm n 4 ≤ 1 / 8 := by
  have hnpos : (0 : ℚ) < (n : ℚ) := by
    exact_mod_cast (by omega : 0 < n)
  have hn40 : (40 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  rw [temperedFactorialGasTerm_four]
  unfold saddleBeta
  field_simp [hnpos.ne']
  nlinarith

private theorem temperedFactorialGas_last_scaled_le
    {n : Nat} (hn : 40 ≤ n) :
    (n : ℚ)^2 * temperedFactorialGasTerm n n ≤ 1 / 2 := by
  rw [temperedEndpointW_eq_scaled_last_term (by omega : 1 ≤ n)]
  exact temperedEndpointW_le_half hn

private theorem temperedFactorialGas_tail_le_endpoints
    {n : Nat} (hn : 40 ≤ n) :
    ∑ r ∈ Finset.Icc 4 n, temperedFactorialGasTerm n r
      ≤ (n : ℚ) *
          (temperedFactorialGasTerm n 4 + temperedFactorialGasTerm n n) := by
  have hterm :
      ∀ r ∈ Finset.Icc 4 n,
        temperedFactorialGasTerm n r
          ≤ temperedFactorialGasTerm n 4 + temperedFactorialGasTerm n n := by
    intro r hr
    have hr' := Finset.mem_Icc.mp hr
    exact temperedFactorialGasTerm_le_four_add_last hn hr'.1 hr'.2
  have hcard : (Finset.Icc 4 n).card ≤ n := by
    have hsubset : Finset.Icc 4 n ⊆ Finset.Ico 1 (n + 1) := by
      intro r hr
      have hr' := Finset.mem_Icc.mp hr
      exact Finset.mem_Ico.mpr (by omega)
    calc
      (Finset.Icc 4 n).card ≤ (Finset.Ico 1 (n + 1)).card :=
        Finset.card_le_card hsubset
      _ = n := by
        simp
  have hconst :
      0 ≤ temperedFactorialGasTerm n 4 + temperedFactorialGasTerm n n :=
    add_nonneg (temperedFactorialGasTerm_nonneg n 4)
      (temperedFactorialGasTerm_nonneg n n)
  calc
    ∑ r ∈ Finset.Icc 4 n, temperedFactorialGasTerm n r
        ≤ ∑ _r ∈ Finset.Icc 4 n,
            (temperedFactorialGasTerm n 4 + temperedFactorialGasTerm n n) :=
          Finset.sum_le_sum hterm
    _ = ((Finset.Icc 4 n).card : ℚ) *
          (temperedFactorialGasTerm n 4 + temperedFactorialGasTerm n n) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (n : ℚ) *
          (temperedFactorialGasTerm n 4 + temperedFactorialGasTerm n n) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hconst

/-
Implementation note: the working notes split the middle and high blocks at
`n - 10`.  For Lean this shorter variant is enough: unimodality bounds every
term with `4 <= r <= n` by `u_4 + u_n`, and the sharper endpoint estimate
`n^2 u_n <= 1/2` leaves the final budget below `1`.
-/
theorem temperedFactorialGas_le_inv {n : Nat} (hn : 40 ≤ n) :
    temperedFactorialGas n ≤ 1 / (n : ℚ) := by
  have hnpos : (0 : ℚ) < (n : ℚ) := by
    exact_mod_cast (by omega : 0 < n)
  unfold temperedFactorialGas
  rw [smallFactorialGas_sum_Icc_two_eq
    (fun r => temperedFactorialGasTerm n r) (by omega : 3 ≤ n)]
  let tail : ℚ := ∑ r ∈ Finset.Icc 4 n, temperedFactorialGasTerm n r
  have hlow := temperedFactorialGas_low_scaled_le (n := n) hn
  have htail_base :
      tail ≤ (n : ℚ) *
        (temperedFactorialGasTerm n 4 + temperedFactorialGasTerm n n) := by
    dsimp [tail]
    exact temperedFactorialGas_tail_le_endpoints hn
  have htail_scaled :
      (n : ℚ) * tail ≤ 1 / 8 + 1 / 2 := by
    have hmul := mul_le_mul_of_nonneg_left htail_base hnpos.le
    calc
      (n : ℚ) * tail
          ≤ (n : ℚ) *
              ((n : ℚ) *
                (temperedFactorialGasTerm n 4 + temperedFactorialGasTerm n n)) :=
            hmul
      _ = (n : ℚ)^2 * temperedFactorialGasTerm n 4 +
            (n : ℚ)^2 * temperedFactorialGasTerm n n := by
            ring
      _ ≤ 1 / 8 + 1 / 2 :=
            add_le_add
              (temperedFactorialGas_four_scaled_le (n := n) hn)
              (temperedFactorialGas_last_scaled_le (n := n) hn)
  have hscaled :
      (n : ℚ) *
        (temperedFactorialGasTerm n 2 + temperedFactorialGasTerm n 3 + tail)
        ≤ 1 := by
    calc
      (n : ℚ) *
          (temperedFactorialGasTerm n 2 + temperedFactorialGasTerm n 3 + tail)
          =
        (n : ℚ) *
          (temperedFactorialGasTerm n 2 + temperedFactorialGasTerm n 3) +
            (n : ℚ) * tail := by
            ring
      _ ≤ 1 / 6 + (1 / 8 + 1 / 2) :=
            add_le_add hlow htail_scaled
      _ ≤ 1 := by norm_num
  rw [le_div_iff₀ hnpos]
  simpa [tail, mul_comm, mul_left_comm, mul_assoc] using hscaled

theorem Bplusq_tempered_weightedGas_le
    {N k : Nat} (hk : 40 ≤ k) :
    ∑ r ∈ Finset.range (k + 1),
        (17 / (45 * (k : ℚ)))^r * ((N : ℚ) * c r)
      ≤ 17 * (N : ℚ) / (54 * (k : ℚ)) +
          4 * (N : ℚ) / (25 * (k : ℚ)) := by
  have hkpos : (0 : ℚ) < (k : ℚ) := by
    exact_mod_cast (by omega : 0 < k)
  let rho : ℚ := 17 / (45 * (k : ℚ))
  let F : Nat → ℚ := fun r => rho^r * ((N : ℚ) * c r)
  have hzero : F 0 = 0 := by
    dsimp [F, rho]
    simp
  have hone : F 1 = 17 * (N : ℚ) / (54 * (k : ℚ)) := by
    dsimp [F, rho]
    field_simp [hkpos.ne']
    ring_nf
  have htail :
      ∑ r ∈ Finset.Icc 2 k, F r
        ≤ 4 * (N : ℚ) / (25 * (k : ℚ)) := by
    have hterm :
        ∀ r ∈ Finset.Icc 2 k,
          F r ≤ ((4 * (N : ℚ)) / 25) * temperedFactorialGasTerm k r := by
      intro r hr
      have hr' := Finset.mem_Icc.mp hr
      have hc := c_ub r (by omega : 1 ≤ r)
      have hscale_nonneg : 0 ≤ rho^r * (N : ℚ) := by
        exact mul_nonneg (pow_nonneg (by dsimp [rho]; positivity) r)
          (Nat.cast_nonneg N)
      calc
        F r
            = (rho^r * (N : ℚ)) * c r := by
              dsimp [F]
              ring
        _ ≤ (rho^r * (N : ℚ)) *
              ((4 / 25 : ℚ) * (6^r * ((r - 1).factorial : ℚ))) :=
              mul_le_mul_of_nonneg_left hc hscale_nonneg
        _ = ((4 * (N : ℚ)) / 25) * temperedFactorialGasTerm k r := by
              have hpow :
                  rho^r * (6 : ℚ)^r * (k : ℚ)^r = saddleBeta^r := by
                dsimp [rho, saddleBeta]
                rw [← mul_pow, ← mul_pow]
                field_simp [hkpos.ne']
                ring
              unfold temperedFactorialGasTerm
              field_simp [hkpos.ne']
              calc
                rho ^ r * (N : ℚ) * 6 ^ r * (k : ℚ)^r
                    = (N : ℚ) * (rho^r * 6^r * (k : ℚ)^r) := by
                      ring
                _ = (N : ℚ) * saddleBeta^r := by rw [hpow]
                _ = (N : ℚ) * saddleBeta^r := rfl
    calc
      ∑ r ∈ Finset.Icc 2 k, F r
          ≤ ∑ r ∈ Finset.Icc 2 k,
              ((4 * (N : ℚ)) / 25) * temperedFactorialGasTerm k r :=
            Finset.sum_le_sum hterm
      _ = ((4 * (N : ℚ)) / 25) * temperedFactorialGas k := by
            unfold temperedFactorialGas
            rw [Finset.mul_sum]
      _ ≤ ((4 * (N : ℚ)) / 25) * (1 / (k : ℚ)) :=
            mul_le_mul_of_nonneg_left
              (temperedFactorialGas_le_inv hk)
              (by positivity : 0 ≤ (4 * (N : ℚ)) / 25)
      _ = 4 * (N : ℚ) / (25 * (k : ℚ)) := by
            field_simp [hkpos.ne']
  calc
    ∑ r ∈ Finset.range (k + 1), F r
        = F 0 + F 1 + ∑ r ∈ Finset.Icc 2 k, F r :=
          sum_range_zero_one_Icc_two_eq F (by omega : 2 ≤ k)
    _ = 0 + 17 * (N : ℚ) / (54 * (k : ℚ)) +
          ∑ r ∈ Finset.Icc 2 k, F r := by
          rw [hzero, hone]
    _ ≤ 0 + 17 * (N : ℚ) / (54 * (k : ℚ)) +
          4 * (N : ℚ) / (25 * (k : ℚ)) := by
          linarith
    _ = 17 * (N : ℚ) / (54 * (k : ℚ)) +
          4 * (N : ℚ) / (25 * (k : ℚ)) := by ring

theorem Bplusq_le_tempered_saddle
    {N k : Nat} (hk : 40 ≤ k) :
    Bplusq N k
      ≤ (45 * (k : ℚ) / 17)^k *
          expPrefix
            (17 * (N : ℚ) / (54 * (k : ℚ)) +
              4 * (N : ℚ) / (25 * (k : ℚ))) k := by
  let rho : ℚ := 17 / (45 * (k : ℚ))
  let gas : ℚ :=
    ∑ r ∈ Finset.range (k + 1), rho^r * ((N : ℚ) * c r)
  let G : ℚ :=
    17 * (N : ℚ) / (54 * (k : ℚ)) +
      4 * (N : ℚ) / (25 * (k : ℚ))
  have hkpos : (0 : ℚ) < (k : ℚ) := by
    exact_mod_cast (by omega : 0 < k)
  have hrho_pos : 0 < rho := by
    dsimp [rho]
    positivity
  have hgas_nonneg : 0 ≤ gas := by
    dsimp [gas, rho]
    exact Finset.sum_nonneg fun r _ => by
      exact mul_nonneg (pow_nonneg (le_of_lt hrho_pos) r)
        (mul_nonneg (Nat.cast_nonneg N) (c_nonneg r))
  have hgas_le : gas ≤ G := by
    dsimp [gas, G, rho]
    exact Bplusq_tempered_weightedGas_le hk
  have hsaddle :
      rho^k * Bplusq N k ≤ expPrefix gas k := by
    have hraw :=
      expCoeff_saddle (rho := rho) (L := fun r => (N : ℚ) * c r)
        (le_of_lt hrho_pos)
        (by
          dsimp
          simp)
        (fun r => mul_nonneg (Nat.cast_nonneg N) (c_nonneg r))
        k
    simpa [Bplusq, gas] using hraw
  have hscaled :
      rho^k * Bplusq N k ≤ expPrefix G k :=
    hsaddle.trans (expPrefix_mono_arg hgas_nonneg hgas_le k)
  have hrhopow_pos : 0 < rho^k := pow_pos hrho_pos k
  have hdiv : Bplusq N k ≤ expPrefix G k / rho^k := by
    rw [le_div_iff₀ hrhopow_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
  have hdiv_eq :
      expPrefix G k / rho^k =
        (45 * (k : ℚ) / 17)^k * expPrefix G k := by
    have hcancel : (45 * (k : ℚ) / 17)^k * rho^k = 1 := by
      dsimp [rho]
      rw [← mul_pow]
      field_simp [hkpos.ne']
      ring
    rw [div_eq_iff hrhopow_pos.ne']
    symm
    calc
      (45 * (k : ℚ) / 17)^k * expPrefix G k * rho^k
          = expPrefix G k * ((45 * (k : ℚ) / 17)^k * rho^k) := by
            rw [mul_comm ((45 * (k : ℚ) / 17)^k) (expPrefix G k)]
            rw [mul_assoc]
      _ = expPrefix G k * 1 := by rw [hcancel]
      _ = expPrefix G k := by ring
  calc
    Bplusq N k ≤ expPrefix G k / rho^k := hdiv
    _ = (45 * (k : ℚ) / 17)^k * expPrefix G k := hdiv_eq

theorem Qq_tempered_weightedGas_le
    {N j : Nat} (hj : 40 ≤ j) :
    ∑ r ∈ Finset.range (j + 1),
        (34 / (45 * (j : ℚ)))^r *
          (((N : ℚ) / 2) * c r / (2 : ℚ)^r)
      ≤ 17 * (N : ℚ) / (108 * (j : ℚ)) +
          2 * (N : ℚ) / (25 * (j : ℚ)) := by
  have hjpos : (0 : ℚ) < (j : ℚ) := by
    exact_mod_cast (by omega : 0 < j)
  let rho : ℚ := 34 / (45 * (j : ℚ))
  let F : Nat → ℚ :=
    fun r => rho^r * (((N : ℚ) / 2) * c r / (2 : ℚ)^r)
  have hzero : F 0 = 0 := by
    dsimp [F, rho]
    simp
  have hone : F 1 = 17 * (N : ℚ) / (108 * (j : ℚ)) := by
    dsimp [F, rho]
    field_simp [hjpos.ne']
    ring_nf
  have htail :
      ∑ r ∈ Finset.Icc 2 j, F r
        ≤ 2 * (N : ℚ) / (25 * (j : ℚ)) := by
    have hterm :
        ∀ r ∈ Finset.Icc 2 j,
          F r ≤ ((2 * (N : ℚ)) / 25) * temperedFactorialGasTerm j r := by
      intro r hr
      have hr' := Finset.mem_Icc.mp hr
      have hc := c_ub r (by omega : 1 ≤ r)
      have hscale_nonneg :
          0 ≤ rho^r * (((N : ℚ) / 2) / (2 : ℚ)^r) := by
        exact mul_nonneg (pow_nonneg (by dsimp [rho]; positivity) r)
          (div_nonneg (div_nonneg (Nat.cast_nonneg N) (by norm_num))
            (by positivity))
      calc
        F r
            = (rho^r * (((N : ℚ) / 2) / (2 : ℚ)^r)) * c r := by
              dsimp [F]
              field_simp
        _ ≤ (rho^r * (((N : ℚ) / 2) / (2 : ℚ)^r)) *
              ((4 / 25 : ℚ) * (6^r * ((r - 1).factorial : ℚ))) :=
              mul_le_mul_of_nonneg_left hc hscale_nonneg
        _ = ((2 * (N : ℚ)) / 25) * temperedFactorialGasTerm j r := by
              have hpow :
                  rho^r * (3 : ℚ)^r * (j : ℚ)^r = saddleBeta^r := by
                dsimp [rho, saddleBeta]
                rw [← mul_pow, ← mul_pow]
                field_simp [hjpos.ne']
                ring
              have h6pow : (6 : ℚ)^r = (2 : ℚ)^r * (3 : ℚ)^r := by
                rw [← mul_pow]
                norm_num
              unfold temperedFactorialGasTerm
              field_simp [hjpos.ne']
              rw [h6pow]
              calc
                rho ^ r * (N : ℚ) * 4 * ((2 : ℚ)^r * 3 ^ r) * (j : ℚ)^r
                    = (N : ℚ) * 4 * (2 : ℚ)^r *
                        (rho^r * 3^r * (j : ℚ)^r) := by
                      ring
                _ = (N : ℚ) * 4 * (2 : ℚ)^r * saddleBeta^r := by rw [hpow]
                _ = (N : ℚ) * 2^2 * (2 : ℚ)^r * saddleBeta^r := by norm_num
    calc
      ∑ r ∈ Finset.Icc 2 j, F r
          ≤ ∑ r ∈ Finset.Icc 2 j,
              ((2 * (N : ℚ)) / 25) * temperedFactorialGasTerm j r :=
            Finset.sum_le_sum hterm
      _ = ((2 * (N : ℚ)) / 25) * temperedFactorialGas j := by
            unfold temperedFactorialGas
            rw [Finset.mul_sum]
      _ ≤ ((2 * (N : ℚ)) / 25) * (1 / (j : ℚ)) :=
            mul_le_mul_of_nonneg_left
              (temperedFactorialGas_le_inv hj)
              (by positivity : 0 ≤ (2 * (N : ℚ)) / 25)
      _ = 2 * (N : ℚ) / (25 * (j : ℚ)) := by
            field_simp [hjpos.ne']
  calc
    ∑ r ∈ Finset.range (j + 1), F r
        = F 0 + F 1 + ∑ r ∈ Finset.Icc 2 j, F r :=
          sum_range_zero_one_Icc_two_eq F (by omega : 2 ≤ j)
    _ = 0 + 17 * (N : ℚ) / (108 * (j : ℚ)) +
          ∑ r ∈ Finset.Icc 2 j, F r := by
          rw [hzero, hone]
    _ ≤ 0 + 17 * (N : ℚ) / (108 * (j : ℚ)) +
          2 * (N : ℚ) / (25 * (j : ℚ)) := by
          linarith
    _ = 17 * (N : ℚ) / (108 * (j : ℚ)) +
          2 * (N : ℚ) / (25 * (j : ℚ)) := by ring

theorem Qq_le_tempered_saddle
    {N j : Nat} (hj : 40 ≤ j) :
    Qq N j
      ≤ (45 * (j : ℚ) / 34)^j *
          expPrefix
            (17 * (N : ℚ) / (108 * (j : ℚ)) +
              2 * (N : ℚ) / (25 * (j : ℚ))) j := by
  let rho : ℚ := 34 / (45 * (j : ℚ))
  let gas : ℚ :=
    ∑ r ∈ Finset.range (j + 1),
      rho^r * (((N : ℚ) / 2) * c r / (2 : ℚ)^r)
  let G : ℚ :=
    17 * (N : ℚ) / (108 * (j : ℚ)) +
      2 * (N : ℚ) / (25 * (j : ℚ))
  have hjpos : (0 : ℚ) < (j : ℚ) := by
    exact_mod_cast (by omega : 0 < j)
  have hrho_pos : 0 < rho := by
    dsimp [rho]
    positivity
  have hgas_nonneg : 0 ≤ gas := by
    dsimp [gas, rho]
    exact Finset.sum_nonneg fun r _ => by
      exact mul_nonneg (pow_nonneg (le_of_lt hrho_pos) r)
        (div_nonneg
          (mul_nonneg (div_nonneg (Nat.cast_nonneg N) (by norm_num)) (c_nonneg r))
          (by positivity))
  have hgas_le : gas ≤ G := by
    dsimp [gas, G, rho]
    exact Qq_tempered_weightedGas_le hj
  have hsaddle :
      rho^j * Qq N j ≤ expPrefix gas j := by
    have hraw :=
      expCoeff_saddle (rho := rho)
        (L := fun r => ((N : ℚ) / 2) * c r / (2 : ℚ)^r)
        (le_of_lt hrho_pos)
        (by
          dsimp
          simp)
        (fun r => by
          exact div_nonneg
            (mul_nonneg (div_nonneg (Nat.cast_nonneg N) (by norm_num))
              (c_nonneg r))
            (by positivity))
        j
    simpa [Qq, gas] using hraw
  have hscaled :
      rho^j * Qq N j ≤ expPrefix G j :=
    hsaddle.trans (expPrefix_mono_arg hgas_nonneg hgas_le j)
  have hrhopow_pos : 0 < rho^j := pow_pos hrho_pos j
  have hdiv : Qq N j ≤ expPrefix G j / rho^j := by
    rw [le_div_iff₀ hrhopow_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
  have hdiv_eq :
      expPrefix G j / rho^j =
        (45 * (j : ℚ) / 34)^j * expPrefix G j := by
    have hcancel : (45 * (j : ℚ) / 34)^j * rho^j = 1 := by
      dsimp [rho]
      rw [← mul_pow]
      field_simp [hjpos.ne']
      ring
    rw [div_eq_iff hrhopow_pos.ne']
    symm
    calc
      (45 * (j : ℚ) / 34)^j * expPrefix G j * rho^j
          = expPrefix G j * ((45 * (j : ℚ) / 34)^j * rho^j) := by
            rw [mul_comm ((45 * (j : ℚ) / 34)^j) (expPrefix G j)]
            rw [mul_assoc]
      _ = expPrefix G j * 1 := by rw [hcancel]
      _ = expPrefix G j := by ring
  calc
    Qq N j ≤ expPrefix G j / rho^j := hdiv
    _ = (45 * (j : ℚ) / 34)^j * expPrefix G j := hdiv_eq

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
