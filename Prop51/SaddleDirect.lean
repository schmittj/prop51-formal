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
