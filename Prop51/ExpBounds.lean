/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Rational surrogates for `e` and `exp` (Layer C analytic toolkit)

Layer C is formalized entirely in `ℚ`; this file provides the two
ingredients that replace real exponentials:

* **partial-exp majorants** (`sum_exp_le`): a bound on `Σ_{t<T} y^t/t!`
  that is *uniform in the truncation* `T` — the first `T₀` terms exactly,
  plus a geometric tail `(y^{T₀}/T₀!)/(1 - y/T₀)`.  All the Poisson-type
  moments of the sign-lock (paper §5) are finite sums of this shape.
* **the rational Stirling lower bound** (`factorial_lb`):
  `(25r/68)^r ≤ r!`, i.e. `r! ≥ (r/e')^r` with `e' = 68/25 = 2.72 ≥ e`.
  It follows from `(1+1/n)^n ≤ Σ_{k} 1/k! ≤ 1631/600 < 68/25`
  (binomial theorem + the partial-exp majorant at `y = 1`), and replaces
  every Stirling estimate of the paper at the cost of `(68/(25e))^r`,
  absorbed by the constants' slack.
-/

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Prop51

/-! ## Geometric sums -/

/-- Closed form of the partial geometric sum. -/
theorem geom_sum_closed (q : ℚ) (hq : q ≠ 1) (K : ℕ) :
    ∑ j ∈ Finset.range K, q^j = (1 - q^K)/(1-q) := by
  have hne : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      field_simp
      ring

/-- `Σ_{j<K} q^j ≤ 1/(1-q)` for `0 ≤ q < 1`, uniformly in `K`. -/
theorem geom_sum_le_inv_one_sub (q : ℚ) (h0 : 0 ≤ q) (h1 : q < 1) (K : ℕ) :
    ∑ j ∈ Finset.range K, q^j ≤ 1/(1-q) := by
  have hpos : (0:ℚ) < 1 - q := by linarith
  rw [geom_sum_closed q (by linarith) K, div_le_div_iff₀ hpos hpos]
  have hK : (0:ℚ) ≤ q^K := pow_nonneg h0 K
  nlinarith [mul_nonneg hK hpos.le]

/-! ## The partial-exp majorant -/

private theorem exp_tail_term_le (y : ℚ) (hy : 0 ≤ y) (T₀ j : ℕ)
    (hT : 1 ≤ T₀) :
    y^(T₀+j) / ((T₀+j).factorial : ℚ)
      ≤ (y^T₀ / (T₀.factorial : ℚ)) * (y/(T₀:ℚ))^j := by
  have hNat : T₀.factorial * T₀^j ≤ (T₀+j).factorial :=
    le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) j))
      Nat.factorial_mul_pow_le_factorial
  have hden : (0:ℚ) < (T₀.factorial : ℚ) * (T₀:ℚ)^j := by
    have h1 : (0:ℚ) < (T₀.factorial : ℚ) := by
      exact_mod_cast T₀.factorial_pos
    have h2 : (0:ℚ) < (T₀:ℚ)^j := by
      have : (0:ℚ) < (T₀:ℚ) := by exact_mod_cast (by omega : 0 < T₀)
      positivity
    positivity
  rw [pow_add, div_pow, div_mul_div_comm]
  apply div_le_div_of_nonneg_left (by positivity) hden
  exact_mod_cast hNat

/-- **The partial-exp majorant**, uniform in the truncation `T`:
for `0 ≤ y < T₀`,
`Σ_{t<T} y^t/t! ≤ Σ_{t<T₀} y^t/t! + (y^{T₀}/T₀!)·(1/(1 - y/T₀))`. -/
theorem sum_exp_le (y : ℚ) (T₀ : ℕ) (hy : 0 ≤ y) (hyT : y < (T₀:ℚ)) (T : ℕ) :
    ∑ t ∈ Finset.range T, y^t / (t.factorial : ℚ)
      ≤ (∑ t ∈ Finset.range T₀, y^t / (t.factorial : ℚ))
        + (y^T₀ / (T₀.factorial : ℚ)) * (1 / (1 - y/(T₀:ℚ))) := by
  have hT0 : 1 ≤ T₀ := by
    rcases Nat.eq_zero_or_pos T₀ with rfl | h
    · exfalso
      rw [Nat.cast_zero] at hyT
      linarith
    · exact h
  have hT0Q : (0:ℚ) < (T₀:ℚ) := by exact_mod_cast (by omega : 0 < T₀)
  have hq0 : 0 ≤ y/(T₀:ℚ) := div_nonneg hy hT0Q.le
  have hq1 : y/(T₀:ℚ) < 1 := by rw [div_lt_one hT0Q]; exact hyT
  have h1q : (0:ℚ) < 1 - y/(T₀:ℚ) := by linarith
  have htermnn : ∀ t : ℕ, (0:ℚ) ≤ y^t / (t.factorial : ℚ) := fun t => by
    have : (0:ℚ) < (t.factorial : ℚ) := by exact_mod_cast t.factorial_pos
    positivity
  have hgnn : (0:ℚ) ≤ (y^T₀ / (T₀.factorial : ℚ)) * (1 / (1 - y/(T₀:ℚ))) := by
    have h1 : (0:ℚ) ≤ y^T₀ / (T₀.factorial : ℚ) := htermnn T₀
    exact mul_nonneg h1 (one_div_nonneg.mpr h1q.le)
  rcases Nat.lt_or_ge T T₀ with hTlt | hTge
  · have hmono : ∑ t ∈ Finset.range T, y^t / (t.factorial : ℚ)
        ≤ ∑ t ∈ Finset.range T₀, y^t / (t.factorial : ℚ) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun x hx => Finset.mem_range.mpr
          (by have := Finset.mem_range.mp hx; omega))
        (fun t _ _ => htermnn t)
    linarith
  · have hsplit : ∑ t ∈ Finset.range T, y^t / (t.factorial : ℚ)
        = (∑ t ∈ Finset.range T₀, y^t / (t.factorial : ℚ))
          + ∑ t ∈ Finset.Ico T₀ T, y^t / (t.factorial : ℚ) := by
      rw [Finset.range_eq_Ico,
          ← Finset.sum_Ico_consecutive _ (Nat.zero_le T₀) hTge,
          ← Finset.range_eq_Ico]
    rw [hsplit]
    have htail : ∑ t ∈ Finset.Ico T₀ T, y^t / (t.factorial : ℚ)
        ≤ (y^T₀ / (T₀.factorial : ℚ)) * (1 / (1 - y/(T₀:ℚ))) := by
      rw [Finset.sum_Ico_eq_sum_range]
      calc ∑ j ∈ Finset.range (T - T₀), y^(T₀+j) / ((T₀+j).factorial : ℚ)
          ≤ ∑ j ∈ Finset.range (T - T₀),
              (y^T₀ / (T₀.factorial : ℚ)) * (y/(T₀:ℚ))^j :=
            Finset.sum_le_sum fun j _ => exp_tail_term_le y hy T₀ j hT0
        _ = (y^T₀ / (T₀.factorial : ℚ))
              * ∑ j ∈ Finset.range (T - T₀), (y/(T₀:ℚ))^j := by
            rw [Finset.mul_sum]
        _ ≤ (y^T₀ / (T₀.factorial : ℚ)) * (1 / (1 - y/(T₀:ℚ))) :=
            mul_le_mul_of_nonneg_left
              (geom_sum_le_inv_one_sub _ hq0 hq1 _) (htermnn T₀)
    linarith

/-! ## The rational replacement for `e` -/

/-- `Σ_{k<K} 1/k! ≤ 1631/600 = 2.71833…`, uniformly in `K`. -/
theorem sum_inv_factorial_le (K : ℕ) :
    ∑ k ∈ Finset.range K, (1:ℚ)/(k.factorial : ℚ) ≤ 1631/600 := by
  have h := sum_exp_le 1 6 (by norm_num) (by norm_num) K
  simp only [one_pow] at h
  refine h.trans ?_
  rw [show (6:ℕ) = 5+1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [show Nat.factorial 0 = 1 from rfl, show Nat.factorial 1 = 1 from rfl,
    show Nat.factorial 2 = 2 from rfl, show Nat.factorial 3 = 6 from rfl,
    show Nat.factorial 4 = 24 from rfl, show Nat.factorial 5 = 120 from rfl,
    show Nat.factorial 6 = 720 from rfl]

/-- `(1+1/n)^n ≤ 68/25 = 2.72` — the rational surrogate for `e`. -/
theorem one_add_inv_pow_le (n : ℕ) (hn : 1 ≤ n) :
    (1 + 1/(n:ℚ))^n ≤ 68/25 := by
  have hnpos : (0:ℚ) < (n:ℚ) := by exact_mod_cast hn
  have hterm : ∀ m ∈ Finset.range (n+1),
      ((1:ℚ)/(n:ℚ))^m * 1^(n-m) * (n.choose m : ℚ) ≤ 1/(m.factorial : ℚ) := by
    intro m hm
    have hNat : n.choose m * m.factorial ≤ n^m := by
      calc n.choose m * m.factorial = m.factorial * n.choose m := Nat.mul_comm _ _
        _ = n.descFactorial m := (Nat.descFactorial_eq_factorial_mul_choose n m).symm
        _ ≤ n^m := Nat.descFactorial_le_pow n m
    have hnm : (0:ℚ) < (n:ℚ)^m := by positivity
    have hmf : (0:ℚ) < (m.factorial : ℚ) := by exact_mod_cast m.factorial_pos
    rw [one_pow, mul_one, div_pow, one_pow, one_div_mul_eq_div,
        div_le_div_iff₀ hnm hmf, one_mul]
    exact_mod_cast hNat
  calc (1 + 1/(n:ℚ))^n = (1/(n:ℚ) + 1)^n := by ring_nf
    _ = ∑ m ∈ Finset.range (n+1),
          ((1:ℚ)/(n:ℚ))^m * 1^(n-m) * (n.choose m : ℚ) := add_pow _ _ n
    _ ≤ ∑ m ∈ Finset.range (n+1), (1:ℚ)/(m.factorial : ℚ) :=
        Finset.sum_le_sum hterm
    _ ≤ 1631/600 := sum_inv_factorial_le (n+1)
    _ ≤ 68/25 := by norm_num

/-- Auxiliary one-step estimate for the monotonicity of `(1+1/n)^n`.

The proof is purely rational: expand binomially and dominate the finite sum by
the geometric series with ratio `1/(n+2)`. -/
theorem one_add_inv_mul_succ_succ_pow_le_succ_inv (n : ℕ) (hn : 1 ≤ n) :
    (1 + 1 / ((n : ℚ) * (((n + 2 : ℕ) : ℚ))))^n
      ≤ 1 + 1 / (((n + 1 : ℕ) : ℚ)) := by
  let y : ℚ := 1 / ((n : ℚ) * (((n + 2 : ℕ) : ℚ)))
  have hnpos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast (by omega : 0 < n)
  have hn1pos : (0 : ℚ) < (((n + 1 : ℕ) : ℚ)) := by positivity
  have hn2pos : (0 : ℚ) < (((n + 2 : ℕ) : ℚ)) := by positivity
  have hy0 : 0 ≤ y := by
    dsimp [y]
    positivity
  have hny_eq : (n : ℚ) * y = 1 / (((n + 2 : ℕ) : ℚ)) := by
    dsimp [y]
    field_simp [hnpos.ne', hn2pos.ne']
  have hny0 : 0 ≤ (n : ℚ) * y := by
    rw [hny_eq]
    positivity
  have hny1 : (n : ℚ) * y < 1 := by
    rw [hny_eq]
    rw [div_lt_iff₀ hn2pos]
    norm_num
    exact_mod_cast (by omega : 1 < n + 2)
  have hterm : ∀ m ∈ Finset.range (n + 1),
      y^m * 1^(n-m) * (n.choose m : ℚ)
        ≤ ((n : ℚ) * y)^m := by
    intro m hm
    have hNatMul : n.choose m * m.factorial ≤ n^m := by
      calc n.choose m * m.factorial = m.factorial * n.choose m := Nat.mul_comm _ _
        _ = n.descFactorial m := (Nat.descFactorial_eq_factorial_mul_choose n m).symm
        _ ≤ n^m := Nat.descFactorial_le_pow n m
    have hNat : n.choose m ≤ n^m :=
      (Nat.le_mul_of_pos_right (n.choose m) m.factorial_pos).trans hNatMul
    have hChoose : (n.choose m : ℚ) ≤ ((n : ℚ)^m) := by
      exact_mod_cast hNat
    calc
      y^m * 1^(n-m) * (n.choose m : ℚ)
          = y^m * (n.choose m : ℚ) := by rw [one_pow, mul_one]
      _ ≤ y^m * ((n : ℚ)^m) :=
          mul_le_mul_of_nonneg_left hChoose (pow_nonneg hy0 m)
      _ = ((n : ℚ) * y)^m := by
          rw [mul_pow]
          ring
  calc
    (1 + 1 / ((n : ℚ) * (((n + 2 : ℕ) : ℚ))))^n
        = (y + 1)^n := by
            dsimp [y]
            ring
    _ = ∑ m ∈ Finset.range (n + 1),
          y^m * 1^(n-m) * (n.choose m : ℚ) := add_pow _ _ n
    _ ≤ ∑ m ∈ Finset.range (n + 1), ((n : ℚ) * y)^m :=
        Finset.sum_le_sum hterm
    _ ≤ 1 / (1 - (n : ℚ) * y) :=
        geom_sum_le_inv_one_sub ((n : ℚ) * y) hny0 hny1 (n + 1)
    _ = 1 + 1 / (((n + 1 : ℕ) : ℚ)) := by
        rw [hny_eq]
        have hden :
            1 - 1 / (((n + 2 : ℕ) : ℚ))
              = (((n + 1 : ℕ) : ℚ)) / (((n + 2 : ℕ) : ℚ)) := by
          field_simp [hn2pos.ne']
          push_cast
          ring
        rw [hden]
        field_simp [hn1pos.ne', hn2pos.ne']
        push_cast
        ring_nf

/-- The rational sequence `(1+1/n)^n` is increasing, in one-step form. -/
theorem one_add_inv_pow_mono_succ (n : ℕ) (hn : 1 ≤ n) :
    (1 + 1/(n:ℚ))^n
      ≤ (1 + 1/(((n + 1 : ℕ) : ℚ)))^(n + 1) := by
  let y : ℚ := 1 / ((n : ℚ) * (((n + 2 : ℕ) : ℚ)))
  have hnpos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast (by omega : 0 < n)
  have hn1pos : (0 : ℚ) < (((n + 1 : ℕ) : ℚ)) := by positivity
  have hn2pos : (0 : ℚ) < (((n + 2 : ℕ) : ℚ)) := by positivity
  have hratio :
      1 + 1 / (n : ℚ) =
        (1 + 1 / (((n + 1 : ℕ) : ℚ))) * (1 + y) := by
    dsimp [y]
    field_simp [hnpos.ne', hn1pos.ne', hn2pos.ne']
    push_cast
    ring_nf
  have hsmall :
      (1 + y)^n ≤ 1 + 1 / (((n + 1 : ℕ) : ℚ)) := by
    simpa [y] using one_add_inv_mul_succ_succ_pow_le_succ_inv n hn
  calc
    (1 + 1/(n:ℚ))^n
        = ((1 + 1 / (((n + 1 : ℕ) : ℚ))) * (1 + y))^n := by
            rw [hratio]
    _ = (1 + 1 / (((n + 1 : ℕ) : ℚ)))^n * (1 + y)^n := by
        rw [mul_pow]
    _ ≤ (1 + 1 / (((n + 1 : ℕ) : ℚ)))^n *
          (1 + 1 / (((n + 1 : ℕ) : ℚ))) :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = (1 + 1 / (((n + 1 : ℕ) : ℚ)))^(n + 1) := by
        rw [pow_succ]

/-- The rational sequence `(1+1/n)^n` is increasing on positive naturals. -/
theorem one_add_inv_pow_mono {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    (1 + 1/(n:ℚ))^n ≤ (1 + 1/(m:ℚ))^m := by
  induction m, hnm using Nat.le_induction with
  | base =>
      rfl
  | succ m hnm ih =>
      exact ih.trans (one_add_inv_pow_mono_succ m (le_trans hn hnm))

/-! ## The rational Stirling lower bound -/

/-- **Rational Stirling**: `(25r/68)^r ≤ r!` — i.e. `r! ≥ (r/e')^r` with
`e' = 68/25 ≥ e`. -/
theorem factorial_lb (r : ℕ) : ((25*(r:ℚ))/68)^r ≤ (r.factorial : ℚ) := by
  induction r with
  | zero => norm_num
  | succ r ih =>
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · norm_num [Nat.factorial]
      · have hrpos : (0:ℚ) < (r:ℚ) := by exact_mod_cast hr
        have hsplit2 : (25*((r:ℚ)+1)/68)^r
            = ((25*(r:ℚ))/68)^r * (1 + 1/(r:ℚ))^r := by
          rw [← mul_pow]
          congr 1
          field_simp
        have he := one_add_inv_pow_le r hr
        have hp : (0:ℚ) ≤ ((25*(r:ℚ))/68)^r := by positivity
        have ha : (0:ℚ) ≤ 25*((r:ℚ)+1)/68 := by positivity
        have hkey : (25*((r:ℚ)+1)/68)^(r+1)
            ≤ ((r:ℚ)+1) * ((25*(r:ℚ))/68)^r := by
          calc (25*((r:ℚ)+1)/68)^(r+1)
              = (25*((r:ℚ)+1)/68)^r * (25*((r:ℚ)+1)/68) := pow_succ _ r
            _ = ((25*(r:ℚ))/68)^r * (1 + 1/(r:ℚ))^r * (25*((r:ℚ)+1)/68) := by
                rw [hsplit2]
            _ ≤ ((25*(r:ℚ))/68)^r * (68/25) * (25*((r:ℚ)+1)/68) := by
                apply mul_le_mul_of_nonneg_right _ ha
                exact mul_le_mul_of_nonneg_left he hp
            _ = ((r:ℚ)+1) * ((25*(r:ℚ))/68)^r := by
                field_simp
        have hfact : (((r+1).factorial : ℕ) : ℚ) = ((r:ℚ)+1) * (r.factorial : ℚ) := by
          push_cast [Nat.factorial_succ]
          ring
        calc ((25*((r+1 : ℕ):ℚ))/68)^(r+1)
            = (25*((r:ℚ)+1)/68)^(r+1) := by push_cast; ring_nf
          _ ≤ ((r:ℚ)+1) * ((25*(r:ℚ))/68)^r := hkey
          _ ≤ ((r:ℚ)+1) * (r.factorial : ℚ) :=
              mul_le_mul_of_nonneg_left ih (by positivity)
          _ = (((r+1).factorial : ℕ) : ℚ) := hfact.symm

end Prop51
