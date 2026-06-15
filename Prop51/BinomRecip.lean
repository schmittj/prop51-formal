/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Reciprocal binomial sums (paper Lemma 2.2)

The two elementary bounds

* `Σ_{i=1}^{n-1} 1/C(n,i) ≤ 4/n` for `n ≥ 2`, and
* `Σ_{i=2}^{n-2} 1/C(n,i) ≤ 10/(n(n-1))` for `n ≥ 4`.

They drive the increment control of the `d`-normalization
(`Prop51/DNorm.lean`), the ordered-composition estimate
(`Prop51/Composition.lean`), and the two-block estimates of the effective
sign-lock (Layer C).  Everything is exact rational arithmetic: for `n ≥ 6`
the four boundary terms are evaluated exactly and the `n - 5` middle terms
are each bounded by `1/C(n,3)`.
-/

import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases

namespace Prop51

/-! ## Monotonicity of binomial coefficients up to the middle -/

/-- `C(n,·)` is monotone below the middle: `a ≤ b`, `2b ≤ n` ⟹
`C(n,a) ≤ C(n,b)`. -/
theorem choose_mono_of_le_half {n a b : ℕ} (hab : a ≤ b) (hb : 2*b ≤ n) :
    n.choose a ≤ n.choose b := by
  revert hb
  induction b, hab using Nat.le_induction with
  | base => exact fun _ => le_rfl
  | succ j hj ih =>
      intro hb
      exact (ih (by omega)).trans
        (Nat.choose_le_succ_of_lt_half_left (by omega))

/-- Every middle binomial dominates `C(n,3)`: for `3 ≤ i ≤ n-3`,
`C(n,3) ≤ C(n,i)`. -/
theorem choose_three_le {n i : ℕ} (h3 : 3 ≤ i) (h3' : i + 3 ≤ n) :
    n.choose 3 ≤ n.choose i := by
  rcases Nat.lt_or_ge n (2*i) with h | h
  · have hi : i ≤ n := by omega
    calc n.choose 3 ≤ n.choose (n - i) :=
          choose_mono_of_le_half (by omega) (by omega)
      _ = n.choose i := Nat.choose_symm hi
  · exact choose_mono_of_le_half h3 h

/-- Every deeper middle binomial dominates `C(n,4)`: for `4 ≤ i ≤ n-4`,
`C(n,4) ≤ C(n,i)`. -/
theorem choose_four_le {n i : ℕ} (h4 : 4 ≤ i) (h4' : i + 4 ≤ n) :
    n.choose 4 ≤ n.choose i := by
  rcases Nat.lt_or_ge n (2*i) with h | h
  · have hi : i ≤ n := by omega
    calc n.choose 4 ≤ n.choose (n - i) :=
          choose_mono_of_le_half (by omega) (by omega)
      _ = n.choose i := Nat.choose_symm hi
  · exact choose_mono_of_le_half h4 h

/-! ## Exact values of the boundary binomials (in the regime `n = m+6`) -/

private theorem cast_factorial_six (m : ℕ) :
    ((m+6).factorial : ℚ)
      = ((m:ℚ)+6) * ((m:ℚ)+5) * ((m:ℚ)+4) * ((m+3).factorial : ℚ) := by
  rw [show m+6 = (m+3)+1+1+1 by omega, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ]
  push_cast
  ring

private theorem choose_two_val (m : ℕ) :
    (((m+6).choose 2 : ℕ) : ℚ) = ((m:ℚ)+6) * ((m:ℚ)+5) / 2 := by
  rw [Nat.cast_choose_two]
  push_cast
  ring

private theorem choose_three_val (m : ℕ) :
    (((m+6).choose 3 : ℕ) : ℚ) = ((m:ℚ)+6) * ((m:ℚ)+5) * ((m:ℚ)+4) / 6 := by
  have h := Nat.choose_mul_factorial_mul_factorial (show 3 ≤ m+6 by omega)
  rw [show m+6-3 = m+3 by omega, show Nat.factorial 3 = 6 from rfl] at h
  have hq : (((m+6).choose 3 : ℕ) : ℚ) * 6 * ((m+3).factorial : ℚ)
      = ((m+6).factorial : ℚ) := by exact_mod_cast h
  rw [cast_factorial_six] at hq
  have hf : ((m+3).factorial : ℚ) ≠ 0 := by
    exact_mod_cast (m+3).factorial_pos.ne'
  have h6 : (((m+6).choose 3 : ℕ) : ℚ) * 6
      = ((m:ℚ)+6) * ((m:ℚ)+5) * ((m:ℚ)+4) := mul_right_cancel₀ hf hq
  linarith

private theorem choose_top_two_val (m : ℕ) :
    (((m+6).choose (m+4) : ℕ) : ℚ) = ((m:ℚ)+6) * ((m:ℚ)+5) / 2 := by
  rw [show m+4 = m+6-2 by omega, Nat.choose_symm (by omega)]
  exact choose_two_val m

private theorem choose_top_one_val (m : ℕ) :
    (((m+6).choose (m+5) : ℕ) : ℚ) = (m:ℚ)+6 := by
  rw [show m+5 = m+6-1 by omega, Nat.choose_symm (by omega),
      Nat.choose_one_right]
  push_cast
  ring

/-! ## The middle block `3 ≤ i ≤ n-3` -/

private theorem middle_sum_le (m : ℕ) :
    ∑ i ∈ Finset.Ico 3 (m+4), (1:ℚ)/((m+6).choose i)
      ≤ ((m:ℚ)+1) * 6 / (((m:ℚ)+6) * ((m:ℚ)+5) * ((m:ℚ)+4)) := by
  have hb : ∀ i ∈ Finset.Ico 3 (m+4),
      (1:ℚ)/((m+6).choose i) ≤ (1:ℚ)/((m+6).choose 3) := by
    intro i hi
    obtain ⟨h3, h4⟩ := Finset.mem_Ico.mp hi
    gcongr
    · exact_mod_cast Nat.choose_pos (show 3 ≤ m+6 by omega)
    · exact_mod_cast choose_three_le h3 (by omega)
  calc ∑ i ∈ Finset.Ico 3 (m+4), (1:ℚ)/((m+6).choose i)
      ≤ (Finset.Ico 3 (m+4)).card • ((1:ℚ)/((m+6).choose 3)) :=
        Finset.sum_le_card_nsmul _ _ _ hb
    _ = ((m:ℚ)+1) * (1/((m+6).choose 3)) := by
        rw [Nat.card_Ico, show m+4-3 = m+1 by omega, nsmul_eq_mul]
        push_cast
        ring
    _ = ((m:ℚ)+1) * 6 / (((m:ℚ)+6) * ((m:ℚ)+5) * ((m:ℚ)+4)) := by
        rw [choose_three_val, one_div_div]
        ring

/-! ## The two reciprocal-binomial bounds -/

/-- **Paper Lemma 2.2, first bound**: `Σ_{i=1}^{n-1} 1/C(n,i) ≤ 4/n` for
`n ≥ 2`. -/
theorem sum_choose_recip_le (n : ℕ) (hn : 2 ≤ n) :
    ∑ i ∈ Finset.Ico 1 n, (1:ℚ)/(n.choose i) ≤ 4 / (n:ℚ) := by
  rcases Nat.lt_or_ge n 6 with h6 | h6
  · interval_cases n
    · rw [show Finset.Ico 1 2 = {1} by decide]
      norm_num [show Nat.choose 2 1 = 2 from rfl]
    · rw [show Finset.Ico 1 3 = {1, 2} by decide,
          Finset.sum_pair (by norm_num)]
      norm_num [show Nat.choose 3 1 = 3 from rfl,
        show Nat.choose 3 2 = 3 from rfl]
    · rw [show Finset.Ico 1 4 = {1, 2, 3} by decide,
          Finset.sum_insert (by decide), Finset.sum_pair (by norm_num)]
      norm_num [show Nat.choose 4 1 = 4 from rfl,
        show Nat.choose 4 2 = 6 from rfl, show Nat.choose 4 3 = 4 from rfl]
    · rw [show Finset.Ico 1 5 = {1, 2, 3, 4} by decide,
          Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_pair (by norm_num)]
      norm_num [show Nat.choose 5 1 = 5 from rfl,
        show Nat.choose 5 2 = 10 from rfl, show Nat.choose 5 3 = 10 from rfl,
        show Nat.choose 5 4 = 5 from rfl]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m+6 := ⟨n-6, by omega⟩
    have split1 : (∑ i ∈ Finset.Ico 1 3, (1:ℚ)/((m+6).choose i))
          + ∑ i ∈ Finset.Ico 3 (m+6), (1:ℚ)/((m+6).choose i)
        = ∑ i ∈ Finset.Ico 1 (m+6), (1:ℚ)/((m+6).choose i) :=
      Finset.sum_Ico_consecutive _ (by omega) (by omega)
    have split2 : (∑ i ∈ Finset.Ico 3 (m+4), (1:ℚ)/((m+6).choose i))
          + ∑ i ∈ Finset.Ico (m+4) (m+6), (1:ℚ)/((m+6).choose i)
        = ∑ i ∈ Finset.Ico 3 (m+6), (1:ℚ)/((m+6).choose i) :=
      Finset.sum_Ico_consecutive _ (by omega) (by omega)
    have e1 : Finset.Ico 1 3 = ({1, 2} : Finset ℕ) := by decide
    have e2 : Finset.Ico (m+4) (m+6) = ({m+4, m+5} : Finset ℕ) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [← split1, ← split2, e1, e2, Finset.sum_pair (by norm_num),
        Finset.sum_pair (show m+4 ≠ m+5 by omega)]
    have v1 : (1:ℚ)/(((m+6).choose 1 : ℕ):ℚ) = 1/((m:ℚ)+6) := by
      rw [Nat.choose_one_right]
      push_cast
      ring
    have v2 : (1:ℚ)/(((m+6).choose 2 : ℕ):ℚ)
        = 2/(((m:ℚ)+6) * ((m:ℚ)+5)) := by
      rw [choose_two_val, one_div_div]
    have v4 : (1:ℚ)/(((m+6).choose (m+4) : ℕ):ℚ)
        = 2/(((m:ℚ)+6) * ((m:ℚ)+5)) := by
      rw [choose_top_two_val, one_div_div]
    have v5 : (1:ℚ)/(((m+6).choose (m+5) : ℕ):ℚ) = 1/((m:ℚ)+6) := by
      rw [choose_top_one_val]
    simp only [v1, v2, v4, v5]
    have hmid := middle_sum_le m
    have hx0 : (0:ℚ) ≤ (m:ℚ) := Nat.cast_nonneg m
    have hc6 : ((m:ℚ)+6) ≠ 0 := by positivity
    have hc5 : ((m:ℚ)+5) ≠ 0 := by positivity
    have hc4 : ((m:ℚ)+4) ≠ 0 := by positivity
    have hcast : ((m+6 : ℕ) : ℚ) = (m:ℚ) + 6 := by push_cast; ring
    rw [hcast]
    have key : 4/((m:ℚ)+6)
        - (1/((m:ℚ)+6) + 2/(((m:ℚ)+6)*((m:ℚ)+5))
            + (((m:ℚ)+1) * 6 / (((m:ℚ)+6)*((m:ℚ)+5)*((m:ℚ)+4))
              + (2/(((m:ℚ)+6)*((m:ℚ)+5)) + 1/((m:ℚ)+6))))
        = (2*(m:ℚ)^2 + 8*(m:ℚ) + 18)
            / (((m:ℚ)+6)*((m:ℚ)+5)*((m:ℚ)+4)) := by
      field_simp [hc6, hc5, hc4]
      ring
    have hpos : (0:ℚ) ≤ (2*(m:ℚ)^2 + 8*(m:ℚ) + 18)
        / (((m:ℚ)+6)*((m:ℚ)+5)*((m:ℚ)+4)) := by
      have h1 : (0:ℚ) ≤ 2*(m:ℚ)^2 + 8*(m:ℚ) + 18 := by positivity
      have h2 : (0:ℚ) < ((m:ℚ)+6)*((m:ℚ)+5)*((m:ℚ)+4) := by positivity
      exact div_nonneg h1 h2.le
    linarith [hmid]

/-- **Paper Lemma 2.2, second bound**: `Σ_{i=2}^{n-2} 1/C(n,i) ≤ 10/(n(n-1))`
for `n ≥ 4` (stated with `Ico 2 (n-1) = Icc 2 (n-2)`). -/
theorem sum_choose_recip_inner_le (n : ℕ) (hn : 4 ≤ n) :
    ∑ i ∈ Finset.Ico 2 (n-1), (1:ℚ)/(n.choose i)
      ≤ 10 / ((n:ℚ) * ((n:ℚ)-1)) := by
  rcases Nat.lt_or_ge n 6 with h6 | h6
  · interval_cases n
    · rw [show Finset.Ico 2 (4-1) = {2} by decide]
      norm_num [show Nat.choose 4 2 = 6 from rfl]
    · rw [show Finset.Ico 2 (5-1) = {2, 3} by decide,
          Finset.sum_pair (by norm_num)]
      norm_num [show Nat.choose 5 2 = 10 from rfl,
        show Nat.choose 5 3 = 10 from rfl]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m+6 := ⟨n-6, by omega⟩
    rw [show m+6-1 = m+5 by omega]
    have split2 : (∑ i ∈ Finset.Ico 2 3, (1:ℚ)/((m+6).choose i))
          + ∑ i ∈ Finset.Ico 3 (m+5), (1:ℚ)/((m+6).choose i)
        = ∑ i ∈ Finset.Ico 2 (m+5), (1:ℚ)/((m+6).choose i) :=
      Finset.sum_Ico_consecutive _ (by omega) (by omega)
    have split3 : (∑ i ∈ Finset.Ico 3 (m+4), (1:ℚ)/((m+6).choose i))
          + ∑ i ∈ Finset.Ico (m+4) (m+5), (1:ℚ)/((m+6).choose i)
        = ∑ i ∈ Finset.Ico 3 (m+5), (1:ℚ)/((m+6).choose i) :=
      Finset.sum_Ico_consecutive _ (by omega) (by omega)
    have e1 : Finset.Ico 2 3 = ({2} : Finset ℕ) := by decide
    have e2 : Finset.Ico (m+4) (m+5) = ({m+4} : Finset ℕ) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_singleton]
      omega
    rw [← split2, ← split3, e1, e2, Finset.sum_singleton,
        Finset.sum_singleton]
    have v2 : (1:ℚ)/(((m+6).choose 2 : ℕ):ℚ)
        = 2/(((m:ℚ)+6) * ((m:ℚ)+5)) := by
      rw [choose_two_val, one_div_div]
    have v4 : (1:ℚ)/(((m+6).choose (m+4) : ℕ):ℚ)
        = 2/(((m:ℚ)+6) * ((m:ℚ)+5)) := by
      rw [choose_top_two_val, one_div_div]
    simp only [v2, v4]
    have hmid := middle_sum_le m
    have hx0 : (0:ℚ) ≤ (m:ℚ) := Nat.cast_nonneg m
    have hc6 : ((m:ℚ)+6) ≠ 0 := by positivity
    have hc5 : ((m:ℚ)+5) ≠ 0 := by positivity
    have hc4 : ((m:ℚ)+4) ≠ 0 := by positivity
    have hcast : ((m+6 : ℕ) : ℚ) = (m:ℚ) + 6 := by push_cast; ring
    rw [hcast]
    have key : 10/(((m:ℚ)+6)*(((m:ℚ)+6)-1))
        - (2/(((m:ℚ)+6)*((m:ℚ)+5))
            + (((m:ℚ)+1) * 6 / (((m:ℚ)+6)*((m:ℚ)+5)*((m:ℚ)+4))
              + 2/(((m:ℚ)+6)*((m:ℚ)+5))))
        = 18 / (((m:ℚ)+6)*((m:ℚ)+5)*((m:ℚ)+4)) := by
      rw [show ((m:ℚ)+6)-1 = (m:ℚ)+5 by ring]
      field_simp
      ring
    have hpos : (0:ℚ) ≤ 18 / (((m:ℚ)+6)*((m:ℚ)+5)*((m:ℚ)+4)) := by
      have h2 : (0:ℚ) < ((m:ℚ)+6)*((m:ℚ)+5)*((m:ℚ)+4) := by positivity
      exact div_nonneg (by norm_num) h2.le
    linarith [hmid]

/-! ## A sharper large-`n` inner bound -/

private theorem cast_factorial_large_three (m : ℕ) :
    ((m+239).factorial : ℚ)
      = ((m:ℚ)+239) * ((m:ℚ)+238) * ((m:ℚ)+237)
          * ((m+236).factorial : ℚ) := by
  rw [show m+239 = (m+236)+1+1+1 by omega, Nat.factorial_succ,
    Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  ring

private theorem cast_factorial_large_four (m : ℕ) :
    ((m+239).factorial : ℚ)
      = ((m:ℚ)+239) * ((m:ℚ)+238) * ((m:ℚ)+237) * ((m:ℚ)+236)
          * ((m+235).factorial : ℚ) := by
  rw [show m+239 = (m+235)+1+1+1+1 by omega, Nat.factorial_succ,
    Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  ring

private theorem choose_two_val_large (m : ℕ) :
    (((m+239).choose 2 : ℕ) : ℚ)
      = ((m:ℚ)+239) * ((m:ℚ)+238) / 2 := by
  rw [Nat.cast_choose_two]
  push_cast
  ring

private theorem choose_three_val_large (m : ℕ) :
    (((m+239).choose 3 : ℕ) : ℚ)
      = ((m:ℚ)+239) * ((m:ℚ)+238) * ((m:ℚ)+237) / 6 := by
  have h := Nat.choose_mul_factorial_mul_factorial (show 3 ≤ m+239 by omega)
  rw [show m+239-3 = m+236 by omega, show Nat.factorial 3 = 6 from rfl] at h
  have hq : (((m+239).choose 3 : ℕ) : ℚ) * 6 * ((m+236).factorial : ℚ)
      = ((m+239).factorial : ℚ) := by exact_mod_cast h
  rw [cast_factorial_large_three] at hq
  have hf : ((m+236).factorial : ℚ) ≠ 0 := by
    exact_mod_cast (m+236).factorial_pos.ne'
  have h6 : (((m+239).choose 3 : ℕ) : ℚ) * 6
      = ((m:ℚ)+239) * ((m:ℚ)+238) * ((m:ℚ)+237) :=
    mul_right_cancel₀ hf hq
  linarith

private theorem choose_four_val_large (m : ℕ) :
    (((m+239).choose 4 : ℕ) : ℚ)
      = ((m:ℚ)+239) * ((m:ℚ)+238) * ((m:ℚ)+237) * ((m:ℚ)+236) / 24 := by
  have h := Nat.choose_mul_factorial_mul_factorial (show 4 ≤ m+239 by omega)
  rw [show m+239-4 = m+235 by omega, show Nat.factorial 4 = 24 from rfl] at h
  have hq : (((m+239).choose 4 : ℕ) : ℚ) * 24 * ((m+235).factorial : ℚ)
      = ((m+239).factorial : ℚ) := by exact_mod_cast h
  rw [cast_factorial_large_four] at hq
  have hf : ((m+235).factorial : ℚ) ≠ 0 := by
    exact_mod_cast (m+235).factorial_pos.ne'
  have h24 : (((m+239).choose 4 : ℕ) : ℚ) * 24
      = ((m:ℚ)+239) * ((m:ℚ)+238) * ((m:ℚ)+237) * ((m:ℚ)+236) :=
    mul_right_cancel₀ hf hq
  linarith

private theorem choose_top_three_val_large (m : ℕ) :
    (((m+239).choose (m+236) : ℕ) : ℚ)
      = ((m:ℚ)+239) * ((m:ℚ)+238) * ((m:ℚ)+237) / 6 := by
  rw [show m+236 = m+239-3 by omega, Nat.choose_symm (by omega)]
  exact choose_three_val_large m

private theorem choose_top_two_val_large (m : ℕ) :
    (((m+239).choose (m+237) : ℕ) : ℚ)
      = ((m:ℚ)+239) * ((m:ℚ)+238) / 2 := by
  rw [show m+237 = m+239-2 by omega, Nat.choose_symm (by omega)]
  exact choose_two_val_large m

private theorem middle_sum_le_large (m : ℕ) :
    ∑ i ∈ Finset.Ico 4 (m+236), (1:ℚ)/((m+239).choose i)
      ≤ ((m:ℚ)+232) * 24
          / (((m:ℚ)+239) * ((m:ℚ)+238) * ((m:ℚ)+237) * ((m:ℚ)+236)) := by
  have hb : ∀ i ∈ Finset.Ico 4 (m+236),
      (1:ℚ)/((m+239).choose i) ≤ (1:ℚ)/((m+239).choose 4) := by
    intro i hi
    obtain ⟨h4, htop⟩ := Finset.mem_Ico.mp hi
    have hpos : (0:ℚ) < (((m+239).choose 4 : ℕ) : ℚ) := by
      exact_mod_cast Nat.choose_pos (show 4 ≤ m+239 by omega)
    have hle : (((m+239).choose 4 : ℕ) : ℚ)
        ≤ (((m+239).choose i : ℕ) : ℚ) := by
      exact_mod_cast choose_four_le h4 (by omega)
    exact div_le_div_of_nonneg_left (by norm_num : (0:ℚ) ≤ 1) hpos hle
  calc ∑ i ∈ Finset.Ico 4 (m+236), (1:ℚ)/((m+239).choose i)
      ≤ (Finset.Ico 4 (m+236)).card • ((1:ℚ)/((m+239).choose 4)) :=
        Finset.sum_le_card_nsmul _ _ _ hb
    _ = ((m:ℚ)+232) * (1/((m+239).choose 4)) := by
        rw [Nat.card_Ico, show m+236-4 = m+232 by omega, nsmul_eq_mul]
        push_cast
        ring
    _ = ((m:ℚ)+232) * 24
        / (((m:ℚ)+239) * ((m:ℚ)+238) * ((m:ℚ)+237) * ((m:ℚ)+236)) := by
        rw [choose_four_val_large, one_div_div]
        ring

/-- Sharpened large-`n` form of the inner reciprocal-binomial bound.  For the
sign-lock two-block estimate the relevant `n` is at least `239`, and peeling
the `2,3,n-3,n-2` boundary terms leaves a middle block controlled by
`C(n,4)`. -/
theorem sum_choose_recip_inner_le_large (n : ℕ) (hn : 239 ≤ n) :
    ∑ i ∈ Finset.Ico 2 (n-1), (1:ℚ)/(n.choose i)
      ≤ 5 / ((n:ℚ) * ((n:ℚ)-1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m+239 := ⟨n-239, by omega⟩
  rw [show m+239-1 = m+238 by omega]
  have split1 : (∑ i ∈ Finset.Ico 2 4, (1:ℚ)/((m+239).choose i))
        + ∑ i ∈ Finset.Ico 4 (m+238), (1:ℚ)/((m+239).choose i)
      = ∑ i ∈ Finset.Ico 2 (m+238), (1:ℚ)/((m+239).choose i) :=
    Finset.sum_Ico_consecutive _ (by omega) (by omega)
  have split2 : (∑ i ∈ Finset.Ico 4 (m+236), (1:ℚ)/((m+239).choose i))
        + ∑ i ∈ Finset.Ico (m+236) (m+238), (1:ℚ)/((m+239).choose i)
      = ∑ i ∈ Finset.Ico 4 (m+238), (1:ℚ)/((m+239).choose i) :=
    Finset.sum_Ico_consecutive _ (by omega) (by omega)
  have e1 : Finset.Ico 2 4 = ({2, 3} : Finset ℕ) := by decide
  have e2 : Finset.Ico (m+236) (m+238) = ({m+236, m+237} : Finset ℕ) := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [← split1, ← split2, e1, e2, Finset.sum_pair (by norm_num),
    Finset.sum_pair (show m+236 ≠ m+237 by omega)]
  have v2 : (1:ℚ)/(((m+239).choose 2 : ℕ):ℚ)
      = 2/(((m:ℚ)+239) * ((m:ℚ)+238)) := by
    rw [choose_two_val_large, one_div_div]
  have v3 : (1:ℚ)/(((m+239).choose 3 : ℕ):ℚ)
      = 6/(((m:ℚ)+239) * ((m:ℚ)+238) * ((m:ℚ)+237)) := by
    rw [choose_three_val_large, one_div_div]
  have vt3 : (1:ℚ)/(((m+239).choose (m+236) : ℕ):ℚ)
      = 6/(((m:ℚ)+239) * ((m:ℚ)+238) * ((m:ℚ)+237)) := by
    rw [choose_top_three_val_large, one_div_div]
  have vt2 : (1:ℚ)/(((m+239).choose (m+237) : ℕ):ℚ)
      = 2/(((m:ℚ)+239) * ((m:ℚ)+238)) := by
    rw [choose_top_two_val_large, one_div_div]
  simp only [v2, v3, vt3, vt2]
  have hmid := middle_sum_le_large m
  have hc239 : ((m:ℚ)+239) ≠ 0 := by positivity
  have hc238 : ((m:ℚ)+238) ≠ 0 := by positivity
  have hc237 : ((m:ℚ)+237) ≠ 0 := by positivity
  have hc236 : ((m:ℚ)+236) ≠ 0 := by positivity
  have hcast : ((m+239 : ℕ) : ℚ) = (m:ℚ) + 239 := by push_cast; ring
  rw [hcast]
  have key : 5/(((m:ℚ)+239)*(((m:ℚ)+239)-1))
      - (2/(((m:ℚ)+239)*((m:ℚ)+238))
          + 6/(((m:ℚ)+239)*((m:ℚ)+238)*((m:ℚ)+237))
          + (((m:ℚ)+232) * 24
              / (((m:ℚ)+239)*((m:ℚ)+238)*((m:ℚ)+237)*((m:ℚ)+236)))
          + (6/(((m:ℚ)+239)*((m:ℚ)+238)*((m:ℚ)+237))
              + 2/(((m:ℚ)+239)*((m:ℚ)+238))))
      = ((m:ℚ)^2 + 437*(m:ℚ) + 47532)
          / (((m:ℚ)+239)*((m:ℚ)+238)*((m:ℚ)+237)*((m:ℚ)+236)) := by
    rw [show ((m:ℚ)+239)-1 = (m:ℚ)+238 by ring]
    field_simp [hc239, hc238, hc237, hc236]
    ring
  have hpos : (0:ℚ) ≤ ((m:ℚ)^2 + 437*(m:ℚ) + 47532)
      / (((m:ℚ)+239)*((m:ℚ)+238)*((m:ℚ)+237)*((m:ℚ)+236)) := by
    have hnum : (0:ℚ) ≤ (m:ℚ)^2 + 437*(m:ℚ) + 47532 := by positivity
    have hden : (0:ℚ) < ((m:ℚ)+239)*((m:ℚ)+238)*((m:ℚ)+237)*((m:ℚ)+236) := by
      positivity
    exact div_nonneg hnum hden.le
  linarith [hmid]

end Prop51
