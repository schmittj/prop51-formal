/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Exact normalization lemmas for the Prop52 mid certificate

This module connects the executable mid-range recurrence kernel in
`Prop52.Mid` to the mathematical normalized logarithmic coefficients already
proved in `Prop51.DNorm`.
-/

import Prop52.Mid
import Prop51.DNorm

namespace Prop52

/-! ## Prefix-list stability for `midD` -/

/-- Each `midDList` step appends exactly one entry. -/
theorem midDList_succ_append :
    ∀ n : Nat, ∃ x : ℚ, midDList (n + 1) = midDList n ++ [x]
  | 0 => ⟨5 / 36, rfl⟩
  | 1 => ⟨5 / 36, rfl⟩
  | _ + 2 => ⟨_, rfl⟩

/-- `midDList n` contains exactly the entries `0, ..., n`. -/
theorem midDList_length : ∀ n : Nat, (midDList n).length = n + 1
  | 0 => rfl
  | n + 1 => by
      obtain ⟨x, hx⟩ := midDList_succ_append n
      rw [hx, List.length_append, midDList_length n]
      rfl

/-- Prefix stability: entries of `midDList` do not change as the list grows. -/
theorem midDList_getD_eq (r m : Nat) (h : r ≤ m) :
    (midDList m).getD r 0 = midD r := by
  induction m with
  | zero =>
      have : r = 0 := by omega
      subst this
      rfl
  | succ m ih =>
      rcases Nat.lt_or_ge r (m + 1) with hlt | hge
      · obtain ⟨x, hx⟩ := midDList_succ_append m
        rw [hx, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by rw [midDList_length]; omega),
          ← List.getD_eq_getElem?_getD]
        exact ih (by omega)
      · have : r = m + 1 := le_antisymm h hge
        subst this
        rfl

/-- The executable `midD` recurrence is exactly Prop51's normalized
logarithmic coefficient `d`. -/
theorem midD_eq_d (r : Nat) : midD r = Prop51.d r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
      rcases r with _ | r
      · norm_num [midD, midDList, Prop51.d]
      rcases r with _ | r
      · norm_num [midD, midDList, Prop51.d_one]
      rcases r with _ | n
      · norm_num [midD, midDList, Prop51.d_two]
      rw [Prop51.d_succ_succ (n + 1)]
      have hlast :
          midD (n + 3) =
            (midDList (n + 2)).getD (n + 2) 0 +
              ((List.range (n + 1)).map fun j : Nat =>
                (midDList (n + 2)).getD (j + 1) 0 *
                  (midDList (n + 2)).getD (n + 1 - j) 0 *
                    midInvChoose (n + 2) (j + 1)).sum /
                ((n + 3 : Nat) : ℚ) := by
        unfold midD
        simp [midDList, midDList_length]
      have htop :
          (midDList (n + 2)).getD (n + 2) 0 = Prop51.d (n + 2) := by
        rw [midDList_getD_eq (n + 2) (n + 2) le_rfl]
        exact ih (n + 2) (by omega)
      have hsum_get :
          ((List.range (n + 1)).map fun j : Nat =>
                (midDList (n + 2)).getD (j + 1) 0 *
                  (midDList (n + 2)).getD (n + 1 - j) 0 *
                    midInvChoose (n + 2) (j + 1)).sum =
            ∑ j ∈ Finset.range (n + 1),
              Prop51.d (j + 1) * Prop51.d (n + 1 - j) *
                midInvChoose (n + 2) (j + 1) := by
        rw [Prop51.list_range_map_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjlt : j < n + 1 := Finset.mem_range.mp hj
        rw [midDList_getD_eq (j + 1) (n + 2) (by omega),
          midDList_getD_eq (n + 1 - j) (n + 2) (by omega),
          ih (j + 1) (by omega), ih (n + 1 - j) (by omega)]
      have hconv :
          Prop51.dconv (n + 2) =
            ∑ j ∈ Finset.range (n + 1),
              Prop51.d (j + 1) * Prop51.d (n + 1 - j) *
                midInvChoose (n + 2) (j + 1) := by
        unfold Prop51.dconv
        let f : Nat → ℚ := fun i : Nat =>
          Prop51.d i * Prop51.d (n + 2 - i) /
            (((n + 2).choose i : Nat) : ℚ)
        change (∑ i ∈ Finset.range (n + 2), f i) =
          ∑ j ∈ Finset.range (n + 1),
            Prop51.d (j + 1) * Prop51.d (n + 1 - j) *
              midInvChoose (n + 2) (j + 1)
        have hshift :
            (∑ i ∈ Finset.range (n + 2), f i) =
              (∑ j ∈ Finset.range (n + 1), f (j + 1)) + f 0 := by
          simpa [show n + 2 = n + 1 + 1 by omega] using
            (Finset.sum_range_succ' f (n + 1))
        rw [hshift]
        have hf0 : f 0 = 0 := by
          simp [f, Prop51.d_zero]
        rw [hf0, add_zero]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjlt : j < n + 1 := Finset.mem_range.mp hj
        have hsub : n + 2 - (j + 1) = n + 1 - j := by omega
        dsimp [f, midInvChoose]
        rw [hsub]
        ring
      rw [hlast, htop, hsum_get, ← hconv]

/-! ## The normalized convolution quotient -/

/-- The executable `midR` quotient rewritten with Prop51's normalized `d`. -/
theorem midR_eq_d_ratio (k r : Nat) (hk : 1 ≤ k) (hkr : k < r) :
    midR k r =
      Prop51.d k * Prop51.d (r - k) / Prop51.d r /
        (((r - 1 : Nat) : ℚ) *
          (((r - 2).choose (k - 1) : Nat) : ℚ)) := by
  simp [midR, hk, hkr, midD_eq_d]

/-- Positivity of the normalized convolution quotient in its active range. -/
theorem midR_pos (k r : Nat) (hk : 1 ≤ k) (hkr : k < r) :
    0 < midR k r := by
  rw [midR_eq_d_ratio k r hk hkr]
  have hk' : 1 ≤ r - k := by omega
  have hd_k : 0 < Prop51.d k := Prop51.d_pos k hk
  have hd_rk : 0 < Prop51.d (r - k) := Prop51.d_pos (r - k) hk'
  have hd_r : 0 < Prop51.d r := Prop51.d_pos r (by omega)
  have hchoose_nat : 0 < (r - 2).choose (k - 1) :=
    Nat.choose_pos (by omega : k - 1 ≤ r - 2)
  have hchoose : (0 : ℚ) < (((r - 2).choose (k - 1) : Nat) : ℚ) := by
    exact_mod_cast hchoose_nat
  have hrminus : (0 : ℚ) < ((r - 1 : Nat) : ℚ) := by
    exact_mod_cast (by omega : 0 < r - 1)
  exact div_pos (div_pos (mul_pos hd_k hd_rk) hd_r)
    (mul_pos hrminus hchoose)

private theorem midR_factorial_identity (k r : Nat) (hk : 1 ≤ k) (hkr : k < r) :
    (((r - 1 : Nat) : ℚ) *
        (((r - 2).choose (k - 1) : Nat) : ℚ)) *
        (((k - 1).factorial : Nat) : ℚ) *
        (((r - k - 1).factorial : Nat) : ℚ) =
      (((r - 1).factorial : Nat) : ℚ) := by
  have hchooseNat :=
    Nat.choose_mul_factorial_mul_factorial
      (n := r - 2) (k := k - 1) (by omega : k - 1 ≤ r - 2)
  have hchoose :
      (((r - 2).choose (k - 1) : Nat) : ℚ) *
          (((k - 1).factorial : Nat) : ℚ) *
          ((((r - 2) - (k - 1)).factorial : Nat) : ℚ) =
        (((r - 2).factorial : Nat) : ℚ) := by
    exact_mod_cast hchooseNat
  have hsub : (r - 2) - (k - 1) = r - k - 1 := by omega
  rw [hsub] at hchoose
  have hfact :
      (((r - 1).factorial : Nat) : ℚ) =
        ((r - 1 : Nat) : ℚ) * (((r - 2).factorial : Nat) : ℚ) := by
    have hnat : (r - 1).factorial = (r - 1) * (r - 2).factorial := by
      rw [show r - 1 = (r - 2) + 1 by omega, Nat.factorial_succ]
    exact_mod_cast hnat
  rw [hfact, ← hchoose]
  ring

/-- The executable `midR` is the coefficient quotient
`c_k c_{r-k} / c_r` in the active range. -/
theorem midR_eq_c_ratio (k r : Nat) (hk : 1 ≤ k) (hkr : k < r) :
    midR k r = Prop51.c k * Prop51.c (r - k) / Prop51.c r := by
  rw [midR_eq_d_ratio k r hk hkr]
  rw [Prop51.c_eq_d k, Prop51.c_eq_d (r - k), Prop51.c_eq_d r]
  let D : ℚ :=
    ((r - 1 : Nat) : ℚ) * (((r - 2).choose (k - 1) : Nat) : ℚ)
  let A : ℚ := (6 : ℚ)^k * (((k - 1).factorial : Nat) : ℚ)
  let B : ℚ := (6 : ℚ)^(r - k) * (((r - k - 1).factorial : Nat) : ℚ)
  let C : ℚ := (6 : ℚ)^r * (((r - 1).factorial : Nat) : ℚ)
  have hpow : (6 : ℚ)^k * (6 : ℚ)^(r - k) = (6 : ℚ)^r := by
    rw [← pow_add]
    congr 1
    omega
  have hfact := midR_factorial_identity k r hk hkr
  have hC : C = A * B * D := by
    dsimp [A, B, C, D]
    rw [← hpow, ← hfact]
    ring
  have hd_r_ne : Prop51.d r ≠ 0 :=
    (Prop51.d_pos r (by omega)).ne'
  have hA_ne : A ≠ 0 := by
    dsimp [A]
    positivity
  have hB_ne : B ≠ 0 := by
    dsimp [B]
    positivity
  have hD_ne : D ≠ 0 := by
    dsimp [D]
    have hrminus : (0 : ℚ) < ((r - 1 : Nat) : ℚ) := by
      exact_mod_cast (by omega : 0 < r - 1)
    have hchoose_nat : 0 < (r - 2).choose (k - 1) :=
      Nat.choose_pos (by omega : k - 1 ≤ r - 2)
    have hchoose : (0 : ℚ) < (((r - 2).choose (k - 1 : Nat) : Nat) : ℚ) := by
      exact_mod_cast hchoose_nat
    exact (mul_pos hrminus hchoose).ne'
  change Prop51.d k * Prop51.d (r - k) / Prop51.d r / D =
    (A * Prop51.d k) * (B * Prop51.d (r - k)) / (C * Prop51.d r)
  rw [hC]
  field_simp [hd_r_ne, hA_ne, hB_ne, hD_ne]

end Prop52
