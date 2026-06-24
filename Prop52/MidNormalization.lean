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

/-! ## The `X` recurrence and `Bq` -/

/-- Each `midXList` step appends exactly one entry. -/
theorem midXList_succ_append (N : Nat) :
    ∀ n : Nat, ∃ x : ℚ, midXList N (n + 1) = midXList N n ++ [x]
  | 0 => ⟨-1, rfl⟩
  | _ + 1 => ⟨_, rfl⟩

/-- `midXList N n` contains exactly the entries `0, ..., n`. -/
theorem midXList_length (N : Nat) :
    ∀ n : Nat, (midXList N n).length = n + 1
  | 0 => rfl
  | n + 1 => by
      obtain ⟨x, hx⟩ := midXList_succ_append N n
      rw [hx, List.length_append, midXList_length N n]
      rfl

/-- Prefix stability for `midXList`. -/
theorem midXList_getD_eq (N r m : Nat) (h : r ≤ m) :
    (midXList N m).getD r 0 = midX N r := by
  induction m with
  | zero =>
      have : r = 0 := by omega
      subst this
      rfl
  | succ m ih =>
      rcases Nat.lt_or_ge r (m + 1) with hlt | hge
      · obtain ⟨x, hx⟩ := midXList_succ_append N m
        rw [hx, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by rw [midXList_length]; omega),
          ← List.getD_eq_getElem?_getD]
        exact ih (by omega)
      · have : r = m + 1 := le_antisymm h hge
        subst this
        rfl

/-- The defining recurrence of `Bq`, in division form. -/
theorem Bq_succ (N n : Nat) :
    Prop51.Bq N (n + 1) =
      (∑ t ∈ Finset.range (n + 1),
        ((t + 1 : Nat) : ℚ) * (-(N : ℚ) * Prop51.c (t + 1)) *
          Prop51.Bq N (n - t)) / ((n + 1 : Nat) : ℚ) := by
  have h := Prop51.expCoeff_succ_mul
    (fun r => -(N : ℚ) * Prop51.c r) n
  rw [eq_div_iff (by exact_mod_cast (by omega : (0 : Nat) < n + 1).ne')]
  rw [mul_comm]
  exact h

/-- The explicit recurrence step for the normalized `X` coefficients. -/
theorem midX_succ_succ (N n : Nat) :
    midX N (n + 2) =
      -1 - ((N : ℚ) / ((n + 2 : Nat) : ℚ)) *
        ∑ j ∈ Finset.range (n + 1),
          ((j + 1 : Nat) : ℚ) * midR (j + 1) (n + 2) *
            midX N (n + 1 - j) := by
  change (midXList N (n + 2)).getD (n + 2) 0 = _
  have hlast :
      (midXList N (n + 2)).getD (n + 2) 0 =
        -1 - ((N : ℚ) / ((n + 2 : Nat) : ℚ)) *
          ∑ j ∈ Finset.range (n + 1),
            ((j + 1 : Nat) : ℚ) * midR (j + 1) (n + 2) *
              (midXList N (n + 1)).getD (n + 1 - j) 0 := by
    simp [midXList, midXList_length, Prop51.list_range_map_sum]
  rw [hlast]
  apply congrArg (fun s : ℚ => -1 - ((N : ℚ) / ((n + 2 : Nat) : ℚ)) * s)
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjlt : j < n + 1 := Finset.mem_range.mp hj
  rw [midXList_getD_eq N (n + 1 - j) (n + 1) (by omega)]

@[simp] theorem Bq_zero (N : Nat) : Prop51.Bq N 0 = 1 := by
  simp [Prop51.Bq]

/-- The normalized `X` recurrence computes `Bq N r / (N c_r)` in scaled form. -/
theorem Bq_eq_N_c_mul_midX (N r : Nat) (hr : 1 ≤ r) :
    Prop51.Bq N r = ((N : ℚ) * Prop51.c r) * midX N r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
      rcases r with _ | r
      · omega
      rcases r with _ | n
      · rw [Prop51.Bq_one]
        norm_num [midX, midXList]
      have hB := Bq_succ N (n + 1)
      rw [hB, midX_succ_succ]
      rw [Finset.sum_range_succ]
      have hpre :
          (∑ t ∈ Finset.range (n + 1),
              ((t + 1 : Nat) : ℚ) * (-(N : ℚ) * Prop51.c (t + 1)) *
                Prop51.Bq N (n + 1 - t)) =
            ∑ t ∈ Finset.range (n + 1),
              -(((N : ℚ) ^ 2) *
                (((t + 1 : Nat) : ℚ) * Prop51.c (t + 1) *
                  Prop51.c (n + 1 - t) * midX N (n + 1 - t))) := by
        refine Finset.sum_congr rfl fun t ht => ?_
        have htlt : t < n + 1 := Finset.mem_range.mp ht
        have hdeg : 1 ≤ n + 1 - t := by omega
        rw [ih (n + 1 - t) (by omega) hdeg]
        ring
      rw [hpre]
      have hmidR :
          (∑ t ∈ Finset.range (n + 1),
              -(((N : ℚ) ^ 2) *
                (((t + 1 : Nat) : ℚ) * Prop51.c (t + 1) *
                  Prop51.c (n + 1 - t) * midX N (n + 1 - t)))) =
            -((N : ℚ) ^ 2 * Prop51.c (n + 2)) *
              ∑ t ∈ Finset.range (n + 1),
                ((t + 1 : Nat) : ℚ) * midR (t + 1) (n + 2) *
                  midX N (n + 1 - t) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t ht => ?_
        have htlt : t < n + 1 := Finset.mem_range.mp ht
        have hR := midR_eq_c_ratio (t + 1) (n + 2) (by omega) (by omega)
        rw [hR]
        have hsub : n + 2 - (t + 1) = n + 1 - t := by omega
        rw [hsub]
        have hc_ne : Prop51.c (n + 2) ≠ 0 :=
          (Prop51.c_pos (n + 2) (by omega)).ne'
        field_simp [hc_ne]
      rw [hmidR]
      have hden : (((n + 2 : Nat) : ℚ)) ≠ 0 := by
        exact_mod_cast (by omega : (n + 2 : Nat) ≠ 0)
      field_simp [hden]
      rw [show n + 1 - (n + 1) = 0 by omega, Bq_zero]
      ring

/-! ## The `Y` recurrence and `Q_r(M) = [t^r] C(t/2)^M` -/

/-- The coefficient `Q_r(M) = [t^r] C(t/2)^M` from the Prop52 mid proof. -/
def midQCoeff (M r : Nat) : ℚ :=
  Prop51.expCoeff (fun s => (M : ℚ) * Prop51.c s / (2 : ℚ)^s) r

@[simp] theorem midQCoeff_zero (M : Nat) : midQCoeff M 0 = 1 := by
  simp [midQCoeff]

/-- Each `midYList` step appends exactly one entry. -/
theorem midYList_succ_append (M : Nat) :
    ∀ n : Nat, ∃ x : ℚ, midYList M (n + 1) = midYList M n ++ [x]
  | 0 => ⟨1, rfl⟩
  | _ + 1 => ⟨_, rfl⟩

/-- `midYList M n` contains exactly the entries `0, ..., n`. -/
theorem midYList_length (M : Nat) :
    ∀ n : Nat, (midYList M n).length = n + 1
  | 0 => rfl
  | n + 1 => by
      obtain ⟨x, hx⟩ := midYList_succ_append M n
      rw [hx, List.length_append, midYList_length M n]
      rfl

/-- Prefix stability for `midYList`. -/
theorem midYList_getD_eq (M r m : Nat) (h : r ≤ m) :
    (midYList M m).getD r 0 = midY M r := by
  induction m with
  | zero =>
      have : r = 0 := by omega
      subst this
      rfl
  | succ m ih =>
      rcases Nat.lt_or_ge r (m + 1) with hlt | hge
      · obtain ⟨x, hx⟩ := midYList_succ_append M m
        rw [hx, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by rw [midYList_length]; omega),
          ← List.getD_eq_getElem?_getD]
        exact ih (by omega)
      · have : r = m + 1 := le_antisymm h hge
        subst this
        rfl

/-- The defining recurrence of `Q_r(M)`, in division form. -/
theorem midQCoeff_succ (M n : Nat) :
    midQCoeff M (n + 1) =
      (∑ t ∈ Finset.range (n + 1),
        ((t + 1 : Nat) : ℚ) *
          ((M : ℚ) * Prop51.c (t + 1) / (2 : ℚ)^(t + 1)) *
          midQCoeff M (n - t)) / ((n + 1 : Nat) : ℚ) := by
  have h := Prop51.expCoeff_succ_mul
    (fun s => (M : ℚ) * Prop51.c s / (2 : ℚ)^s) n
  rw [eq_div_iff (by exact_mod_cast (by omega : (0 : Nat) < n + 1).ne')]
  rw [mul_comm]
  exact h

/-- The explicit recurrence step for the normalized `Y` coefficients. -/
theorem midY_succ_succ (M n : Nat) :
    midY M (n + 2) =
      1 + ((M : ℚ) / ((n + 2 : Nat) : ℚ)) *
        ∑ j ∈ Finset.range (n + 1),
          ((j + 1 : Nat) : ℚ) * midR (j + 1) (n + 2) *
            midY M (n + 1 - j) := by
  change (midYList M (n + 2)).getD (n + 2) 0 = _
  have hlast :
      (midYList M (n + 2)).getD (n + 2) 0 =
        1 + ((M : ℚ) / ((n + 2 : Nat) : ℚ)) *
          ∑ j ∈ Finset.range (n + 1),
            ((j + 1 : Nat) : ℚ) * midR (j + 1) (n + 2) *
              (midYList M (n + 1)).getD (n + 1 - j) 0 := by
    simp [midYList, midYList_length, Prop51.list_range_map_sum]
  rw [hlast]
  apply congrArg (fun s : ℚ => 1 + ((M : ℚ) / ((n + 2 : Nat) : ℚ)) * s)
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjlt : j < n + 1 := Finset.mem_range.mp hj
  rw [midYList_getD_eq M (n + 1 - j) (n + 1) (by omega)]

/-- The normalized `Y` recurrence computes `Q_r(M)` in scaled form. -/
theorem midQCoeff_eq_M_c_mul_midY_div_pow (M r : Nat) (hr : 1 ≤ r) :
    midQCoeff M r =
      (((M : ℚ) * Prop51.c r) / (2 : ℚ)^r) * midY M r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
      rcases r with _ | r
      · omega
      rcases r with _ | n
      · rw [midQCoeff_succ M 0]
        norm_num [midY, midYList]
      have hQ := midQCoeff_succ M (n + 1)
      rw [hQ, midY_succ_succ]
      rw [Finset.sum_range_succ]
      have hpre :
          (∑ t ∈ Finset.range (n + 1),
              ((t + 1 : Nat) : ℚ) *
                ((M : ℚ) * Prop51.c (t + 1) / (2 : ℚ)^(t + 1)) *
                midQCoeff M (n + 1 - t)) =
            ∑ t ∈ Finset.range (n + 1),
              ((M : ℚ) ^ 2) *
                (((t + 1 : Nat) : ℚ) * Prop51.c (t + 1) *
                  Prop51.c (n + 1 - t) * midY M (n + 1 - t)) /
                  (2 : ℚ)^(n + 2) := by
        refine Finset.sum_congr rfl fun t ht => ?_
        have htlt : t < n + 1 := Finset.mem_range.mp ht
        have hdeg : 1 ≤ n + 1 - t := by omega
        rw [ih (n + 1 - t) (by omega) hdeg]
        have hpow : (2 : ℚ)^(t + 1) * (2 : ℚ)^(n + 1 - t) =
            (2 : ℚ)^(n + 2) := by
          rw [← pow_add]
          congr 1
          omega
        field_simp [(by positivity : (2 : ℚ)^(t + 1) ≠ 0),
          (by positivity : (2 : ℚ)^(n + 1 - t) ≠ 0),
          (by positivity : (2 : ℚ)^(n + 2) ≠ 0)]
        rw [← hpow]
        ring
      rw [hpre]
      have hmidR :
          (∑ t ∈ Finset.range (n + 1),
              ((M : ℚ) ^ 2) *
                (((t + 1 : Nat) : ℚ) * Prop51.c (t + 1) *
                  Prop51.c (n + 1 - t) * midY M (n + 1 - t)) /
                  (2 : ℚ)^(n + 2)) =
            (((M : ℚ) ^ 2) * Prop51.c (n + 2) / (2 : ℚ)^(n + 2)) *
              ∑ t ∈ Finset.range (n + 1),
                ((t + 1 : Nat) : ℚ) * midR (t + 1) (n + 2) *
                  midY M (n + 1 - t) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t ht => ?_
        have htlt : t < n + 1 := Finset.mem_range.mp ht
        have hR := midR_eq_c_ratio (t + 1) (n + 2) (by omega) (by omega)
        rw [hR]
        have hsub : n + 2 - (t + 1) = n + 1 - t := by omega
        rw [hsub]
        have hc_ne : Prop51.c (n + 2) ≠ 0 :=
          (Prop51.c_pos (n + 2) (by omega)).ne'
        field_simp [hc_ne]
      rw [hmidR]
      have hden : (((n + 2 : Nat) : ℚ)) ≠ 0 := by
        exact_mod_cast (by omega : (n + 2 : Nat) ≠ 0)
      have hpow_ne : (2 : ℚ)^(n + 2) ≠ 0 := by positivity
      field_simp [hden, hpow_ne]
      rw [show n + 1 - (n + 1) = 0 by omega, midQCoeff_zero]
      ring

/-! ## The `S` normalization -/

/-- The `d`-ratio in the executable `S` recurrence is the coefficient ratio
`c_{r-1}/c_r`. -/
theorem midD_ratio_div_eq_c_ratio_succ_succ (n : Nat) :
    midD (n + 1) / midD (n + 2) / (6 * ((n + 1 : Nat) : ℚ)) =
      Prop51.c (n + 1) / Prop51.c (n + 2) := by
  rw [midD_eq_d (n + 1), midD_eq_d (n + 2)]
  rw [Prop51.c_eq_d (n + 1), Prop51.c_eq_d (n + 2)]
  rw [show n + 1 - 1 = n by omega, show n + 2 - 1 = n + 1 by omega]
  have hd_ne : Prop51.d (n + 2) ≠ 0 :=
    (Prop51.d_pos (n + 2) (by omega)).ne'
  have hpow_ne : (6 : ℚ)^(n + 1) ≠ 0 := by positivity
  have hfact_ne : (((n.factorial : Nat) : ℚ)) ≠ 0 := by
    exact_mod_cast n.factorial_pos.ne'
  have hsucc_ne : ((n + 1 : Nat) : ℚ) ≠ 0 := by
    exact_mod_cast (by omega : (n + 1 : Nat) ≠ 0)
  have hfact :
      (((n + 1).factorial : Nat) : ℚ) =
        ((n + 1 : Nat) : ℚ) * ((n.factorial : Nat) : ℚ) := by
    exact_mod_cast Nat.factorial_succ n
  rw [hfact]
  field_simp [hd_ne, hpow_ne, hfact_ne, hsucc_ne]
  ring

/-- Scaled form of the printed identity
`S_r(M) = 2^r R_r(M)/(M c_r)`.

The right side is the unnormalized `R_r(M)` expression from
`R_r(M) = (M + 6r - 6) Q_{r-1}(M) - Q_r(M)`, and the statement avoids
dividing by `M`.
-/
theorem midS_scaled_eq_Q (M r : Nat) (hr : 1 ≤ r) :
    (((M : ℚ) * Prop51.c r) / (2 : ℚ)^r) * midS M r =
      (((M : ℚ) + 6 * (r : ℚ) - 6) * midQCoeff M (r - 1)) -
        midQCoeff M r := by
  rcases r with _ | r
  · omega
  rcases r with _ | n
  · rw [midQCoeff_succ M 0]
    norm_num [midS, Prop51.c_one]
    ring
  rw [show n + 1 + 1 - 1 = n + 1 by omega]
  rw [midQCoeff_eq_M_c_mul_midY_div_pow M (n + 2) (by omega)]
  rw [midQCoeff_eq_M_c_mul_midY_div_pow M (n + 1) (by omega)]
  change (((M : ℚ) * Prop51.c (n + 2)) / (2 : ℚ)^(n + 2)) *
      (2 * ((M : ℚ) + 6 * ((n + 2 : Nat) : ℚ) - 6) *
          (midD (n + 1) / midD (n + 2) /
            (6 * ((n + 1 : Nat) : ℚ))) * midY M (n + 1) -
        midY M (n + 2)) =
    ((M : ℚ) + 6 * ((n + 2 : Nat) : ℚ) - 6) *
        (((M : ℚ) * Prop51.c (n + 1)) / (2 : ℚ)^(n + 1) *
          midY M (n + 1)) -
      ((M : ℚ) * Prop51.c (n + 2)) / (2 : ℚ)^(n + 2) *
        midY M (n + 2)
  rw [midD_ratio_div_eq_c_ratio_succ_succ n]
  have hc_ne : Prop51.c (n + 2) ≠ 0 :=
    (Prop51.c_pos (n + 2) (by omega)).ne'
  have hpow_succ :
      (2 : ℚ)^(n + 2) = (2 : ℚ) * (2 : ℚ)^(n + 1) := by
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
    ring
  rw [hpow_succ]
  field_simp [hc_ne, (by positivity : (2 : ℚ)^(n + 1) ≠ 0)]

end Prop52
