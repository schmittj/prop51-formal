/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Positive-part saddle setup (paper §6)

This file records the integer bookkeeping for the repaired positive-part
estimate.  The analytic saddle majorants and the rational certificate are
added later; the goal here is to make the corrected two-edge rectangle scan a
Lean interface rather than an informal convention in the Python script.
-/

import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.BigOperators
import Prop51.SignLock

namespace Prop51

/-! ## Rectangle and square-root cutoffs -/

/-- Lower edge `6a-7` of the post-certificate rectangle. -/
def posNlo (a : Nat) : Nat := 6*a - 7

/-- Upper edge `12a-8` of the post-certificate rectangle. -/
def posNhi (a : Nat) : Nat := 12*a - 8

/-- The positive-part rectangle `6a-7 ≤ N ≤ 12a-8`. -/
def positiveRectangle (a N : Nat) : Prop := posNlo a ≤ N ∧ N ≤ posNhi a

/-- Exact integer ceiling of `sqrt n`.

The formula `sqrt (n-1)+1` for `n>0` avoids `Real.ceil`; it is exactly
`⌈√n⌉` because `Nat.sqrt` is the floor square root. -/
def ceilSqrt (n : Nat) : Nat :=
  if n = 0 then 0 else Nat.sqrt (n-1) + 1

@[simp] theorem ceilSqrt_zero : ceilSqrt 0 = 0 := by
  simp [ceilSqrt]

@[simp] theorem ceilSqrt_succ (n : Nat) :
    ceilSqrt (n+1) = Nat.sqrt n + 1 := by
  simp [ceilSqrt]

/-- Defining upper property of `ceilSqrt`: its square is at least `n`. -/
theorem le_ceilSqrt_sq (n : Nat) : n ≤ ceilSqrt n * ceilSqrt n := by
  rcases n with _ | n
  · simp
  · simpa [ceilSqrt] using Nat.succ_le_succ_sqrt n

/-- Minimality of `ceilSqrt` among natural numbers whose square is at least
`n`. -/
theorem ceilSqrt_le_of_le_sq {n k : Nat} (h : n ≤ k*k) :
    ceilSqrt n ≤ k := by
  rcases n with _ | n
  · simp
  · have hnlt : n < k*k := by omega
    have hsqrt : Nat.sqrt n < k := (Nat.sqrt_lt).2 hnlt
    simpa [ceilSqrt] using hsqrt

/-- Characterization of the exact integer ceiling square root. -/
theorem ceilSqrt_le_iff_le_sq {n k : Nat} :
    ceilSqrt n ≤ k ↔ n ≤ k*k := by
  constructor
  · intro h
    exact (le_ceilSqrt_sq n).trans (Nat.mul_le_mul h h)
  · exact ceilSqrt_le_of_le_sq

/-- Monotonicity of the integer ceiling square root. -/
theorem ceilSqrt_mono {m n : Nat} (h : m ≤ n) :
    ceilSqrt m ≤ ceilSqrt n :=
  ceilSqrt_le_of_le_sq (h.trans (le_ceilSqrt_sq n))

theorem lt_ceilSqrt_of_sq_lt {n k : Nat} (h : k*k < n) :
    k < ceilSqrt n := by
  by_contra hnot
  have hle : ceilSqrt n ≤ k := Nat.le_of_not_gt hnot
  have hn : n ≤ k*k := (ceilSqrt_le_iff_le_sq).mp hle
  omega

theorem one_le_ceilSqrt_of_pos {n : Nat} (hn : 0 < n) :
    1 ≤ ceilSqrt n := by
  rcases n with _ | n
  · omega
  · simp [ceilSqrt]

/-- The largest cutoff at which the small-`k` saddle regime can occur anywhere
in the rectangle.  This is the corrected `ceil(sqrt(12a-8))` edge from
`scripts/positive_saddle_scan.py`. -/
def posSmallCutoff (a : Nat) : Nat := ceilSqrt (posNhi a)

/-- The smallest cutoff at which the tempered saddle regime can occur anywhere
in the rectangle.  This is the corrected `ceil(sqrt(6a-7))` edge from
`scripts/positive_saddle_scan.py`. -/
def posTemperedCutoff (a : Nat) : Nat := ceilSqrt (posNlo a)

/-- The possible values of `ceilSqrt N` as `N` ranges over the positive
rectangle for a fixed `a`. -/
def positiveSmallCeilRange (a : Nat) : Finset Nat :=
  Finset.Icc (posTemperedCutoff a) (posSmallCutoff a)

/-- The first natural number in the plateau with ceiling square root `s`. -/
def ceilSqrtPlateauLo (s : Nat) : Nat :=
  if s = 0 then 0 else (s - 1)^2 + 1

/-- The first `N` in the positive rectangle with a given ceiling-square-root
plateau.  Finite checks at this anchor imply the same small-edge exponential
gap throughout that plateau, because the right side is linear in `N`. -/
def positiveSmallEdgeAnchor (a s : Nat) : Nat :=
  max (posNlo a) (ceilSqrtPlateauLo s)

theorem posNlo_le_posNhi {a : Nat} (ha : 1 ≤ a) :
    posNlo a ≤ posNhi a := by
  unfold posNlo posNhi
  omega

theorem posNlo_pos {a : Nat} (ha : 2 ≤ a) :
    0 < posNlo a := by
  unfold posNlo
  omega

theorem posNhi_pos {a : Nat} (ha : 1 ≤ a) :
    0 < posNhi a := by
  unfold posNhi
  omega

theorem positiveRectangle_nonempty {a : Nat} (ha : 1 ≤ a) :
    positiveRectangle a (posNlo a) := by
  exact ⟨le_rfl, posNlo_le_posNhi ha⟩

theorem positiveRectangle_N_pos {a N : Nat} (ha : 2 ≤ a)
    (hrect : positiveRectangle a N) :
    1 ≤ N := by
  have hlo : 0 < posNlo a := posNlo_pos ha
  exact Nat.succ_le_of_lt (hlo.trans_le hrect.1)

/-- If a `k` can lie in the small-`k` regime for some `N` in the rectangle,
then it is below the upper-edge cutoff. -/
theorem smallRegime_le_upper_edge {a N k : Nat}
    (hN : N ≤ posNhi a) (hk : k ≤ ceilSqrt N) :
    k ≤ posSmallCutoff a := by
  exact hk.trans (ceilSqrt_mono hN)

/-- If a `k` can lie in the tempered regime for some `N` in the rectangle,
then it is above the lower-edge cutoff. -/
theorem lower_edge_lt_of_temperedRegime {a N k : Nat}
    (hN : posNlo a ≤ N) (hk : ceilSqrt N < k) :
    posTemperedCutoff a < k := by
  exact (ceilSqrt_mono hN).trans_lt hk

theorem smallRegime_of_rectangle {a N k : Nat}
    (hrect : positiveRectangle a N) (hk : k ≤ ceilSqrt N) :
    k ≤ posSmallCutoff a :=
  smallRegime_le_upper_edge hrect.2 hk

theorem temperedRegime_of_rectangle {a N k : Nat}
    (hrect : positiveRectangle a N) (hk : ceilSqrt N < k) :
    posTemperedCutoff a < k :=
  lower_edge_lt_of_temperedRegime hrect.1 hk

/-- The actual `ceilSqrt N` lies in the finite plateau range for the rectangle. -/
theorem ceilSqrt_mem_positiveSmallCeilRange_of_rectangle {a N : Nat}
    (hrect : positiveRectangle a N) :
    ceilSqrt N ∈ positiveSmallCeilRange a := by
  simp [positiveSmallCeilRange, posTemperedCutoff, posSmallCutoff]
  exact ⟨ceilSqrt_mono hrect.1, ceilSqrt_mono hrect.2⟩

/-- The lower endpoint of the `ceilSqrt` plateau containing `N` is at most
`N`. -/
theorem ceilSqrtPlateauLo_le_self (N : Nat) :
    ceilSqrtPlateauLo (ceilSqrt N) ≤ N := by
  rcases N with _ | n
  · simp [ceilSqrtPlateauLo]
  · simpa [ceilSqrt, ceilSqrtPlateauLo, pow_two] using
      Nat.succ_le_succ (Nat.sqrt_le n)

/-- The rectangle-and-plateau anchor attached to `N` is at most `N`. -/
theorem positiveSmallEdgeAnchor_le_of_rectangle {a N : Nat}
    (hrect : positiveRectangle a N) :
    positiveSmallEdgeAnchor a (ceilSqrt N) ≤ N := by
  unfold positiveSmallEdgeAnchor
  exact max_le hrect.1 (ceilSqrtPlateauLo_le_self N)

/-! ## The retained `k ≤ 0.9a` range -/

/-- The finite range retained in the positive-part sum, `1 ≤ k ≤ floor(0.9a)`.
Terms above this range are sign-locked negative. -/
def positiveKRange (a : Nat) : Finset Nat := Finset.Icc 1 (9*a / 10)

/-- The floor cutoff `floor(0.9a)`. -/
def posKmax (a : Nat) : Nat := 9*a / 10

/-- The complementary index `j=a-k` used in the saddle formulas. -/
def posJ (a k : Nat) : Nat := a - k

theorem mem_positiveKRange {a k : Nat} :
    k ∈ positiveKRange a ↔ 1 ≤ k ∧ k ≤ posKmax a := by
  simp [positiveKRange, posKmax]

theorem ten_mul_le_nine_mul_of_le_posKmax {a k : Nat}
    (hk : k ≤ posKmax a) :
    10*k ≤ 9*a := by
  unfold posKmax at hk
  have h : k*10 ≤ 9*a :=
    (Nat.le_div_iff_mul_le (by norm_num : 0 < 10)).mp hk
  omega

theorem posKmax_lt_self {a : Nat} (ha : 1 ≤ a) :
    posKmax a < a := by
  unfold posKmax
  rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 10)]
  omega

theorem one_le_posKmax {a : Nat} (ha : 2 ≤ a) :
    1 ≤ posKmax a := by
  unfold posKmax
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 10)]
  omega

theorem four_mul_self_le_five_mul_posKmax {a : Nat} (ha : 9 ≤ a) :
    4 * a ≤ 5 * posKmax a := by
  have hlt : 9 * a < 10 * (posKmax a + 1) := by
    have hsucc : posKmax a < posKmax a + 1 := Nat.lt_succ_self _
    unfold posKmax at hsucc ⊢
    simpa [Nat.mul_comm] using
      (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 10)).mp hsucc
  omega

theorem lt_self_of_le_posKmax {a k : Nat} (ha : 1 ≤ a)
    (hk : k ≤ posKmax a) :
    k < a :=
  hk.trans_lt (posKmax_lt_self ha)

theorem posJ_pos_of_le_posKmax {a k : Nat} (ha : 1 ≤ a)
    (hk : k ≤ posKmax a) :
    0 < posJ a k := by
  unfold posJ
  have hka : k < a := lt_self_of_le_posKmax ha hk
  omega

theorem posJ_pos_of_mem_positiveKRange {a k : Nat} (ha : 1 ≤ a)
    (hk : k ∈ positiveKRange a) :
    0 < posJ a k := by
  exact posJ_pos_of_le_posKmax ha (mem_positiveKRange.mp hk).2

theorem one_le_posJ_of_mem_positiveKRange {a k : Nat} (ha : 1 ≤ a)
    (hk : k ∈ positiveKRange a) :
    1 ≤ posJ a k :=
  Nat.succ_le_of_lt (posJ_pos_of_mem_positiveKRange ha hk)

/-- In the retained range, `j=a-k` still has size at least `a/10`. -/
theorem self_le_ten_mul_posJ_of_le_posKmax {a k : Nat}
    (hk : k ≤ posKmax a) :
    a ≤ 10 * posJ a k := by
  unfold posJ
  have h10 : 10*k ≤ 9*a := ten_mul_le_nine_mul_of_le_posKmax hk
  omega

theorem lt_pred_of_le_posKmax_of_large {a k : Nat}
    (ha : 20 ≤ a) (hk : k ≤ posKmax a) :
    k < a - 1 := by
  have h10 : 10*k ≤ 9*a := ten_mul_le_nine_mul_of_le_posKmax hk
  omega

theorem two_le_posJ_of_le_posKmax_of_large {a k : Nat}
    (ha : 20 ≤ a) (hk : k ≤ posKmax a) :
    2 ≤ posJ a k := by
  have hka : k < a - 1 := lt_pred_of_le_posKmax_of_large ha hk
  unfold posJ
  omega

theorem lt_pred_of_mem_positiveKRange_of_large {a k : Nat}
    (ha : 20 ≤ a) (hk : k ∈ positiveKRange a) :
    k < a - 1 :=
  lt_pred_of_le_posKmax_of_large ha (mem_positiveKRange.mp hk).2

theorem two_le_posJ_of_mem_positiveKRange_of_large {a k : Nat}
    (ha : 20 ≤ a) (hk : k ∈ positiveKRange a) :
    2 ≤ posJ a k :=
  two_le_posJ_of_le_posKmax_of_large ha (mem_positiveKRange.mp hk).2

theorem one_le_posSmallCutoff {a : Nat} (ha : 1 ≤ a) :
    1 ≤ posSmallCutoff a := by
  unfold posSmallCutoff
  exact one_le_ceilSqrt_of_pos (posNhi_pos ha)

theorem positiveSmallBranch_hi_nonempty_of_large {a : Nat} (ha : 2000 < a) :
    1 ≤ min (posKmax a) (posSmallCutoff a) := by
  exact le_min (one_le_posKmax (by omega : 2 ≤ a))
    (one_le_posSmallCutoff (by omega : 1 ≤ a))

theorem posTemperedCutoff_add_one_le_posKmax_of_large {a : Nat}
    (ha : 2000 < a) :
    posTemperedCutoff a + 1 ≤ posKmax a := by
  let q := posKmax a
  let r := q - 1
  have hq1 : 1 ≤ q := by
    dsimp [q]
    exact one_le_posKmax (by omega : 2 ≤ a)
  have hq4 : 4 * a ≤ 5 * q := by
    dsimp [q]
    exact four_mul_self_le_five_mul_posKmax (by omega : 9 ≤ a)
  have ha_le_2r : a ≤ 2 * r := by
    dsimp [r]
    omega
  have hr_ge : 12 ≤ r := by
    dsimp [r]
    omega
  have h6a_le : 6 * a ≤ r * r := by
    have h6a : 6 * a ≤ 12 * r := by omega
    have h12r : 12 * r ≤ r * r := by
      exact Nat.mul_le_mul_right r hr_ge
    exact h6a.trans h12r
  have hr_sq : posNlo a ≤ r * r := by
    unfold posNlo
    omega
  have hceil : posTemperedCutoff a ≤ r := by
    unfold posTemperedCutoff
    exact ceilSqrt_le_of_le_sq hr_sq
  dsimp [r] at hceil
  omega

theorem positiveTemperedBranch_start_le_posKmax_of_large {a : Nat}
    (ha : 2000 < a) :
    max 1 (posTemperedCutoff a + 1) ≤ posKmax a := by
  exact max_le (one_le_posKmax (by omega : 2 ≤ a))
    (posTemperedCutoff_add_one_le_posKmax_of_large ha)

theorem nine_mul_le_ten_mul_of_posKmax_lt {a k : Nat}
    (hk : posKmax a < k) :
    9*a ≤ 10*k := by
  unfold posKmax at hk
  have hlt : 9*a < k*10 := by
    rwa [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 10)] at hk
  omega

/-- A `k` above the retained range is large enough for the sign-lock theorem
once `a ≥ 401`. -/
theorem signLock_m_ge_of_posKmax_lt {a k : Nat}
    (ha : 401 ≤ a) (hk : posKmax a < k) :
    361 ≤ k := by
  have h9 : 9*a ≤ 10*k := nine_mul_le_ten_mul_of_posKmax_lt hk
  omega

/-- The upper rectangle edge is within the `40m/3` sign-lock range for every
`k` above the retained range. -/
theorem posNhi_le_signLock_range_of_posKmax_lt {a k : Nat}
    (hk : posKmax a < k) :
    3 * posNhi a ≤ 40*k := by
  have h9 : 9*a ≤ 10*k := nine_mul_le_ten_mul_of_posKmax_lt hk
  unfold posNhi
  omega

theorem rectangle_N_le_signLock_range_of_posKmax_lt
    {a N k : Nat} (hrect : positiveRectangle a N)
    (hk : posKmax a < k) :
    (N : ℚ) ≤ (40/3) * (k : ℚ) := by
  have h3N_hi : 3*N ≤ 3*posNhi a :=
    Nat.mul_le_mul_left 3 hrect.2
  have h3hi_k : 3*posNhi a ≤ 40*k :=
    posNhi_le_signLock_range_of_posKmax_lt hk
  have h3N_k : 3*N ≤ 40*k := h3N_hi.trans h3hi_k
  have hQ : (3 : ℚ) * (N : ℚ) ≤ 40 * (k : ℚ) := by
    exact_mod_cast h3N_k
  nlinarith

theorem rectangle_N_le_signLock_range_self {a N : Nat}
    (hrect : positiveRectangle a N) :
    (N : ℚ) ≤ (40/3) * (a : ℚ) := by
  have h3N_hi : 3*N ≤ 3*posNhi a :=
    Nat.mul_le_mul_left 3 hrect.2
  have h3hi_a : 3*posNhi a ≤ 40*a := by
    unfold posNhi
    omega
  have h3N_a : 3*N ≤ 40*a := h3N_hi.trans h3hi_a
  have hQ : (3 : ℚ) * (N : ℚ) ≤ 40 * (a : ℚ) := by
    exact_mod_cast h3N_a
  nlinarith

theorem div_natCast_le_div_posNlo_of_rectangle {a N : Nat} {C : ℚ}
    (hC : 0 ≤ C) (ha : 2 ≤ a) (hrect : positiveRectangle a N) :
    C / (N : ℚ) ≤ C / (posNlo a : ℚ) := by
  have hlo_pos : (0 : ℚ) < (posNlo a : ℚ) := by
    exact_mod_cast posNlo_pos ha
  have hlo_le_N : (posNlo a : ℚ) ≤ (N : ℚ) := by
    exact_mod_cast hrect.1
  exact div_le_div_of_nonneg_left hC hlo_pos hlo_le_N

theorem div_posNhi_le_div_natCast_of_rectangle {a N : Nat} {C : ℚ}
    (hC : 0 ≤ C) (ha : 2 ≤ a) (hrect : positiveRectangle a N) :
    C / (posNhi a : ℚ) ≤ C / (N : ℚ) := by
  have hN_pos : (0 : ℚ) < (N : ℚ) := by
    exact_mod_cast positiveRectangle_N_pos ha hrect
  have hN_le_hi : (N : ℚ) ≤ (posNhi a : ℚ) := by
    exact_mod_cast hrect.2
  exact div_le_div_of_nonneg_left hC hN_pos hN_le_hi

/-! ## Executable rational summand majorants -/

/-- The finite-window partial-exp cutoff for the §6 scan.  On
`401 ≤ a ≤ 2000`, both rationalized edge exponents are `< 800`; see
`positiveSmallExponentUpper_lt_expCutoff` and
`positiveTemperedExponentUpper_lt_expCutoff`. -/
def positiveExpCutoff : Nat := 800

/-- The binomial denominator retained in paper §6:
`\binom{a-2}{k-1}`. -/
def positiveBinomDen (a k : Nat) : Nat := Nat.choose (a-2) (k-1)

/-- The reciprocal binomial prefactor in paper §6:
`1 / ((a-1) * \binom{a-2}{k-1})`. -/
def positiveBinomRatio (a k : Nat) : ℚ :=
  1 / (((a-1 : Nat) : ℚ) * (positiveBinomDen a k : ℚ))

/-- Rational `2^{-j}`. -/
def positiveDyadicDecay (j : Nat) : ℚ := 1 / (2 : ℚ)^j

/-- Rational upper exponent for the small-`k` edge formula.  The real
`sqrt(12a-8)` from the paper/script is replaced by the exact integer ceiling,
which is a sound rational upper bound. -/
def positiveSmallExponentUpper (a k : Nat) : ℚ :=
  (1139/1000) * (posSmallCutoff a : ℚ)
    + (1/5) * (posJ a k : ℚ)
    + (29/10) * ((a : ℚ) / (posJ a k : ℚ))
    + 1

/-- The same small-regime exponent before replacing the actual `N` by the
upper rectangle edge. -/
def positiveSmallExponentAt (a N k : Nat) : ℚ :=
  (1139/1000) * (ceilSqrt N : ℚ)
    + (1/5) * (posJ a k : ℚ)
    + (29/10) * ((a : ℚ) / (posJ a k : ℚ))
    + 1

/-- Small-regime exponent with the ceiling-square-root value supplied
explicitly.  This is the finite plateau-check form of
`positiveSmallExponentAt`. -/
def positiveSmallExponentWithCeil (a s k : Nat) : ℚ :=
  (1139/1000) * (s : ℚ)
    + (1/5) * (posJ a k : ℚ)
    + (29/10) * ((a : ℚ) / (posJ a k : ℚ))
    + 1

/-- Rational tangent-line upper surrogate for `sqrt N`.

For `s = ceilSqrt N`, the expression `(N+s^2)/(2s)` is the standard tangent
upper bound for `sqrt N` at `s`.  Unlike `ceilSqrt N`, it still varies inside a
fixed ceiling-square-root plateau, preserving the monotonic slack used by the
paper's small-regime edge replacement. -/
def positiveSqrtTangentUpper (N : Nat) : ℚ :=
  if N = 0 then 0
  else ((N : ℚ) + (ceilSqrt N : ℚ)^2) / (2 * (ceilSqrt N : ℚ))

/-- Small-regime exponent with the rational tangent-line square-root surrogate
at the actual value of `N`. -/
def positiveSmallTangentExponentAt (a N k : Nat) : ℚ :=
  (1139/1000) * positiveSqrtTangentUpper N
    + (1/5) * (posJ a k : ℚ)
    + (29/10) * ((a : ℚ) / (posJ a k : ℚ))
    + 1

/-- Rational upper exponent for the tempered edge formula. -/
def positiveTemperedExponentUpper (a k : Nat) : ℚ :=
  (1/5) * (a : ℚ)
    + (57/10) * ((a : ℚ) / (k : ℚ))
    + (29/10) * ((a : ℚ) / (posJ a k : ℚ))
    + 2

/-- Shared rational prefactor
`C/N * k*j / ((a-1) * choose(a-2,k-1)) * 2^{-j}`. -/
def positivePrefactor (C : ℚ) (a N k : Nat) : ℚ :=
  (C / (N : ℚ))
    * (((k : ℚ) * (posJ a k : ℚ))
      / (((a-1 : Nat) : ℚ) * (positiveBinomDen a k : ℚ)))
    * positiveDyadicDecay (posJ a k)

/-- The same prefactor written using the reciprocal-binomial ratio that comes
out of the coefficient-ratio bound. -/
theorem positivePrefactor_eq_binomRatio (C : ℚ) (a N k : Nat) :
    positivePrefactor C a N k =
      (C / (N : ℚ)) * ((k : ℚ) * (posJ a k : ℚ)) *
        positiveBinomRatio a k * positiveDyadicDecay (posJ a k) := by
  unfold positivePrefactor positiveBinomRatio
  ring

/-- The rationalized small-regime edge majorant for one summand. -/
def positiveSmallMajorantTerm (a k : Nat) : ℚ :=
  positivePrefactor 65 a (posNhi a) k
    * partialExpUpper (positiveSmallExponentUpper a k) positiveExpCutoff

/-- Small-regime majorant in the same scalar form as the product bridge:
constant, edge denominator, reciprocal binomial ratio, dyadic decay, and the
rationalized exponential upper bound. -/
theorem positiveSmallMajorantTerm_eq_binomRatio (a k : Nat) :
    positiveSmallMajorantTerm a k =
      (65 / (posNhi a : ℚ)) * ((k : ℚ) * (posJ a k : ℚ)) *
        positiveBinomRatio a k * positiveDyadicDecay (posJ a k) *
        partialExpUpper (positiveSmallExponentUpper a k) positiveExpCutoff := by
  unfold positiveSmallMajorantTerm
  rw [positivePrefactor_eq_binomRatio]

/-- The rationalized tempered-regime edge majorant for one summand. -/
def positiveTemperedMajorantTerm (a k : Nat) : ℚ :=
  positivePrefactor 96 a (posNlo a) k
    * partialExpUpper (positiveTemperedExponentUpper a k) positiveExpCutoff

/-- Tempered-regime majorant in the same scalar form as the product bridge. -/
theorem positiveTemperedMajorantTerm_eq_binomRatio (a k : Nat) :
    positiveTemperedMajorantTerm a k =
      (96 / (posNlo a : ℚ)) * ((k : ℚ) * (posJ a k : ℚ)) *
        positiveBinomRatio a k * positiveDyadicDecay (posJ a k) *
        partialExpUpper (positiveTemperedExponentUpper a k) positiveExpCutoff := by
  unfold positiveTemperedMajorantTerm
  rw [positivePrefactor_eq_binomRatio]

/-- The scalar product of the small-regime `X` and `Y` constants after the
coefficient-ratio bound and the upper-edge replacement have been inserted. -/
def positiveSmallScalarProductBound (a k : Nat) : ℚ :=
  ((2581/40) / (posNhi a : ℚ)) * ((k : ℚ) * (posJ a k : ℚ)) *
    positiveBinomRatio a k * positiveDyadicDecay (posJ a k) *
    partialExpUpper (positiveSmallExponentUpper a k) positiveExpCutoff

/-- The scalar product of the tempered-regime `X` and `Y` constants before
replacing the actual `N` denominator by the lower rectangle edge. -/
def positiveTemperedScalarProductBound (a N k : Nat) : ℚ :=
  ((2117/40) / (N : ℚ)) * ((k : ℚ) * (posJ a k : ℚ)) *
    positiveBinomRatio a k * positiveDyadicDecay (posJ a k) *
    partialExpUpper (positiveTemperedExponentUpper a k) positiveExpCutoff

/-- Direct combined small-regime target for `X_k(N) * Y_{a-k}(N)`.
This is the product form that implies `positiveSmallScalarProductBound`
without multiplying two independent `partialExpUpper` estimates. -/
def positiveSmallXYProductBound (a N k : Nat) : ℚ :=
  (2581/20) * (((k : ℚ) * (posJ a k : ℚ)) /
    ((N : ℚ) * (posNhi a : ℚ))) *
    partialExpUpper (positiveSmallExponentUpper a k) positiveExpCutoff

/-- Actual-`N` combined small-regime target before the upper-edge replacement.
This is the direct rational form of the displayed small `X` constant times
the tempered `Y` constant, with a single combined exponent surrogate. -/
def positiveSmallXYProductAtBound (a N k : Nat) : ℚ :=
  (2581/20) * (((k : ℚ) * (posJ a k : ℚ)) / ((N : ℚ)^2)) *
    partialExpUpper (positiveSmallExponentAt a N k) positiveExpCutoff

/-- Actual-`N` combined small-regime target using the rational tangent-line
square-root surrogate.  This is the corrected replacement for the too-coarse
`ceilSqrt N` target when doing the upper-edge comparison. -/
def positiveSmallXYProductTangentBound (a N k : Nat) : ℚ :=
  (2581/20) * (((k : ℚ) * (posJ a k : ℚ)) / ((N : ℚ)^2)) *
    partialExpUpper (positiveSmallTangentExponentAt a N k) positiveExpCutoff

/-- Direct combined tempered-regime target for `X_k(N) * Y_{a-k}(N)`. -/
def positiveTemperedXYProductBound (a N k : Nat) : ℚ :=
  (2117/20) * (((k : ℚ) * (posJ a k : ℚ)) / ((N : ℚ)^2)) *
    partialExpUpper (positiveTemperedExponentUpper a k) positiveExpCutoff

/-! ### Finite-check targets for the remaining positive saddle budgets -/

/-- The scalar exponential gap needed to replace the actual small-regime
`N`-denominator by the upper rectangle edge.  This is the finite rational
inequality that remains after cancelling the common positive factors in
`positiveSmallXYProductAtBound ≤ positiveSmallXYProductBound`. -/
def positiveSmallExpEdgeGap (a N k : Nat) : Prop :=
  (posNhi a : ℚ) *
      partialExpUpper (positiveSmallExponentAt a N k) positiveExpCutoff
    ≤
    (N : ℚ) *
      partialExpUpper (positiveSmallExponentUpper a k) positiveExpCutoff

/-- Plateau-anchor form of `positiveSmallExpEdgeGap`, checking the worst `N`
for a fixed ceiling-square-root value `s`. -/
def positiveSmallExpEdgeGapAtCeil (a s k : Nat) : Prop :=
  (posNhi a : ℚ) *
      partialExpUpper (positiveSmallExponentWithCeil a s k) positiveExpCutoff
    ≤
    (positiveSmallEdgeAnchor a s : ℚ) *
      partialExpUpper (positiveSmallExponentUpper a k) positiveExpCutoff

/-- Corrected small-edge exponential gap for the tangent-line actual-`N`
surrogate. -/
def positiveSmallTangentExpEdgeGap (a N k : Nat) : Prop :=
  (posNhi a : ℚ) *
      partialExpUpper (positiveSmallTangentExponentAt a N k) positiveExpCutoff
    ≤
    (N : ℚ) *
      partialExpUpper (positiveSmallExponentUpper a k) positiveExpCutoff

/-! ### Displayed `X`/`Y` saddle-bound shapes -/

/-- The small-regime `X_k(N)` exponent from the TeX display. -/
def positiveSmallXExponentAt (N : Nat) : ℚ :=
  (1139/1000) * (ceilSqrt N : ℚ)

/-- The upper-edge version of the small-regime `X_k(N)` exponent. -/
def positiveSmallXExponentUpper (a : Nat) : ℚ :=
  (1139/1000) * (posSmallCutoff a : ℚ)

/-- The tempered-regime `X_k(N)` exponent from the TeX display. -/
def positiveTemperedXExponent (a k : Nat) : ℚ :=
  (1/5) * (k : ℚ) + (57/10) * ((a : ℚ) / (k : ℚ)) + 1

/-- The tempered `Y_j(N)` exponent from the TeX display. -/
def positiveYExponent (a j : Nat) : ℚ :=
  (1/5) * (j : ℚ) + (29/10) * ((a : ℚ) / (j : ℚ)) + 1

/-- TeX small-regime bound target:
`X_k(N) ≤ 8.9·k/N·exp(1.139 ceilSqrt N)`, with the rational exponential
surrogate used everywhere in this file. -/
def positiveSmallXBound (N k : Nat) : ℚ :=
  (89/10) * ((k : ℚ) / (N : ℚ)) *
    partialExpUpper (positiveSmallXExponentAt N) positiveExpCutoff

/-- TeX tempered-regime bound target:
`X_k(N) ≤ 7.3·k/N·exp(0.2k + 5.7a/k + 1)`. -/
def positiveTemperedXBound (a N k : Nat) : ℚ :=
  (73/10) * ((k : ℚ) / (N : ℚ)) *
    partialExpUpper (positiveTemperedXExponent a k) positiveExpCutoff

/-- TeX tempered `Y_j(N)` bound target:
`Y_j(N) ≤ 14.5·j/N·exp(0.2j + 2.9a/j + 1)`. -/
def positiveYBound (a N j : Nat) : ℚ :=
  (29/2) * ((j : ℚ) / (N : ℚ)) *
    partialExpUpper (positiveYExponent a j) positiveExpCutoff

/-- Product of the displayed small-`X` and `Y` bounds after inserting the
reciprocal-binomial ratio. -/
def positiveSmallDisplayedProductBound (a N k : Nat) : ℚ :=
  ((N : ℚ) / 2) * positiveBinomRatio a k *
    positiveDyadicDecay (posJ a k) *
    positiveSmallXBound N k *
    positiveYBound a N (posJ a k)

/-- Product of the displayed tempered-`X` and `Y` bounds after inserting the
reciprocal-binomial ratio. -/
def positiveTemperedDisplayedProductBound (a N k : Nat) : ℚ :=
  ((N : ℚ) / 2) * positiveBinomRatio a k *
    positiveDyadicDecay (posJ a k) *
    positiveTemperedXBound a N k *
    positiveYBound a N (posJ a k)

/-- Common nonnegative scalar outside the rational exponential comparison in
the displayed product bounds. -/
def positiveDisplayedCommonFactor (C : ℚ) (a k : Nat) : ℚ :=
  C * ((k : ℚ) * (posJ a k : ℚ)) *
    positiveBinomRatio a k * positiveDyadicDecay (posJ a k)

/-- Pure exponential/edge part of the displayed small-regime product. -/
def positiveSmallDisplayedExpEdge (a N k : Nat) : ℚ :=
  (1 / (N : ℚ)) *
    partialExpUpper (positiveSmallXExponentAt N) positiveExpCutoff *
    partialExpUpper (positiveYExponent a (posJ a k)) positiveExpCutoff

/-- Pure exponential/edge part of the combined small-regime scalar bound. -/
def positiveSmallCombinedExpEdge (a k : Nat) : ℚ :=
  (1 / (posNhi a : ℚ)) *
    partialExpUpper (positiveSmallExponentUpper a k) positiveExpCutoff

/-- Pure exponential/edge part of the displayed tempered-regime product. -/
def positiveTemperedDisplayedExpEdge (a N k : Nat) : ℚ :=
  (1 / (N : ℚ)) *
    partialExpUpper (positiveTemperedXExponent a k) positiveExpCutoff *
    partialExpUpper (positiveYExponent a (posJ a k)) positiveExpCutoff

/-- Pure exponential/edge part of the combined tempered-regime scalar bound. -/
def positiveTemperedCombinedExpEdge (a N k : Nat) : ℚ :=
  (1 / (N : ℚ)) *
    partialExpUpper (positiveTemperedExponentUpper a k) positiveExpCutoff

theorem positiveSmallExponentAt_eq_smallX_add_Y (a N k : Nat) :
    positiveSmallExponentAt a N k =
      positiveSmallXExponentAt N + positiveYExponent a (posJ a k) := by
  unfold positiveSmallExponentAt positiveSmallXExponentAt positiveYExponent
  ring

theorem positiveSmallExponentAt_eq_withCeil (a N k : Nat) :
    positiveSmallExponentAt a N k =
      positiveSmallExponentWithCeil a (ceilSqrt N) k := by
  unfold positiveSmallExponentAt positiveSmallExponentWithCeil
  ring

theorem positiveSqrtTangentUpper_nonneg (N : Nat) :
    0 ≤ positiveSqrtTangentUpper N := by
  unfold positiveSqrtTangentUpper
  split
  · norm_num
  · positivity

theorem positiveSqrtTangentUpper_le_ceilSqrt (N : Nat) :
    positiveSqrtTangentUpper N ≤ (ceilSqrt N : ℚ) := by
  by_cases hzero : N = 0
  · simp [positiveSqrtTangentUpper, hzero]
  · have hNpos : 1 ≤ N := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hzero)
    have hsposNat : 0 < ceilSqrt N := by
      have hNsq : 1 ≤ ceilSqrt N * ceilSqrt N := hNpos.trans (le_ceilSqrt_sq N)
      exact Nat.pos_of_ne_zero (by
        intro hs
        simp [hs] at hNsq)
    have hspos : (0 : ℚ) < (ceilSqrt N : ℚ) := by exact_mod_cast hsposNat
    have hNsqQ : (N : ℚ) ≤ (ceilSqrt N : ℚ)^2 := by
      rw [pow_two]
      exact_mod_cast le_ceilSqrt_sq N
    unfold positiveSqrtTangentUpper
    rw [if_neg hzero]
    rw [div_le_iff₀ (by positivity : (0 : ℚ) < 2 * (ceilSqrt N : ℚ))]
    nlinarith

theorem positiveSmallTangentExponentAt_le_at (a N k : Nat) :
    positiveSmallTangentExponentAt a N k ≤ positiveSmallExponentAt a N k := by
  have hs := positiveSqrtTangentUpper_le_ceilSqrt N
  unfold positiveSmallTangentExponentAt positiveSmallExponentAt
  nlinarith

theorem positiveSmallExponentUpper_eq_smallX_add_Y (a k : Nat) :
    positiveSmallExponentUpper a k =
      positiveSmallXExponentUpper a + positiveYExponent a (posJ a k) := by
  unfold positiveSmallExponentUpper positiveSmallXExponentUpper positiveYExponent
  ring

theorem positiveTemperedExponentUpper_eq_X_add_Y
    {a k : Nat} (hk : k ≤ a) :
    positiveTemperedExponentUpper a k =
      positiveTemperedXExponent a k + positiveYExponent a (posJ a k) := by
  have hsum : ((k : ℚ) + (posJ a k : ℚ)) = (a : ℚ) := by
    have hnat : k + posJ a k = a := by
      unfold posJ
      omega
    exact_mod_cast hnat
  have hlin :
      (1/5 : ℚ) * (a : ℚ) =
        (1/5) * (k : ℚ) + (1/5) * (posJ a k : ℚ) := by
    nlinarith
  unfold positiveTemperedExponentUpper positiveTemperedXExponent positiveYExponent
  rw [hlin]
  ring

theorem positiveDisplayedCommonFactor_nonneg
    {C : ℚ} (hC : 0 ≤ C) (a k : Nat) :
    0 ≤ positiveDisplayedCommonFactor C a k := by
  unfold positiveDisplayedCommonFactor positiveBinomRatio positiveDyadicDecay
  positivity

theorem positiveSmallDisplayedProductBound_eq
    {a N k : Nat} (hN : 1 ≤ N) :
    positiveSmallDisplayedProductBound a N k =
      ((2581/40) / (N : ℚ)) * ((k : ℚ) * (posJ a k : ℚ)) *
        positiveBinomRatio a k * positiveDyadicDecay (posJ a k) *
        partialExpUpper (positiveSmallXExponentAt N) positiveExpCutoff *
        partialExpUpper (positiveYExponent a (posJ a k)) positiveExpCutoff := by
  have hNQ : (N : ℚ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  unfold positiveSmallDisplayedProductBound positiveSmallXBound positiveYBound
  field_simp [hNQ]
  ring

theorem positiveSmallDisplayedProductBound_eq_expEdge
    {a N k : Nat} (hN : 1 ≤ N) :
    positiveSmallDisplayedProductBound a N k =
      positiveDisplayedCommonFactor (2581/40) a k *
        positiveSmallDisplayedExpEdge a N k := by
  rw [positiveSmallDisplayedProductBound_eq hN]
  unfold positiveDisplayedCommonFactor positiveSmallDisplayedExpEdge
  ring

theorem positiveSmallScalarProductBound_eq_expEdge (a k : Nat) :
    positiveSmallScalarProductBound a k =
      positiveDisplayedCommonFactor (2581/40) a k *
        positiveSmallCombinedExpEdge a k := by
  unfold positiveSmallScalarProductBound positiveDisplayedCommonFactor
    positiveSmallCombinedExpEdge
  ring

theorem positiveTemperedDisplayedProductBound_eq
    {a N k : Nat} (hN : 1 ≤ N) :
    positiveTemperedDisplayedProductBound a N k =
      ((2117/40) / (N : ℚ)) * ((k : ℚ) * (posJ a k : ℚ)) *
        positiveBinomRatio a k * positiveDyadicDecay (posJ a k) *
        partialExpUpper (positiveTemperedXExponent a k) positiveExpCutoff *
        partialExpUpper (positiveYExponent a (posJ a k)) positiveExpCutoff := by
  have hNQ : (N : ℚ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  unfold positiveTemperedDisplayedProductBound positiveTemperedXBound positiveYBound
  field_simp [hNQ]
  ring

theorem positiveTemperedDisplayedProductBound_eq_expEdge
    {a N k : Nat} (hN : 1 ≤ N) :
    positiveTemperedDisplayedProductBound a N k =
      positiveDisplayedCommonFactor (2117/40) a k *
        positiveTemperedDisplayedExpEdge a N k := by
  rw [positiveTemperedDisplayedProductBound_eq hN]
  unfold positiveDisplayedCommonFactor positiveTemperedDisplayedExpEdge
  ring

theorem positiveTemperedScalarProductBound_eq_expEdge (a N k : Nat) :
    positiveTemperedScalarProductBound a N k =
      positiveDisplayedCommonFactor (2117/40) a k *
        positiveTemperedCombinedExpEdge a N k := by
  unfold positiveTemperedScalarProductBound positiveDisplayedCommonFactor
    positiveTemperedCombinedExpEdge
  ring

/- The displayed-product normal forms above are kept for auditability, but
they are not used as a certificate interface.  Unlike the real exponential in
the TeX proof, the rational `partialExpUpper` surrogate is not submultiplicative
with enough slack here; the formal certificate therefore targets the combined
scalar-product bounds directly. -/

/-- Concrete audit witness for the preceding note: at this small-regime point,
the product of the separate rational exponential surrogates is already larger
than the combined surrogate used in the executable majorant. -/
theorem positiveSmallDisplayedExpEdge_not_le_combined_example :
    ¬ positiveSmallDisplayedExpEdge 401 4762 70 ≤
      positiveSmallCombinedExpEdge 401 70 := by
  native_decide

theorem positiveSmallDisplayedProductBound_le_scalar_of_expEdge
    {a N k : Nat} (hN : 1 ≤ N)
    (hexp : positiveSmallDisplayedExpEdge a N k ≤
      positiveSmallCombinedExpEdge a k) :
    positiveSmallDisplayedProductBound a N k ≤
      positiveSmallScalarProductBound a k := by
  rw [positiveSmallDisplayedProductBound_eq_expEdge hN,
    positiveSmallScalarProductBound_eq_expEdge]
  exact mul_le_mul_of_nonneg_left hexp
    (positiveDisplayedCommonFactor_nonneg (by norm_num) a k)

theorem positiveTemperedDisplayedProductBound_le_scalar_of_expEdge
    {a N k : Nat} (hN : 1 ≤ N)
    (hexp : positiveTemperedDisplayedExpEdge a N k ≤
      positiveTemperedCombinedExpEdge a N k) :
    positiveTemperedDisplayedProductBound a N k ≤
      positiveTemperedScalarProductBound a N k := by
  rw [positiveTemperedDisplayedProductBound_eq_expEdge hN,
    positiveTemperedScalarProductBound_eq_expEdge]
  exact mul_le_mul_of_nonneg_left hexp
    (positiveDisplayedCommonFactor_nonneg (by norm_num) a k)

/-- Corrected two-edge summand majorant from `scripts/positive_saddle_scan.py`:
use the small formula only when the small regime is possible somewhere in the
rectangle, use the tempered formula only when the tempered regime is possible
somewhere in the rectangle, and take the larger applicable value. -/
def positiveEdgeMajorantTerm (a k : Nat) : ℚ :=
  max
    (if k ≤ posSmallCutoff a then positiveSmallMajorantTerm a k else 0)
    (if posTemperedCutoff a < k then positiveTemperedMajorantTerm a k else 0)

/-- The executable finite-window sum over `1 ≤ k ≤ floor(0.9a)`.  The solo
`2^{-a-1}Y_a(N)` term is intentionally not folded in here yet. -/
def positiveEdgeMajorantSum (a : Nat) : ℚ :=
  ∑ k ∈ positiveKRange a, positiveEdgeMajorantTerm a k

/-! ### Custom edge majorants

The finite-window scan uses `positiveSmallMajorantTerm` and
`positiveTemperedMajorantTerm`, whose rational exponential surrogate is tuned
for `401 ≤ a ≤ 2000`.  The entropy tail for `a > 2000` needs different
closed rational summand bounds.  The following parameterized edge reducer
keeps the corrected two-regime rectangle bookkeeping reusable without
pretending the finite-window terms are valid outside their range. -/

def positiveCustomEdgeMajorantTerm
    (smallTerm temperedTerm : Nat → Nat → ℚ) (a k : Nat) : ℚ :=
  max
    (if k ≤ posSmallCutoff a then smallTerm a k else 0)
    (if posTemperedCutoff a < k then temperedTerm a k else 0)

def positiveCustomEdgeMajorantSum
    (smallTerm temperedTerm : Nat → Nat → ℚ) (a : Nat) : ℚ :=
  ∑ k ∈ positiveKRange a, positiveCustomEdgeMajorantTerm smallTerm temperedTerm a k

def positiveCustomSmallBranchSum
    (smallTerm : Nat → Nat → ℚ) (a : Nat) : ℚ :=
  ∑ k ∈ positiveKRange a,
    if k ≤ posSmallCutoff a then smallTerm a k else 0

def positiveCustomTemperedBranchSum
    (temperedTerm : Nat → Nat → ℚ) (a : Nat) : ℚ :=
  ∑ k ∈ positiveKRange a,
    if posTemperedCutoff a < k then temperedTerm a k else 0

theorem positiveCustomSmallBranchSum_eq_Icc
    (smallTerm : Nat → Nat → ℚ) (a : Nat) :
    positiveCustomSmallBranchSum smallTerm a =
      ∑ k ∈ Finset.Icc 1 (min (posKmax a) (posSmallCutoff a)),
        smallTerm a k := by
  unfold positiveCustomSmallBranchSum positiveKRange
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp [posKmax, and_assoc]

theorem positiveCustomTemperedBranchSum_eq_Icc
    (temperedTerm : Nat → Nat → ℚ) (a : Nat) :
    positiveCustomTemperedBranchSum temperedTerm a =
      ∑ k ∈ Finset.Icc (max 1 (posTemperedCutoff a + 1)) (posKmax a),
        temperedTerm a k := by
  unfold positiveCustomTemperedBranchSum positiveKRange
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp [posKmax]
  omega

@[simp] theorem positiveCustomEdgeMajorantTerm_finite (a k : Nat) :
    positiveCustomEdgeMajorantTerm positiveSmallMajorantTerm positiveTemperedMajorantTerm a k
      = positiveEdgeMajorantTerm a k := rfl

@[simp] theorem positiveCustomEdgeMajorantSum_finite (a : Nat) :
    positiveCustomEdgeMajorantSum positiveSmallMajorantTerm positiveTemperedMajorantTerm a
      = positiveEdgeMajorantSum a := rfl

theorem positiveSmallCustomTerm_le_edge
    {smallTerm temperedTerm : Nat → Nat → ℚ} {a k : Nat}
    (hk : k ≤ posSmallCutoff a) :
    smallTerm a k ≤ positiveCustomEdgeMajorantTerm smallTerm temperedTerm a k := by
  unfold positiveCustomEdgeMajorantTerm
  rw [if_pos hk]
  exact le_max_left _ _

theorem positiveTemperedCustomTerm_le_edge
    {smallTerm temperedTerm : Nat → Nat → ℚ} {a k : Nat}
    (hk : posTemperedCutoff a < k) :
    temperedTerm a k ≤ positiveCustomEdgeMajorantTerm smallTerm temperedTerm a k := by
  unfold positiveCustomEdgeMajorantTerm
  rw [if_pos hk]
  exact le_max_right _ _

theorem positiveCustomEdgeMajorantTerm_le_branch_sum_of_nonneg
    {smallTerm temperedTerm : Nat → Nat → ℚ} {a k : Nat}
    (hsmall0 : 0 ≤ smallTerm a k)
    (htempered0 : 0 ≤ temperedTerm a k) :
    positiveCustomEdgeMajorantTerm smallTerm temperedTerm a k
      ≤ (if k ≤ posSmallCutoff a then smallTerm a k else 0)
        + (if posTemperedCutoff a < k then temperedTerm a k else 0) := by
  unfold positiveCustomEdgeMajorantTerm
  have hsmallBranch :
      0 ≤ (if k ≤ posSmallCutoff a then smallTerm a k else 0 : ℚ) := by
    by_cases hk : k ≤ posSmallCutoff a <;> simp [hk, hsmall0]
  have htemperedBranch :
      0 ≤ (if posTemperedCutoff a < k then temperedTerm a k else 0 : ℚ) := by
    by_cases hk : posTemperedCutoff a < k <;> simp [hk, htempered0]
  exact max_le (by linarith) (by linarith)

theorem term_le_positiveCustomEdgeMajorantTerm_of_regime_bounds
    {smallTerm temperedTerm : Nat → Nat → ℚ} {a N k : Nat}
    {T : ℚ} (hrect : positiveRectangle a N)
    (hsmall : k ≤ ceilSqrt N → T ≤ smallTerm a k)
    (htempered : ceilSqrt N < k → T ≤ temperedTerm a k) :
    T ≤ positiveCustomEdgeMajorantTerm smallTerm temperedTerm a k := by
  rcases le_or_gt k (ceilSqrt N) with hkSmall | hkTemp
  · exact (hsmall hkSmall).trans
      (positiveSmallCustomTerm_le_edge
        (smallRegime_of_rectangle hrect hkSmall))
  · exact (htempered hkTemp).trans
      (positiveTemperedCustomTerm_le_edge
        (temperedRegime_of_rectangle hrect hkTemp))

theorem sum_le_positiveCustomEdgeMajorantSum
    {smallTerm temperedTerm : Nat → Nat → ℚ} {a : Nat} {F : Nat → ℚ}
    (hF : ∀ k, k ∈ positiveKRange a →
      F k ≤ positiveCustomEdgeMajorantTerm smallTerm temperedTerm a k) :
    (∑ k ∈ positiveKRange a, F k)
      ≤ positiveCustomEdgeMajorantSum smallTerm temperedTerm a := by
  unfold positiveCustomEdgeMajorantSum
  exact Finset.sum_le_sum hF

theorem sum_le_positiveCustomEdgeMajorantSum_of_regime_bounds
    {smallTerm temperedTerm : Nat → Nat → ℚ} {a N : Nat}
    {F : Nat → ℚ} (hrect : positiveRectangle a N)
    (hFsmall :
      ∀ k, k ∈ positiveKRange a →
        k ≤ ceilSqrt N → F k ≤ smallTerm a k)
    (hFtempered :
      ∀ k, k ∈ positiveKRange a →
        ceilSqrt N < k → F k ≤ temperedTerm a k) :
    (∑ k ∈ positiveKRange a, F k)
      ≤ positiveCustomEdgeMajorantSum smallTerm temperedTerm a :=
  sum_le_positiveCustomEdgeMajorantSum fun k hk =>
    term_le_positiveCustomEdgeMajorantTerm_of_regime_bounds hrect
      (hFsmall k hk) (hFtempered k hk)

theorem positiveCustomEdgeMajorantSum_le_branchSums_of_nonneg
    {smallTerm temperedTerm : Nat → Nat → ℚ} {a : Nat}
    (hsmall0 : ∀ k, k ∈ positiveKRange a → 0 ≤ smallTerm a k)
    (htempered0 : ∀ k, k ∈ positiveKRange a → 0 ≤ temperedTerm a k) :
    positiveCustomEdgeMajorantSum smallTerm temperedTerm a
      ≤ positiveCustomSmallBranchSum smallTerm a
        + positiveCustomTemperedBranchSum temperedTerm a := by
  unfold positiveCustomEdgeMajorantSum
    positiveCustomSmallBranchSum positiveCustomTemperedBranchSum
  calc
    ∑ k ∈ positiveKRange a,
        positiveCustomEdgeMajorantTerm smallTerm temperedTerm a k
        ≤
      ∑ k ∈ positiveKRange a,
        ((if k ≤ posSmallCutoff a then smallTerm a k else 0)
          + (if posTemperedCutoff a < k then temperedTerm a k else 0)) := by
          exact Finset.sum_le_sum fun k hk =>
            positiveCustomEdgeMajorantTerm_le_branch_sum_of_nonneg
              (hsmall0 k hk) (htempered0 k hk)
    _ =
      (∑ k ∈ positiveKRange a,
        (if k ≤ posSmallCutoff a then smallTerm a k else 0))
        +
      (∑ k ∈ positiveKRange a,
        (if posTemperedCutoff a < k then temperedTerm a k else 0)) := by
          rw [Finset.sum_add_distrib]

theorem positiveCustomEdgeMajorantSum_le_edgeBudget_of_branch_budgets
    {smallTerm temperedTerm : Nat → Nat → ℚ} {a : Nat}
    {smallBudget temperedBudget edgeBudget : ℚ}
    (hsmall0 : ∀ k, k ∈ positiveKRange a → 0 ≤ smallTerm a k)
    (htempered0 : ∀ k, k ∈ positiveKRange a → 0 ≤ temperedTerm a k)
    (hsmall :
      positiveCustomSmallBranchSum smallTerm a ≤ smallBudget)
    (htempered :
      positiveCustomTemperedBranchSum temperedTerm a ≤ temperedBudget)
    (hbudget : smallBudget + temperedBudget ≤ edgeBudget) :
    positiveCustomEdgeMajorantSum smallTerm temperedTerm a ≤ edgeBudget := by
  calc
    positiveCustomEdgeMajorantSum smallTerm temperedTerm a
        ≤ positiveCustomSmallBranchSum smallTerm a
          + positiveCustomTemperedBranchSum temperedTerm a :=
          positiveCustomEdgeMajorantSum_le_branchSums_of_nonneg
            hsmall0 htempered0
    _ ≤ smallBudget + temperedBudget := add_le_add hsmall htempered
    _ ≤ edgeBudget := hbudget

/-! ### Geometric branch-sum helpers -/

theorem sum_Icc_eq_sum_range_shift (F : Nat → ℚ) {lo hi : Nat}
    (_hlohi : lo ≤ hi) :
    ∑ r ∈ Finset.Icc lo hi, F r =
      ∑ j ∈ Finset.range (hi + 1 - lo), F (lo + j) := by
  have hIccIco : Finset.Icc lo hi = Finset.Ico lo (hi + 1) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIccIco, Finset.sum_Ico_eq_sum_range]

private theorem positiveGeom_chain_bound_from_upto
    (F : Nat → ℚ) {lo K : Nat} {q : ℚ} (hq0 : 0 ≤ q)
    (hstep : ∀ j, j + 1 < K → F (lo + j + 1) ≤ F (lo + j) * q) :
    ∀ j, j < K → F (lo + j) ≤ F lo * q^j
  | 0, _ => by simp
  | j + 1, hj => by
      have hprev : j < K := by omega
      have hrec := positiveGeom_chain_bound_from_upto F hq0 hstep j hprev
      calc
        F (lo + (j + 1)) = F (lo + j + 1) := rfl
        _ ≤ F (lo + j) * q := hstep j hj
        _ ≤ (F lo * q^j) * q := mul_le_mul_of_nonneg_right hrec hq0
        _ = F lo * q^(j + 1) := by
          rw [pow_succ]
          ring

/-- Finite interval version of geometric domination.  If every successor in
`[lo, hi]` is at most `q` times the preceding term, the interval sum is bounded
by the first term times the corresponding finite geometric sum. -/
theorem geom_chain_Icc_sum_le_geom (F : Nat → ℚ) {lo hi : Nat} {q : ℚ}
    (hlohi : lo ≤ hi) (hq0 : 0 ≤ q)
    (hstep : ∀ r, lo ≤ r → r < hi → F (r + 1) ≤ F r * q) :
    ∑ r ∈ Finset.Icc lo hi, F r
      ≤ F lo * ∑ j ∈ Finset.range (hi + 1 - lo), q^j := by
  rw [sum_Icc_eq_sum_range_shift F hlohi]
  let K := hi + 1 - lo
  have hstepShift :
      ∀ j, j + 1 < K → F (lo + j + 1) ≤ F (lo + j) * q := by
    intro j hj
    exact hstep (lo + j) (by omega) (by omega)
  calc
    ∑ j ∈ Finset.range K, F (lo + j)
        ≤ ∑ j ∈ Finset.range K, F lo * q^j := by
          exact Finset.sum_le_sum fun j hj =>
            positiveGeom_chain_bound_from_upto F hq0 hstepShift j
              (Finset.mem_range.mp hj)
    _ = F lo * ∑ j ∈ Finset.range K, q^j := by
          rw [Finset.mul_sum]

/-- Closed geometric-tail version of `geom_chain_Icc_sum_le_geom`. -/
theorem geom_chain_Icc_sum_le_inv_one_sub
    (F : Nat → ℚ) {lo hi : Nat} {q : ℚ}
    (hlohi : lo ≤ hi) (hF0 : 0 ≤ F lo) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hstep : ∀ r, lo ≤ r → r < hi → F (r + 1) ≤ F r * q) :
    ∑ r ∈ Finset.Icc lo hi, F r
      ≤ F lo * (1 / (1 - q)) := by
  have hgeom := geom_chain_Icc_sum_le_geom F hlohi hq0 hstep
  exact hgeom.trans
    (mul_le_mul_of_nonneg_left
      (geom_sum_le_inv_one_sub q hq0 hq1 (hi + 1 - lo)) hF0)

theorem mul_inv_one_sub_le_of_le_mul_one_sub {x B q : ℚ}
    (hq1 : q < 1) (h : x ≤ B * (1 - q)) :
    x * (1 / (1 - q)) ≤ B := by
  have hden : 0 < 1 - q := by linarith
  rw [← div_eq_mul_one_div, div_le_iff₀ hden]
  simpa [mul_comm] using h

/-! ## Large-`a` final margins -/

/-- The positive-part target from paper §6. -/
def positiveTarget : ℚ := 1 / 100000000

/-- Lean's finite-envelope bookkeeping gives the solo term half of the
`positiveTarget` budget.  This is intentionally looser than the TeX statement
`2^{-a-1}Y_a(N) < exp(-0.49a)`; the latter will imply this budget with ample
room once the solo saddle bound is formalized. -/
def positiveSoloBudget : ℚ := positiveTarget / 2

/-- The remaining half of the `positiveTarget` budget, reserved for the
corrected two-edge finite scan. -/
def positiveEdgeBudget : ℚ := positiveTarget / 2

/-- Boolean row check for the corrected two-edge finite budget.  Directly
evaluating the full range is currently too slow to use as the main certificate;
this definition is nevertheless useful for generated chunks and small audits. -/
def checkPositiveEdgeBudgetRow (a : Nat) : Bool :=
  decide (positiveEdgeMajorantSum a ≤ positiveEdgeBudget)

/-- Boolean range check for the corrected two-edge finite budget over
`a ∈ [lo, lo+len)`. -/
def checkPositiveEdgeBudgetRange (lo len : Nat) : Bool :=
  (List.range' lo len).all checkPositiveEdgeBudgetRow

/-- Executable list form of `positiveKRange a`. -/
def positiveKRangeList (a : Nat) : List Nat :=
  List.range' 1 (posKmax a)

/-- Executable list form of `positiveSmallCeilRange a`. -/
def positiveSmallCeilRangeList (a : Nat) : List Nat :=
  List.range' (posTemperedCutoff a)
    (posSmallCutoff a + 1 - posTemperedCutoff a)

/-- Executable list form of the positive rectangle's `N`-range at fixed `a`. -/
def positiveNRangeList (a : Nat) : List Nat :=
  List.range' (posNlo a) (posNhi a + 1 - posNlo a)

instance decidablePositiveSmallExpEdgeGapAtCeil (a s k : Nat) :
    Decidable (positiveSmallExpEdgeGapAtCeil a s k) := by
  unfold positiveSmallExpEdgeGapAtCeil
  infer_instance

instance decidablePositiveSmallTangentExpEdgeGap (a N k : Nat) :
    Decidable (positiveSmallTangentExpEdgeGap a N k) := by
  unfold positiveSmallTangentExpEdgeGap
  infer_instance

/-- Boolean check for one plateau-anchor small-edge exponential gap. -/
def checkPositiveSmallExpEdgeAnchorCell (a s k : Nat) : Bool :=
  decide (positiveSmallExpEdgeGapAtCeil a s k)

/-- Boolean check for all retained `k ≤ s` at a fixed `(a,s)` plateau. -/
def checkPositiveSmallExpEdgeAnchorCeil (a s : Nat) : Bool :=
  (positiveKRangeList a).all fun k =>
    if k ≤ s then checkPositiveSmallExpEdgeAnchorCell a s k else true

/-- Boolean check for every small-regime plateau at a fixed row `a`. -/
def checkPositiveSmallExpEdgeAnchorRow (a : Nat) : Bool :=
  (positiveSmallCeilRangeList a).all fun s =>
    checkPositiveSmallExpEdgeAnchorCeil a s

/-- Boolean range check for the plateau-anchor small-edge exponential gaps over
`a ∈ [lo, lo+len)`. -/
def checkPositiveSmallExpEdgeAnchorRange (lo len : Nat) : Bool :=
  (List.range' lo len).all checkPositiveSmallExpEdgeAnchorRow

/-- Boolean check for one corrected tangent small-edge exponential gap. -/
def checkPositiveSmallTangentExpEdgeCell (a N k : Nat) : Bool :=
  decide (positiveSmallTangentExpEdgeGap a N k)

/-- Boolean check for all retained small-regime `k` at one `(a,N)`. -/
def checkPositiveSmallTangentExpEdgeAtN (a N : Nat) : Bool :=
  (positiveKRangeList a).all fun k =>
    if k ≤ ceilSqrt N then checkPositiveSmallTangentExpEdgeCell a N k else true

/-- Boolean check for every `N` in one row's positive rectangle. -/
def checkPositiveSmallTangentExpEdgeRow (a : Nat) : Bool :=
  (positiveNRangeList a).all fun N =>
    checkPositiveSmallTangentExpEdgeAtN a N

/-- Boolean range check for corrected tangent small-edge gaps over
`a ∈ [lo, lo+len)`. -/
def checkPositiveSmallTangentExpEdgeRange (lo len : Nat) : Bool :=
  (List.range' lo len).all checkPositiveSmallTangentExpEdgeRow

/-- The rational sign-lock margin left after the `2215/m²` error budget. -/
def signLockMargin (m : Nat) : ℚ :=
  expNegLower50 * (1 - 2/(m : ℚ)) - 2215 / (m : ℚ)^2

/-! ## Raw normalized positive contribution -/

/-- The normalized solo `Q_a` contribution in `Unorm`.  In the paper's
notation this is the term written as `2^{-a-1}Y_a(N)`. -/
def normalizedSoloTerm (a N : Nat) : ℚ :=
  Qq N a / ((N : ℚ) * c a)

/-- The positive contribution envelope used by the large-`a` assembly. -/
def positiveEnvelope (a N : Nat) : ℚ :=
  normalizedSoloTerm a N + positiveEdgeMajorantSum a

/-- A positive-envelope majorant after replacing the solo term by an external
upper bound.  In the TeX proof this solo bound is supplied by the same
tempered saddle estimate as the positive summands, giving
`2^{-a-1}Y_a(N) < exp(-0.49a)`.  Lean keeps that analytic input separate. -/
def positiveEnvelopeBound (a : Nat) (soloBound : ℚ) : ℚ :=
  soloBound + positiveEdgeMajorantSum a

/-- Positive-envelope analogue for a custom pair of small/tempered edge
majorants, used by the `a > 2000` entropy-tail route. -/
def positiveCustomEnvelope
    (smallTerm temperedTerm : Nat → Nat → ℚ) (a N : Nat) : ℚ :=
  normalizedSoloTerm a N + positiveCustomEdgeMajorantSum smallTerm temperedTerm a

def positiveCustomEnvelopeBound
    (smallTerm temperedTerm : Nat → Nat → ℚ) (a : Nat) (soloBound : ℚ) : ℚ :=
  soloBound + positiveCustomEdgeMajorantSum smallTerm temperedTerm a

@[simp] theorem positiveCustomEnvelope_finite (a N : Nat) :
    positiveCustomEnvelope positiveSmallMajorantTerm positiveTemperedMajorantTerm a N
      = positiveEnvelope a N := rfl

@[simp] theorem positiveCustomEnvelopeBound_finite (a : Nat) (soloBound : ℚ) :
    positiveCustomEnvelopeBound positiveSmallMajorantTerm positiveTemperedMajorantTerm
        a soloBound
      = positiveEnvelopeBound a soloBound := rfl

theorem positiveEnvelope_le_bound_of_solo
    {a N : Nat} {soloBound : ℚ}
    (hsolo : normalizedSoloTerm a N ≤ soloBound) :
    positiveEnvelope a N ≤ positiveEnvelopeBound a soloBound := by
  unfold positiveEnvelope positiveEnvelopeBound
  linarith

theorem positiveCustomEnvelope_le_bound_of_solo
    {smallTerm temperedTerm : Nat → Nat → ℚ}
    {a N : Nat} {soloBound : ℚ}
    (hsolo : normalizedSoloTerm a N ≤ soloBound) :
    positiveCustomEnvelope smallTerm temperedTerm a N
      ≤ positiveCustomEnvelopeBound smallTerm temperedTerm a soloBound := by
  unfold positiveCustomEnvelope positiveCustomEnvelopeBound
  linarith

theorem positiveTarget_pos : 0 < positiveTarget := by
  norm_num [positiveTarget]

theorem positiveSoloBudget_nonneg : 0 ≤ positiveSoloBudget := by
  norm_num [positiveSoloBudget, positiveTarget]

theorem positiveEdgeBudget_nonneg : 0 ≤ positiveEdgeBudget := by
  norm_num [positiveEdgeBudget, positiveTarget]

theorem positiveSoloBudget_add_edgeBudget :
    positiveSoloBudget + positiveEdgeBudget = positiveTarget := by
  norm_num [positiveSoloBudget, positiveEdgeBudget, positiveTarget]

/-- Soundness of one executable row check for the corrected two-edge budget. -/
theorem positiveEdgeBudget_of_checkPositiveEdgeBudgetRow {a : Nat}
    (h : checkPositiveEdgeBudgetRow a = true) :
    positiveEdgeMajorantSum a ≤ positiveEdgeBudget := by
  exact of_decide_eq_true h

/-- Soundness of a finite executable range check for the corrected two-edge
budget.  The range is half-open: `lo ≤ a < lo+len`. -/
theorem positiveEdgeBudget_of_checkPositiveEdgeBudgetRange
    {lo len a : Nat} (h : checkPositiveEdgeBudgetRange lo len = true)
    (hlo : lo ≤ a) (hhi : a < lo + len) :
    positiveEdgeMajorantSum a ≤ positiveEdgeBudget := by
  apply positiveEdgeBudget_of_checkPositiveEdgeBudgetRow
  have hall :
      ∀ x ∈ List.range' lo len, checkPositiveEdgeBudgetRow x = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveEdgeBudgetRange] using h)
  exact hall a ((List.mem_range'_1).mpr ⟨hlo, hhi⟩)

theorem checkPositiveEdgeBudgetRow_of_checkPositiveEdgeBudgetRange
    {lo len a : Nat} (h : checkPositiveEdgeBudgetRange lo len = true)
    (hlo : lo ≤ a) (hhi : a < lo + len) :
    checkPositiveEdgeBudgetRow a = true := by
  have hall :
      ∀ x ∈ List.range' lo len, checkPositiveEdgeBudgetRow x = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveEdgeBudgetRange] using h)
  exact hall a ((List.mem_range'_1).mpr ⟨hlo, hhi⟩)

/-- The full finite-window edge-budget field follows from a single range check
over `401 ≤ a ≤ 2000`.  In practice this theorem is meant to be used with
smaller generated chunk theorems or a faster checker rather than one enormous
`native_decide`. -/
theorem positiveEdgeBudget_401_2000_of_checkPositiveEdgeBudgetRange
    (h : checkPositiveEdgeBudgetRange 401 1600 = true) :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeMajorantSum a ≤ positiveEdgeBudget := by
  intro a ha h2000
  exact positiveEdgeBudget_of_checkPositiveEdgeBudgetRange
    (lo := 401) (len := 1600) h ha (by omega)

/-- Membership bridge from the `Finset` retained range to its executable list
enumerator. -/
theorem mem_positiveKRangeList_of_mem {a k : Nat}
    (hk : k ∈ positiveKRange a) :
    k ∈ positiveKRangeList a := by
  rcases (mem_positiveKRange.mp hk) with ⟨hk1, hkmax⟩
  exact (List.mem_range'_1).mpr (by
    exact ⟨hk1, by omega⟩)

/-- Membership bridge from the `Finset` plateau range to its executable list
enumerator. -/
theorem mem_positiveSmallCeilRangeList_of_mem {a s : Nat}
    (hs : s ∈ positiveSmallCeilRange a) :
    s ∈ positiveSmallCeilRangeList a := by
  rcases (Finset.mem_Icc.mp hs) with ⟨hslo, hshi⟩
  exact (List.mem_range'_1).mpr (by
    exact ⟨hslo, by omega⟩)

/-- Membership bridge from the rectangle predicate to its executable `N` list. -/
theorem mem_positiveNRangeList_of_rectangle {a N : Nat}
    (hrect : positiveRectangle a N) :
    N ∈ positiveNRangeList a := by
  have hlohi : posNlo a ≤ posNhi a + 1 := hrect.1.trans (Nat.le_succ_of_le hrect.2)
  have hlen : posNlo a + (posNhi a + 1 - posNlo a) = posNhi a + 1 :=
    Nat.add_sub_of_le hlohi
  have hlt_hi : N < posNhi a + 1 := Nat.lt_succ_of_le hrect.2
  have hlt_list : N < posNlo a + (posNhi a + 1 - posNlo a) := by
    rwa [hlen]
  exact (List.mem_range'_1).mpr ⟨hrect.1, hlt_list⟩

/-- Soundness of one executable plateau-anchor small-edge check. -/
theorem positiveSmallExpEdgeGapAtCeil_of_checkCell {a s k : Nat}
    (h : checkPositiveSmallExpEdgeAnchorCell a s k = true) :
    positiveSmallExpEdgeGapAtCeil a s k := by
  exact of_decide_eq_true h

/-- Soundness of the executable `(a,s)` plateau check. -/
theorem positiveSmallExpEdgeGapAtCeil_of_checkCeil {a s k : Nat}
    (h : checkPositiveSmallExpEdgeAnchorCeil a s = true)
    (hk : k ∈ positiveKRange a) (hks : k ≤ s) :
    positiveSmallExpEdgeGapAtCeil a s k := by
  apply positiveSmallExpEdgeGapAtCeil_of_checkCell
  have hall :
      ∀ x ∈ positiveKRangeList a,
        (if x ≤ s then checkPositiveSmallExpEdgeAnchorCell a s x else true) = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveSmallExpEdgeAnchorCeil] using h)
  have hx := hall k (mem_positiveKRangeList_of_mem hk)
  simpa [hks] using hx

/-- Soundness of the executable small-edge row check. -/
theorem positiveSmallExpEdgeGapAtCeil_of_checkRow {a s k : Nat}
    (h : checkPositiveSmallExpEdgeAnchorRow a = true)
    (hs : s ∈ positiveSmallCeilRange a) (hk : k ∈ positiveKRange a)
    (hks : k ≤ s) :
    positiveSmallExpEdgeGapAtCeil a s k := by
  have hall :
      ∀ x ∈ positiveSmallCeilRangeList a,
        checkPositiveSmallExpEdgeAnchorCeil a x = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveSmallExpEdgeAnchorRow] using h)
  exact positiveSmallExpEdgeGapAtCeil_of_checkCeil
    (hall s (mem_positiveSmallCeilRangeList_of_mem hs)) hk hks

/-- Soundness of an executable range check for the plateau-anchor small edge. -/
theorem positiveSmallExpEdgeGapAtCeil_of_checkRange
    {lo len a s k : Nat}
    (h : checkPositiveSmallExpEdgeAnchorRange lo len = true)
    (ha_lo : lo ≤ a) (ha_hi : a < lo + len)
    (hs : s ∈ positiveSmallCeilRange a) (hk : k ∈ positiveKRange a)
    (hks : k ≤ s) :
    positiveSmallExpEdgeGapAtCeil a s k := by
  have hall :
      ∀ x ∈ List.range' lo len,
        checkPositiveSmallExpEdgeAnchorRow x = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveSmallExpEdgeAnchorRange] using h)
  exact positiveSmallExpEdgeGapAtCeil_of_checkRow
    (hall a ((List.mem_range'_1).mpr ⟨ha_lo, ha_hi⟩)) hs hk hks

/-- The full finite-window `smallExpEdgeAnchor` certificate field follows from
a range check over `401 ≤ a ≤ 2000`. -/
theorem positiveSmallExpEdgeAnchor_401_2000_of_checkRange
    (h : checkPositiveSmallExpEdgeAnchorRange 401 1600 = true) :
    ∀ {a s k : Nat}, 401 ≤ a → a ≤ 2000 →
      s ∈ positiveSmallCeilRange a → k ∈ positiveKRange a → k ≤ s →
        positiveSmallExpEdgeGapAtCeil a s k := by
  intro a s k ha h2000 hs hk hks
  exact positiveSmallExpEdgeGapAtCeil_of_checkRange
    (lo := 401) (len := 1600) h ha (by omega) hs hk hks

/-- Audit witness for the failed `ceilSqrt N` small-edge replacement path.

At the first row and the top ceiling-square-root plateau, the plateau-anchor
gap is false: replacing the actual `N` denominator by `posNhi a` loses more
than the stepwise `ceilSqrt` exponent surrogate gains.  This is why the
corrected interface uses `positiveSmallTangentExponentAt` instead. -/
theorem positiveSmallExpEdgeGapAtCeil_topPlateau_not :
    ¬ positiveSmallExpEdgeGapAtCeil 401 70 1 := by
  native_decide

/-- Soundness of one executable corrected tangent small-edge check. -/
theorem positiveSmallTangentExpEdgeGap_of_checkCell {a N k : Nat}
    (h : checkPositiveSmallTangentExpEdgeCell a N k = true) :
    positiveSmallTangentExpEdgeGap a N k := by
  exact of_decide_eq_true h

/-- Soundness of the executable corrected tangent small-edge check at one
`(a,N)`. -/
theorem positiveSmallTangentExpEdgeGap_of_checkAtN {a N k : Nat}
    (h : checkPositiveSmallTangentExpEdgeAtN a N = true)
    (hk : k ∈ positiveKRange a) (hsmall : k ≤ ceilSqrt N) :
    positiveSmallTangentExpEdgeGap a N k := by
  apply positiveSmallTangentExpEdgeGap_of_checkCell
  have hall :
      ∀ x ∈ positiveKRangeList a,
        (if x ≤ ceilSqrt N then checkPositiveSmallTangentExpEdgeCell a N x else true)
          = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveSmallTangentExpEdgeAtN] using h)
  have hx := hall k (mem_positiveKRangeList_of_mem hk)
  simpa [hsmall] using hx

/-- Soundness of one executable row check for the corrected tangent small edge. -/
theorem positiveSmallTangentExpEdgeGap_of_checkRow {a N k : Nat}
    (h : checkPositiveSmallTangentExpEdgeRow a = true)
    (hrect : positiveRectangle a N) (hk : k ∈ positiveKRange a)
    (hsmall : k ≤ ceilSqrt N) :
    positiveSmallTangentExpEdgeGap a N k := by
  have hall :
      ∀ x ∈ positiveNRangeList a,
        checkPositiveSmallTangentExpEdgeAtN a x = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveSmallTangentExpEdgeRow] using h)
  exact positiveSmallTangentExpEdgeGap_of_checkAtN
    (hall N (mem_positiveNRangeList_of_rectangle hrect)) hk hsmall

/-- Soundness of an executable range check for the corrected tangent small edge. -/
theorem positiveSmallTangentExpEdgeGap_of_checkRange
    {lo len a N k : Nat}
    (h : checkPositiveSmallTangentExpEdgeRange lo len = true)
    (ha_lo : lo ≤ a) (ha_hi : a < lo + len)
    (hrect : positiveRectangle a N) (hk : k ∈ positiveKRange a)
    (hsmall : k ≤ ceilSqrt N) :
    positiveSmallTangentExpEdgeGap a N k := by
  have hall :
      ∀ x ∈ List.range' lo len,
        checkPositiveSmallTangentExpEdgeRow x = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveSmallTangentExpEdgeRange] using h)
  exact positiveSmallTangentExpEdgeGap_of_checkRow
    (hall a ((List.mem_range'_1).mpr ⟨ha_lo, ha_hi⟩)) hrect hk hsmall

theorem checkPositiveSmallTangentExpEdgeRow_of_checkRange
    {lo len a : Nat}
    (h : checkPositiveSmallTangentExpEdgeRange lo len = true)
    (ha_lo : lo ≤ a) (ha_hi : a < lo + len) :
    checkPositiveSmallTangentExpEdgeRow a = true := by
  have hall :
      ∀ x ∈ List.range' lo len,
        checkPositiveSmallTangentExpEdgeRow x = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveSmallTangentExpEdgeRange] using h)
  exact hall a ((List.mem_range'_1).mpr ⟨ha_lo, ha_hi⟩)

/-- The full finite-window corrected `smallTangentEdge` certificate field
follows from a range check over `401 ≤ a ≤ 2000`. -/
theorem positiveSmallTangentEdge_401_2000_of_checkRange
    (h : checkPositiveSmallTangentExpEdgeRange 401 1600 = true) :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        positiveSmallTangentExpEdgeGap a N k := by
  intro a N k ha h2000 hrect hk hsmall
  exact positiveSmallTangentExpEdgeGap_of_checkRange
    (lo := 401) (len := 1600) h ha (by omega) hrect hk hsmall

theorem positiveEnvelopeBound_le_target_of_budgets
    {a : Nat} {soloBound : ℚ}
    (hsolo : soloBound ≤ positiveSoloBudget)
    (hedge : positiveEdgeMajorantSum a ≤ positiveEdgeBudget) :
    positiveEnvelopeBound a soloBound ≤ positiveTarget := by
  unfold positiveEnvelopeBound
  calc
    soloBound + positiveEdgeMajorantSum a
        ≤ positiveSoloBudget + positiveEdgeBudget := add_le_add hsolo hedge
    _ = positiveTarget := positiveSoloBudget_add_edgeBudget

theorem positiveEnvelopeBound_le_target_of_edgeBudget
    {a : Nat} (hedge : positiveEdgeMajorantSum a ≤ positiveEdgeBudget) :
    positiveEnvelopeBound a positiveSoloBudget ≤ positiveTarget :=
  positiveEnvelopeBound_le_target_of_budgets le_rfl hedge

theorem signLockMargin_pos_of_ge_361 {m : Nat} (hm : 361 ≤ m) :
    0 < signLockMargin m := by
  have hmargin := signLock_final_margin_of_ge_361 (m := m) hm
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  have hm2pos : (0 : ℚ) < (m : ℚ)^2 := by positivity
  unfold signLockMargin
  rw [sub_pos]
  rw [div_lt_iff₀ hm2pos]
  nlinarith

/-- The sign-lock margin is far larger than the §6 positive-part target on the
whole post-certificate range. -/
theorem positiveTarget_lt_signLockMargin_of_ge_401 {m : Nat} (hm : 401 ≤ m) :
    positiveTarget < signLockMargin m := by
  have hmQ : (401 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have hmpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
  have hfactor :
      (399/401 : ℚ) ≤ 1 - 2/(m : ℚ) := by
    have hdiv : (2 : ℚ) / (m : ℚ) ≤ 2 / 401 := by
      rw [div_le_div_iff₀ hmpos (by norm_num : (0 : ℚ) < 401)]
      nlinarith
    nlinarith
  have hfactor_exp :
      expNegLower50 * (399/401 : ℚ)
        ≤ expNegLower50 * (1 - 2/(m : ℚ)) :=
    mul_le_mul_of_nonneg_left hfactor expNegLower50_pos.le
  have hm_sq :
      (401 : ℚ)^2 ≤ (m : ℚ)^2 := by
    nlinarith
  have hbudget :
      2215 / (m : ℚ)^2 ≤ 2215 / (401 : ℚ)^2 := by
    exact div_le_div_of_nonneg_left
      (by norm_num : (0 : ℚ) ≤ 2215)
      (by norm_num : (0 : ℚ) < (401 : ℚ)^2)
      hm_sq
  have hendpoint :
      positiveTarget <
        expNegLower50 * (399/401 : ℚ) - 2215 / (401 : ℚ)^2 := by
    rw [expNegLower50_eq]
    norm_num [positiveTarget]
  have hlower :
      expNegLower50 * (399/401 : ℚ) - 2215 / (401 : ℚ)^2
        ≤ signLockMargin m := by
    unfold signLockMargin
    linarith
  exact hendpoint.trans_le hlower

theorem Xnorm_nonpos_of_signLockMargin_bound
    {N m : Nat} (hm : 361 ≤ m)
    (hX : Xnorm N m ≤ -signLockMargin m) :
    Xnorm N m ≤ 0 := by
  have hmargin := signLockMargin_pos_of_ge_361 hm
  linarith

theorem Xnorm_le_neg_signLockMargin_of_signLockNearBase
    {N m : Nat} (hN : 1 ≤ N)
    (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ)) (hm : 361 ≤ m)
    (hbase :
      expNegLower50 * (1 - 2/(m : ℚ)) ≤ signLockNearBase N m) :
    Xnorm N m ≤ -signLockMargin m := by
  unfold signLockMargin
  exact Xnorm_le_neg_final_margin_of_signLockNearBase
    (N := N) (m := m) hN hN40 hm hbase

theorem Xnorm_le_neg_signLockMargin_of_signLockBasePrefix_tail
    {N m : Nat} (hN : 1 ≤ N)
    (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ)) (hm : 361 ≤ m)
    (hprefix :
      expNegLower50 * (1 - 2/(m : ℚ)) ≤ signLockBasePrefix N m 12)
    (htail : 0 ≤ signLockBaseTailFrom12 N m) :
    Xnorm N m ≤ -signLockMargin m := by
  unfold signLockMargin
  exact Xnorm_le_neg_final_margin_of_signLockBasePrefix_tail
    (N := N) (m := m) hN hN40 hm hprefix htail

theorem Xnorm_le_neg_signLockMargin_of_signLockBasePrefix
    {N m : Nat} (hN : 1 ≤ N)
    (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ)) (hm : 361 ≤ m)
    (hprefix :
      expNegLower50 * (1 - 2/(m : ℚ)) ≤ signLockBasePrefix N m 12) :
    Xnorm N m ≤ -signLockMargin m :=
  Xnorm_le_neg_signLockMargin_of_signLockBasePrefix_tail
    (N := N) (m := m) hN hN40 hm hprefix
    (signLockBaseTailFrom12_nonneg (N := N) (m := m) hN40 hm)

theorem Xnorm_le_neg_signLockMargin
    {N m : Nat} (hN : 1 ≤ N)
    (hN40 : (N : ℚ) ≤ (40/3) * (m : ℚ)) (hm : 361 ≤ m) :
    Xnorm N m ≤ -signLockMargin m := by
  unfold signLockMargin
  exact Xnorm_le_neg_final_margin (N := N) (m := m) hN hN40 hm

/-- One normalized raw positive summand from `Unorm_eq`, without the positivity
guard. -/
def normalizedPositiveRawTerm (a N k : Nat) : ℚ :=
  Bq N k * Qq N (a-k) / ((N : ℚ) * c a)

/-- Paper §6's normalized `Y_j(N)`:
`Q_j(N) = (N/2)c_j 2^{-j}Y_j(N)`.  This is only a definition; the analytic
upper bounds on `Y_j` are supplied separately by the saddle certificate. -/
def Ynorm (N j : Nat) : ℚ :=
  Qq N j / (((N : ℚ) / 2) * c j / (2 : ℚ)^j)

/-- The coefficient ratio `R_{k,a}=c_k c_{a-k}/c_a` from paper §6. -/
def positiveCRatio (a k : Nat) : ℚ :=
  c k * c (posJ a k) / c a

/-- The factorized form of a raw positive summand used in paper §6 before
the small/tempered saddle estimates are inserted. -/
def positiveFactorizedRawTerm (a N k : Nat) : ℚ :=
  ((N : ℚ) / 2) * positiveCRatio a k *
    positiveDyadicDecay (posJ a k) * Xnorm N k * Ynorm N (posJ a k)

/-- One normalized raw positive summand with the same guard as `Unorm_eq`. -/
def normalizedPositiveIfTerm (a N k : Nat) : ℚ :=
  if 1 ≤ k ∧ 0 < Bq N k then normalizedPositiveRawTerm a N k else 0

/-- The full normalized positive sum appearing in `Unorm_eq`. -/
def normalizedPositiveRangeSum (a N : Nat) : ℚ :=
  ∑ k ∈ Finset.range a, normalizedPositiveIfTerm a N k

/-- The retained normalized positive sum after the `k > floor(0.9a)`
sign-lock exclusion. -/
def normalizedPositiveRetainedSum (a N : Nat) : ℚ :=
  ∑ k ∈ positiveKRange a, normalizedPositiveIfTerm a N k

theorem normalizedPositiveIfTerm_le_of_raw_le
    {a N k : Nat} {M : ℚ} (hM : 0 ≤ M)
    (hraw : 1 ≤ k → 0 < Bq N k → normalizedPositiveRawTerm a N k ≤ M) :
    normalizedPositiveIfTerm a N k ≤ M := by
  unfold normalizedPositiveIfTerm
  by_cases hguard : 1 ≤ k ∧ 0 < Bq N k
  · rw [if_pos hguard]
    exact hraw hguard.1 hguard.2
  · rw [if_neg hguard]
    exact hM

theorem Qq_nonneg (N j : Nat) : 0 ≤ Qq N j := by
  unfold Qq
  refine expCoeff_nonneg ?_ j
  intro r
  have hN : 0 ≤ (N : ℚ) := Nat.cast_nonneg N
  exact div_nonneg
    (mul_nonneg (div_nonneg hN (by norm_num)) (c_nonneg r))
    (by positivity)

theorem Ynorm_nonneg (N j : Nat) : 0 ≤ Ynorm N j := by
  unfold Ynorm
  have hN : 0 ≤ (N : ℚ) := Nat.cast_nonneg N
  exact div_nonneg (Qq_nonneg N j)
    (div_nonneg
      (mul_nonneg (div_nonneg hN (by norm_num)) (c_nonneg j))
      (by positivity))

/-- If the positive exponential majorant `XplusNorm` controls the product,
then the original `Xnorm` product is controlled too.  This is the Lean
bridge corresponding to the paper's replacement of `B_k(N)` by
`\overline B_k(N)` on the positive side. -/
theorem Xnorm_mul_Ynorm_le_of_Xplus_mul_Ynorm {N k j : Nat} {M : ℚ}
    (hXY : XplusNorm N k * Ynorm N j ≤ M) :
    Xnorm N k * Ynorm N j ≤ M := by
  exact (mul_le_mul_of_nonneg_right (Xnorm_le_XplusNorm N k)
    (Ynorm_nonneg N j)).trans hXY

/-- The exact positive-side linear/nonlinear decomposition, normalized as
`Y_j(N)`.  This is the `Y`/`Q` analogue of
`neg_Xnorm_eq_linear_Eminus_sum`: after the linear `c_1 X/2` exponential is
split off, the remaining coefficients are `Eplus`. -/
theorem Ynorm_eq_linear_Eplus_sum (N j : Nat) :
    Ynorm N j =
      (∑ s ∈ Finset.range (j+1),
        (((N : ℚ) / 2 * c 1 / 2)^s / (s.factorial : ℚ)) *
          Eplus (N : ℚ) (j-s))
        / (((N : ℚ) / 2) * c j / (2 : ℚ)^j) := by
  unfold Ynorm
  rw [Qq_eq_linear_Eplus_sum]

theorem positiveCRatio_nonneg (a k : Nat) : 0 ≤ positiveCRatio a k := by
  unfold positiveCRatio
  exact div_nonneg (mul_nonneg (c_nonneg k) (c_nonneg (posJ a k))) (c_nonneg a)

theorem positiveCRatio_pos {a k : Nat} (ha : 1 ≤ a) (hk : 1 ≤ k)
    (hj : 1 ≤ posJ a k) :
    0 < positiveCRatio a k := by
  unfold positiveCRatio
  exact div_pos (mul_pos (c_pos k hk) (c_pos (posJ a k) hj)) (c_pos a ha)

theorem positiveDyadicDecay_nonneg (j : Nat) : 0 ≤ positiveDyadicDecay j := by
  unfold positiveDyadicDecay
  positivity

theorem positiveDyadicDecay_pos (j : Nat) : 0 < positiveDyadicDecay j := by
  unfold positiveDyadicDecay
  positivity

theorem Qq_eq_yfactor_mul_Ynorm {N j : Nat} (hN : 1 ≤ N) (hj : 1 ≤ j) :
    Qq N j = ((N : ℚ) / 2) * c j / (2 : ℚ)^j * Ynorm N j := by
  have hden :
      ((N : ℚ) / 2) * c j / (2 : ℚ)^j ≠ 0 := by
    have hNQ : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
    have hcj : 0 < c j := c_pos j hj
    positivity
  unfold Ynorm
  rw [mul_comm]
  exact (div_mul_cancel₀ (Qq N j) hden).symm

theorem normalizedPositiveRawTerm_eq_Xnorm_mul_c
    {a N k : Nat} (hN : 1 ≤ N) (ha : 1 ≤ a) (hk : 1 ≤ k) :
    normalizedPositiveRawTerm a N k =
      Xnorm N k * c k * Qq N (a-k) / c a := by
  have hNQ : (N : ℚ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hca : c a ≠ 0 := (c_pos a ha).ne'
  have hck : c k ≠ 0 := (c_pos k hk).ne'
  unfold normalizedPositiveRawTerm Xnorm
  field_simp [hNQ, hca, hck]

theorem normalizedSoloTerm_eq_dyadic_Ynorm
    {a N : Nat} (hN : 1 ≤ N) (ha : 1 ≤ a) :
    normalizedSoloTerm a N = positiveDyadicDecay a / 2 * Ynorm N a := by
  have hNQ : (N : ℚ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hca : c a ≠ 0 := (c_pos a ha).ne'
  have hYden :
      ((N : ℚ) / 2) * c a / (2 : ℚ)^a ≠ 0 := by
    have hNpos : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
    have hcapos : 0 < c a := c_pos a ha
    positivity
  unfold normalizedSoloTerm Ynorm positiveDyadicDecay
  field_simp [hNQ, hca, hYden]

/-- The solo `Q_a` contribution after splitting off the linear exponential.
This is the exact finite-sum target for the remaining §6 solo estimate. -/
theorem normalizedSoloTerm_eq_linear_Eplus_sum
    {a N : Nat} (hN : 1 ≤ N) (ha : 1 ≤ a) :
    normalizedSoloTerm a N =
      (∑ s ∈ Finset.range (a+1),
        (((N : ℚ) / 2 * c 1 / 2)^s / (s.factorial : ℚ)) *
          Eplus (N : ℚ) (a-s)) / ((N : ℚ) * c a) := by
  have hNQ : (N : ℚ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hca : c a ≠ 0 := (c_pos a ha).ne'
  have hpow : (2 : ℚ)^a ≠ 0 := by positivity
  rw [normalizedSoloTerm_eq_dyadic_Ynorm hN ha,
    Ynorm_eq_linear_Eplus_sum]
  unfold positiveDyadicDecay
  field_simp [hNQ, hca, hpow]

/-- Explicit normalized upper bound for the solo `Q_a` term obtained from the
positive-side `Eplus`/`Gcomp` majorant. -/
def positiveSoloGcompBound (a N : Nat) : ℚ :=
  QqEplusGcompBound N a / ((N : ℚ) * c a)

/-- Boolean check that the explicit `Eplus`/`Gcomp` solo upper bound stays
within its half-target budget at one point of the positive rectangle. -/
def checkPositiveSoloGcompCell (a N : Nat) : Bool :=
  decide (positiveSoloGcompBound a N ≤ positiveSoloBudget)

/-- Boolean row check for the explicit solo bound over every `N` in the
positive rectangle at fixed `a`. -/
def checkPositiveSoloGcompRow (a : Nat) : Bool :=
  (positiveNRangeList a).all fun N => checkPositiveSoloGcompCell a N

/-- Boolean range check for the explicit solo bound over `a ∈ [lo, lo+len)`. -/
def checkPositiveSoloGcompRange (lo len : Nat) : Bool :=
  (List.range' lo len).all checkPositiveSoloGcompRow

theorem normalizedSoloTerm_le_positiveSoloGcompBound
    {a N : Nat} (hN : 1 ≤ N) (ha : 1 ≤ a) :
    normalizedSoloTerm a N ≤ positiveSoloGcompBound a N := by
  unfold normalizedSoloTerm positiveSoloGcompBound
  have hden : 0 ≤ (N : ℚ) * c a := by
    have hNQ : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
    exact mul_nonneg hNQ.le (c_pos a ha).le
  exact div_le_div_of_nonneg_right (Qq_le_EplusGcompBound N a) hden

theorem dyadic_Ynorm_le_positiveSoloGcompBound
    {a N : Nat} (hN : 1 ≤ N) (ha : 1 ≤ a) :
    positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloGcompBound a N := by
  rw [← normalizedSoloTerm_eq_dyadic_Ynorm hN ha]
  exact normalizedSoloTerm_le_positiveSoloGcompBound hN ha

/-- Soundness of one executable solo-bound point check. -/
theorem positiveSoloGcompBound_of_checkCell {a N : Nat}
    (h : checkPositiveSoloGcompCell a N = true) :
    positiveSoloGcompBound a N ≤ positiveSoloBudget := by
  exact of_decide_eq_true h

/-- Soundness of one executable solo-bound row check. -/
theorem positiveSoloGcompBound_of_checkRow {a N : Nat}
    (h : checkPositiveSoloGcompRow a = true)
    (hrect : positiveRectangle a N) :
    positiveSoloGcompBound a N ≤ positiveSoloBudget := by
  apply positiveSoloGcompBound_of_checkCell
  have hall :
      ∀ x ∈ positiveNRangeList a,
        checkPositiveSoloGcompCell a x = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveSoloGcompRow] using h)
  exact hall N (mem_positiveNRangeList_of_rectangle hrect)

/-- Soundness of an executable range check for the solo `Eplus`/`Gcomp` bound. -/
theorem positiveSoloGcompBound_of_checkRange
    {lo len a N : Nat}
    (h : checkPositiveSoloGcompRange lo len = true)
    (ha_lo : lo ≤ a) (ha_hi : a < lo + len)
    (hrect : positiveRectangle a N) :
    positiveSoloGcompBound a N ≤ positiveSoloBudget := by
  have hall :
      ∀ x ∈ List.range' lo len,
        checkPositiveSoloGcompRow x = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveSoloGcompRange] using h)
  exact positiveSoloGcompBound_of_checkRow
    (hall a ((List.mem_range'_1).mpr ⟨ha_lo, ha_hi⟩)) hrect

theorem checkPositiveSoloGcompRow_of_checkRange
    {lo len a : Nat}
    (h : checkPositiveSoloGcompRange lo len = true)
    (ha_lo : lo ≤ a) (ha_hi : a < lo + len) :
    checkPositiveSoloGcompRow a = true := by
  have hall :
      ∀ x ∈ List.range' lo len,
        checkPositiveSoloGcompRow x = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveSoloGcompRange] using h)
  exact hall a ((List.mem_range'_1).mpr ⟨ha_lo, ha_hi⟩)

/-- The finite-window solo certificate field follows from a single range
check over `401 ≤ a ≤ 2000`. -/
theorem dyadic_Ynorm_le_positiveSoloBudget_of_checkPositiveSoloGcompRange
    (h : checkPositiveSoloGcompRange 401 1600 = true) :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget := by
  intro a N ha ha2000 hrect
  have hN : 1 ≤ N := positiveRectangle_N_pos (by omega : 2 ≤ a) hrect
  calc
    positiveDyadicDecay a / 2 * Ynorm N a
        ≤ positiveSoloGcompBound a N :=
          dyadic_Ynorm_le_positiveSoloGcompBound hN (by omega : 1 ≤ a)
    _ ≤ positiveSoloBudget :=
          positiveSoloGcompBound_of_checkRange
            (lo := 401) (len := 1600) h ha (by omega) hrect

/-- Row-level solo certificate field from a generated row theorem. -/
theorem dyadic_Ynorm_le_positiveSoloBudget_of_checkPositiveSoloGcompRow
    {a N : Nat} (h : checkPositiveSoloGcompRow a = true)
    (ha : 401 ≤ a) (hrect : positiveRectangle a N) :
    positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget := by
  have hN : 1 ≤ N := positiveRectangle_N_pos (by omega : 2 ≤ a) hrect
  exact (dyadic_Ynorm_le_positiveSoloGcompBound hN (by omega : 1 ≤ a)).trans
    (positiveSoloGcompBound_of_checkRow h hrect)

/-- Normalized explicit `Gcomp` upper bound for the positive `X` majorant
`\overline X_k(N)`. -/
def positiveXplusGcompBound (N k : Nat) : ℚ :=
  BplusqGcompBound N k / ((N : ℚ) * c k)

theorem XplusNorm_le_positiveXplusGcompBound (N k : Nat) :
    XplusNorm N k ≤ positiveXplusGcompBound N k := by
  unfold XplusNorm positiveXplusGcompBound
  exact div_le_div_of_nonneg_right (Bplusq_le_GcompBound N k)
    (mul_nonneg (Nat.cast_nonneg N) (c_nonneg k))

/-- Explicit normalized `Eplus`/`Gcomp` upper bound for `Y_j(N)`. -/
def positiveYgcompBound (N j : Nat) : ℚ :=
  QqEplusGcompBound N j / (((N : ℚ) / 2) * c j / (2 : ℚ)^j)

theorem Ynorm_le_positiveYgcompBound (N j : Nat) :
    Ynorm N j ≤ positiveYgcompBound N j := by
  unfold Ynorm positiveYgcompBound
  have hden : 0 ≤ ((N : ℚ) / 2) * c j / (2 : ℚ)^j := by
    exact div_nonneg
      (mul_nonneg (div_nonneg (Nat.cast_nonneg N) (by norm_num)) (c_nonneg j))
      (by positivity)
  exact div_le_div_of_nonneg_right (Qq_le_EplusGcompBound N j) hden

theorem EplusGcompBound_nonneg (N p : Nat) :
    0 ≤ EplusGcompBound N p := by
  unfold EplusGcompBound
  refine Finset.sum_nonneg fun r _ => ?_
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg
        (pow_nonneg (div_nonneg (Nat.cast_nonneg N) (by norm_num)) r)
        (by positivity))
      (Gcomp_nonneg r p))
    (Nat.cast_nonneg _)

theorem QqEplusGcompBound_nonneg (N j : Nat) :
    0 ≤ QqEplusGcompBound N j := by
  unfold QqEplusGcompBound
  refine Finset.sum_nonneg fun s _ => ?_
  have hbase : 0 ≤ (N : ℚ) / 2 * c 1 / 2 := by
    norm_num [c_one]
    positivity
  exact mul_nonneg
    (div_nonneg (pow_nonneg hbase s) (Nat.cast_nonneg _))
    (EplusGcompBound_nonneg N (j-s))

theorem positiveYgcompBound_nonneg (N j : Nat) :
    0 ≤ positiveYgcompBound N j := by
  unfold positiveYgcompBound
  have hden : 0 ≤ ((N : ℚ) / 2) * c j / (2 : ℚ)^j := by
    exact div_nonneg
      (mul_nonneg (div_nonneg (Nat.cast_nonneg N) (by norm_num)) (c_nonneg j))
      (by positivity)
  exact div_nonneg (QqEplusGcompBound_nonneg N j) hden

theorem BplusNonlinearGcompBound_nonneg (N p : Nat) :
    0 ≤ BplusNonlinearGcompBound N p := by
  unfold BplusNonlinearGcompBound
  refine Finset.sum_nonneg fun r _ => ?_
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg
        (pow_nonneg (mul_nonneg (Nat.cast_nonneg N) (by norm_num)) r)
        (by positivity))
      (Gcomp_nonneg r p))
    (Nat.cast_nonneg _)

theorem BplusqGcompBound_nonneg (N k : Nat) :
    0 ≤ BplusqGcompBound N k := by
  unfold BplusqGcompBound
  refine Finset.sum_nonneg fun s _ => ?_
  have hbase : 0 ≤ (N : ℚ) * c 1 :=
    mul_nonneg (Nat.cast_nonneg N) (c_nonneg 1)
  exact mul_nonneg
    (div_nonneg (pow_nonneg hbase s) (Nat.cast_nonneg _))
    (BplusNonlinearGcompBound_nonneg N (k-s))

theorem positiveXplusGcompBound_nonneg (N k : Nat) :
    0 ≤ positiveXplusGcompBound N k := by
  unfold positiveXplusGcompBound
  exact div_nonneg (BplusqGcompBound_nonneg N k)
    (mul_nonneg (Nat.cast_nonneg N) (c_nonneg k))

/-- Fully explicit `Gcomp` product bound for the positive-side saddle product
`XplusNorm N k * Ynorm N (a-k)`. -/
def positiveXplusYProductGcompBound (a N k : Nat) : ℚ :=
  positiveXplusGcompBound N k * positiveYgcompBound N (posJ a k)

theorem XplusYnorm_le_positiveXplusYProductGcompBound (a N k : Nat) :
    XplusNorm N k * Ynorm N (posJ a k)
      ≤ positiveXplusYProductGcompBound a N k := by
  unfold positiveXplusYProductGcompBound
  calc
    XplusNorm N k * Ynorm N (posJ a k)
        ≤ positiveXplusGcompBound N k * Ynorm N (posJ a k) :=
          mul_le_mul_of_nonneg_right
            (XplusNorm_le_positiveXplusGcompBound N k)
            (Ynorm_nonneg N (posJ a k))
    _ ≤ positiveXplusGcompBound N k *
          positiveYgcompBound N (posJ a k) :=
          mul_le_mul_of_nonneg_left
            (Ynorm_le_positiveYgcompBound N (posJ a k))
            (positiveXplusGcompBound_nonneg N k)

/-- Point check that the explicit `Gcomp` product bound fits the corrected
small-regime tangent target. -/
def checkPositiveSmallXplusYProductGcompCell (a N k : Nat) : Bool :=
  decide (positiveXplusYProductGcompBound a N k ≤
    positiveSmallXYProductTangentBound a N k)

/-- Point check that the explicit `Gcomp` product bound fits the tempered
target. -/
def checkPositiveTemperedXplusYProductGcompCell (a N k : Nat) : Bool :=
  decide (positiveXplusYProductGcompBound a N k ≤
    positiveTemperedXYProductBound a N k)

/-- Check all small-regime retained `k` for one `(a,N)`. -/
def checkPositiveSmallXplusYProductGcompAtN (a N : Nat) : Bool :=
  (positiveKRangeList a).all fun k =>
    if k ≤ ceilSqrt N then checkPositiveSmallXplusYProductGcompCell a N k else true

/-- Check all tempered-regime retained `k` for one `(a,N)`. -/
def checkPositiveTemperedXplusYProductGcompAtN (a N : Nat) : Bool :=
  (positiveKRangeList a).all fun k =>
    if ceilSqrt N < k then checkPositiveTemperedXplusYProductGcompCell a N k else true

/-- Row check for the small-regime explicit `Xplus*Y` product bound. -/
def checkPositiveSmallXplusYProductGcompRow (a : Nat) : Bool :=
  (positiveNRangeList a).all fun N =>
    checkPositiveSmallXplusYProductGcompAtN a N

/-- Row check for the tempered-regime explicit `Xplus*Y` product bound. -/
def checkPositiveTemperedXplusYProductGcompRow (a : Nat) : Bool :=
  (positiveNRangeList a).all fun N =>
    checkPositiveTemperedXplusYProductGcompAtN a N

/-- Range check for the small-regime explicit `Xplus*Y` product bound over
`a ∈ [lo, lo+len)`. -/
def checkPositiveSmallXplusYProductGcompRange (lo len : Nat) : Bool :=
  (List.range' lo len).all checkPositiveSmallXplusYProductGcompRow

/-- Range check for the tempered-regime explicit `Xplus*Y` product bound over
`a ∈ [lo, lo+len)`. -/
def checkPositiveTemperedXplusYProductGcompRange (lo len : Nat) : Bool :=
  (List.range' lo len).all checkPositiveTemperedXplusYProductGcompRow

/-- Soundness of one small-regime explicit `Xplus*Y` product check. -/
theorem positiveSmallXplusYProductGcompBound_of_checkCell {a N k : Nat}
    (h : checkPositiveSmallXplusYProductGcompCell a N k = true) :
    positiveXplusYProductGcompBound a N k ≤
      positiveSmallXYProductTangentBound a N k := by
  exact of_decide_eq_true h

/-- Soundness of one tempered-regime explicit `Xplus*Y` product check. -/
theorem positiveTemperedXplusYProductGcompBound_of_checkCell {a N k : Nat}
    (h : checkPositiveTemperedXplusYProductGcompCell a N k = true) :
    positiveXplusYProductGcompBound a N k ≤
      positiveTemperedXYProductBound a N k := by
  exact of_decide_eq_true h

/-- Soundness of the small-regime product check at one `(a,N)`. -/
theorem positiveSmallXplusYProductGcompBound_of_checkAtN
    {a N k : Nat}
    (h : checkPositiveSmallXplusYProductGcompAtN a N = true)
    (hk : k ∈ positiveKRange a) (hsmall : k ≤ ceilSqrt N) :
    positiveXplusYProductGcompBound a N k ≤
      positiveSmallXYProductTangentBound a N k := by
  apply positiveSmallXplusYProductGcompBound_of_checkCell
  have hall :
      ∀ x ∈ positiveKRangeList a,
        (if x ≤ ceilSqrt N then checkPositiveSmallXplusYProductGcompCell a N x
          else true) = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveSmallXplusYProductGcompAtN] using h)
  have hx := hall k (mem_positiveKRangeList_of_mem hk)
  simpa [hsmall] using hx

/-- Soundness of the tempered-regime product check at one `(a,N)`. -/
theorem positiveTemperedXplusYProductGcompBound_of_checkAtN
    {a N k : Nat}
    (h : checkPositiveTemperedXplusYProductGcompAtN a N = true)
    (hk : k ∈ positiveKRange a) (htempered : ceilSqrt N < k) :
    positiveXplusYProductGcompBound a N k ≤
      positiveTemperedXYProductBound a N k := by
  apply positiveTemperedXplusYProductGcompBound_of_checkCell
  have hall :
      ∀ x ∈ positiveKRangeList a,
        (if ceilSqrt N < x then checkPositiveTemperedXplusYProductGcompCell a N x
          else true) = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveTemperedXplusYProductGcompAtN] using h)
  have hx := hall k (mem_positiveKRangeList_of_mem hk)
  simpa [htempered] using hx

/-- Soundness of a small-regime product row check. -/
theorem positiveSmallXplusYProductGcompBound_of_checkRow
    {a N k : Nat}
    (h : checkPositiveSmallXplusYProductGcompRow a = true)
    (hrect : positiveRectangle a N) (hk : k ∈ positiveKRange a)
    (hsmall : k ≤ ceilSqrt N) :
    positiveXplusYProductGcompBound a N k ≤
      positiveSmallXYProductTangentBound a N k := by
  have hall :
      ∀ x ∈ positiveNRangeList a,
        checkPositiveSmallXplusYProductGcompAtN a x = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveSmallXplusYProductGcompRow] using h)
  exact positiveSmallXplusYProductGcompBound_of_checkAtN
    (hall N (mem_positiveNRangeList_of_rectangle hrect)) hk hsmall

/-- Soundness of a tempered-regime product row check. -/
theorem positiveTemperedXplusYProductGcompBound_of_checkRow
    {a N k : Nat}
    (h : checkPositiveTemperedXplusYProductGcompRow a = true)
    (hrect : positiveRectangle a N) (hk : k ∈ positiveKRange a)
    (htempered : ceilSqrt N < k) :
    positiveXplusYProductGcompBound a N k ≤
      positiveTemperedXYProductBound a N k := by
  have hall :
      ∀ x ∈ positiveNRangeList a,
        checkPositiveTemperedXplusYProductGcompAtN a x = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveTemperedXplusYProductGcompRow] using h)
  exact positiveTemperedXplusYProductGcompBound_of_checkAtN
    (hall N (mem_positiveNRangeList_of_rectangle hrect)) hk htempered

/-- Soundness of a small-regime product range check. -/
theorem positiveSmallXplusYProductGcompBound_of_checkRange
    {lo len a N k : Nat}
    (h : checkPositiveSmallXplusYProductGcompRange lo len = true)
    (ha_lo : lo ≤ a) (ha_hi : a < lo + len)
    (hrect : positiveRectangle a N) (hk : k ∈ positiveKRange a)
    (hsmall : k ≤ ceilSqrt N) :
    positiveXplusYProductGcompBound a N k ≤
      positiveSmallXYProductTangentBound a N k := by
  have hall :
      ∀ x ∈ List.range' lo len,
        checkPositiveSmallXplusYProductGcompRow x = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveSmallXplusYProductGcompRange] using h)
  exact positiveSmallXplusYProductGcompBound_of_checkRow
    (hall a ((List.mem_range'_1).mpr ⟨ha_lo, ha_hi⟩)) hrect hk hsmall

theorem checkPositiveSmallXplusYProductGcompRow_of_checkRange
    {lo len a : Nat}
    (h : checkPositiveSmallXplusYProductGcompRange lo len = true)
    (ha_lo : lo ≤ a) (ha_hi : a < lo + len) :
    checkPositiveSmallXplusYProductGcompRow a = true := by
  have hall :
      ∀ x ∈ List.range' lo len,
        checkPositiveSmallXplusYProductGcompRow x = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveSmallXplusYProductGcompRange] using h)
  exact hall a ((List.mem_range'_1).mpr ⟨ha_lo, ha_hi⟩)

/-- Soundness of a tempered-regime product range check. -/
theorem positiveTemperedXplusYProductGcompBound_of_checkRange
    {lo len a N k : Nat}
    (h : checkPositiveTemperedXplusYProductGcompRange lo len = true)
    (ha_lo : lo ≤ a) (ha_hi : a < lo + len)
    (hrect : positiveRectangle a N) (hk : k ∈ positiveKRange a)
    (htempered : ceilSqrt N < k) :
    positiveXplusYProductGcompBound a N k ≤
      positiveTemperedXYProductBound a N k := by
  have hall :
      ∀ x ∈ List.range' lo len,
        checkPositiveTemperedXplusYProductGcompRow x = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveTemperedXplusYProductGcompRange] using h)
  exact positiveTemperedXplusYProductGcompBound_of_checkRow
    (hall a ((List.mem_range'_1).mpr ⟨ha_lo, ha_hi⟩)) hrect hk htempered

theorem checkPositiveTemperedXplusYProductGcompRow_of_checkRange
    {lo len a : Nat}
    (h : checkPositiveTemperedXplusYProductGcompRange lo len = true)
    (ha_lo : lo ≤ a) (ha_hi : a < lo + len) :
    checkPositiveTemperedXplusYProductGcompRow a = true := by
  have hall :
      ∀ x ∈ List.range' lo len,
        checkPositiveTemperedXplusYProductGcompRow x = true := by
    exact List.all_eq_true.mp (by
      simpa [checkPositiveTemperedXplusYProductGcompRange] using h)
  exact hall a ((List.mem_range'_1).mpr ⟨ha_lo, ha_hi⟩)

/-- The full finite-window small-regime `Xplus*Y` product field follows from a
range check over `401 ≤ a ≤ 2000`. -/
theorem positiveSmallXplusYProductGcomp_401_2000_of_checkRange
    (h : checkPositiveSmallXplusYProductGcompRange 401 1600 = true) :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        positiveXplusYProductGcompBound a N k ≤
          positiveSmallXYProductTangentBound a N k := by
  intro a N k ha h2000 hrect hk hsmall
  exact positiveSmallXplusYProductGcompBound_of_checkRange
    (lo := 401) (len := 1600) h ha (by omega) hrect hk hsmall

/-- The full finite-window tempered-regime `Xplus*Y` product field follows from
a range check over `401 ≤ a ≤ 2000`. -/
theorem positiveTemperedXplusYProductGcomp_401_2000_of_checkRange
    (h : checkPositiveTemperedXplusYProductGcompRange 401 1600 = true) :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k →
        positiveXplusYProductGcompBound a N k ≤
          positiveTemperedXYProductBound a N k := by
  intro a N k ha h2000 hrect hk htempered
  exact positiveTemperedXplusYProductGcompBound_of_checkRange
    (lo := 401) (len := 1600) h ha (by omega) hrect hk htempered

/-- A list of half-open chunks covers the finite positive-saddle window. -/
def PositiveSaddleFiniteWindowChunkCover
    (chunks : List (Nat × Nat)) : Prop :=
  ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
    ∃ chunk : Nat × Nat,
      chunk ∈ chunks ∧ chunk.1 ≤ a ∧ a < chunk.1 + chunk.2

/-- Generic extraction of one row from a verified range chunk covering it. -/
theorem checkRow_of_checkRangeChunks
    {row : Nat → Bool} {chunks : List (Nat × Nat)} {a : Nat}
    (hchunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ chunks →
        (List.range' chunk.1 chunk.2).all row = true)
    (hcover :
      ∃ chunk : Nat × Nat,
        chunk ∈ chunks ∧ chunk.1 ≤ a ∧ a < chunk.1 + chunk.2) :
    row a = true := by
  rcases hcover with ⟨chunk, hmem, hlo, hhi⟩
  have hall : ∀ x ∈ List.range' chunk.1 chunk.2, row x = true := by
    exact List.all_eq_true.mp (hchunks (chunk := chunk) hmem)
  exact hall a ((List.mem_range'_1).mpr ⟨hlo, hhi⟩)

theorem checkPositiveSmallXplusYProductGcompRow_of_checkRangeChunks
    {chunks : List (Nat × Nat)} {a : Nat}
    (hchunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ chunks →
        checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true)
    (hcover :
      ∃ chunk : Nat × Nat,
        chunk ∈ chunks ∧ chunk.1 ≤ a ∧ a < chunk.1 + chunk.2) :
    checkPositiveSmallXplusYProductGcompRow a = true := by
  exact checkRow_of_checkRangeChunks
    (row := checkPositiveSmallXplusYProductGcompRow)
    (chunks := chunks) (a := a)
    (by
      intro chunk hmem
      simpa [checkPositiveSmallXplusYProductGcompRange]
        using hchunks (chunk := chunk) hmem)
    hcover

theorem checkPositiveTemperedXplusYProductGcompRow_of_checkRangeChunks
    {chunks : List (Nat × Nat)} {a : Nat}
    (hchunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ chunks →
        checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true)
    (hcover :
      ∃ chunk : Nat × Nat,
        chunk ∈ chunks ∧ chunk.1 ≤ a ∧ a < chunk.1 + chunk.2) :
    checkPositiveTemperedXplusYProductGcompRow a = true := by
  exact checkRow_of_checkRangeChunks
    (row := checkPositiveTemperedXplusYProductGcompRow)
    (chunks := chunks) (a := a)
    (by
      intro chunk hmem
      simpa [checkPositiveTemperedXplusYProductGcompRange]
        using hchunks (chunk := chunk) hmem)
    hcover

theorem checkPositiveSmallTangentExpEdgeRow_of_checkRangeChunks
    {chunks : List (Nat × Nat)} {a : Nat}
    (hchunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ chunks →
        checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true)
    (hcover :
      ∃ chunk : Nat × Nat,
        chunk ∈ chunks ∧ chunk.1 ≤ a ∧ a < chunk.1 + chunk.2) :
    checkPositiveSmallTangentExpEdgeRow a = true := by
  exact checkRow_of_checkRangeChunks
    (row := checkPositiveSmallTangentExpEdgeRow)
    (chunks := chunks) (a := a)
    (by
      intro chunk hmem
      simpa [checkPositiveSmallTangentExpEdgeRange]
        using hchunks (chunk := chunk) hmem)
    hcover

theorem checkPositiveSoloGcompRow_of_checkRangeChunks
    {chunks : List (Nat × Nat)} {a : Nat}
    (hchunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ chunks →
        checkPositiveSoloGcompRange chunk.1 chunk.2 = true)
    (hcover :
      ∃ chunk : Nat × Nat,
        chunk ∈ chunks ∧ chunk.1 ≤ a ∧ a < chunk.1 + chunk.2) :
    checkPositiveSoloGcompRow a = true := by
  exact checkRow_of_checkRangeChunks
    (row := checkPositiveSoloGcompRow)
    (chunks := chunks) (a := a)
    (by
      intro chunk hmem
      simpa [checkPositiveSoloGcompRange]
        using hchunks (chunk := chunk) hmem)
    hcover

theorem checkPositiveEdgeBudgetRow_of_checkPositiveEdgeBudgetRangeChunks
    {chunks : List (Nat × Nat)} {a : Nat}
    (hchunks :
      ∀ {chunk : Nat × Nat}, chunk ∈ chunks →
        checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true)
    (hcover :
      ∃ chunk : Nat × Nat,
        chunk ∈ chunks ∧ chunk.1 ≤ a ∧ a < chunk.1 + chunk.2) :
    checkPositiveEdgeBudgetRow a = true := by
  exact checkRow_of_checkRangeChunks
    (row := checkPositiveEdgeBudgetRow)
    (chunks := chunks) (a := a)
    (by
      intro chunk hmem
      simpa [checkPositiveEdgeBudgetRange]
        using hchunks (chunk := chunk) hmem)
    hcover

/-- Exact algebraic form of the raw §6 summand before analytic saddle
estimates are inserted:
`B_k Q_{a-k}/(N c_a) = (N/2) R_{k,a} 2^{-(a-k)} X_k Y_{a-k}`. -/
theorem normalizedPositiveRawTerm_eq_Xnorm_Ynorm
    {a N k : Nat} (hN : 1 ≤ N) (ha : 1 ≤ a) (hk : 1 ≤ k)
    (hj : 1 ≤ posJ a k) :
    normalizedPositiveRawTerm a N k = positiveFactorizedRawTerm a N k := by
  have hNQ : (N : ℚ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hca : c a ≠ 0 := (c_pos a ha).ne'
  have hck : c k ≠ 0 := (c_pos k hk).ne'
  have hcj : c (posJ a k) ≠ 0 := (c_pos (posJ a k) hj).ne'
  have hYden :
      ((N : ℚ) / 2) * c (posJ a k) / (2 : ℚ)^(posJ a k) ≠ 0 := by
    have hNpos : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
    have hcjpos : 0 < c (posJ a k) := c_pos (posJ a k) hj
    positivity
  unfold normalizedPositiveRawTerm
  change Bq N k * Qq N (posJ a k) / ((N : ℚ) * c a) =
      positiveFactorizedRawTerm a N k
  unfold positiveFactorizedRawTerm Xnorm Ynorm positiveCRatio positiveDyadicDecay
  field_simp [hNQ, hca, hck, hcj, hYden]

theorem normalizedPositiveRawTerm_nonneg_of_Bq_nonneg
    {a N k : Nat} (hN : 1 ≤ N) (ha : 1 ≤ a) (hB : 0 ≤ Bq N k) :
    0 ≤ normalizedPositiveRawTerm a N k := by
  have hNQ : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  have hca : 0 < c a := c_pos a ha
  unfold normalizedPositiveRawTerm
  exact div_nonneg (mul_nonneg hB (Qq_nonneg N (a-k)))
    (mul_nonneg hNQ.le hca.le)

theorem normalizedPositiveRawTerm_nonpos_of_Bq_nonpos
    {a N k : Nat} (hN : 1 ≤ N) (ha : 1 ≤ a) (hB : Bq N k ≤ 0) :
    normalizedPositiveRawTerm a N k ≤ 0 := by
  have hNQ : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  have hca : 0 < c a := c_pos a ha
  unfold normalizedPositiveRawTerm
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg hB (Qq_nonneg N (a-k)))
    (mul_nonneg hNQ.le hca.le)

/-- To prove a raw positive summand is below a nonnegative majorant, it is
enough to prove the factorized §6 bound in the only case that matters,
`B_k(N)>0`.  If `B_k(N)≤0`, the raw summand is already nonpositive. -/
theorem normalizedPositiveRawTerm_le_of_factorized_bound
    {a N k : Nat} {M : ℚ} (hN : 1 ≤ N) (ha : 1 ≤ a) (hk : 1 ≤ k)
    (hj : 1 ≤ posJ a k) (hM : 0 ≤ M)
    (hfactor : 0 < Bq N k → positiveFactorizedRawTerm a N k ≤ M) :
    normalizedPositiveRawTerm a N k ≤ M := by
  by_cases hB : 0 < Bq N k
  · rw [normalizedPositiveRawTerm_eq_Xnorm_Ynorm hN ha hk hj]
    exact hfactor hB
  · exact (normalizedPositiveRawTerm_nonpos_of_Bq_nonpos hN ha
      (le_of_not_gt hB)).trans hM

theorem normalizedPositiveIfTerm_nonneg
    {a N k : Nat} (hN : 1 ≤ N) (ha : 1 ≤ a) :
    0 ≤ normalizedPositiveIfTerm a N k := by
  unfold normalizedPositiveIfTerm
  by_cases hguard : 1 ≤ k ∧ 0 < Bq N k
  · rw [if_pos hguard]
    exact normalizedPositiveRawTerm_nonneg_of_Bq_nonneg hN ha hguard.2.le
  · rw [if_neg hguard]

theorem Bq_pos_iff_Xnorm_pos {N k : Nat} (hN : 1 ≤ N) (hk : 1 ≤ k) :
    0 < Bq N k ↔ 0 < Xnorm N k := by
  have hNQ : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  have hcQ : 0 < c k := c_pos k hk
  have hden : 0 < (N : ℚ) * c k := mul_pos hNQ hcQ
  unfold Xnorm
  constructor
  · intro hB
    exact div_pos hB hden
  · intro hX
    have hmul : 0 < (Bq N k / ((N : ℚ) * c k)) * ((N : ℚ) * c k) :=
      mul_pos hX hden
    rwa [div_mul_cancel₀ _ hden.ne'] at hmul

theorem not_Bq_pos_of_Xnorm_nonpos {N k : Nat} (hN : 1 ≤ N) (hk : 1 ≤ k)
    (hX : Xnorm N k ≤ 0) :
    ¬ 0 < Bq N k := by
  intro hB
  have hXpos := (Bq_pos_iff_Xnorm_pos hN hk).mp hB
  linarith

/-- Monotonicity bridge for the factorized positive summand: once `B_k(N)>0`,
independent upper bounds for the coefficient ratio, `X_k(N)`, and
`Y_{a-k}(N)` multiply to an upper bound for the factorized summand. -/
theorem positiveFactorizedRawTerm_le_of_bounds
    {a N k : Nat} {R X Y : ℚ} (hN : 1 ≤ N) (hk : 1 ≤ k)
    (hB : 0 < Bq N k)
    (hR : positiveCRatio a k ≤ R)
    (hX : Xnorm N k ≤ X)
    (hY : Ynorm N (posJ a k) ≤ Y) :
    positiveFactorizedRawTerm a N k ≤
      ((N : ℚ) / 2) * R * positiveDyadicDecay (posJ a k) * X * Y := by
  have hNhalf : 0 ≤ (N : ℚ) / 2 := by positivity
  have hR0 : 0 ≤ positiveCRatio a k := positiveCRatio_nonneg a k
  have hX0 : 0 ≤ Xnorm N k := ((Bq_pos_iff_Xnorm_pos hN hk).mp hB).le
  have hY0 : 0 ≤ Ynorm N (posJ a k) := Ynorm_nonneg N (posJ a k)
  have hRtarget : 0 ≤ R := hR0.trans hR
  have hXtarget : 0 ≤ X := hX0.trans hX
  have hYtarget : 0 ≤ Y := hY0.trans hY
  unfold positiveFactorizedRawTerm
  gcongr
  · exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hNhalf hRtarget)
        (positiveDyadicDecay_nonneg (posJ a k)))
      hXtarget
  · exact mul_nonneg
      (mul_nonneg hNhalf hRtarget)
      (positiveDyadicDecay_nonneg (posJ a k))
  · exact positiveDyadicDecay_nonneg (posJ a k)

theorem normalizedPositiveIfTerm_eq_guard_div (a N k : Nat) :
    normalizedPositiveIfTerm a N k
      =
    (if 1 ≤ k ∧ 0 < Bq N k then Bq N k * Qq N (a-k) else 0)
      / ((N : ℚ) * c a) := by
  unfold normalizedPositiveIfTerm normalizedPositiveRawTerm
  split <;> ring

theorem normalizedPositiveRangeSum_eq_guard_div (a N : Nat) :
    normalizedPositiveRangeSum a N
      =
    (∑ k ∈ Finset.range a,
        (if 1 ≤ k ∧ 0 < Bq N k then Bq N k * Qq N (a-k) else 0))
      / ((N : ℚ) * c a) := by
  unfold normalizedPositiveRangeSum
  calc
    ∑ k ∈ Finset.range a, normalizedPositiveIfTerm a N k
        =
      ∑ k ∈ Finset.range a,
        ((if 1 ≤ k ∧ 0 < Bq N k then Bq N k * Qq N (a-k) else 0)
          / ((N : ℚ) * c a)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          exact normalizedPositiveIfTerm_eq_guard_div a N k
    _ =
      (∑ k ∈ Finset.range a,
        (if 1 ≤ k ∧ 0 < Bq N k then Bq N k * Qq N (a-k) else 0))
      / ((N : ℚ) * c a) := by
        rw [← Finset.sum_div]

/-- Algebraic form of paper equation `(Unorm)`: `Unorm` splits into the
sign-lock term, the solo `Q_a` term, and the guarded positive sum. -/
theorem Unorm_eq_Xnorm_add_solo_add_positive (a N : Nat) :
    Unorm a N =
      Xnorm N a + normalizedSoloTerm a N + normalizedPositiveRangeSum a N := by
  rw [Unorm_eq, normalizedPositiveRangeSum_eq_guard_div]
  unfold Xnorm normalizedSoloTerm
  ring

theorem positiveKRange_subset_range {a : Nat} (ha : 1 ≤ a) :
    positiveKRange a ⊆ Finset.range a := by
  intro k hk
  rcases (mem_positiveKRange.mp hk) with ⟨_hk1, hkmax⟩
  exact Finset.mem_range.mpr (lt_self_of_le_posKmax ha hkmax)

/-- Restrict the guarded positive sum to the retained `k` range once all
larger `k < a` have nonpositive `Bq`. -/
theorem normalizedPositiveRangeSum_eq_retained_of_large_nonpos
    {a N : Nat} (ha : 1 ≤ a)
    (hlarge : ∀ k, k < a → posKmax a < k → ¬ 0 < Bq N k) :
    normalizedPositiveRangeSum a N = normalizedPositiveRetainedSum a N := by
  unfold normalizedPositiveRangeSum normalizedPositiveRetainedSum
  symm
  apply Finset.sum_subset (positiveKRange_subset_range ha)
  intro k hkRange hkNot
  have hklt : k < a := Finset.mem_range.mp hkRange
  by_cases hk1 : 1 ≤ k
  · have hklarge : posKmax a < k := by
      by_contra hnot
      exact hkNot (mem_positiveKRange.mpr ⟨hk1, Nat.le_of_not_gt hnot⟩)
    have hnotB : ¬ 0 < Bq N k := hlarge k hklt hklarge
    simp [normalizedPositiveIfTerm, hnotB]
  · have hguard : ¬ (1 ≤ k ∧ 0 < Bq N k) := fun h => hk1 h.1
    simp [normalizedPositiveIfTerm, hguard]

/-- Variant of `normalizedPositiveRangeSum_eq_retained_of_large_nonpos`
using the normalized sign-lock quantity `Xnorm`. -/
theorem normalizedPositiveRangeSum_eq_retained_of_large_Xnorm_nonpos
    {a N : Nat} (ha : 1 ≤ a) (hN : 1 ≤ N)
    (hlarge : ∀ k, k < a → posKmax a < k → 1 ≤ k → Xnorm N k ≤ 0) :
    normalizedPositiveRangeSum a N = normalizedPositiveRetainedSum a N :=
  normalizedPositiveRangeSum_eq_retained_of_large_nonpos (a := a) (N := N) ha
    fun k hklt hklarge =>
      not_Bq_pos_of_Xnorm_nonpos hN (by omega : 1 ≤ k)
        (hlarge k hklt hklarge (by omega : 1 ≤ k))

/-- The rectangle arithmetic needed to feed the sign-lock theorem into the
large-`k` exclusion in §6. -/
theorem large_Xnorm_nonpos_of_signLock_nonpos
    {a N : Nat} (ha : 401 ≤ a) (hrect : positiveRectangle a N)
    (hSL : ∀ k : Nat, 361 ≤ k →
      (N : ℚ) ≤ (40/3) * (k : ℚ) → Xnorm N k ≤ 0) :
    ∀ k, k < a → posKmax a < k → 1 ≤ k → Xnorm N k ≤ 0 := by
  intro k _hklt hklarge _hk1
  exact hSL k
    (signLock_m_ge_of_posKmax_lt ha hklarge)
    (rectangle_N_le_signLock_range_of_posKmax_lt hrect hklarge)

theorem normalizedPositiveRangeSum_eq_retained_of_signLock_nonpos
    {a N : Nat} (ha : 401 ≤ a) (hrect : positiveRectangle a N)
    (hSL : ∀ k : Nat, 361 ≤ k →
      (N : ℚ) ≤ (40/3) * (k : ℚ) → Xnorm N k ≤ 0) :
    normalizedPositiveRangeSum a N = normalizedPositiveRetainedSum a N := by
  exact normalizedPositiveRangeSum_eq_retained_of_large_Xnorm_nonpos
    (a := a) (N := N) (by omega : 1 ≤ a)
    (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect)
    (large_Xnorm_nonpos_of_signLock_nonpos ha hrect hSL)

theorem Unorm_eq_Xnorm_add_solo_add_retained_of_large_Xnorm_nonpos
    {a N : Nat} (ha : 1 ≤ a) (hN : 1 ≤ N)
    (hlarge : ∀ k, k < a → posKmax a < k → 1 ≤ k → Xnorm N k ≤ 0) :
    Unorm a N =
      Xnorm N a + normalizedSoloTerm a N + normalizedPositiveRetainedSum a N := by
  rw [Unorm_eq_Xnorm_add_solo_add_positive,
    normalizedPositiveRangeSum_eq_retained_of_large_Xnorm_nonpos ha hN hlarge]

theorem Unorm_eq_Xnorm_add_solo_add_retained_of_signLock_nonpos
    {a N : Nat} (ha : 401 ≤ a) (hrect : positiveRectangle a N)
    (hSL : ∀ k : Nat, 361 ≤ k →
      (N : ℚ) ≤ (40/3) * (k : ℚ) → Xnorm N k ≤ 0) :
    Unorm a N =
      Xnorm N a + normalizedSoloTerm a N + normalizedPositiveRetainedSum a N := by
  rw [Unorm_eq_Xnorm_add_solo_add_positive,
    normalizedPositiveRangeSum_eq_retained_of_signLock_nonpos ha hrect hSL]

theorem positiveBinomDen_pos {a k : Nat} (ha : 2 ≤ a) (hk1 : 1 ≤ k)
    (hkmax : k ≤ posKmax a) :
    0 < positiveBinomDen a k := by
  unfold positiveBinomDen
  have hka : k < a := lt_self_of_le_posKmax (by omega : 1 ≤ a) hkmax
  exact Nat.choose_pos (by omega : k - 1 ≤ a - 2)

theorem positiveBinomRatio_nonneg {a k : Nat} :
    0 ≤ positiveBinomRatio a k := by
  unfold positiveBinomRatio
  positivity

theorem positiveBinomRatio_pos {a k : Nat} (ha : 2 ≤ a) (hk1 : 1 ≤ k)
    (hkmax : k ≤ posKmax a) :
    0 < positiveBinomRatio a k := by
  have ha1 : (0 : ℚ) < ((a-1 : Nat) : ℚ) := by
    exact_mod_cast (by omega : 0 < a-1)
  have hchoose : (0 : ℚ) < (positiveBinomDen a k : ℚ) := by
    exact_mod_cast positiveBinomDen_pos ha hk1 hkmax
  unfold positiveBinomRatio
  positivity

/-! ### Binomial tail helper for the positive saddle

The latest TeX uses the sharper entropy lower bound for
`choose (a-2) (k-1)` in the `a > 2000` tail.  The Lean route keeps this
standard rational shadow explicit: `C(n,k) ≥ (n/k)^k`.  It is weaker than the
printed entropy estimate, but it is a mechanically checkable combinatorial
bridge for the same denominator-growth step and can be strengthened later
without changing the finite certificate interface. -/

theorem choose_ge_pow_div_pow {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n) :
    ((n : ℚ) / (k : ℚ))^k ≤ ((n.choose k : Nat) : ℚ) := by
  have hkpos : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
  have hfacpos : (0 : ℚ) < (k.factorial : ℚ) := by
    exact_mod_cast k.factorial_pos
  have hasc :
      (((n - k + 1).ascFactorial k : Nat) : ℚ)
        = ((n.choose k : Nat) : ℚ) * (k.factorial : ℚ) := by
    have htop : n - k + 1 + k - 1 = n := by omega
    calc
      (((n - k + 1).ascFactorial k : Nat) : ℚ)
          = ((k.factorial * ((n - k + 1 + k - 1).choose k) : Nat) : ℚ) := by
              rw [Nat.ascFactorial_eq_factorial_mul_choose']
      _ = (k.factorial : ℚ) * ((n.choose k : Nat) : ℚ) := by
              simp [Nat.cast_mul, htop]
      _ = ((n.choose k : Nat) : ℚ) * (k.factorial : ℚ) := by ring
  have hprod :
      ((n : ℚ) / (k : ℚ))^k * (k.factorial : ℚ)
        ≤ (((n - k + 1).ascFactorial k : Nat) : ℚ) := by
    rw [Nat.ascFactorial_eq_prod_range, Nat.factorial_eq_prod_range_add_one]
    push_cast
    rw [Finset.pow_eq_prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod ?_ ?_
    · intro i hi
      exact mul_nonneg (div_nonneg (by positivity) hkpos.le) (by positivity)
    · intro i hi
      have hi_lt : i < k := Finset.mem_range.mp hi
      have hi_succ_le : i + 1 ≤ k := Nat.succ_le_of_lt hi_lt
      rw [div_mul_eq_mul_div, div_le_iff₀ hkpos]
      rw [Nat.cast_sub hkn]
      have hleft : 0 ≤ (k : ℚ) - ((i : ℚ) + 1) := by
        have hle : (i : ℚ) + 1 ≤ (k : ℚ) := by exact_mod_cast hi_succ_le
        linarith
      have hright : 0 ≤ (n : ℚ) - (k : ℚ) := by
        have hle : (k : ℚ) ≤ (n : ℚ) := by exact_mod_cast hkn
        linarith
      have hnonneg :
          0 ≤ ((k : ℚ) - ((i : ℚ) + 1)) * ((n : ℚ) - (k : ℚ)) :=
        mul_nonneg hleft hright
      nlinarith
  have hmul :
      ((n : ℚ) / (k : ℚ))^k * (k.factorial : ℚ)
        ≤ ((n.choose k : Nat) : ℚ) * (k.factorial : ℚ) := by
    simpa [hasc] using hprod
  exact (mul_le_mul_iff_of_pos_right hfacpos).mp hmul

theorem positiveBinomDen_ge_tail_pow {a k : Nat} (ha : 3 ≤ a)
    (hk : 2 ≤ k) (hkmax : k ≤ a - 1) :
    (((a - 2 : Nat) : ℚ) / ((k - 1 : Nat) : ℚ))^(k - 1)
      ≤ (positiveBinomDen a k : ℚ) := by
  unfold positiveBinomDen
  exact choose_ge_pow_div_pow (by omega : 1 ≤ k - 1) (by omega : k - 1 ≤ a - 2)

/-- Closed rational upper bound for the reciprocal binomial prefactor in the
large-`a` tail, obtained from `C(n,k) ≥ (n/k)^k`. -/
def positiveBinomRatioTailPowBound (a k : Nat) : ℚ :=
  1 / (((a - 1 : Nat) : ℚ) *
    ((((a - 2 : Nat) : ℚ) / ((k - 1 : Nat) : ℚ))^(k - 1)))

theorem positiveBinomRatio_le_tail_powBound {a k : Nat} (ha : 3 ≤ a)
    (hk : 2 ≤ k) (hkmax : k ≤ a - 1) :
    positiveBinomRatio a k ≤ positiveBinomRatioTailPowBound a k := by
  have hpow_pos :
      0 < (((a - 2 : Nat) : ℚ) / ((k - 1 : Nat) : ℚ))^(k - 1) := by
    have hnum : (0 : ℚ) < ((a - 2 : Nat) : ℚ) := by
      exact_mod_cast (by omega : 0 < a - 2)
    have hden : (0 : ℚ) < ((k - 1 : Nat) : ℚ) := by
      exact_mod_cast (by omega : 0 < k - 1)
    exact pow_pos (div_pos hnum hden) _
  have ha1_pos : (0 : ℚ) < ((a - 1 : Nat) : ℚ) := by
    exact_mod_cast (by omega : 0 < a - 1)
  have htail_denom_pos :
      0 < ((a - 1 : Nat) : ℚ) *
        ((((a - 2 : Nat) : ℚ) / ((k - 1 : Nat) : ℚ))^(k - 1)) :=
    mul_pos ha1_pos hpow_pos
  have hden_ge := positiveBinomDen_ge_tail_pow ha hk hkmax
  have hmul_ge :
      ((a - 1 : Nat) : ℚ) *
          ((((a - 2 : Nat) : ℚ) / ((k - 1 : Nat) : ℚ))^(k - 1))
        ≤ ((a - 1 : Nat) : ℚ) * (positiveBinomDen a k : ℚ) :=
    mul_le_mul_of_nonneg_left hden_ge ha1_pos.le
  unfold positiveBinomRatioTailPowBound positiveBinomRatio
  exact one_div_le_one_div_of_le htail_denom_pos hmul_ge

/-! ### Rational entropy-shadow denominator bound

The exact TeX entropy inequality is
`C(n,k) ≥ exp(n H(k/n))/(n+2)` in the positive-tail parameters.  The following
log-free rational form is the same denominator-growth mechanism:

`n^n ≤ (n+1) C(n,k) k^k (n-k)^(n-k)`.

It comes from expanding `(k + (n-k))^n` and proving the weighted binomial term
is maximal at the mode `k`.  The lemmas below isolate the adjacent-ratio part
of that proof. -/

def weightedChooseTerm (n k i : Nat) : ℚ :=
  ((n.choose i : Nat) : ℚ) * (k : ℚ)^i * ((n - k : Nat) : ℚ)^(n - i)

theorem weightedChooseTerm_nonneg (n k i : Nat) :
    0 ≤ weightedChooseTerm n k i := by
  unfold weightedChooseTerm
  positivity

theorem weightedChooseTerm_succ_mul {n k i : Nat} (hi : i < n) :
    weightedChooseTerm n k (i + 1) * ((i + 1 : Nat) : ℚ) * ((n - k : Nat) : ℚ)
      = weightedChooseTerm n k i * ((n - i : Nat) : ℚ) * (k : ℚ) := by
  unfold weightedChooseTerm
  have hchoose := Nat.choose_succ_right_eq n i
  have hchooseQ :
      ((n.choose (i + 1) : Nat) : ℚ) * ((i + 1 : Nat) : ℚ)
        = ((n.choose i : Nat) : ℚ) * ((n - i : Nat) : ℚ) := by
    exact_mod_cast hchoose
  have hnisucc : n - (i + 1) + 1 = n - i := by omega
  have hpowk : (k : ℚ)^(i + 1) = (k : ℚ)^i * (k : ℚ) := by
    rw [pow_succ]
  have hpownk :
      ((n - k : Nat) : ℚ)^(n - (i + 1)) * ((n - k : Nat) : ℚ)
        = ((n - k : Nat) : ℚ)^(n - i) := by
    rw [← pow_succ, hnisucc]
  calc
    ((n.choose (i + 1) : Nat) : ℚ) * (k : ℚ)^(i + 1) *
          ((n - k : Nat) : ℚ)^(n - (i + 1)) *
          ((i + 1 : Nat) : ℚ) * ((n - k : Nat) : ℚ)
        = (((n.choose (i + 1) : Nat) : ℚ) * ((i + 1 : Nat) : ℚ)) *
          (k : ℚ)^(i + 1) *
          (((n - k : Nat) : ℚ)^(n - (i + 1)) * ((n - k : Nat) : ℚ)) := by
            ring
    _ = (((n.choose i : Nat) : ℚ) * ((n - i : Nat) : ℚ)) *
          (k : ℚ)^(i + 1) *
          (((n - k : Nat) : ℚ)^(n - (i + 1)) * ((n - k : Nat) : ℚ)) := by
            rw [hchooseQ]
    _ = ((n.choose i : Nat) : ℚ) * (k : ℚ)^i *
          ((n - k : Nat) : ℚ)^(n - i) *
          ((n - i : Nat) : ℚ) * (k : ℚ) := by
            rw [hpowk, hpownk]
            ring

theorem weightedChooseTerm_le_succ_of_lt_mode {n k i : Nat}
    (hkpos : 0 < k) (hkn : k ≤ n) (hi : i < k) :
    weightedChooseTerm n k i ≤ weightedChooseTerm n k (i + 1) := by
  have hin : i < n := hi.trans_le hkn
  have hrec := weightedChooseTerm_succ_mul (n := n) (k := k) (i := i) hin
  let A : ℚ := ((i + 1 : Nat) : ℚ) * ((n - k : Nat) : ℚ)
  let B : ℚ := ((n - i : Nat) : ℚ) * (k : ℚ)
  have hrec' : weightedChooseTerm n k i * B = weightedChooseTerm n k (i + 1) * A := by
    dsimp [A, B]
    calc
      weightedChooseTerm n k i * (↑(n - i) * ↑k)
          = weightedChooseTerm n k i * ↑(n - i) * ↑k := by ring
      _ = weightedChooseTerm n k (i + 1) * ↑(i + 1) * ↑(n - k) := hrec.symm
      _ = weightedChooseTerm n k (i + 1) * (↑(i + 1) * ↑(n - k)) := by ring
  have hAB : A ≤ B := by
    have hi1 : (i : ℚ) + 1 ≤ (k : ℚ) := by
      exact_mod_cast Nat.succ_le_of_lt hi
    have hgap : 0 ≤ (k : ℚ) - ((i : ℚ) + 1) := by linarith
    have hnnonneg : 0 ≤ (n : ℚ) := by positivity
    have hprod : 0 ≤ (n : ℚ) * ((k : ℚ) - ((i : ℚ) + 1)) :=
      mul_nonneg hnnonneg hgap
    have hkQnonneg : 0 ≤ (k : ℚ) := by positivity
    have hdiff : B - A = (n : ℚ) * ((k : ℚ) - ((i : ℚ) + 1)) + (k : ℚ) := by
      dsimp [A, B]
      rw [Nat.cast_sub hkn, Nat.cast_sub (by omega : i ≤ n)]
      push_cast
      ring
    have hdiff_nonneg : 0 ≤ B - A := by
      rw [hdiff]
      linarith
    exact sub_nonneg.mp hdiff_nonneg
  have hBpos : 0 < B := by
    dsimp [B]
    have hni : (0 : ℚ) < ((n - i : Nat) : ℚ) := by
      exact_mod_cast (by omega : 0 < n - i)
    have hkQ : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hkpos
    positivity
  rw [← mul_le_mul_iff_of_pos_right hBpos]
  calc
    weightedChooseTerm n k i * B = weightedChooseTerm n k (i + 1) * A := hrec'
    _ ≤ weightedChooseTerm n k (i + 1) * B :=
        mul_le_mul_of_nonneg_left hAB (weightedChooseTerm_nonneg n k (i + 1))

theorem weightedChooseTerm_succ_le_of_mode_le {n k i : Nat}
    (hkn : k < n) (hki : k ≤ i) (hin : i < n) :
    weightedChooseTerm n k (i + 1) ≤ weightedChooseTerm n k i := by
  have hrec := weightedChooseTerm_succ_mul (n := n) (k := k) (i := i) hin
  let A : ℚ := ((i + 1 : Nat) : ℚ) * ((n - k : Nat) : ℚ)
  let B : ℚ := ((n - i : Nat) : ℚ) * (k : ℚ)
  have hrec' : weightedChooseTerm n k (i + 1) * A = weightedChooseTerm n k i * B := by
    dsimp [A, B]
    calc
      weightedChooseTerm n k (i + 1) * (↑(i + 1) * ↑(n - k))
          = weightedChooseTerm n k (i + 1) * ↑(i + 1) * ↑(n - k) := by ring
      _ = weightedChooseTerm n k i * ↑(n - i) * ↑k := hrec
      _ = weightedChooseTerm n k i * (↑(n - i) * ↑k) := by ring
  have hBA : B ≤ A := by
    have hkiQ : (k : ℚ) ≤ (i : ℚ) := by exact_mod_cast hki
    have hknQ : (k : ℚ) < (n : ℚ) := by exact_mod_cast hkn
    have hgap : 1 ≤ (i : ℚ) + 1 - (k : ℚ) := by linarith
    have hnnonneg : 0 ≤ (n : ℚ) := by positivity
    have hprod : (n : ℚ) ≤ (n : ℚ) * ((i : ℚ) + 1 - (k : ℚ)) := by
      have := mul_le_mul_of_nonneg_left hgap hnnonneg
      simpa using this
    have hdiff : A - B = (n : ℚ) * ((i : ℚ) + 1 - (k : ℚ)) - (k : ℚ) := by
      dsimp [A, B]
      rw [Nat.cast_sub hkn.le, Nat.cast_sub (by omega : i ≤ n)]
      push_cast
      ring
    have hdiff_nonneg : 0 ≤ A - B := by
      rw [hdiff]
      linarith
    exact sub_nonneg.mp hdiff_nonneg
  have hApos : 0 < A := by
    dsimp [A]
    have hi1 : (0 : ℚ) < ((i + 1 : Nat) : ℚ) := by positivity
    have hnk : (0 : ℚ) < ((n - k : Nat) : ℚ) := by
      exact_mod_cast (by omega : 0 < n - k)
    positivity
  rw [← mul_le_mul_iff_of_pos_right hApos]
  calc
    weightedChooseTerm n k (i + 1) * A = weightedChooseTerm n k i * B := hrec'
    _ ≤ weightedChooseTerm n k i * A :=
        mul_le_mul_of_nonneg_left hBA (weightedChooseTerm_nonneg n k i)

theorem weightedChooseTerm_le_mode_of_le {n k i : Nat}
    (hkpos : 0 < k) (hkn : k ≤ n) (hik : i ≤ k) :
    weightedChooseTerm n k i ≤ weightedChooseTerm n k k := by
  let F : Nat → ℚ := fun j =>
    if j ≤ k then weightedChooseTerm n k j else weightedChooseTerm n k k
  have hstep : ∀ j, i ≤ j → F j ≤ F (j + 1) := by
    intro j _hij
    by_cases hj : j < k
    · have hjle : j ≤ k := hj.le
      have hsucc : j + 1 ≤ k := Nat.succ_le_of_lt hj
      simp [F, hjle, hsucc,
        weightedChooseTerm_le_succ_of_lt_mode hkpos hkn hj]
    · have hsucc_not : ¬ j + 1 ≤ k := by omega
      by_cases hjle : j ≤ k
      · have hjeq : j = k := le_antisymm hjle (le_of_not_gt hj)
        simp [F, hjeq]
      · simp [F, hjle, hsucc_not]
  have hchain :
      F i ≤ F k :=
    Nat.rel_of_forall_rel_succ_of_le_of_le (· ≤ ·) hstep le_rfl hik
  simpa [F, hik] using hchain

theorem weightedChooseTerm_le_mode_of_mode_le {n k i : Nat}
    (hkn : k < n) (hki : k ≤ i) (hin : i ≤ n) :
    weightedChooseTerm n k i ≤ weightedChooseTerm n k k := by
  let F : Nat → ℚ := fun j =>
    if j ≤ n then weightedChooseTerm n k j else weightedChooseTerm n k n
  have hstep : ∀ j, k ≤ j → F (j + 1) ≤ F j := by
    intro j hkj
    by_cases hjn : j < n
    · have hjle : j ≤ n := hjn.le
      have hsucc : j + 1 ≤ n := Nat.succ_le_of_lt hjn
      simp [F, hjle, hsucc,
        weightedChooseTerm_succ_le_of_mode_le hkn hkj hjn]
    · have hsucc_not : ¬ j + 1 ≤ n := by omega
      by_cases hjle : j ≤ n
      · have hjeq : j = n := le_antisymm hjle (le_of_not_gt hjn)
        simp [F, hjeq]
      · simp [F, hjle, hsucc_not]
  have hchain :
      F i ≤ F k :=
    Nat.rel_of_forall_rel_succ_of_le_of_le (fun x y => y ≤ x) hstep le_rfl hki
  simpa [F, hkn.le, hin] using hchain

theorem weightedChooseTerm_le_mode {n k i : Nat}
    (hkpos : 0 < k) (hkn : k < n) (hin : i ≤ n) :
    weightedChooseTerm n k i ≤ weightedChooseTerm n k k := by
  rcases le_total i k with hik | hki
  · exact weightedChooseTerm_le_mode_of_le hkpos hkn.le hik
  · exact weightedChooseTerm_le_mode_of_mode_le hkn hki hin

theorem pow_le_card_mul_weightedChooseTerm_mode {n k : Nat}
    (hkpos : 0 < k) (hkn : k < n) :
    (n : ℚ)^n ≤ ((n + 1 : Nat) : ℚ) * weightedChooseTerm n k k := by
  have hsum_eq :
      (n : ℚ)^n = ∑ i ∈ Finset.range (n + 1), weightedChooseTerm n k i := by
    have hkn_cast : (k : ℚ) + ((n - k : Nat) : ℚ) = (n : ℚ) := by
      rw [Nat.cast_sub hkn.le]
      ring
    calc
      (n : ℚ)^n = ((k : ℚ) + ((n - k : Nat) : ℚ))^n := by rw [hkn_cast]
      _ = ∑ i ∈ Finset.range (n + 1),
            (k : ℚ)^i * ((n - k : Nat) : ℚ)^(n - i) *
              ((n.choose i : Nat) : ℚ) := by
              rw [add_pow]
      _ = ∑ i ∈ Finset.range (n + 1), weightedChooseTerm n k i := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              unfold weightedChooseTerm
              ring
  have hsum_le :
      (∑ i ∈ Finset.range (n + 1), weightedChooseTerm n k i)
        ≤ (Finset.range (n + 1)).card • weightedChooseTerm n k k := by
    exact Finset.sum_le_card_nsmul _ _ _ fun i hi =>
      weightedChooseTerm_le_mode hkpos hkn
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  calc
    (n : ℚ)^n = ∑ i ∈ Finset.range (n + 1), weightedChooseTerm n k i := hsum_eq
    _ ≤ (Finset.range (n + 1)).card • weightedChooseTerm n k k := hsum_le
    _ = ((n + 1 : Nat) : ℚ) * weightedChooseTerm n k k := by
      simp [Finset.card_range, nsmul_eq_mul]

theorem choose_ge_entropy_shadow {n k : Nat} (hkpos : 0 < k) (hkn : k < n) :
    (n : ℚ)^n /
        (((n + 1 : Nat) : ℚ) * (k : ℚ)^k * ((n - k : Nat) : ℚ)^(n - k))
      ≤ ((n.choose k : Nat) : ℚ) := by
  have hmain := pow_le_card_mul_weightedChooseTerm_mode (n := n) (k := k) hkpos hkn
  have hden_pos :
      0 < ((n + 1 : Nat) : ℚ) * (k : ℚ)^k * ((n - k : Nat) : ℚ)^(n - k) := by
    have hn1 : (0 : ℚ) < ((n + 1 : Nat) : ℚ) := by positivity
    have hkQ : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hkpos
    have hnkQ : (0 : ℚ) < ((n - k : Nat) : ℚ) := by
      exact_mod_cast (by omega : 0 < n - k)
    positivity
  rw [div_le_iff₀ hden_pos]
  unfold weightedChooseTerm at hmain
  nlinarith [hmain]

/-- Rational, log-free specialization of the TeX entropy lower bound for
`choose(a-2,k-1)`.  The denominator uses `a-1 = (a-2)+1`; this is slightly
stronger than the printed `1/a` entropy prefactor and avoids real `exp/log`. -/
def positiveBinomDenEntropyShadowBound (a k : Nat) : ℚ :=
  ((a - 2 : Nat) : ℚ)^(a - 2) /
    (((a - 1 : Nat) : ℚ) * ((k - 1 : Nat) : ℚ)^(k - 1) *
      ((a - 2 - (k - 1) : Nat) : ℚ)^(a - 2 - (k - 1)))

theorem positiveBinomDen_ge_entropyShadowBound {a k : Nat}
    (hk : 2 ≤ k) (hklt : k < a - 1) :
    positiveBinomDenEntropyShadowBound a k ≤ (positiveBinomDen a k : ℚ) := by
  unfold positiveBinomDenEntropyShadowBound positiveBinomDen
  have ha : a - 2 + 1 = a - 1 := by omega
  simpa [ha] using choose_ge_entropy_shadow (n := a - 2) (k := k - 1)
    (by omega : 0 < k - 1) (by omega : k - 1 < a - 2)

theorem positiveBinomDenEntropyShadowBound_pos {a k : Nat}
    (hk : 2 ≤ k) (hklt : k < a - 1) :
    0 < positiveBinomDenEntropyShadowBound a k := by
  unfold positiveBinomDenEntropyShadowBound
  have ha2 : (0 : ℚ) < ((a - 2 : Nat) : ℚ) := by
    exact_mod_cast (by omega : 0 < a - 2)
  have ha1 : (0 : ℚ) < ((a - 1 : Nat) : ℚ) := by
    exact_mod_cast (by omega : 0 < a - 1)
  have hk1 : (0 : ℚ) < ((k - 1 : Nat) : ℚ) := by
    exact_mod_cast (by omega : 0 < k - 1)
  have hcomp : (0 : ℚ) < ((a - 2 - (k - 1) : Nat) : ℚ) := by
    exact_mod_cast (by omega : 0 < a - 2 - (k - 1))
  positivity

/-- Reciprocal-binomial prefactor bound from the rational entropy shadow. -/
def positiveBinomRatioEntropyShadowBound (a k : Nat) : ℚ :=
  1 / (((a - 1 : Nat) : ℚ) * positiveBinomDenEntropyShadowBound a k)

theorem positiveBinomRatio_le_entropyShadowBound {a k : Nat}
    (hk : 2 ≤ k) (hklt : k < a - 1) :
    positiveBinomRatio a k ≤ positiveBinomRatioEntropyShadowBound a k := by
  have hEpos := positiveBinomDenEntropyShadowBound_pos hk hklt
  have ha1_pos : (0 : ℚ) < ((a - 1 : Nat) : ℚ) := by
    exact_mod_cast (by omega : 0 < a - 1)
  have htail_denom_pos :
      0 < ((a - 1 : Nat) : ℚ) * positiveBinomDenEntropyShadowBound a k :=
    mul_pos ha1_pos hEpos
  have hden_ge := positiveBinomDen_ge_entropyShadowBound hk hklt
  have hmul_ge :
      ((a - 1 : Nat) : ℚ) * positiveBinomDenEntropyShadowBound a k
        ≤ ((a - 1 : Nat) : ℚ) * (positiveBinomDen a k : ℚ) :=
    mul_le_mul_of_nonneg_left hden_ge ha1_pos.le
  unfold positiveBinomRatioEntropyShadowBound positiveBinomRatio
  exact one_div_le_one_div_of_le htail_denom_pos hmul_ge

theorem positiveBinomRatioEntropyShadowBound_eq {a k : Nat}
    (hk : 2 ≤ k) (hklt : k < a - 1) :
    positiveBinomRatioEntropyShadowBound a k =
      (((k - 1 : Nat) : ℚ)^(k - 1) *
        ((a - 2 - (k - 1) : Nat) : ℚ)^(a - 2 - (k - 1))) /
        ((a - 2 : Nat) : ℚ)^(a - 2) := by
  have ha1_ne : ((a - 1 : Nat) : ℚ) ≠ 0 := by
    exact_mod_cast (by omega : a - 1 ≠ 0)
  have ha2_pow_ne : ((a - 2 : Nat) : ℚ)^(a - 2) ≠ 0 := by
    have ha2 : (0 : ℚ) < ((a - 2 : Nat) : ℚ) := by
      exact_mod_cast (by omega : 0 < a - 2)
    exact (pow_pos ha2 _).ne'
  have hk1_pow_ne : ((k - 1 : Nat) : ℚ)^(k - 1) ≠ 0 := by
    have hk1 : (0 : ℚ) < ((k - 1 : Nat) : ℚ) := by
      exact_mod_cast (by omega : 0 < k - 1)
    exact (pow_pos hk1 _).ne'
  have hcomp_pow_ne :
      ((a - 2 - (k - 1) : Nat) : ℚ)^(a - 2 - (k - 1)) ≠ 0 := by
    have hcomp : (0 : ℚ) < ((a - 2 - (k - 1) : Nat) : ℚ) := by
      exact_mod_cast (by omega : 0 < a - 2 - (k - 1))
    exact (pow_pos hcomp _).ne'
  unfold positiveBinomRatioEntropyShadowBound positiveBinomDenEntropyShadowBound
  field_simp [ha1_ne, ha2_pow_ne, hk1_pow_ne, hcomp_pow_ne]

theorem positiveBinomRatio_le_entropyShadowRatio {a k : Nat}
    (hk : 2 ≤ k) (hklt : k < a - 1) :
    positiveBinomRatio a k ≤
      (((k - 1 : Nat) : ℚ)^(k - 1) *
        ((a - 2 - (k - 1) : Nat) : ℚ)^(a - 2 - (k - 1))) /
        ((a - 2 : Nat) : ℚ)^(a - 2) := by
  simpa [positiveBinomRatioEntropyShadowBound_eq hk hklt]
    using positiveBinomRatio_le_entropyShadowBound hk hklt

/-- The entropy-shadow reciprocal bound in the paper's `j = a-k`
notation. -/
def positiveBinomRatioEntropyShadowPosJBound (a k : Nat) : ℚ :=
  (((k - 1 : Nat) : ℚ)^(k - 1) *
    ((posJ a k - 1 : Nat) : ℚ)^(posJ a k - 1)) /
    ((a - 2 : Nat) : ℚ)^(a - 2)

theorem positiveBinomRatio_le_entropyShadowPosJBound {a k : Nat}
    (hk : 2 ≤ k) (hklt : k < a - 1) :
    positiveBinomRatio a k ≤ positiveBinomRatioEntropyShadowPosJBound a k := by
  have hcomp : a - 2 - (k - 1) = posJ a k - 1 := by
    unfold posJ
    omega
  simpa [positiveBinomRatioEntropyShadowPosJBound, hcomp]
    using positiveBinomRatio_le_entropyShadowRatio (a := a) (k := k) hk hklt

theorem positiveBinomRatio_one (a : Nat) :
    positiveBinomRatio a 1 = 1 / ((a - 1 : Nat) : ℚ) := by
  simp [positiveBinomRatio, positiveBinomDen]

theorem positiveBinomRatioEntropyShadowPosJBound_one {a : Nat} (ha : 3 ≤ a) :
    positiveBinomRatioEntropyShadowPosJBound a 1 = 1 := by
  have hJ : posJ a 1 - 1 = a - 2 := by
    unfold posJ
    omega
  have hpow_ne : ((a - 2 : Nat) : ℚ)^(a - 2) ≠ 0 := by
    have ha2 : (0 : ℚ) < ((a - 2 : Nat) : ℚ) := by
      exact_mod_cast (by omega : 0 < a - 2)
    exact (pow_pos ha2 _).ne'
  simp [positiveBinomRatioEntropyShadowPosJBound, hJ, hpow_ne]

theorem positiveBinomRatio_le_entropyShadowPosJBound_one {a : Nat} (ha : 3 ≤ a) :
    positiveBinomRatio a 1 ≤ positiveBinomRatioEntropyShadowPosJBound a 1 := by
  rw [positiveBinomRatio_one, positiveBinomRatioEntropyShadowPosJBound_one ha]
  have hpos : (0 : ℚ) < ((a - 1 : Nat) : ℚ) := by
    exact_mod_cast (by omega : 0 < a - 1)
  rw [div_le_iff₀ hpos]
  norm_num
  exact_mod_cast (by omega : 1 ≤ a - 1)

theorem positiveBinomRatio_le_entropyShadowPosJBound_of_mem_large
    {a k : Nat} (ha : 20 ≤ a) (hkRange : k ∈ positiveKRange a) :
    positiveBinomRatio a k ≤ positiveBinomRatioEntropyShadowPosJBound a k := by
  rcases (mem_positiveKRange.mp hkRange) with ⟨hk1, _hkmax⟩
  rcases Nat.eq_or_lt_of_le hk1 with hkeq | hkgt
  · subst k
    exact positiveBinomRatio_le_entropyShadowPosJBound_one (by omega : 3 ≤ a)
  · have hk2 : 2 ≤ k := by omega
    have hklt : k < a - 1 := lt_pred_of_mem_positiveKRange_of_large ha hkRange
    exact positiveBinomRatio_le_entropyShadowPosJBound hk2 hklt

theorem positiveBinomRatioEntropyShadowPosJBound_nonneg (a k : Nat) :
    0 ≤ positiveBinomRatioEntropyShadowPosJBound a k := by
  unfold positiveBinomRatioEntropyShadowPosJBound
  positivity

theorem positiveBinomRatioEntropyShadowPosJBound_pos_of_mem_large
    {a k : Nat} (ha : 20 ≤ a) (hkRange : k ∈ positiveKRange a) :
    0 < positiveBinomRatioEntropyShadowPosJBound a k := by
  rcases (mem_positiveKRange.mp hkRange) with ⟨hk1, _hkmax⟩
  rcases Nat.eq_or_lt_of_le hk1 with hkeq | hkgt
  · subst k
    rw [positiveBinomRatioEntropyShadowPosJBound_one (by omega : 3 ≤ a)]
    norm_num
  · have hk1pos : (0 : ℚ) < ((k - 1 : Nat) : ℚ) := by
      exact_mod_cast (by omega : 0 < k - 1)
    have hj1pos : (0 : ℚ) < ((posJ a k - 1 : Nat) : ℚ) := by
      exact_mod_cast (by
        have hj2 := two_le_posJ_of_mem_positiveKRange_of_large ha hkRange
        omega : 0 < posJ a k - 1)
    have ha2pos : (0 : ℚ) < ((a - 2 : Nat) : ℚ) := by
      exact_mod_cast (by omega : 0 < a - 2)
    unfold positiveBinomRatioEntropyShadowPosJBound
    positivity

/-- Small-regime summand with the binomial reciprocal replaced by the
entropy-shadow ratio.  This is a rational shell for the large-`a` tail; a
later step still supplies the appropriate exponential tail majorant. -/
def positiveSmallEntropyShadowMajorantTerm (a k : Nat) : ℚ :=
  (65 / (posNhi a : ℚ)) * ((k : ℚ) * (posJ a k : ℚ)) *
    positiveBinomRatioEntropyShadowPosJBound a k *
    positiveDyadicDecay (posJ a k) *
    partialExpUpper (positiveSmallExponentUpper a k) positiveExpCutoff

/-- Tempered-regime summand with the binomial reciprocal replaced by the
entropy-shadow ratio. -/
def positiveTemperedEntropyShadowMajorantTerm (a k : Nat) : ℚ :=
  (96 / (posNlo a : ℚ)) * ((k : ℚ) * (posJ a k : ℚ)) *
    positiveBinomRatioEntropyShadowPosJBound a k *
    positiveDyadicDecay (posJ a k) *
    partialExpUpper (positiveTemperedExponentUpper a k) positiveExpCutoff

/- The preceding two entropy-shadow terms keep the finite-window
`partialExpUpper` exponential shell for audit continuity.  The actual
large-`a` tail may use sharper rational exponential majorants; the following
parameterized forms expose that replacement without changing the binomial and
dyadic bookkeeping. -/
def positiveSmallEntropyShadowExpMajorantTerm
    (smallExp : Nat → Nat → ℚ) (a k : Nat) : ℚ :=
  (65 / (posNhi a : ℚ)) * ((k : ℚ) * (posJ a k : ℚ)) *
    positiveBinomRatioEntropyShadowPosJBound a k *
    positiveDyadicDecay (posJ a k) *
    smallExp a k

def positiveTemperedEntropyShadowExpMajorantTerm
    (temperedExp : Nat → Nat → ℚ) (a k : Nat) : ℚ :=
  (96 / (posNlo a : ℚ)) * ((k : ℚ) * (posJ a k : ℚ)) *
    positiveBinomRatioEntropyShadowPosJBound a k *
    positiveDyadicDecay (posJ a k) *
    temperedExp a k

/-- Small-regime entropy-shadow summand with the exponential factor removed. -/
def positiveSmallEntropyShadowBaseTerm (a k : Nat) : ℚ :=
  (65 / (posNhi a : ℚ)) * ((k : ℚ) * (posJ a k : ℚ)) *
    positiveBinomRatioEntropyShadowPosJBound a k *
    positiveDyadicDecay (posJ a k)

/-- Tempered-regime entropy-shadow summand with the exponential factor removed. -/
def positiveTemperedEntropyShadowBaseTerm (a k : Nat) : ℚ :=
  (96 / (posNlo a : ℚ)) * ((k : ℚ) * (posJ a k : ℚ)) *
    positiveBinomRatioEntropyShadowPosJBound a k *
    positiveDyadicDecay (posJ a k)

def positiveSmallEntropyShadowBaseStepQuotient (a r : Nat) : ℚ :=
  positiveSmallEntropyShadowBaseTerm a (r + 1) /
    positiveSmallEntropyShadowBaseTerm a r

def positiveTemperedEntropyShadowBaseStepQuotient (a r : Nat) : ℚ :=
  positiveTemperedEntropyShadowBaseTerm a (r + 1) /
    positiveTemperedEntropyShadowBaseTerm a r

/-- Explicit adjacent quotient for the entropy-shadow base summand, before
any analytic exponential factor is inserted.  This keeps the quotient audit
purely rational in `r` and `j = a-r`. -/
def positiveEntropyShadowBaseStepRawQuotient (a r : Nat) : ℚ :=
  (((r + 1 : Nat) : ℚ) * ((posJ a r - 1 : Nat) : ℚ) *
      ((r : Nat) : ℚ)^r *
      ((posJ a r - 2 : Nat) : ℚ)^(posJ a r - 2)) /
    (((r : Nat) : ℚ) * ((posJ a r : Nat) : ℚ) *
      ((r - 1 : Nat) : ℚ)^(r - 1) *
      ((posJ a r - 1 : Nat) : ℚ)^(posJ a r - 1)) *
    ((2 : ℚ)^(posJ a r) / (2 : ℚ)^(posJ a r - 1))

theorem ratCast_natSub_selfPow_pos {n d : Nat} (hd : d ≤ n) :
    (0 : ℚ) < (((n - d : Nat) : ℚ)^(n - d)) := by
  by_cases hnd : n = d
  · subst n
    norm_num
  · have hbase : (0 : ℚ) < ((n - d : Nat) : ℚ) := by
      exact_mod_cast (by omega : 0 < n - d)
    exact pow_pos hbase _

theorem positiveEntropyShadowBaseStepRawQuotient_pos
    {a r : Nat} (hr1 : 1 ≤ r) (hj2 : 2 ≤ posJ a r) :
    0 < positiveEntropyShadowBaseStepRawQuotient a r := by
  have hsucc : (0 : ℚ) < ((r + 1 : Nat) : ℚ) := by
    exact_mod_cast (by omega : 0 < r + 1)
  have hrQ : (0 : ℚ) < ((r : Nat) : ℚ) := by
    exact_mod_cast (by omega : 0 < r)
  have hrPow : (0 : ℚ) < ((r : Nat) : ℚ)^r :=
    pow_pos hrQ _
  have hrPredPow : (0 : ℚ) < (((r - 1 : Nat) : ℚ)^(r - 1)) :=
    ratCast_natSub_selfPow_pos (n := r) (d := 1) hr1
  have hj1 : 1 ≤ posJ a r := by omega
  have hjQ : (0 : ℚ) < ((posJ a r : Nat) : ℚ) := by
    exact_mod_cast (by omega : 0 < posJ a r)
  have hjPredQ : (0 : ℚ) < ((posJ a r - 1 : Nat) : ℚ) := by
    exact_mod_cast (by omega : 0 < posJ a r - 1)
  have hjPredPow :
      (0 : ℚ) < (((posJ a r - 1 : Nat) : ℚ)^(posJ a r - 1)) :=
    ratCast_natSub_selfPow_pos (n := posJ a r) (d := 1) hj1
  have hjTwoPredPow :
      (0 : ℚ) < (((posJ a r - 2 : Nat) : ℚ)^(posJ a r - 2)) :=
    ratCast_natSub_selfPow_pos (n := posJ a r) (d := 2) hj2
  have hdyadic :
      (0 : ℚ) < (2 : ℚ)^(posJ a r) / (2 : ℚ)^(posJ a r - 1) := by
    positivity
  have hnum :
      (0 : ℚ) <
        ((r + 1 : Nat) : ℚ) * ((posJ a r - 1 : Nat) : ℚ) *
          ((r : Nat) : ℚ)^r *
          ((posJ a r - 2 : Nat) : ℚ)^(posJ a r - 2) :=
    mul_pos (mul_pos (mul_pos hsucc hjPredQ) hrPow) hjTwoPredPow
  have hden :
      (0 : ℚ) <
        ((r : Nat) : ℚ) * ((posJ a r : Nat) : ℚ) *
          ((r - 1 : Nat) : ℚ)^(r - 1) *
          ((posJ a r - 1 : Nat) : ℚ)^(posJ a r - 1) :=
    mul_pos (mul_pos (mul_pos hrQ hjQ) hrPredPow) hjPredPow
  simpa [positiveEntropyShadowBaseStepRawQuotient] using
    mul_pos (div_pos hnum hden) hdyadic

theorem positiveSmallEntropyShadowExpMajorantTerm_eq_base_mul
    (smallExp : Nat → Nat → ℚ) (a k : Nat) :
    positiveSmallEntropyShadowExpMajorantTerm smallExp a k =
      positiveSmallEntropyShadowBaseTerm a k * smallExp a k := rfl

theorem positiveTemperedEntropyShadowExpMajorantTerm_eq_base_mul
    (temperedExp : Nat → Nat → ℚ) (a k : Nat) :
    positiveTemperedEntropyShadowExpMajorantTerm temperedExp a k =
      positiveTemperedEntropyShadowBaseTerm a k * temperedExp a k := rfl

@[simp] theorem positiveSmallEntropyShadowExpMajorantTerm_partialExp (a k : Nat) :
    positiveSmallEntropyShadowExpMajorantTerm
        (fun a k => partialExpUpper (positiveSmallExponentUpper a k) positiveExpCutoff)
        a k =
      positiveSmallEntropyShadowMajorantTerm a k := rfl

@[simp] theorem positiveTemperedEntropyShadowExpMajorantTerm_partialExp (a k : Nat) :
    positiveTemperedEntropyShadowExpMajorantTerm
        (fun a k => partialExpUpper (positiveTemperedExponentUpper a k) positiveExpCutoff)
        a k =
      positiveTemperedEntropyShadowMajorantTerm a k := rfl

theorem positiveSmallEntropyShadowExpMajorantTerm_nonneg
    {smallExp : Nat → Nat → ℚ} {a k : Nat}
    (ha : 20 ≤ a) (hkRange : k ∈ positiveKRange a)
    (hExp : 0 ≤ smallExp a k) :
    0 ≤ positiveSmallEntropyShadowExpMajorantTerm smallExp a k := by
  have hhi : (0 : ℚ) < (posNhi a : ℚ) := by
    exact_mod_cast posNhi_pos (by omega : 1 ≤ a)
  have hkQ : (0 : ℚ) ≤ (k : ℚ) := by positivity
  have hjQ : (0 : ℚ) ≤ (posJ a k : ℚ) := by positivity
  have hbinom :
      0 ≤ positiveBinomRatioEntropyShadowPosJBound a k :=
    (positiveBinomRatioEntropyShadowPosJBound_pos_of_mem_large ha hkRange).le
  have hcoef : (0 : ℚ) ≤ 65 / (posNhi a : ℚ) := by positivity
  have hkj : (0 : ℚ) ≤ (k : ℚ) * (posJ a k : ℚ) :=
    mul_nonneg hkQ hjQ
  have hdecay : 0 ≤ positiveDyadicDecay (posJ a k) :=
    positiveDyadicDecay_nonneg (posJ a k)
  unfold positiveSmallEntropyShadowExpMajorantTerm
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg hcoef hkj) hbinom) hdecay)
    hExp

theorem positiveTemperedEntropyShadowExpMajorantTerm_nonneg
    {temperedExp : Nat → Nat → ℚ} {a k : Nat}
    (ha : 20 ≤ a) (hkRange : k ∈ positiveKRange a)
    (hExp : 0 ≤ temperedExp a k) :
    0 ≤ positiveTemperedEntropyShadowExpMajorantTerm temperedExp a k := by
  have hlo : (0 : ℚ) < (posNlo a : ℚ) := by
    exact_mod_cast posNlo_pos (by omega : 2 ≤ a)
  have hkQ : (0 : ℚ) ≤ (k : ℚ) := by positivity
  have hjQ : (0 : ℚ) ≤ (posJ a k : ℚ) := by positivity
  have hbinom :
      0 ≤ positiveBinomRatioEntropyShadowPosJBound a k :=
    (positiveBinomRatioEntropyShadowPosJBound_pos_of_mem_large ha hkRange).le
  have hcoef : (0 : ℚ) ≤ 96 / (posNlo a : ℚ) := by positivity
  have hkj : (0 : ℚ) ≤ (k : ℚ) * (posJ a k : ℚ) :=
    mul_nonneg hkQ hjQ
  have hdecay : 0 ≤ positiveDyadicDecay (posJ a k) :=
    positiveDyadicDecay_nonneg (posJ a k)
  unfold positiveTemperedEntropyShadowExpMajorantTerm
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg hcoef hkj) hbinom) hdecay)
    hExp

theorem positiveSmallEntropyShadowExpMajorantTerm_pos
    {smallExp : Nat → Nat → ℚ} {a k : Nat}
    (ha : 20 ≤ a) (hkRange : k ∈ positiveKRange a)
    (hExp : 0 < smallExp a k) :
    0 < positiveSmallEntropyShadowExpMajorantTerm smallExp a k := by
  have hhi : (0 : ℚ) < (posNhi a : ℚ) := by
    exact_mod_cast posNhi_pos (by omega : 1 ≤ a)
  have hkpos : 0 < k := by
    have hk1 := (mem_positiveKRange.mp hkRange).1
    omega
  have hkQ : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hkpos
  have hjpos : 0 < posJ a k :=
    posJ_pos_of_mem_positiveKRange (by omega : 1 ≤ a) hkRange
  have hjQ : (0 : ℚ) < (posJ a k : ℚ) := by exact_mod_cast hjpos
  have hbinom :
      0 < positiveBinomRatioEntropyShadowPosJBound a k :=
    positiveBinomRatioEntropyShadowPosJBound_pos_of_mem_large ha hkRange
  have hcoef : (0 : ℚ) < 65 / (posNhi a : ℚ) := by positivity
  have hkj : (0 : ℚ) < (k : ℚ) * (posJ a k : ℚ) :=
    mul_pos hkQ hjQ
  have hdecay : 0 < positiveDyadicDecay (posJ a k) :=
    positiveDyadicDecay_pos (posJ a k)
  unfold positiveSmallEntropyShadowExpMajorantTerm
  exact mul_pos
    (mul_pos (mul_pos (mul_pos hcoef hkj) hbinom) hdecay)
    hExp

theorem positiveTemperedEntropyShadowExpMajorantTerm_pos
    {temperedExp : Nat → Nat → ℚ} {a k : Nat}
    (ha : 20 ≤ a) (hkRange : k ∈ positiveKRange a)
    (hExp : 0 < temperedExp a k) :
    0 < positiveTemperedEntropyShadowExpMajorantTerm temperedExp a k := by
  have hlo : (0 : ℚ) < (posNlo a : ℚ) := by
    exact_mod_cast posNlo_pos (by omega : 2 ≤ a)
  have hkpos : 0 < k := by
    have hk1 := (mem_positiveKRange.mp hkRange).1
    omega
  have hkQ : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hkpos
  have hjpos : 0 < posJ a k :=
    posJ_pos_of_mem_positiveKRange (by omega : 1 ≤ a) hkRange
  have hjQ : (0 : ℚ) < (posJ a k : ℚ) := by exact_mod_cast hjpos
  have hbinom :
      0 < positiveBinomRatioEntropyShadowPosJBound a k :=
    positiveBinomRatioEntropyShadowPosJBound_pos_of_mem_large ha hkRange
  have hcoef : (0 : ℚ) < 96 / (posNlo a : ℚ) := by positivity
  have hkj : (0 : ℚ) < (k : ℚ) * (posJ a k : ℚ) :=
    mul_pos hkQ hjQ
  have hdecay : 0 < positiveDyadicDecay (posJ a k) :=
    positiveDyadicDecay_pos (posJ a k)
  unfold positiveTemperedEntropyShadowExpMajorantTerm
  exact mul_pos
    (mul_pos (mul_pos (mul_pos hcoef hkj) hbinom) hdecay)
    hExp

theorem positiveSmallEntropyShadowBaseTerm_pos
    {a k : Nat} (ha : 20 ≤ a) (hkRange : k ∈ positiveKRange a) :
    0 < positiveSmallEntropyShadowBaseTerm a k := by
  have h := positiveSmallEntropyShadowExpMajorantTerm_pos
    (smallExp := fun _ _ => (1 : ℚ)) ha hkRange (by norm_num)
  simpa [positiveSmallEntropyShadowExpMajorantTerm_eq_base_mul] using h

theorem positiveTemperedEntropyShadowBaseTerm_pos
    {a k : Nat} (ha : 20 ≤ a) (hkRange : k ∈ positiveKRange a) :
    0 < positiveTemperedEntropyShadowBaseTerm a k := by
  have h := positiveTemperedEntropyShadowExpMajorantTerm_pos
    (temperedExp := fun _ _ => (1 : ℚ)) ha hkRange (by norm_num)
  simpa [positiveTemperedEntropyShadowExpMajorantTerm_eq_base_mul] using h

theorem positiveSmallEntropyShadowBaseStepQuotient_eq_raw
    {a r : Nat} (hr1 : 1 ≤ r) (hj2 : 2 ≤ posJ a r)
    (hjr1 : posJ a (r + 1) = posJ a r - 1) :
    positiveSmallEntropyShadowBaseStepQuotient a r =
      positiveEntropyShadowBaseStepRawQuotient a r := by
  have ha2 : 2 ≤ a := by
    unfold posJ at hj2
    omega
  have ha_sub : 0 < a - 2 := by
    unfold posJ at hj2
    omega
  have hhi : ((posNhi a : Nat) : ℚ) ≠ 0 := by
    exact_mod_cast (by
      have hpos := posNhi_pos (a := a) (by omega : 1 ≤ a)
      omega)
  have hrQ : ((r : Nat) : ℚ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  have hjQ : ((posJ a r : Nat) : ℚ) ≠ 0 := by
    exact_mod_cast (by omega : posJ a r ≠ 0)
  have hj1Q : (((posJ a r - 1 : Nat) : ℚ)) ≠ 0 := by
    exact_mod_cast (by omega : posJ a r - 1 ≠ 0)
  have hpow_r1 : (((r - 1 : Nat) : ℚ)^(r - 1)) ≠ 0 := by
    rcases Nat.eq_or_lt_of_le hr1 with hr | hr
    · subst r
      norm_num
    · have hpos : (0 : ℚ) < ((r - 1 : Nat) : ℚ) := by
        exact_mod_cast (by omega : 0 < r - 1)
      exact (pow_pos hpos _).ne'
  have hj1pos : (0 : ℚ) < ((posJ a r - 1 : Nat) : ℚ) := by
    exact_mod_cast (by omega : 0 < posJ a r - 1)
  have hpow_j1 : (((posJ a r - 1 : Nat) : ℚ)^(posJ a r - 1)) ≠ 0 :=
    (pow_pos hj1pos _).ne'
  have hpow_a2 : (((a - 2 : Nat) : ℚ)^(a - 2)) ≠ 0 := by
    have ha2Q : (0 : ℚ) < ((a - 2 : Nat) : ℚ) := by
      exact_mod_cast ha_sub
    exact (pow_pos ha2Q _).ne'
  have hpow2j : ((2 : ℚ)^(posJ a r)) ≠ 0 := by positivity
  have hpow2j1 : ((2 : ℚ)^(posJ a r - 1)) ≠ 0 := by positivity
  have hrpred : r + 1 - 1 = r := by omega
  have hjpred' : posJ a r - 1 - 1 = posJ a r - 2 := by
    rw [Nat.sub_sub]
  unfold positiveSmallEntropyShadowBaseStepQuotient
    positiveSmallEntropyShadowBaseTerm
    positiveBinomRatioEntropyShadowPosJBound
    positiveDyadicDecay
    positiveEntropyShadowBaseStepRawQuotient
  rw [hjr1, hrpred]
  rw [hjpred']
  field_simp [hhi, hrQ, hjQ, hj1Q, hpow_r1, hpow_j1, hpow_a2,
    hpow2j, hpow2j1]

theorem positiveTemperedEntropyShadowBaseStepQuotient_eq_raw
    {a r : Nat} (hr1 : 1 ≤ r) (hj2 : 2 ≤ posJ a r)
    (hjr1 : posJ a (r + 1) = posJ a r - 1) :
    positiveTemperedEntropyShadowBaseStepQuotient a r =
      positiveEntropyShadowBaseStepRawQuotient a r := by
  have ha2 : 2 ≤ a := by
    unfold posJ at hj2
    omega
  have ha_sub : 0 < a - 2 := by
    unfold posJ at hj2
    omega
  have hlo : ((posNlo a : Nat) : ℚ) ≠ 0 := by
    exact_mod_cast (by
      have hpos := posNlo_pos (a := a) ha2
      omega)
  have hrQ : ((r : Nat) : ℚ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  have hjQ : ((posJ a r : Nat) : ℚ) ≠ 0 := by
    exact_mod_cast (by omega : posJ a r ≠ 0)
  have hj1Q : (((posJ a r - 1 : Nat) : ℚ)) ≠ 0 := by
    exact_mod_cast (by omega : posJ a r - 1 ≠ 0)
  have hpow_r1 : (((r - 1 : Nat) : ℚ)^(r - 1)) ≠ 0 := by
    rcases Nat.eq_or_lt_of_le hr1 with hr | hr
    · subst r
      norm_num
    · have hpos : (0 : ℚ) < ((r - 1 : Nat) : ℚ) := by
        exact_mod_cast (by omega : 0 < r - 1)
      exact (pow_pos hpos _).ne'
  have hj1pos : (0 : ℚ) < ((posJ a r - 1 : Nat) : ℚ) := by
    exact_mod_cast (by omega : 0 < posJ a r - 1)
  have hpow_j1 : (((posJ a r - 1 : Nat) : ℚ)^(posJ a r - 1)) ≠ 0 :=
    (pow_pos hj1pos _).ne'
  have hpow_a2 : (((a - 2 : Nat) : ℚ)^(a - 2)) ≠ 0 := by
    have ha2Q : (0 : ℚ) < ((a - 2 : Nat) : ℚ) := by
      exact_mod_cast ha_sub
    exact (pow_pos ha2Q _).ne'
  have hpow2j : ((2 : ℚ)^(posJ a r)) ≠ 0 := by positivity
  have hpow2j1 : ((2 : ℚ)^(posJ a r - 1)) ≠ 0 := by positivity
  have hrpred : r + 1 - 1 = r := by omega
  have hjpred' : posJ a r - 1 - 1 = posJ a r - 2 := by
    rw [Nat.sub_sub]
  unfold positiveTemperedEntropyShadowBaseStepQuotient
    positiveTemperedEntropyShadowBaseTerm
    positiveBinomRatioEntropyShadowPosJBound
    positiveDyadicDecay
    positiveEntropyShadowBaseStepRawQuotient
  rw [hjr1, hrpred]
  rw [hjpred']
  field_simp [hlo, hrQ, hjQ, hj1Q, hpow_r1, hpow_j1, hpow_a2,
    hpow2j, hpow2j1]

theorem positiveSmallEntropyShadowBaseStepQuotient_eq_raw_of_branch
    {a r : Nat} (ha : 20 ≤ a) (hr1 : 1 ≤ r)
    (hrhi : r < min (posKmax a) (posSmallCutoff a)) :
    positiveSmallEntropyShadowBaseStepQuotient a r =
      positiveEntropyShadowBaseStepRawQuotient a r := by
  have hrK : r ≤ posKmax a := by omega
  have hj2 : 2 ≤ posJ a r :=
    two_le_posJ_of_le_posKmax_of_large ha hrK
  have hjr1 : posJ a (r + 1) = posJ a r - 1 := by
    unfold posJ at hj2 ⊢
    omega
  exact positiveSmallEntropyShadowBaseStepQuotient_eq_raw hr1 hj2 hjr1

theorem positiveTemperedEntropyShadowBaseStepQuotient_eq_raw_of_branch
    {a r : Nat} (ha : 20 ≤ a)
    (hrlo : max 1 (posTemperedCutoff a + 1) ≤ r)
    (hrhi : r < posKmax a) :
    positiveTemperedEntropyShadowBaseStepQuotient a r =
      positiveEntropyShadowBaseStepRawQuotient a r := by
  have hr1 : 1 ≤ r := le_trans (le_max_left _ _) hrlo
  have hrK : r ≤ posKmax a := by omega
  have hj2 : 2 ≤ posJ a r :=
    two_le_posJ_of_le_posKmax_of_large ha hrK
  have hjr1 : posJ a (r + 1) = posJ a r - 1 := by
    unfold posJ at hj2 ⊢
    omega
  exact positiveTemperedEntropyShadowBaseStepQuotient_eq_raw hr1 hj2 hjr1

theorem positiveEntropyShadowBaseStepRawQuotient_pos_of_small_branch
    {a r : Nat} (ha : 20 ≤ a) (hr1 : 1 ≤ r)
    (hrhi : r < min (posKmax a) (posSmallCutoff a)) :
    0 < positiveEntropyShadowBaseStepRawQuotient a r := by
  have hrK : r ≤ posKmax a := by omega
  exact positiveEntropyShadowBaseStepRawQuotient_pos hr1
    (two_le_posJ_of_le_posKmax_of_large ha hrK)

theorem positiveEntropyShadowBaseStepRawQuotient_pos_of_tempered_branch
    {a r : Nat} (ha : 20 ≤ a)
    (hrlo : max 1 (posTemperedCutoff a + 1) ≤ r)
    (hrhi : r < posKmax a) :
    0 < positiveEntropyShadowBaseStepRawQuotient a r := by
  have hr1 : 1 ≤ r := le_trans (le_max_left _ _) hrlo
  have hrK : r ≤ posKmax a := by omega
  exact positiveEntropyShadowBaseStepRawQuotient_pos hr1
    (two_le_posJ_of_le_posKmax_of_large ha hrK)

theorem positiveSmallEntropyShadowMajorantTerm_nonneg_of_exp
    {a k : Nat} (ha : 20 ≤ a) (hkRange : k ∈ positiveKRange a)
    (hExp :
      0 ≤ partialExpUpper (positiveSmallExponentUpper a k) positiveExpCutoff) :
    0 ≤ positiveSmallEntropyShadowMajorantTerm a k := by
  simpa using
    positiveSmallEntropyShadowExpMajorantTerm_nonneg
      (smallExp := fun a k =>
        partialExpUpper (positiveSmallExponentUpper a k) positiveExpCutoff)
      ha hkRange hExp

theorem positiveTemperedEntropyShadowMajorantTerm_nonneg_of_exp
    {a k : Nat} (ha : 20 ≤ a) (hkRange : k ∈ positiveKRange a)
    (hExp :
      0 ≤ partialExpUpper (positiveTemperedExponentUpper a k) positiveExpCutoff) :
    0 ≤ positiveTemperedEntropyShadowMajorantTerm a k := by
  simpa using
    positiveTemperedEntropyShadowExpMajorantTerm_nonneg
      (temperedExp := fun a k =>
        partialExpUpper (positiveTemperedExponentUpper a k) positiveExpCutoff)
      ha hkRange hExp

def positiveEntropyShadowEdgeMajorantTerm (a k : Nat) : ℚ :=
  positiveCustomEdgeMajorantTerm
    positiveSmallEntropyShadowMajorantTerm
    positiveTemperedEntropyShadowMajorantTerm a k

def positiveEntropyShadowEdgeMajorantSum (a : Nat) : ℚ :=
  positiveCustomEdgeMajorantSum
    positiveSmallEntropyShadowMajorantTerm
    positiveTemperedEntropyShadowMajorantTerm a

def positiveEntropyShadowSmallBranchSum (a : Nat) : ℚ :=
  positiveCustomSmallBranchSum positiveSmallEntropyShadowMajorantTerm a

def positiveEntropyShadowTemperedBranchSum (a : Nat) : ℚ :=
  positiveCustomTemperedBranchSum positiveTemperedEntropyShadowMajorantTerm a

def positiveEntropyShadowExpEdgeMajorantTerm
    (smallExp temperedExp : Nat → Nat → ℚ) (a k : Nat) : ℚ :=
  positiveCustomEdgeMajorantTerm
    (positiveSmallEntropyShadowExpMajorantTerm smallExp)
    (positiveTemperedEntropyShadowExpMajorantTerm temperedExp) a k

def positiveEntropyShadowExpEdgeMajorantSum
    (smallExp temperedExp : Nat → Nat → ℚ) (a : Nat) : ℚ :=
  positiveCustomEdgeMajorantSum
    (positiveSmallEntropyShadowExpMajorantTerm smallExp)
    (positiveTemperedEntropyShadowExpMajorantTerm temperedExp) a

def positiveEntropyShadowExpSmallBranchSum
    (smallExp : Nat → Nat → ℚ) (a : Nat) : ℚ :=
  positiveCustomSmallBranchSum
    (positiveSmallEntropyShadowExpMajorantTerm smallExp) a

def positiveEntropyShadowExpTemperedBranchSum
    (temperedExp : Nat → Nat → ℚ) (a : Nat) : ℚ :=
  positiveCustomTemperedBranchSum
    (positiveTemperedEntropyShadowExpMajorantTerm temperedExp) a

@[simp] theorem positiveEntropyShadowEdgeMajorantTerm_eq (a k : Nat) :
    positiveEntropyShadowEdgeMajorantTerm a k =
      positiveCustomEdgeMajorantTerm
        positiveSmallEntropyShadowMajorantTerm
        positiveTemperedEntropyShadowMajorantTerm a k := rfl

@[simp] theorem positiveEntropyShadowEdgeMajorantSum_eq (a : Nat) :
    positiveEntropyShadowEdgeMajorantSum a =
      positiveCustomEdgeMajorantSum
        positiveSmallEntropyShadowMajorantTerm
        positiveTemperedEntropyShadowMajorantTerm a := rfl

@[simp] theorem positiveEntropyShadowSmallBranchSum_eq (a : Nat) :
    positiveEntropyShadowSmallBranchSum a =
      positiveCustomSmallBranchSum positiveSmallEntropyShadowMajorantTerm a := rfl

@[simp] theorem positiveEntropyShadowTemperedBranchSum_eq (a : Nat) :
    positiveEntropyShadowTemperedBranchSum a =
      positiveCustomTemperedBranchSum positiveTemperedEntropyShadowMajorantTerm a := rfl

theorem positiveEntropyShadowSmallBranchSum_eq_Icc (a : Nat) :
    positiveEntropyShadowSmallBranchSum a =
      ∑ k ∈ Finset.Icc 1 (min (posKmax a) (posSmallCutoff a)),
        positiveSmallEntropyShadowMajorantTerm a k :=
  positiveCustomSmallBranchSum_eq_Icc positiveSmallEntropyShadowMajorantTerm a

theorem positiveEntropyShadowTemperedBranchSum_eq_Icc (a : Nat) :
    positiveEntropyShadowTemperedBranchSum a =
      ∑ k ∈ Finset.Icc (max 1 (posTemperedCutoff a + 1)) (posKmax a),
        positiveTemperedEntropyShadowMajorantTerm a k :=
  positiveCustomTemperedBranchSum_eq_Icc positiveTemperedEntropyShadowMajorantTerm a

@[simp] theorem positiveEntropyShadowExpEdgeMajorantTerm_eq
    (smallExp temperedExp : Nat → Nat → ℚ) (a k : Nat) :
    positiveEntropyShadowExpEdgeMajorantTerm smallExp temperedExp a k =
      positiveCustomEdgeMajorantTerm
        (positiveSmallEntropyShadowExpMajorantTerm smallExp)
        (positiveTemperedEntropyShadowExpMajorantTerm temperedExp) a k := rfl

@[simp] theorem positiveEntropyShadowExpEdgeMajorantSum_eq
    (smallExp temperedExp : Nat → Nat → ℚ) (a : Nat) :
    positiveEntropyShadowExpEdgeMajorantSum smallExp temperedExp a =
      positiveCustomEdgeMajorantSum
        (positiveSmallEntropyShadowExpMajorantTerm smallExp)
        (positiveTemperedEntropyShadowExpMajorantTerm temperedExp) a := rfl

@[simp] theorem positiveEntropyShadowExpSmallBranchSum_eq
    (smallExp : Nat → Nat → ℚ) (a : Nat) :
    positiveEntropyShadowExpSmallBranchSum smallExp a =
      positiveCustomSmallBranchSum
        (positiveSmallEntropyShadowExpMajorantTerm smallExp) a := rfl

@[simp] theorem positiveEntropyShadowExpTemperedBranchSum_eq
    (temperedExp : Nat → Nat → ℚ) (a : Nat) :
    positiveEntropyShadowExpTemperedBranchSum temperedExp a =
      positiveCustomTemperedBranchSum
        (positiveTemperedEntropyShadowExpMajorantTerm temperedExp) a := rfl

theorem positiveEntropyShadowExpSmallBranchSum_eq_Icc
    (smallExp : Nat → Nat → ℚ) (a : Nat) :
    positiveEntropyShadowExpSmallBranchSum smallExp a =
      ∑ k ∈ Finset.Icc 1 (min (posKmax a) (posSmallCutoff a)),
        positiveSmallEntropyShadowExpMajorantTerm smallExp a k :=
  positiveCustomSmallBranchSum_eq_Icc
    (positiveSmallEntropyShadowExpMajorantTerm smallExp) a

theorem positiveEntropyShadowExpTemperedBranchSum_eq_Icc
    (temperedExp : Nat → Nat → ℚ) (a : Nat) :
    positiveEntropyShadowExpTemperedBranchSum temperedExp a =
      ∑ k ∈ Finset.Icc (max 1 (posTemperedCutoff a + 1)) (posKmax a),
        positiveTemperedEntropyShadowExpMajorantTerm temperedExp a k :=
  positiveCustomTemperedBranchSum_eq_Icc
    (positiveTemperedEntropyShadowExpMajorantTerm temperedExp) a

theorem mem_positiveKRange_of_small_branch_step
    {a r : Nat} (hr1 : 1 ≤ r)
    (hrhi : r < min (posKmax a) (posSmallCutoff a)) :
    r ∈ positiveKRange a :=
  mem_positiveKRange.mpr ⟨hr1, by omega⟩

theorem mem_positiveKRange_of_tempered_branch_step
    {a r : Nat} (hrlo : max 1 (posTemperedCutoff a + 1) ≤ r)
    (hrhi : r < posKmax a) :
    r ∈ positiveKRange a :=
  mem_positiveKRange.mpr ⟨(le_trans (le_max_left _ _) hrlo), by omega⟩

theorem positiveSmallEntropyShadowExpMajorantTerm_pos_of_branch_step
    {smallExp : Nat → Nat → ℚ} {a r : Nat}
    (ha : 2000 < a) (hr1 : 1 ≤ r)
    (hrhi : r < min (posKmax a) (posSmallCutoff a))
    (hExp : 0 < smallExp a r) :
    0 < positiveSmallEntropyShadowExpMajorantTerm smallExp a r :=
  positiveSmallEntropyShadowExpMajorantTerm_pos
    (by omega : 20 ≤ a)
    (mem_positiveKRange_of_small_branch_step hr1 hrhi)
    hExp

theorem positiveTemperedEntropyShadowExpMajorantTerm_pos_of_branch_step
    {temperedExp : Nat → Nat → ℚ} {a r : Nat}
    (ha : 2000 < a)
    (hrlo : max 1 (posTemperedCutoff a + 1) ≤ r)
    (hrhi : r < posKmax a)
    (hExp : 0 < temperedExp a r) :
    0 < positiveTemperedEntropyShadowExpMajorantTerm temperedExp a r :=
  positiveTemperedEntropyShadowExpMajorantTerm_pos
    (by omega : 20 ≤ a)
    (mem_positiveKRange_of_tempered_branch_step hrlo hrhi)
    hExp

/-- Convert a quotient-style successor estimate into the multiplicative step
used by the geometric-tail lemmas. -/
theorem le_mul_of_div_le_pos {x y q : ℚ} (hx : 0 < x)
    (hquot : y / x ≤ q) : y ≤ x * q := by
  have hmul : y ≤ q * x := (div_le_iff₀ hx).mp hquot
  simpa [mul_comm] using hmul

theorem positiveSmallEntropyShadowExp_step_of_div_step
    {smallExp : Nat → Nat → ℚ} {a r : Nat} {q : ℚ}
    (hpos : 0 < positiveSmallEntropyShadowExpMajorantTerm smallExp a r)
    (hquot :
      positiveSmallEntropyShadowExpMajorantTerm smallExp a (r + 1) /
          positiveSmallEntropyShadowExpMajorantTerm smallExp a r ≤ q) :
    positiveSmallEntropyShadowExpMajorantTerm smallExp a (r + 1)
      ≤ positiveSmallEntropyShadowExpMajorantTerm smallExp a r * q :=
  le_mul_of_div_le_pos hpos hquot

theorem positiveTemperedEntropyShadowExp_step_of_div_step
    {temperedExp : Nat → Nat → ℚ} {a r : Nat} {q : ℚ}
    (hpos : 0 < positiveTemperedEntropyShadowExpMajorantTerm temperedExp a r)
    (hquot :
      positiveTemperedEntropyShadowExpMajorantTerm temperedExp a (r + 1) /
          positiveTemperedEntropyShadowExpMajorantTerm temperedExp a r ≤ q) :
    positiveTemperedEntropyShadowExpMajorantTerm temperedExp a (r + 1)
      ≤ positiveTemperedEntropyShadowExpMajorantTerm temperedExp a r * q :=
  le_mul_of_div_le_pos hpos hquot

theorem positiveSmallEntropyShadowExp_quotient_eq_base_mul_exp
    {smallExp : Nat → Nat → ℚ} {a r : Nat}
    (hbase : positiveSmallEntropyShadowBaseTerm a r ≠ 0)
    (hExp : smallExp a r ≠ 0) :
    positiveSmallEntropyShadowExpMajorantTerm smallExp a (r + 1) /
        positiveSmallEntropyShadowExpMajorantTerm smallExp a r =
      positiveSmallEntropyShadowBaseStepQuotient a r *
        (smallExp a (r + 1) / smallExp a r) := by
  rw [positiveSmallEntropyShadowExpMajorantTerm_eq_base_mul,
    positiveSmallEntropyShadowExpMajorantTerm_eq_base_mul]
  unfold positiveSmallEntropyShadowBaseStepQuotient
  field_simp [hbase, hExp]

theorem positiveTemperedEntropyShadowExp_quotient_eq_base_mul_exp
    {temperedExp : Nat → Nat → ℚ} {a r : Nat}
    (hbase : positiveTemperedEntropyShadowBaseTerm a r ≠ 0)
    (hExp : temperedExp a r ≠ 0) :
    positiveTemperedEntropyShadowExpMajorantTerm temperedExp a (r + 1) /
        positiveTemperedEntropyShadowExpMajorantTerm temperedExp a r =
      positiveTemperedEntropyShadowBaseStepQuotient a r *
        (temperedExp a (r + 1) / temperedExp a r) := by
  rw [positiveTemperedEntropyShadowExpMajorantTerm_eq_base_mul,
    positiveTemperedEntropyShadowExpMajorantTerm_eq_base_mul]
  unfold positiveTemperedEntropyShadowBaseStepQuotient
  field_simp [hbase, hExp]

theorem positiveSmallEntropyShadowExp_quotient_eq_raw_mul_exp_of_branch
    {smallExp : Nat → Nat → ℚ} {a r : Nat}
    (ha : 2000 < a) (hr1 : 1 ≤ r)
    (hrhi : r < min (posKmax a) (posSmallCutoff a))
    (hExp : smallExp a r ≠ 0) :
    positiveSmallEntropyShadowExpMajorantTerm smallExp a (r + 1) /
        positiveSmallEntropyShadowExpMajorantTerm smallExp a r =
      positiveEntropyShadowBaseStepRawQuotient a r *
        (smallExp a (r + 1) / smallExp a r) := by
  rw [positiveSmallEntropyShadowExp_quotient_eq_base_mul_exp]
  · rw [positiveSmallEntropyShadowBaseStepQuotient_eq_raw_of_branch
      (by omega : 20 ≤ a) hr1 hrhi]
  · exact (positiveSmallEntropyShadowBaseTerm_pos
      (by omega : 20 ≤ a)
      (mem_positiveKRange_of_small_branch_step hr1 hrhi)).ne'
  · exact hExp

theorem positiveTemperedEntropyShadowExp_quotient_eq_raw_mul_exp_of_branch
    {temperedExp : Nat → Nat → ℚ} {a r : Nat}
    (ha : 2000 < a)
    (hrlo : max 1 (posTemperedCutoff a + 1) ≤ r)
    (hrhi : r < posKmax a) (hExp : temperedExp a r ≠ 0) :
    positiveTemperedEntropyShadowExpMajorantTerm temperedExp a (r + 1) /
        positiveTemperedEntropyShadowExpMajorantTerm temperedExp a r =
      positiveEntropyShadowBaseStepRawQuotient a r *
        (temperedExp a (r + 1) / temperedExp a r) := by
  rw [positiveTemperedEntropyShadowExp_quotient_eq_base_mul_exp]
  · rw [positiveTemperedEntropyShadowBaseStepQuotient_eq_raw_of_branch
      (by omega : 20 ≤ a) hrlo hrhi]
  · exact (positiveTemperedEntropyShadowBaseTerm_pos
      (by omega : 20 ≤ a)
      (mem_positiveKRange_of_tempered_branch_step hrlo hrhi)).ne'
  · exact hExp

theorem positiveSmallEntropyShadowExp_step_of_base_exp_quotient
    {smallExp : Nat → Nat → ℚ} {a r : Nat} {q : ℚ}
    (hbase : 0 < positiveSmallEntropyShadowBaseTerm a r)
    (hExp : 0 < smallExp a r)
    (hquot :
      positiveSmallEntropyShadowBaseStepQuotient a r *
          (smallExp a (r + 1) / smallExp a r) ≤ q) :
    positiveSmallEntropyShadowExpMajorantTerm smallExp a (r + 1)
      ≤ positiveSmallEntropyShadowExpMajorantTerm smallExp a r * q := by
  have hterm :
      0 < positiveSmallEntropyShadowExpMajorantTerm smallExp a r := by
    rw [positiveSmallEntropyShadowExpMajorantTerm_eq_base_mul]
    exact mul_pos hbase hExp
  refine positiveSmallEntropyShadowExp_step_of_div_step hterm ?_
  rw [positiveSmallEntropyShadowExp_quotient_eq_base_mul_exp
    hbase.ne' hExp.ne']
  exact hquot

theorem positiveTemperedEntropyShadowExp_step_of_base_exp_quotient
    {temperedExp : Nat → Nat → ℚ} {a r : Nat} {q : ℚ}
    (hbase : 0 < positiveTemperedEntropyShadowBaseTerm a r)
    (hExp : 0 < temperedExp a r)
    (hquot :
      positiveTemperedEntropyShadowBaseStepQuotient a r *
          (temperedExp a (r + 1) / temperedExp a r) ≤ q) :
    positiveTemperedEntropyShadowExpMajorantTerm temperedExp a (r + 1)
      ≤ positiveTemperedEntropyShadowExpMajorantTerm temperedExp a r * q := by
  have hterm :
      0 < positiveTemperedEntropyShadowExpMajorantTerm temperedExp a r := by
    rw [positiveTemperedEntropyShadowExpMajorantTerm_eq_base_mul]
    exact mul_pos hbase hExp
  refine positiveTemperedEntropyShadowExp_step_of_div_step hterm ?_
  rw [positiveTemperedEntropyShadowExp_quotient_eq_base_mul_exp
    hbase.ne' hExp.ne']
  exact hquot

theorem positiveSmallEntropyShadowExp_step_of_branch_base_exp_quotient
    {smallExp : Nat → Nat → ℚ} {a r : Nat} {q : ℚ}
    (ha : 2000 < a) (hr1 : 1 ≤ r)
    (hrhi : r < min (posKmax a) (posSmallCutoff a))
    (hExp : 0 < smallExp a r)
    (hquot :
      positiveSmallEntropyShadowBaseStepQuotient a r *
          (smallExp a (r + 1) / smallExp a r) ≤ q) :
    positiveSmallEntropyShadowExpMajorantTerm smallExp a (r + 1)
      ≤ positiveSmallEntropyShadowExpMajorantTerm smallExp a r * q :=
  positiveSmallEntropyShadowExp_step_of_base_exp_quotient
    (positiveSmallEntropyShadowBaseTerm_pos
      (by omega : 20 ≤ a)
      (mem_positiveKRange_of_small_branch_step hr1 hrhi))
    hExp hquot

theorem positiveTemperedEntropyShadowExp_step_of_branch_base_exp_quotient
    {temperedExp : Nat → Nat → ℚ} {a r : Nat} {q : ℚ}
    (ha : 2000 < a)
    (hrlo : max 1 (posTemperedCutoff a + 1) ≤ r)
    (hrhi : r < posKmax a)
    (hExp : 0 < temperedExp a r)
    (hquot :
      positiveTemperedEntropyShadowBaseStepQuotient a r *
          (temperedExp a (r + 1) / temperedExp a r) ≤ q) :
    positiveTemperedEntropyShadowExpMajorantTerm temperedExp a (r + 1)
      ≤ positiveTemperedEntropyShadowExpMajorantTerm temperedExp a r * q :=
  positiveTemperedEntropyShadowExp_step_of_base_exp_quotient
    (positiveTemperedEntropyShadowBaseTerm_pos
      (by omega : 20 ≤ a)
      (mem_positiveKRange_of_tempered_branch_step hrlo hrhi))
    hExp hquot

theorem positiveSmallEntropyShadowExp_step_of_branch_raw_exp_quotient
    {smallExp : Nat → Nat → ℚ} {a r : Nat} {q : ℚ}
    (ha : 2000 < a) (hr1 : 1 ≤ r)
    (hrhi : r < min (posKmax a) (posSmallCutoff a))
    (hExp : 0 < smallExp a r)
    (hquot :
      positiveEntropyShadowBaseStepRawQuotient a r *
          (smallExp a (r + 1) / smallExp a r) ≤ q) :
    positiveSmallEntropyShadowExpMajorantTerm smallExp a (r + 1)
      ≤ positiveSmallEntropyShadowExpMajorantTerm smallExp a r * q := by
  refine positiveSmallEntropyShadowExp_step_of_div_step
    (positiveSmallEntropyShadowExpMajorantTerm_pos_of_branch_step
      ha hr1 hrhi hExp) ?_
  rw [positiveSmallEntropyShadowExp_quotient_eq_raw_mul_exp_of_branch
    ha hr1 hrhi hExp.ne']
  exact hquot

theorem positiveTemperedEntropyShadowExp_step_of_branch_raw_exp_quotient
    {temperedExp : Nat → Nat → ℚ} {a r : Nat} {q : ℚ}
    (ha : 2000 < a)
    (hrlo : max 1 (posTemperedCutoff a + 1) ≤ r)
    (hrhi : r < posKmax a)
    (hExp : 0 < temperedExp a r)
    (hquot :
      positiveEntropyShadowBaseStepRawQuotient a r *
          (temperedExp a (r + 1) / temperedExp a r) ≤ q) :
    positiveTemperedEntropyShadowExpMajorantTerm temperedExp a (r + 1)
      ≤ positiveTemperedEntropyShadowExpMajorantTerm temperedExp a r * q := by
  refine positiveTemperedEntropyShadowExp_step_of_div_step
    (positiveTemperedEntropyShadowExpMajorantTerm_pos_of_branch_step
      ha hrlo hrhi hExp) ?_
  rw [positiveTemperedEntropyShadowExp_quotient_eq_raw_mul_exp_of_branch
    ha hrlo hrhi hExp.ne']
  exact hquot

theorem positiveSmallEntropyShadowExp_step_of_exp_pos_div_step
    {smallExp : Nat → Nat → ℚ} {a r : Nat} {q : ℚ}
    (ha : 2000 < a) (hr1 : 1 ≤ r)
    (hrhi : r < min (posKmax a) (posSmallCutoff a))
    (hExp : 0 < smallExp a r)
    (hquot :
      positiveSmallEntropyShadowExpMajorantTerm smallExp a (r + 1) /
          positiveSmallEntropyShadowExpMajorantTerm smallExp a r ≤ q) :
    positiveSmallEntropyShadowExpMajorantTerm smallExp a (r + 1)
      ≤ positiveSmallEntropyShadowExpMajorantTerm smallExp a r * q :=
  positiveSmallEntropyShadowExp_step_of_div_step
    (positiveSmallEntropyShadowExpMajorantTerm_pos_of_branch_step
      ha hr1 hrhi hExp)
    hquot

theorem positiveTemperedEntropyShadowExp_step_of_exp_pos_div_step
    {temperedExp : Nat → Nat → ℚ} {a r : Nat} {q : ℚ}
    (ha : 2000 < a)
    (hrlo : max 1 (posTemperedCutoff a + 1) ≤ r)
    (hrhi : r < posKmax a)
    (hExp : 0 < temperedExp a r)
    (hquot :
      positiveTemperedEntropyShadowExpMajorantTerm temperedExp a (r + 1) /
          positiveTemperedEntropyShadowExpMajorantTerm temperedExp a r ≤ q) :
    positiveTemperedEntropyShadowExpMajorantTerm temperedExp a (r + 1)
      ≤ positiveTemperedEntropyShadowExpMajorantTerm temperedExp a r * q :=
  positiveTemperedEntropyShadowExp_step_of_div_step
    (positiveTemperedEntropyShadowExpMajorantTerm_pos_of_branch_step
      ha hrlo hrhi hExp)
    hquot

theorem positiveEntropyShadowExpSmallBranchSum_le_inv_one_sub_of_ratio
    {smallExp : Nat → Nat → ℚ} {a : Nat} {q : ℚ}
    (hlohi : 1 ≤ min (posKmax a) (posSmallCutoff a))
    (hF0 : 0 ≤ positiveSmallEntropyShadowExpMajorantTerm smallExp a 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hstep :
      ∀ r, 1 ≤ r → r < min (posKmax a) (posSmallCutoff a) →
        positiveSmallEntropyShadowExpMajorantTerm smallExp a (r + 1)
          ≤ positiveSmallEntropyShadowExpMajorantTerm smallExp a r * q) :
    positiveEntropyShadowExpSmallBranchSum smallExp a
      ≤ positiveSmallEntropyShadowExpMajorantTerm smallExp a 1 *
        (1 / (1 - q)) := by
  rw [positiveEntropyShadowExpSmallBranchSum_eq_Icc]
  exact geom_chain_Icc_sum_le_inv_one_sub
    (fun k => positiveSmallEntropyShadowExpMajorantTerm smallExp a k)
    hlohi hF0 hq0 hq1 hstep

theorem positiveEntropyShadowExpSmallBranchSum_le_inv_one_sub_of_ratio_large
    {smallExp : Nat → Nat → ℚ} {a : Nat} {q : ℚ}
    (ha : 2000 < a)
    (hF0 : 0 ≤ positiveSmallEntropyShadowExpMajorantTerm smallExp a 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hstep :
      ∀ r, 1 ≤ r → r < min (posKmax a) (posSmallCutoff a) →
        positiveSmallEntropyShadowExpMajorantTerm smallExp a (r + 1)
          ≤ positiveSmallEntropyShadowExpMajorantTerm smallExp a r * q) :
    positiveEntropyShadowExpSmallBranchSum smallExp a
      ≤ positiveSmallEntropyShadowExpMajorantTerm smallExp a 1 *
        (1 / (1 - q)) :=
  positiveEntropyShadowExpSmallBranchSum_le_inv_one_sub_of_ratio
    (positiveSmallBranch_hi_nonempty_of_large ha) hF0 hq0 hq1 hstep

theorem positiveEntropyShadowExpSmallBranchSum_le_halfEdgeBudget_of_ratio_large
    {smallExp : Nat → Nat → ℚ} {a : Nat} {q : ℚ}
    (ha : 2000 < a)
    (hF0 : 0 ≤ positiveSmallEntropyShadowExpMajorantTerm smallExp a 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hstep :
      ∀ r, 1 ≤ r → r < min (posKmax a) (posSmallCutoff a) →
        positiveSmallEntropyShadowExpMajorantTerm smallExp a (r + 1)
          ≤ positiveSmallEntropyShadowExpMajorantTerm smallExp a r * q)
    (hbudget :
      positiveSmallEntropyShadowExpMajorantTerm smallExp a 1 *
        (1 / (1 - q)) ≤ positiveEdgeBudget / 2) :
    positiveEntropyShadowExpSmallBranchSum smallExp a ≤ positiveEdgeBudget / 2 :=
  (positiveEntropyShadowExpSmallBranchSum_le_inv_one_sub_of_ratio_large
    ha hF0 hq0 hq1 hstep).trans hbudget

theorem positiveEntropyShadowExpSmallBranchSum_le_halfEdgeBudget_of_ratio_reserve_large
    {smallExp : Nat → Nat → ℚ} {a : Nat} {q : ℚ}
    (ha : 2000 < a)
    (hF0 : 0 ≤ positiveSmallEntropyShadowExpMajorantTerm smallExp a 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hstep :
      ∀ r, 1 ≤ r → r < min (posKmax a) (posSmallCutoff a) →
        positiveSmallEntropyShadowExpMajorantTerm smallExp a (r + 1)
          ≤ positiveSmallEntropyShadowExpMajorantTerm smallExp a r * q)
    (hfirst :
      positiveSmallEntropyShadowExpMajorantTerm smallExp a 1
        ≤ (positiveEdgeBudget / 2) * (1 - q)) :
    positiveEntropyShadowExpSmallBranchSum smallExp a ≤ positiveEdgeBudget / 2 :=
  positiveEntropyShadowExpSmallBranchSum_le_halfEdgeBudget_of_ratio_large
    ha hF0 hq0 hq1 hstep
    (mul_inv_one_sub_le_of_le_mul_one_sub hq1 hfirst)

theorem positiveEntropyShadowExpTemperedBranchSum_le_inv_one_sub_of_ratio
    {temperedExp : Nat → Nat → ℚ} {a : Nat} {q : ℚ}
    (hlohi : max 1 (posTemperedCutoff a + 1) ≤ posKmax a)
    (hF0 :
      0 ≤ positiveTemperedEntropyShadowExpMajorantTerm temperedExp a
        (max 1 (posTemperedCutoff a + 1)))
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hstep :
      ∀ r, max 1 (posTemperedCutoff a + 1) ≤ r → r < posKmax a →
        positiveTemperedEntropyShadowExpMajorantTerm temperedExp a (r + 1)
          ≤ positiveTemperedEntropyShadowExpMajorantTerm temperedExp a r * q) :
    positiveEntropyShadowExpTemperedBranchSum temperedExp a
      ≤ positiveTemperedEntropyShadowExpMajorantTerm temperedExp a
          (max 1 (posTemperedCutoff a + 1)) * (1 / (1 - q)) := by
  rw [positiveEntropyShadowExpTemperedBranchSum_eq_Icc]
  exact geom_chain_Icc_sum_le_inv_one_sub
    (fun k => positiveTemperedEntropyShadowExpMajorantTerm temperedExp a k)
    hlohi hF0 hq0 hq1 hstep

theorem positiveEntropyShadowExpTemperedBranchSum_le_inv_one_sub_of_ratio_large
    {temperedExp : Nat → Nat → ℚ} {a : Nat} {q : ℚ}
    (ha : 2000 < a)
    (hF0 :
      0 ≤ positiveTemperedEntropyShadowExpMajorantTerm temperedExp a
        (max 1 (posTemperedCutoff a + 1)))
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hstep :
      ∀ r, max 1 (posTemperedCutoff a + 1) ≤ r → r < posKmax a →
        positiveTemperedEntropyShadowExpMajorantTerm temperedExp a (r + 1)
          ≤ positiveTemperedEntropyShadowExpMajorantTerm temperedExp a r * q) :
    positiveEntropyShadowExpTemperedBranchSum temperedExp a
      ≤ positiveTemperedEntropyShadowExpMajorantTerm temperedExp a
          (max 1 (posTemperedCutoff a + 1)) * (1 / (1 - q)) :=
  positiveEntropyShadowExpTemperedBranchSum_le_inv_one_sub_of_ratio
    (positiveTemperedBranch_start_le_posKmax_of_large ha)
    hF0 hq0 hq1 hstep

theorem positiveEntropyShadowExpTemperedBranchSum_le_halfEdgeBudget_of_ratio_large
    {temperedExp : Nat → Nat → ℚ} {a : Nat} {q : ℚ}
    (ha : 2000 < a)
    (hF0 :
      0 ≤ positiveTemperedEntropyShadowExpMajorantTerm temperedExp a
        (max 1 (posTemperedCutoff a + 1)))
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hstep :
      ∀ r, max 1 (posTemperedCutoff a + 1) ≤ r → r < posKmax a →
        positiveTemperedEntropyShadowExpMajorantTerm temperedExp a (r + 1)
          ≤ positiveTemperedEntropyShadowExpMajorantTerm temperedExp a r * q)
    (hbudget :
      positiveTemperedEntropyShadowExpMajorantTerm temperedExp a
        (max 1 (posTemperedCutoff a + 1)) * (1 / (1 - q))
          ≤ positiveEdgeBudget / 2) :
    positiveEntropyShadowExpTemperedBranchSum temperedExp a ≤ positiveEdgeBudget / 2 :=
  (positiveEntropyShadowExpTemperedBranchSum_le_inv_one_sub_of_ratio_large
    ha hF0 hq0 hq1 hstep).trans hbudget

theorem positiveEntropyShadowExpTemperedBranchSum_le_halfEdgeBudget_of_ratio_reserve_large
    {temperedExp : Nat → Nat → ℚ} {a : Nat} {q : ℚ}
    (ha : 2000 < a)
    (hF0 :
      0 ≤ positiveTemperedEntropyShadowExpMajorantTerm temperedExp a
        (max 1 (posTemperedCutoff a + 1)))
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hstep :
      ∀ r, max 1 (posTemperedCutoff a + 1) ≤ r → r < posKmax a →
        positiveTemperedEntropyShadowExpMajorantTerm temperedExp a (r + 1)
          ≤ positiveTemperedEntropyShadowExpMajorantTerm temperedExp a r * q)
    (hfirst :
      positiveTemperedEntropyShadowExpMajorantTerm temperedExp a
        (max 1 (posTemperedCutoff a + 1))
          ≤ (positiveEdgeBudget / 2) * (1 - q)) :
    positiveEntropyShadowExpTemperedBranchSum temperedExp a ≤ positiveEdgeBudget / 2 :=
  positiveEntropyShadowExpTemperedBranchSum_le_halfEdgeBudget_of_ratio_large
    ha hF0 hq0 hq1 hstep
    (mul_inv_one_sub_le_of_le_mul_one_sub hq1 hfirst)

def positiveEntropyShadowEnvelope (a N : Nat) : ℚ :=
  positiveCustomEnvelope
    positiveSmallEntropyShadowMajorantTerm
    positiveTemperedEntropyShadowMajorantTerm a N

def positiveEntropyShadowEnvelopeBound (a : Nat) (soloBound : ℚ) : ℚ :=
  positiveCustomEnvelopeBound
    positiveSmallEntropyShadowMajorantTerm
    positiveTemperedEntropyShadowMajorantTerm a soloBound

@[simp] theorem positiveEntropyShadowEnvelope_eq (a N : Nat) :
    positiveEntropyShadowEnvelope a N =
      positiveCustomEnvelope
        positiveSmallEntropyShadowMajorantTerm
        positiveTemperedEntropyShadowMajorantTerm a N := rfl

@[simp] theorem positiveEntropyShadowEnvelopeBound_eq (a : Nat) (soloBound : ℚ) :
    positiveEntropyShadowEnvelopeBound a soloBound =
      positiveCustomEnvelopeBound
        positiveSmallEntropyShadowMajorantTerm
        positiveTemperedEntropyShadowMajorantTerm a soloBound := rfl

theorem positiveSmallMajorantTerm_le_entropyShadowMajorantTerm
    {a k : Nat} (ha : 1 ≤ a) (hk : 2 ≤ k) (hklt : k < a - 1)
    (hExp :
      0 ≤ partialExpUpper (positiveSmallExponentUpper a k) positiveExpCutoff) :
    positiveSmallMajorantTerm a k ≤ positiveSmallEntropyShadowMajorantTerm a k := by
  have hhi : (0 : ℚ) ≤ 65 / (posNhi a : ℚ) := by
    have hpos : (0 : ℚ) < (posNhi a : ℚ) := by
      exact_mod_cast posNhi_pos ha
    positivity
  rw [positiveSmallMajorantTerm_eq_binomRatio]
  unfold positiveSmallEntropyShadowMajorantTerm
  gcongr
  · exact positiveDyadicDecay_nonneg (posJ a k)
  · exact positiveBinomRatio_le_entropyShadowPosJBound hk hklt

theorem positiveTemperedMajorantTerm_le_entropyShadowMajorantTerm
    {a k : Nat} (ha : 2 ≤ a) (hk : 2 ≤ k) (hklt : k < a - 1)
    (hExp :
      0 ≤ partialExpUpper (positiveTemperedExponentUpper a k) positiveExpCutoff) :
    positiveTemperedMajorantTerm a k ≤
      positiveTemperedEntropyShadowMajorantTerm a k := by
  have hlo : (0 : ℚ) ≤ 96 / (posNlo a : ℚ) := by
    have hpos : (0 : ℚ) < (posNlo a : ℚ) := by
      exact_mod_cast posNlo_pos ha
    positivity
  rw [positiveTemperedMajorantTerm_eq_binomRatio]
  unfold positiveTemperedEntropyShadowMajorantTerm
  gcongr
  · exact positiveDyadicDecay_nonneg (posJ a k)
  · exact positiveBinomRatio_le_entropyShadowPosJBound hk hklt

theorem positiveSmallMajorantTerm_le_entropyShadowMajorantTerm_of_mem_large
    {a k : Nat} (ha : 20 ≤ a) (hkRange : k ∈ positiveKRange a)
    (hExp :
      0 ≤ partialExpUpper (positiveSmallExponentUpper a k) positiveExpCutoff) :
    positiveSmallMajorantTerm a k ≤ positiveSmallEntropyShadowMajorantTerm a k := by
  have hhi : (0 : ℚ) ≤ 65 / (posNhi a : ℚ) := by
    have hpos : (0 : ℚ) < (posNhi a : ℚ) := by
      exact_mod_cast posNhi_pos (by omega : 1 ≤ a)
    positivity
  rw [positiveSmallMajorantTerm_eq_binomRatio]
  unfold positiveSmallEntropyShadowMajorantTerm
  gcongr
  · exact positiveDyadicDecay_nonneg (posJ a k)
  · exact positiveBinomRatio_le_entropyShadowPosJBound_of_mem_large ha hkRange

theorem positiveTemperedMajorantTerm_le_entropyShadowMajorantTerm_of_mem_large
    {a k : Nat} (ha : 20 ≤ a) (hkRange : k ∈ positiveKRange a)
    (hExp :
      0 ≤ partialExpUpper (positiveTemperedExponentUpper a k) positiveExpCutoff) :
    positiveTemperedMajorantTerm a k ≤
      positiveTemperedEntropyShadowMajorantTerm a k := by
  have hlo : (0 : ℚ) ≤ 96 / (posNlo a : ℚ) := by
    have hpos : (0 : ℚ) < (posNlo a : ℚ) := by
      exact_mod_cast posNlo_pos (by omega : 2 ≤ a)
    positivity
  rw [positiveTemperedMajorantTerm_eq_binomRatio]
  unfold positiveTemperedEntropyShadowMajorantTerm
  gcongr
  · exact positiveDyadicDecay_nonneg (posJ a k)
  · exact positiveBinomRatio_le_entropyShadowPosJBound_of_mem_large ha hkRange

/-- Coefficient-ratio bound obtained from the already formalized
`c_r ≤ (4/25)6^r(r-1)!` and `c_r ≥ (5/36)6^r(r-1)!`.
The paper records the sharper `9/(5π²)` constant; Lean uses the rational
`576/3125 < 1`, which is enough for the displayed majorants. -/
theorem positiveCRatio_le_dnorm_binomRatio {a k : Nat}
    (ha : 2 ≤ a) (hk1 : 1 ≤ k) (hkmax : k ≤ posKmax a) :
    positiveCRatio a k ≤ (576/3125) * positiveBinomRatio a k := by
  have ha1 : 1 ≤ a := by omega
  have hka : k < a := lt_self_of_le_posKmax ha1 hkmax
  have hj1 : 1 ≤ posJ a k := by
    exact Nat.succ_le_of_lt (posJ_pos_of_le_posKmax ha1 hkmax)
  have hca_pos : 0 < c a := c_pos a (by omega : 1 ≤ a)
  have hden_lb := c_lb a (by omega : 1 ≤ a)
  have hden_lb_pos :
      0 < (5/36) * (6^a * ((a-1).factorial : ℚ)) := by
    positivity
  have hnum_le :
      c k * c (posJ a k)
        ≤ (4/25 * (6^k * ((k-1).factorial : ℚ))) *
            (4/25 * (6^(posJ a k) * ((posJ a k-1).factorial : ℚ))) := by
    exact mul_le_mul (c_ub k hk1) (c_ub (posJ a k) hj1)
      (c_nonneg (posJ a k)) (by positivity)
  have hnum_bound_nonneg :
      0 ≤ (4/25 * (6^k * ((k-1).factorial : ℚ))) *
            (4/25 * (6^(posJ a k) * ((posJ a k-1).factorial : ℚ))) := by
    positivity
  have hchoose_ne : (((positiveBinomDen a k : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast (positiveBinomDen_pos ha hk1 hkmax).ne'
  have ha1_ne : (((a-1 : Nat) : ℚ)) ≠ 0 := by
    exact_mod_cast (by omega : a-1 ≠ 0)
  have hfac_k_ne : (((k-1).factorial : Nat) : ℚ) ≠ 0 := by positivity
  have hfac_j_ne : (((posJ a k-1).factorial : Nat) : ℚ) ≠ 0 := by positivity
  have hfac_a2_ne : (((a-2).factorial : Nat) : ℚ) ≠ 0 := by positivity
  have hpow6 : (6:ℚ)^k * (6:ℚ)^(posJ a k) = 6^a := by
    rw [← pow_add]
    congr 1
    unfold posJ
    omega
  have hchoose :
      (((positiveBinomDen a k : ℕ) : ℚ))
          * (((k-1).factorial : Nat) : ℚ)
          * (((posJ a k-1).factorial : Nat) : ℚ)
        = (((a-2).factorial : Nat) : ℚ) := by
    unfold positiveBinomDen posJ
    have h := Nat.choose_mul_factorial_mul_factorial
      (show k-1 ≤ a-2 by omega)
    rw [show a-2-(k-1) = a-k-1 by omega] at h
    exact_mod_cast h
  have hfaca :
      (((a-1).factorial : Nat) : ℚ)
        = (((a-1 : Nat) : ℚ)) * (((a-2).factorial : Nat) : ℚ) := by
    rw [show a-1 = (a-2)+1 by omega, Nat.factorial_succ]
    push_cast
    ring
  have halg :
      ((4/25 * (6^k * ((k-1).factorial : ℚ))) *
          (4/25 * (6^(posJ a k) * ((posJ a k-1).factorial : ℚ))))
        / ((5/36) * (6^a * ((a-1).factorial : ℚ)))
      =
        (576/3125) * positiveBinomRatio a k := by
    rw [hfaca, ← hchoose, ← hpow6]
    unfold positiveBinomRatio
    field_simp [ha1_ne, hchoose_ne, hfac_k_ne, hfac_j_ne, hfac_a2_ne]
    ring
  calc
    positiveCRatio a k
        = c k * c (posJ a k) / c a := by
            rfl
    _ ≤ ((4/25 * (6^k * ((k-1).factorial : ℚ))) *
          (4/25 * (6^(posJ a k) * ((posJ a k-1).factorial : ℚ)))) / c a := by
        exact div_le_div_of_nonneg_right hnum_le hca_pos.le
    _ ≤
        ((4/25 * (6^k * ((k-1).factorial : ℚ))) *
          (4/25 * (6^(posJ a k) * ((posJ a k-1).factorial : ℚ))))
        / ((5/36) * (6^a * ((a-1).factorial : ℚ))) := by
        exact div_le_div_of_nonneg_left hnum_bound_nonneg hden_lb_pos hden_lb
    _ = (576/3125) * positiveBinomRatio a k := halg

theorem positiveCRatio_le_binomRatio {a k : Nat}
    (ha : 2 ≤ a) (hk1 : 1 ≤ k) (hkmax : k ≤ posKmax a) :
    positiveCRatio a k ≤ positiveBinomRatio a k := by
  have hratio_nonneg : 0 ≤ positiveBinomRatio a k :=
    positiveBinomRatio_nonneg
  have hconstant : (576/3125 : ℚ) * positiveBinomRatio a k
      ≤ positiveBinomRatio a k := by
    nlinarith
  exact (positiveCRatio_le_dnorm_binomRatio ha hk1 hkmax).trans hconstant

/-- TeX-style product bridge after inserting the reciprocal-binomial bound
for `R_{k,a}`.  The remaining inputs are only pointwise bounds for `X_k(N)`
and `Y_{a-k}(N)`. -/
theorem positiveFactorizedRawTerm_le_of_XY_bounds
    {a N k : Nat} {X Y : ℚ} (hN : 1 ≤ N) (ha : 2 ≤ a)
    (hkRange : k ∈ positiveKRange a) (hB : 0 < Bq N k)
    (hX : Xnorm N k ≤ X)
    (hY : Ynorm N (posJ a k) ≤ Y) :
    positiveFactorizedRawTerm a N k ≤
      ((N : ℚ) / 2) * positiveBinomRatio a k *
        positiveDyadicDecay (posJ a k) * X * Y := by
  rcases (mem_positiveKRange.mp hkRange) with ⟨hk1, hkmax⟩
  exact positiveFactorizedRawTerm_le_of_bounds hN hk1 hB
    (positiveCRatio_le_binomRatio ha hk1 hkmax) hX hY

theorem positiveFactorizedRawTerm_le_smallScalar_of_XYProduct
    {a N k : Nat} (hN : 1 ≤ N) (ha : 2 ≤ a)
    (hkRange : k ∈ positiveKRange a) (hB : 0 < Bq N k)
    (hXY :
      Xnorm N k * Ynorm N (posJ a k) ≤ positiveSmallXYProductBound a N k) :
    positiveFactorizedRawTerm a N k ≤ positiveSmallScalarProductBound a k := by
  rcases (mem_positiveKRange.mp hkRange) with ⟨hk1, hkmax⟩
  have hNQpos : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  have hNQ : (N : ℚ) ≠ 0 := hNQpos.ne'
  have hhiPos : (0 : ℚ) < (posNhi a : ℚ) := by
    exact_mod_cast posNhi_pos (by omega : 1 ≤ a)
  have hhiQ : (posNhi a : ℚ) ≠ 0 := hhiPos.ne'
  have hR := positiveCRatio_le_binomRatio ha hk1 hkmax
  have hX0 : 0 ≤ Xnorm N k := ((Bq_pos_iff_Xnorm_pos hN hk1).mp hB).le
  have hY0 : 0 ≤ Ynorm N (posJ a k) := Ynorm_nonneg N (posJ a k)
  have hprod :
      positiveCRatio a k * (Xnorm N k * Ynorm N (posJ a k))
        ≤ positiveBinomRatio a k * positiveSmallXYProductBound a N k :=
    mul_le_mul hR hXY (mul_nonneg hX0 hY0) positiveBinomRatio_nonneg
  have hcommon :
      0 ≤ ((N : ℚ) / 2) * positiveDyadicDecay (posJ a k) := by
    exact mul_nonneg (by positivity) (positiveDyadicDecay_nonneg (posJ a k))
  calc
    positiveFactorizedRawTerm a N k
        = ((N : ℚ) / 2) * positiveDyadicDecay (posJ a k) *
            (positiveCRatio a k * (Xnorm N k * Ynorm N (posJ a k))) := by
          unfold positiveFactorizedRawTerm
          ring
    _ ≤ ((N : ℚ) / 2) * positiveDyadicDecay (posJ a k) *
            (positiveBinomRatio a k * positiveSmallXYProductBound a N k) :=
          mul_le_mul_of_nonneg_left hprod hcommon
    _ = positiveSmallScalarProductBound a k := by
          unfold positiveSmallXYProductBound positiveSmallScalarProductBound
          field_simp [hNQ, hhiQ]
          ring

theorem positiveFactorizedRawTerm_le_smallScalar_of_XYProductAt
    {a N k : Nat} (hN : 1 ≤ N) (ha : 2 ≤ a)
    (hkRange : k ∈ positiveKRange a) (hB : 0 < Bq N k)
    (hXY :
      Xnorm N k * Ynorm N (posJ a k) ≤ positiveSmallXYProductAtBound a N k)
    (hedge :
      positiveSmallXYProductAtBound a N k ≤ positiveSmallXYProductBound a N k) :
    positiveFactorizedRawTerm a N k ≤ positiveSmallScalarProductBound a k :=
  positiveFactorizedRawTerm_le_smallScalar_of_XYProduct
    hN ha hkRange hB (hXY.trans hedge)

theorem positiveFactorizedRawTerm_le_temperedScalar_of_XYProduct
    {a N k : Nat} (hN : 1 ≤ N) (ha : 2 ≤ a)
    (hkRange : k ∈ positiveKRange a) (hB : 0 < Bq N k)
    (hXY :
      Xnorm N k * Ynorm N (posJ a k) ≤ positiveTemperedXYProductBound a N k) :
    positiveFactorizedRawTerm a N k ≤
      positiveTemperedScalarProductBound a N k := by
  rcases (mem_positiveKRange.mp hkRange) with ⟨hk1, hkmax⟩
  have hNQpos : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  have hNQ : (N : ℚ) ≠ 0 := hNQpos.ne'
  have hR := positiveCRatio_le_binomRatio ha hk1 hkmax
  have hX0 : 0 ≤ Xnorm N k := ((Bq_pos_iff_Xnorm_pos hN hk1).mp hB).le
  have hY0 : 0 ≤ Ynorm N (posJ a k) := Ynorm_nonneg N (posJ a k)
  have hprod :
      positiveCRatio a k * (Xnorm N k * Ynorm N (posJ a k))
        ≤ positiveBinomRatio a k * positiveTemperedXYProductBound a N k :=
    mul_le_mul hR hXY (mul_nonneg hX0 hY0) positiveBinomRatio_nonneg
  have hcommon :
      0 ≤ ((N : ℚ) / 2) * positiveDyadicDecay (posJ a k) := by
    exact mul_nonneg (by positivity) (positiveDyadicDecay_nonneg (posJ a k))
  calc
    positiveFactorizedRawTerm a N k
        = ((N : ℚ) / 2) * positiveDyadicDecay (posJ a k) *
            (positiveCRatio a k * (Xnorm N k * Ynorm N (posJ a k))) := by
          unfold positiveFactorizedRawTerm
          ring
    _ ≤ ((N : ℚ) / 2) * positiveDyadicDecay (posJ a k) *
            (positiveBinomRatio a k * positiveTemperedXYProductBound a N k) :=
          mul_le_mul_of_nonneg_left hprod hcommon
    _ = positiveTemperedScalarProductBound a N k := by
          unfold positiveTemperedXYProductBound positiveTemperedScalarProductBound
          field_simp [hNQ]
          ring

theorem partialExpUpper_nonneg_of_nonneg_lt {y : ℚ} {T₀ : Nat}
    (hy : 0 ≤ y) (hyT : y < (T₀ : ℚ)) :
    0 ≤ partialExpUpper y T₀ := by
  have hTpos : 0 < T₀ := by
    by_contra hnot
    have hzero : T₀ = 0 := Nat.eq_zero_of_not_pos hnot
    subst T₀
    norm_num at hyT
    linarith
  have hTQ : (0 : ℚ) < (T₀ : ℚ) := by exact_mod_cast hTpos
  have hden : (0 : ℚ) < 1 - y/(T₀ : ℚ) := by
    rw [sub_pos, div_lt_one hTQ]
    exact hyT
  unfold partialExpUpper
  apply add_nonneg
  · exact Finset.sum_nonneg fun t _ => by positivity
  · positivity

theorem partialExpUpper_mono_of_nonneg_le_lt {y z : ℚ} {T₀ : Nat}
    (hy0 : 0 ≤ y) (hyz : y ≤ z) (hzT : z < (T₀ : ℚ)) :
    partialExpUpper y T₀ ≤ partialExpUpper z T₀ := by
  have hz0 : 0 ≤ z := hy0.trans hyz
  have hyT : y < (T₀ : ℚ) := lt_of_le_of_lt hyz hzT
  have hTpos : 0 < T₀ := by
    by_contra hnot
    have hzero : T₀ = 0 := Nat.eq_zero_of_not_pos hnot
    subst T₀
    norm_num at hzT
    linarith
  have hTQ : (0 : ℚ) < (T₀ : ℚ) := by exact_mod_cast hTpos
  have hden_y_pos : 0 < 1 - y/(T₀ : ℚ) := by
    rw [sub_pos, div_lt_one hTQ]
    exact hyT
  have hden_z_pos : 0 < 1 - z/(T₀ : ℚ) := by
    rw [sub_pos, div_lt_one hTQ]
    exact hzT
  have hdiv_yz : y/(T₀ : ℚ) ≤ z/(T₀ : ℚ) :=
    div_le_div_of_nonneg_right hyz hTQ.le
  have hden_le : 1 - z/(T₀ : ℚ) ≤ 1 - y/(T₀ : ℚ) := by
    linarith
  have hrecip :
      1 / (1 - y/(T₀ : ℚ)) ≤ 1 / (1 - z/(T₀ : ℚ)) :=
    one_div_le_one_div_of_le hden_z_pos hden_le
  unfold partialExpUpper
  apply add_le_add
  · refine Finset.sum_le_sum fun t _ => ?_
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ hy0 hyz t) (by positivity)
  · exact mul_le_mul
      (div_le_div_of_nonneg_right
        (pow_le_pow_left₀ hy0 hyz T₀) (by positivity))
      hrecip
      (div_nonneg (by norm_num : (0 : ℚ) ≤ 1) hden_y_pos.le)
      (div_nonneg (pow_nonneg hz0 T₀) (by positivity))

theorem positiveSmallExponentUpper_nonneg {a k : Nat}
    (hj : 0 < posJ a k) :
    0 ≤ positiveSmallExponentUpper a k := by
  unfold positiveSmallExponentUpper
  have hjQ : (0 : ℚ) < (posJ a k : ℚ) := by exact_mod_cast hj
  positivity

theorem positiveSmallExponentAt_nonneg {a N k : Nat}
    (hj : 0 < posJ a k) :
    0 ≤ positiveSmallExponentAt a N k := by
  unfold positiveSmallExponentAt
  have hjQ : (0 : ℚ) < (posJ a k : ℚ) := by exact_mod_cast hj
  positivity

theorem positiveSmallExponentAt_le_upper_of_rectangle {a N k : Nat}
    (hrect : positiveRectangle a N) :
    positiveSmallExponentAt a N k ≤ positiveSmallExponentUpper a k := by
  have hcut : (ceilSqrt N : ℚ) ≤ (posSmallCutoff a : ℚ) := by
    exact_mod_cast (smallRegime_le_upper_edge hrect.2 le_rfl)
  unfold positiveSmallExponentAt positiveSmallExponentUpper
  nlinarith

theorem positiveSmallTangentExponentAt_nonneg {a N k : Nat}
    (hj : 0 < posJ a k) :
    0 ≤ positiveSmallTangentExponentAt a N k := by
  unfold positiveSmallTangentExponentAt
  have hjQ : (0 : ℚ) < (posJ a k : ℚ) := by exact_mod_cast hj
  have htangent : 0 ≤ positiveSqrtTangentUpper N :=
    positiveSqrtTangentUpper_nonneg N
  positivity

theorem positiveSmallTangentExponentAt_le_upper_of_rectangle {a N k : Nat}
    (hrect : positiveRectangle a N) :
    positiveSmallTangentExponentAt a N k ≤ positiveSmallExponentUpper a k :=
  (positiveSmallTangentExponentAt_le_at a N k).trans
    (positiveSmallExponentAt_le_upper_of_rectangle hrect)

theorem positiveTemperedExponentUpper_nonneg {a k : Nat}
    (hk : 1 ≤ k) (hj : 0 < posJ a k) :
    0 ≤ positiveTemperedExponentUpper a k := by
  unfold positiveTemperedExponentUpper
  have hkQ : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
  have hjQ : (0 : ℚ) < (posJ a k : ℚ) := by exact_mod_cast hj
  positivity

theorem posSmallCutoff_le_155 {a : Nat} (ha : a ≤ 2000) :
    posSmallCutoff a ≤ 155 := by
  unfold posSmallCutoff
  apply ceilSqrt_le_of_le_sq
  unfold posNhi
  omega

theorem posTemperedCutoff_ge_49 {a : Nat} (ha : 401 ≤ a) :
    49 ≤ posTemperedCutoff a := by
  have hlt : 48 < posTemperedCutoff a := by
    unfold posTemperedCutoff
    apply lt_ceilSqrt_of_sq_lt
    unfold posNlo
    omega
  omega

theorem positiveSmallExponentUpper_lt_expCutoff {a k : Nat}
    (ha1 : 1 ≤ a) (ha2000 : a ≤ 2000) (hkmax : k ≤ posKmax a) :
    positiveSmallExponentUpper a k < (positiveExpCutoff : ℚ) := by
  have hcutNat : posSmallCutoff a ≤ 155 := posSmallCutoff_le_155 ha2000
  have hcut : (posSmallCutoff a : ℚ) ≤ 155 := by exact_mod_cast hcutNat
  have hjpos : 0 < posJ a k := posJ_pos_of_le_posKmax ha1 hkmax
  have hja : posJ a k ≤ a := by
    unfold posJ
    omega
  have hj2000 : (posJ a k : ℚ) ≤ 2000 := by
    exact_mod_cast hja.trans ha2000
  have hratio : (a : ℚ) / (posJ a k : ℚ) ≤ 10 := by
    have hjQ : (0 : ℚ) < (posJ a k : ℚ) := by exact_mod_cast hjpos
    rw [div_le_iff₀ hjQ]
    exact_mod_cast self_le_ten_mul_posJ_of_le_posKmax hkmax
  calc
    positiveSmallExponentUpper a k
        ≤ (1139/1000) * (155 : ℚ) + (1/5) * 2000 + (29/10) * 10 + 1 := by
          unfold positiveSmallExponentUpper
          gcongr
    _ < (positiveExpCutoff : ℚ) := by
          norm_num [positiveExpCutoff]

theorem partialExpUpper_smallExponentAt_le_upper
    {a N k : Nat} (ha1 : 1 ≤ a) (ha2000 : a ≤ 2000)
    (hrect : positiveRectangle a N) (hkRange : k ∈ positiveKRange a) :
    partialExpUpper (positiveSmallExponentAt a N k) positiveExpCutoff
      ≤ partialExpUpper (positiveSmallExponentUpper a k) positiveExpCutoff := by
  rcases (mem_positiveKRange.mp hkRange) with ⟨_hk1, hkmax⟩
  have hjpos : 0 < posJ a k := posJ_pos_of_le_posKmax ha1 hkmax
  exact partialExpUpper_mono_of_nonneg_le_lt
    (positiveSmallExponentAt_nonneg hjpos)
    (positiveSmallExponentAt_le_upper_of_rectangle hrect)
    (positiveSmallExponentUpper_lt_expCutoff ha1 ha2000 hkmax)

theorem positiveSmallExponentAt_lt_expCutoff
    {a N k : Nat} (ha1 : 1 ≤ a) (ha2000 : a ≤ 2000)
    (hrect : positiveRectangle a N) (hkRange : k ∈ positiveKRange a) :
    positiveSmallExponentAt a N k < (positiveExpCutoff : ℚ) := by
  rcases (mem_positiveKRange.mp hkRange) with ⟨_hk1, hkmax⟩
  exact (positiveSmallExponentAt_le_upper_of_rectangle hrect).trans_lt
    (positiveSmallExponentUpper_lt_expCutoff ha1 ha2000 hkmax)

theorem partialExpUpper_smallTangentExponentAt_le_upper
    {a N k : Nat} (ha1 : 1 ≤ a) (ha2000 : a ≤ 2000)
    (hrect : positiveRectangle a N) (hkRange : k ∈ positiveKRange a) :
    partialExpUpper (positiveSmallTangentExponentAt a N k) positiveExpCutoff
      ≤ partialExpUpper (positiveSmallExponentUpper a k) positiveExpCutoff := by
  rcases (mem_positiveKRange.mp hkRange) with ⟨_hk1, hkmax⟩
  have hjpos : 0 < posJ a k := posJ_pos_of_le_posKmax ha1 hkmax
  exact partialExpUpper_mono_of_nonneg_le_lt
    (positiveSmallTangentExponentAt_nonneg hjpos)
    (positiveSmallTangentExponentAt_le_upper_of_rectangle hrect)
    (positiveSmallExponentUpper_lt_expCutoff ha1 ha2000 hkmax)

theorem positiveSmallTangentExponentAt_lt_expCutoff
    {a N k : Nat} (ha1 : 1 ≤ a) (ha2000 : a ≤ 2000)
    (hrect : positiveRectangle a N) (hkRange : k ∈ positiveKRange a) :
    positiveSmallTangentExponentAt a N k < (positiveExpCutoff : ℚ) := by
  rcases (mem_positiveKRange.mp hkRange) with ⟨_hk1, hkmax⟩
  exact (positiveSmallTangentExponentAt_le_upper_of_rectangle hrect).trans_lt
    (positiveSmallExponentUpper_lt_expCutoff ha1 ha2000 hkmax)

theorem positiveTemperedExponentUpper_lt_expCutoff {a k : Nat}
    (ha401 : 401 ≤ a) (ha2000 : a ≤ 2000)
    (hkmax : k ≤ posKmax a) (htempered : posTemperedCutoff a < k) :
    positiveTemperedExponentUpper a k < (positiveExpCutoff : ℚ) := by
  have hk50 : 50 ≤ k := by
    have hcut : 49 ≤ posTemperedCutoff a := posTemperedCutoff_ge_49 ha401
    omega
  have hjpos : 0 < posJ a k :=
    posJ_pos_of_le_posKmax (by omega : 1 ≤ a) hkmax
  have hratioK : (a : ℚ) / (k : ℚ) ≤ 40 := by
    have hkQ : (0 : ℚ) < (k : ℚ) := by exact_mod_cast (by omega : 0 < k)
    rw [div_le_iff₀ hkQ]
    exact_mod_cast (by omega : a ≤ 40*k)
  have hratioJ : (a : ℚ) / (posJ a k : ℚ) ≤ 10 := by
    have hjQ : (0 : ℚ) < (posJ a k : ℚ) := by exact_mod_cast hjpos
    rw [div_le_iff₀ hjQ]
    exact_mod_cast self_le_ten_mul_posJ_of_le_posKmax hkmax
  have haQ : (a : ℚ) ≤ 2000 := by exact_mod_cast ha2000
  calc
    positiveTemperedExponentUpper a k
        ≤ (1/5) * (2000 : ℚ) + (57/10) * 40 + (29/10) * 10 + 2 := by
          unfold positiveTemperedExponentUpper
          gcongr
    _ < (positiveExpCutoff : ℚ) := by
          norm_num [positiveExpCutoff]

theorem positiveSmallXYProductBound_nonneg {a N k : Nat}
    (hN : 1 ≤ N) (ha401 : 401 ≤ a) (ha2000 : a ≤ 2000)
    (hk : k ∈ positiveKRange a) :
    0 ≤ positiveSmallXYProductBound a N k := by
  rcases (mem_positiveKRange.mp hk) with ⟨_hk1, hkmax⟩
  have hjpos : 0 < posJ a k :=
    posJ_pos_of_le_posKmax (by omega : 1 ≤ a) hkmax
  have hNQ : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  have hhiQ : (0 : ℚ) < (posNhi a : ℚ) := by
    exact_mod_cast posNhi_pos (by omega : 1 ≤ a)
  have hExp : 0 ≤ partialExpUpper (positiveSmallExponentUpper a k) positiveExpCutoff :=
    partialExpUpper_nonneg_of_nonneg_lt
      (positiveSmallExponentUpper_nonneg hjpos)
      (positiveSmallExponentUpper_lt_expCutoff (by omega : 1 ≤ a) ha2000 hkmax)
  unfold positiveSmallXYProductBound
  positivity

theorem positiveSmallXYProductAtBound_nonneg {a N k : Nat}
    (hN : 1 ≤ N) (ha401 : 401 ≤ a) (ha2000 : a ≤ 2000)
    (hrect : positiveRectangle a N) (hk : k ∈ positiveKRange a) :
    0 ≤ positiveSmallXYProductAtBound a N k := by
  rcases (mem_positiveKRange.mp hk) with ⟨_hk1, hkmax⟩
  have hjpos : 0 < posJ a k :=
    posJ_pos_of_le_posKmax (by omega : 1 ≤ a) hkmax
  have hNQ : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  have hExp : 0 ≤ partialExpUpper (positiveSmallExponentAt a N k) positiveExpCutoff :=
    partialExpUpper_nonneg_of_nonneg_lt
      (positiveSmallExponentAt_nonneg hjpos)
      (positiveSmallExponentAt_lt_expCutoff (by omega : 1 ≤ a) ha2000 hrect hk)
  unfold positiveSmallXYProductAtBound
  positivity

theorem positiveSmallXYProductTangentBound_nonneg {a N k : Nat}
    (hN : 1 ≤ N) (ha401 : 401 ≤ a) (ha2000 : a ≤ 2000)
    (hrect : positiveRectangle a N) (hk : k ∈ positiveKRange a) :
    0 ≤ positiveSmallXYProductTangentBound a N k := by
  rcases (mem_positiveKRange.mp hk) with ⟨_hk1, hkmax⟩
  have hjpos : 0 < posJ a k :=
    posJ_pos_of_le_posKmax (by omega : 1 ≤ a) hkmax
  have hNQ : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  have hExp :
      0 ≤ partialExpUpper (positiveSmallTangentExponentAt a N k) positiveExpCutoff :=
    partialExpUpper_nonneg_of_nonneg_lt
      (positiveSmallTangentExponentAt_nonneg hjpos)
      (positiveSmallTangentExponentAt_lt_expCutoff (by omega : 1 ≤ a) ha2000 hrect hk)
  unfold positiveSmallXYProductTangentBound
  positivity

/-- Convert the pure small-regime exponential gap into the actual finite-edge
replacement for the combined `X*Y` product target.

After cancelling the common positive factor
`(2581/20) * k * (a-k)`, the remaining inequality is exactly
`posNhi a * partialExpUpper(at) ≤ N * partialExpUpper(upper)`. -/
theorem positiveSmallXYProductAtBound_le_bound_of_expGap {a N k : Nat}
    (hN : 1 ≤ N) (ha : 1 ≤ a)
    (hgap : positiveSmallExpEdgeGap a N k) :
    positiveSmallXYProductAtBound a N k ≤ positiveSmallXYProductBound a N k := by
  let Eat := partialExpUpper (positiveSmallExponentAt a N k) positiveExpCutoff
  let Eup := partialExpUpper (positiveSmallExponentUpper a k) positiveExpCutoff
  have hNpos : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  have hNne : (N : ℚ) ≠ 0 := hNpos.ne'
  have hhiPos : (0 : ℚ) < (posNhi a : ℚ) := by
    exact_mod_cast posNhi_pos ha
  have hhiNe : (posNhi a : ℚ) ≠ 0 := hhiPos.ne'
  have hgap' : (posNhi a : ℚ) * Eat ≤ (N : ℚ) * Eup := by
    simpa [positiveSmallExpEdgeGap, Eat, Eup] using hgap
  have hfrac :
      Eat / ((N : ℚ)^2) ≤ Eup / ((N : ℚ) * (posNhi a : ℚ)) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℚ) < (N : ℚ)^2)
      (by positivity : (0 : ℚ) < (N : ℚ) * (posNhi a : ℚ))]
    have hmul := mul_le_mul_of_nonneg_left hgap' hNpos.le
    nlinarith
  have hcoef :
      0 ≤ (2581/20 : ℚ) * ((k : ℚ) * (posJ a k : ℚ)) := by
    positivity
  unfold positiveSmallXYProductAtBound positiveSmallXYProductBound
  change
    (2581/20 : ℚ) * (((k : ℚ) * (posJ a k : ℚ)) / ((N : ℚ)^2)) * Eat
      ≤
    (2581/20 : ℚ) *
      (((k : ℚ) * (posJ a k : ℚ)) / ((N : ℚ) * (posNhi a : ℚ))) * Eup
  calc
    (2581/20 : ℚ) * (((k : ℚ) * (posJ a k : ℚ)) / ((N : ℚ)^2)) * Eat
        = (2581/20 : ℚ) * ((k : ℚ) * (posJ a k : ℚ)) *
            (Eat / ((N : ℚ)^2)) := by
          field_simp [hNne]
    _ ≤ (2581/20 : ℚ) * ((k : ℚ) * (posJ a k : ℚ)) *
            (Eup / ((N : ℚ) * (posNhi a : ℚ))) :=
          mul_le_mul_of_nonneg_left hfrac hcoef
    _ = (2581/20 : ℚ) *
          (((k : ℚ) * (posJ a k : ℚ)) / ((N : ℚ) * (posNhi a : ℚ))) * Eup := by
          field_simp [hNne, hhiNe]

/-- Convert the corrected tangent-line small-regime exponential gap into the
finite-edge replacement for the combined `X*Y` product target. -/
theorem positiveSmallXYProductTangentBound_le_bound_of_expGap {a N k : Nat}
    (hN : 1 ≤ N) (ha : 1 ≤ a)
    (hgap : positiveSmallTangentExpEdgeGap a N k) :
    positiveSmallXYProductTangentBound a N k ≤ positiveSmallXYProductBound a N k := by
  let Eat := partialExpUpper (positiveSmallTangentExponentAt a N k) positiveExpCutoff
  let Eup := partialExpUpper (positiveSmallExponentUpper a k) positiveExpCutoff
  have hNpos : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  have hNne : (N : ℚ) ≠ 0 := hNpos.ne'
  have hhiPos : (0 : ℚ) < (posNhi a : ℚ) := by
    exact_mod_cast posNhi_pos ha
  have hhiNe : (posNhi a : ℚ) ≠ 0 := hhiPos.ne'
  have hgap' : (posNhi a : ℚ) * Eat ≤ (N : ℚ) * Eup := by
    simpa [positiveSmallTangentExpEdgeGap, Eat, Eup] using hgap
  have hfrac :
      Eat / ((N : ℚ)^2) ≤ Eup / ((N : ℚ) * (posNhi a : ℚ)) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℚ) < (N : ℚ)^2)
      (by positivity : (0 : ℚ) < (N : ℚ) * (posNhi a : ℚ))]
    have hmul := mul_le_mul_of_nonneg_left hgap' hNpos.le
    nlinarith
  have hcoef :
      0 ≤ (2581/20 : ℚ) * ((k : ℚ) * (posJ a k : ℚ)) := by
    positivity
  unfold positiveSmallXYProductTangentBound positiveSmallXYProductBound
  change
    (2581/20 : ℚ) * (((k : ℚ) * (posJ a k : ℚ)) / ((N : ℚ)^2)) * Eat
      ≤
    (2581/20 : ℚ) *
      (((k : ℚ) * (posJ a k : ℚ)) / ((N : ℚ) * (posNhi a : ℚ))) * Eup
  calc
    (2581/20 : ℚ) * (((k : ℚ) * (posJ a k : ℚ)) / ((N : ℚ)^2)) * Eat
        = (2581/20 : ℚ) * ((k : ℚ) * (posJ a k : ℚ)) *
            (Eat / ((N : ℚ)^2)) := by
          field_simp [hNne]
    _ ≤ (2581/20 : ℚ) * ((k : ℚ) * (posJ a k : ℚ)) *
            (Eup / ((N : ℚ) * (posNhi a : ℚ))) :=
          mul_le_mul_of_nonneg_left hfrac hcoef
    _ = (2581/20 : ℚ) *
          (((k : ℚ) * (posJ a k : ℚ)) / ((N : ℚ) * (posNhi a : ℚ))) * Eup := by
          field_simp [hNne, hhiNe]

/-- A plateau-anchor check implies the actual small exponential-gap check at
every `N` in that plateau. -/
theorem positiveSmallExpEdgeGap_of_anchor {a N k : Nat}
    (ha401 : 401 ≤ a) (ha2000 : a ≤ 2000)
    (hrect : positiveRectangle a N) (hk : k ∈ positiveKRange a)
    (hanchor : positiveSmallExpEdgeGapAtCeil a (ceilSqrt N) k) :
    positiveSmallExpEdgeGap a N k := by
  rcases (mem_positiveKRange.mp hk) with ⟨_hk1, hkmax⟩
  have hjpos : 0 < posJ a k :=
    posJ_pos_of_le_posKmax (by omega : 1 ≤ a) hkmax
  have hEup :
      0 ≤ partialExpUpper (positiveSmallExponentUpper a k) positiveExpCutoff :=
    partialExpUpper_nonneg_of_nonneg_lt
      (positiveSmallExponentUpper_nonneg hjpos)
      (positiveSmallExponentUpper_lt_expCutoff (by omega : 1 ≤ a) ha2000 hkmax)
  have hanchor_le :
      (positiveSmallEdgeAnchor a (ceilSqrt N) : ℚ) ≤ (N : ℚ) := by
    exact_mod_cast positiveSmallEdgeAnchor_le_of_rectangle hrect
  have hright :
      (positiveSmallEdgeAnchor a (ceilSqrt N) : ℚ) *
          partialExpUpper (positiveSmallExponentUpper a k) positiveExpCutoff
        ≤
        (N : ℚ) *
          partialExpUpper (positiveSmallExponentUpper a k) positiveExpCutoff :=
    mul_le_mul_of_nonneg_right hanchor_le hEup
  unfold positiveSmallExpEdgeGap at *
  rw [positiveSmallExponentAt_eq_withCeil]
  exact hanchor.trans hright

/-- Plateau-anchor form of the small finite-edge replacement. -/
theorem positiveSmallXYProductAtBound_le_bound_of_anchorGap {a N k : Nat}
    (ha401 : 401 ≤ a) (ha2000 : a ≤ 2000)
    (hrect : positiveRectangle a N) (hk : k ∈ positiveKRange a)
    (hanchor : positiveSmallExpEdgeGapAtCeil a (ceilSqrt N) k) :
    positiveSmallXYProductAtBound a N k ≤ positiveSmallXYProductBound a N k :=
  positiveSmallXYProductAtBound_le_bound_of_expGap
    (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect) (by omega : 1 ≤ a)
    (positiveSmallExpEdgeGap_of_anchor ha401 ha2000 hrect hk hanchor)

theorem positiveTemperedXYProductBound_nonneg {a N k : Nat}
    (hN : 1 ≤ N) (ha401 : 401 ≤ a) (ha2000 : a ≤ 2000)
    (hk : k ∈ positiveKRange a) (htempered : posTemperedCutoff a < k) :
    0 ≤ positiveTemperedXYProductBound a N k := by
  rcases (mem_positiveKRange.mp hk) with ⟨hk1, hkmax⟩
  have hjpos : 0 < posJ a k :=
    posJ_pos_of_le_posKmax (by omega : 1 ≤ a) hkmax
  have hNQ : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  have hExp :
      0 ≤ partialExpUpper (positiveTemperedExponentUpper a k) positiveExpCutoff :=
    partialExpUpper_nonneg_of_nonneg_lt
      (positiveTemperedExponentUpper_nonneg hk1 hjpos)
      (positiveTemperedExponentUpper_lt_expCutoff ha401 ha2000 hkmax htempered)
  unfold positiveTemperedXYProductBound
  positivity

theorem positivePrefactor_nonneg {C : ℚ} {a N k : Nat}
    (hC : 0 ≤ C) (hN : 1 ≤ N) (ha : 2 ≤ a) (hk1 : 1 ≤ k)
    (hkmax : k ≤ posKmax a) :
    0 ≤ positivePrefactor C a N k := by
  have hNQ : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  have ha1Q : (0 : ℚ) < ((a-1 : Nat) : ℚ) := by
    exact_mod_cast (by omega : 0 < a-1)
  have hchooseQ : (0 : ℚ) < (positiveBinomDen a k : ℚ) := by
    exact_mod_cast positiveBinomDen_pos ha hk1 hkmax
  have hjQ : (0 : ℚ) < (posJ a k : ℚ) := by
    exact_mod_cast posJ_pos_of_le_posKmax (by omega : 1 ≤ a) hkmax
  unfold positivePrefactor positiveDyadicDecay
  positivity

theorem positiveSmallMajorantTerm_nonneg {a k : Nat}
    (ha401 : 401 ≤ a) (ha2000 : a ≤ 2000)
    (hk : k ∈ positiveKRange a) :
    0 ≤ positiveSmallMajorantTerm a k := by
  rcases (mem_positiveKRange.mp hk) with ⟨hk1, hkmax⟩
  have hjpos : 0 < posJ a k :=
    posJ_pos_of_le_posKmax (by omega : 1 ≤ a) hkmax
  have hExp : 0 ≤ partialExpUpper (positiveSmallExponentUpper a k) positiveExpCutoff :=
    partialExpUpper_nonneg_of_nonneg_lt
      (positiveSmallExponentUpper_nonneg hjpos)
      (positiveSmallExponentUpper_lt_expCutoff (by omega : 1 ≤ a) ha2000 hkmax)
  unfold positiveSmallMajorantTerm
  exact mul_nonneg
    (positivePrefactor_nonneg (by norm_num) (by
      exact Nat.succ_le_of_lt (posNhi_pos (by omega : 1 ≤ a)))
      (by omega : 2 ≤ a) hk1 hkmax) hExp

theorem positiveTemperedMajorantTerm_nonneg {a k : Nat}
    (ha401 : 401 ≤ a) (ha2000 : a ≤ 2000)
    (hk : k ∈ positiveKRange a) (htempered : posTemperedCutoff a < k) :
    0 ≤ positiveTemperedMajorantTerm a k := by
  rcases (mem_positiveKRange.mp hk) with ⟨hk1, hkmax⟩
  have hjpos : 0 < posJ a k :=
    posJ_pos_of_le_posKmax (by omega : 1 ≤ a) hkmax
  have hExp :
      0 ≤ partialExpUpper (positiveTemperedExponentUpper a k) positiveExpCutoff :=
    partialExpUpper_nonneg_of_nonneg_lt
      (positiveTemperedExponentUpper_nonneg hk1 hjpos)
      (positiveTemperedExponentUpper_lt_expCutoff ha401 ha2000 hkmax htempered)
  unfold positiveTemperedMajorantTerm
  exact mul_nonneg
    (positivePrefactor_nonneg (by norm_num) (by
      exact Nat.succ_le_of_lt (posNlo_pos (by omega : 2 ≤ a)))
      (by omega : 2 ≤ a) hk1 hkmax) hExp

theorem positiveSmallScalarProductBound_le_majorant {a k : Nat}
    (ha401 : 401 ≤ a) (ha2000 : a ≤ 2000)
    (hk : k ∈ positiveKRange a) :
    positiveSmallScalarProductBound a k ≤ positiveSmallMajorantTerm a k := by
  rcases (mem_positiveKRange.mp hk) with ⟨hk1, hkmax⟩
  have hjpos : 0 < posJ a k :=
    posJ_pos_of_le_posKmax (by omega : 1 ≤ a) hkmax
  have hExp : 0 ≤ partialExpUpper (positiveSmallExponentUpper a k) positiveExpCutoff :=
    partialExpUpper_nonneg_of_nonneg_lt
      (positiveSmallExponentUpper_nonneg hjpos)
      (positiveSmallExponentUpper_lt_expCutoff (by omega : 1 ≤ a) ha2000 hkmax)
  rw [positiveSmallMajorantTerm_eq_binomRatio]
  unfold positiveSmallScalarProductBound
  gcongr
  · exact positiveDyadicDecay_nonneg (posJ a k)
  · exact positiveBinomRatio_nonneg
  · norm_num

theorem positiveTemperedScalarProductBound_le_majorant {a N k : Nat}
    (ha401 : 401 ≤ a) (ha2000 : a ≤ 2000)
    (hrect : positiveRectangle a N) (hk : k ∈ positiveKRange a)
    (htempered : posTemperedCutoff a < k) :
    positiveTemperedScalarProductBound a N k ≤ positiveTemperedMajorantTerm a k := by
  rcases (mem_positiveKRange.mp hk) with ⟨hk1, hkmax⟩
  have hjpos : 0 < posJ a k :=
    posJ_pos_of_le_posKmax (by omega : 1 ≤ a) hkmax
  have hExp :
      0 ≤ partialExpUpper (positiveTemperedExponentUpper a k) positiveExpCutoff :=
    partialExpUpper_nonneg_of_nonneg_lt
      (positiveTemperedExponentUpper_nonneg hk1 hjpos)
      (positiveTemperedExponentUpper_lt_expCutoff ha401 ha2000 hkmax htempered)
  have hcoef :
      (2117/40 : ℚ) / (N : ℚ) ≤ 96 / (posNlo a : ℚ) := by
    have hstep : (2117/40 : ℚ) / (N : ℚ)
        ≤ (2117/40 : ℚ) / (posNlo a : ℚ) :=
      div_natCast_le_div_posNlo_of_rectangle (by norm_num) (by omega : 2 ≤ a) hrect
    have hlo_pos : (0 : ℚ) < (posNlo a : ℚ) := by
      exact_mod_cast posNlo_pos (by omega : 2 ≤ a)
    have hconst : (2117/40 : ℚ) / (posNlo a : ℚ)
        ≤ 96 / (posNlo a : ℚ) := by
      exact div_le_div_of_nonneg_right (by norm_num) hlo_pos.le
    exact hstep.trans hconst
  rw [positiveTemperedMajorantTerm_eq_binomRatio]
  unfold positiveTemperedScalarProductBound
  gcongr
  · exact positiveDyadicDecay_nonneg (posJ a k)
  · exact positiveBinomRatio_nonneg

theorem normalizedPositiveRawTerm_le_smallMajorant_of_factorized_bound
    {a N k : Nat} (ha401 : 401 ≤ a) (ha2000 : a ≤ 2000)
    (hrect : positiveRectangle a N) (hkRange : k ∈ positiveKRange a)
    (hfactor :
      0 < Bq N k → positiveFactorizedRawTerm a N k ≤ positiveSmallMajorantTerm a k) :
    normalizedPositiveRawTerm a N k ≤ positiveSmallMajorantTerm a k := by
  rcases (mem_positiveKRange.mp hkRange) with ⟨hk1, _hkmax⟩
  exact normalizedPositiveRawTerm_le_of_factorized_bound
    (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect) (by omega : 1 ≤ a)
    hk1 (one_le_posJ_of_mem_positiveKRange (by omega : 1 ≤ a) hkRange)
    (positiveSmallMajorantTerm_nonneg ha401 ha2000 hkRange) hfactor

theorem normalizedPositiveRawTerm_le_temperedMajorant_of_factorized_bound
    {a N k : Nat} (ha401 : 401 ≤ a) (ha2000 : a ≤ 2000)
    (hrect : positiveRectangle a N) (hkRange : k ∈ positiveKRange a)
    (htempered : ceilSqrt N < k)
    (hfactor :
      0 < Bq N k →
        positiveFactorizedRawTerm a N k ≤ positiveTemperedMajorantTerm a k) :
    normalizedPositiveRawTerm a N k ≤ positiveTemperedMajorantTerm a k := by
  rcases (mem_positiveKRange.mp hkRange) with ⟨hk1, _hkmax⟩
  exact normalizedPositiveRawTerm_le_of_factorized_bound
    (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect) (by omega : 1 ≤ a)
    hk1 (one_le_posJ_of_mem_positiveKRange (by omega : 1 ≤ a) hkRange)
    (positiveTemperedMajorantTerm_nonneg ha401 ha2000 hkRange
      (temperedRegime_of_rectangle hrect htempered)) hfactor

theorem positiveEdgeMajorantTerm_nonneg {a k : Nat}
    (ha401 : 401 ≤ a) (ha2000 : a ≤ 2000)
    (hk : k ∈ positiveKRange a) :
    0 ≤ positiveEdgeMajorantTerm a k := by
  unfold positiveEdgeMajorantTerm
  have hs : 0 ≤
      (if k ≤ posSmallCutoff a then positiveSmallMajorantTerm a k else 0) := by
    split
    · exact positiveSmallMajorantTerm_nonneg ha401 ha2000 hk
    · norm_num
  exact hs.trans (le_max_left _ _)

theorem positiveEdgeMajorantSum_nonneg {a : Nat}
    (ha401 : 401 ≤ a) (ha2000 : a ≤ 2000) :
    0 ≤ positiveEdgeMajorantSum a := by
  unfold positiveEdgeMajorantSum
  exact Finset.sum_nonneg fun k hk =>
    positiveEdgeMajorantTerm_nonneg ha401 ha2000 hk

/-! ## Reducer from pointwise saddle estimates to the corrected edge scan -/

theorem positiveSmallMajorantTerm_le_edge {a k : Nat}
    (hk : k ≤ posSmallCutoff a) :
    positiveSmallMajorantTerm a k ≤ positiveEdgeMajorantTerm a k := by
  unfold positiveEdgeMajorantTerm
  rw [if_pos hk]
  exact le_max_left _ _

theorem positiveTemperedMajorantTerm_le_edge {a k : Nat}
    (hk : posTemperedCutoff a < k) :
    positiveTemperedMajorantTerm a k ≤ positiveEdgeMajorantTerm a k := by
  unfold positiveEdgeMajorantTerm
  rw [if_pos hk]
  exact le_max_right _ _

/-- Core corrected-edge reducer.  Later analytic work only needs to prove the
two pointwise saddle estimates at the actual `N`: the small estimate below
`ceilSqrt N`, and the tempered estimate above it.  The theorem transports
those estimates to the two-edge `max` used by the executable finite scan. -/
theorem term_le_positiveEdgeMajorantTerm_of_regime_bounds {a N k : Nat}
    {T : ℚ} (hrect : positiveRectangle a N)
    (hsmall : k ≤ ceilSqrt N → T ≤ positiveSmallMajorantTerm a k)
    (htempered : ceilSqrt N < k → T ≤ positiveTemperedMajorantTerm a k) :
    T ≤ positiveEdgeMajorantTerm a k := by
  rcases le_or_gt k (ceilSqrt N) with hkSmall | hkTemp
  · exact (hsmall hkSmall).trans
      (positiveSmallMajorantTerm_le_edge
        (smallRegime_of_rectangle hrect hkSmall))
  · exact (htempered hkTemp).trans
      (positiveTemperedMajorantTerm_le_edge
        (temperedRegime_of_rectangle hrect hkTemp))

theorem sum_le_positiveEdgeMajorantSum {a : Nat} {F : Nat → ℚ}
    (hF : ∀ k, k ∈ positiveKRange a → F k ≤ positiveEdgeMajorantTerm a k) :
    (∑ k ∈ positiveKRange a, F k) ≤ positiveEdgeMajorantSum a := by
  unfold positiveEdgeMajorantSum
  exact Finset.sum_le_sum hF

/-- Summed form of `term_le_positiveEdgeMajorantTerm_of_regime_bounds`. -/
theorem sum_le_positiveEdgeMajorantSum_of_regime_bounds {a N : Nat}
    {F : Nat → ℚ} (hrect : positiveRectangle a N)
    (hFsmall :
      ∀ k, k ∈ positiveKRange a →
        k ≤ ceilSqrt N → F k ≤ positiveSmallMajorantTerm a k)
    (hFtempered :
      ∀ k, k ∈ positiveKRange a →
        ceilSqrt N < k → F k ≤ positiveTemperedMajorantTerm a k) :
    (∑ k ∈ positiveKRange a, F k) ≤ positiveEdgeMajorantSum a :=
  sum_le_positiveEdgeMajorantSum fun k hk =>
    term_le_positiveEdgeMajorantTerm_of_regime_bounds hrect
      (hFsmall k hk) (hFtempered k hk)

theorem normalizedPositiveRetainedSum_le_edge_of_regime_bounds {a N : Nat}
    (hrect : positiveRectangle a N)
    (hsmall :
      ∀ k, k ∈ positiveKRange a →
        k ≤ ceilSqrt N →
          normalizedPositiveIfTerm a N k ≤ positiveSmallMajorantTerm a k)
    (htempered :
      ∀ k, k ∈ positiveKRange a →
        ceilSqrt N < k →
          normalizedPositiveIfTerm a N k ≤ positiveTemperedMajorantTerm a k) :
    normalizedPositiveRetainedSum a N ≤ positiveEdgeMajorantSum a := by
  unfold normalizedPositiveRetainedSum
  exact sum_le_positiveEdgeMajorantSum_of_regime_bounds hrect hsmall htempered

theorem normalizedPositiveRetainedSum_le_customEdge_of_regime_bounds
    {smallTerm temperedTerm : Nat → Nat → ℚ} {a N : Nat}
    (hrect : positiveRectangle a N)
    (hsmall :
      ∀ k, k ∈ positiveKRange a →
        k ≤ ceilSqrt N →
          normalizedPositiveIfTerm a N k ≤ smallTerm a k)
    (htempered :
      ∀ k, k ∈ positiveKRange a →
        ceilSqrt N < k →
          normalizedPositiveIfTerm a N k ≤ temperedTerm a k) :
    normalizedPositiveRetainedSum a N
      ≤ positiveCustomEdgeMajorantSum smallTerm temperedTerm a := by
  unfold normalizedPositiveRetainedSum
  exact sum_le_positiveCustomEdgeMajorantSum_of_regime_bounds hrect hsmall htempered

theorem Unorm_le_Xnorm_add_solo_add_customEdge_of_large_Xnorm_nonpos
    {smallTerm temperedTerm : Nat → Nat → ℚ}
    {a N : Nat} (ha : 1 ≤ a) (hN : 1 ≤ N) (hrect : positiveRectangle a N)
    (hlarge : ∀ k, k < a → posKmax a < k → 1 ≤ k → Xnorm N k ≤ 0)
    (hsmall :
      ∀ k, k ∈ positiveKRange a →
        k ≤ ceilSqrt N →
          normalizedPositiveIfTerm a N k ≤ smallTerm a k)
    (htempered :
      ∀ k, k ∈ positiveKRange a →
        ceilSqrt N < k →
          normalizedPositiveIfTerm a N k ≤ temperedTerm a k) :
    Unorm a N ≤ Xnorm N a + normalizedSoloTerm a N +
      positiveCustomEdgeMajorantSum smallTerm temperedTerm a := by
  rw [Unorm_eq_Xnorm_add_solo_add_retained_of_large_Xnorm_nonpos ha hN hlarge]
  have hsum := normalizedPositiveRetainedSum_le_customEdge_of_regime_bounds
    (smallTerm := smallTerm) (temperedTerm := temperedTerm)
    (a := a) (N := N) hrect hsmall htempered
  linarith

theorem Unorm_le_Xnorm_add_solo_add_customEdge_of_signLock_nonpos
    {smallTerm temperedTerm : Nat → Nat → ℚ}
    {a N : Nat} (ha : 401 ≤ a) (hrect : positiveRectangle a N)
    (hSL : ∀ k : Nat, 361 ≤ k →
      (N : ℚ) ≤ (40/3) * (k : ℚ) → Xnorm N k ≤ 0)
    (hsmall :
      ∀ k, k ∈ positiveKRange a →
        k ≤ ceilSqrt N →
          normalizedPositiveIfTerm a N k ≤ smallTerm a k)
    (htempered :
      ∀ k, k ∈ positiveKRange a →
        ceilSqrt N < k →
          normalizedPositiveIfTerm a N k ≤ temperedTerm a k) :
    Unorm a N ≤ Xnorm N a + normalizedSoloTerm a N +
      positiveCustomEdgeMajorantSum smallTerm temperedTerm a := by
  exact Unorm_le_Xnorm_add_solo_add_customEdge_of_large_Xnorm_nonpos
    (smallTerm := smallTerm) (temperedTerm := temperedTerm)
    (a := a) (N := N) (by omega : 1 ≤ a)
    (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect) hrect
    (large_Xnorm_nonpos_of_signLock_nonpos ha hrect hSL)
    hsmall htempered

theorem Unorm_le_Xnorm_add_customEnvelope_of_signLock_nonpos
    {smallTerm temperedTerm : Nat → Nat → ℚ}
    {a N : Nat} (ha : 401 ≤ a) (hrect : positiveRectangle a N)
    (hSL : ∀ k : Nat, 361 ≤ k →
      (N : ℚ) ≤ (40/3) * (k : ℚ) → Xnorm N k ≤ 0)
    (hsmall :
      ∀ k, k ∈ positiveKRange a →
        k ≤ ceilSqrt N →
          normalizedPositiveIfTerm a N k ≤ smallTerm a k)
    (htempered :
      ∀ k, k ∈ positiveKRange a →
        ceilSqrt N < k →
          normalizedPositiveIfTerm a N k ≤ temperedTerm a k) :
    Unorm a N ≤ Xnorm N a +
      positiveCustomEnvelope smallTerm temperedTerm a N := by
  have hU := Unorm_le_Xnorm_add_solo_add_customEdge_of_signLock_nonpos
    (smallTerm := smallTerm) (temperedTerm := temperedTerm)
    (a := a) (N := N) ha hrect hSL hsmall htempered
  unfold positiveCustomEnvelope
  linarith

/-- Conditional large-`a` positive-part assembly.  Once sign-lock has excluded
large `k` and the two saddle estimates bound the retained summands, `Unorm`
is controlled by `Xnorm`, the solo term, and the corrected two-edge scan. -/
theorem Unorm_le_Xnorm_add_solo_add_edge_of_large_Xnorm_nonpos
    {a N : Nat} (ha : 1 ≤ a) (hN : 1 ≤ N) (hrect : positiveRectangle a N)
    (hlarge : ∀ k, k < a → posKmax a < k → 1 ≤ k → Xnorm N k ≤ 0)
    (hsmall :
      ∀ k, k ∈ positiveKRange a →
        k ≤ ceilSqrt N →
          normalizedPositiveIfTerm a N k ≤ positiveSmallMajorantTerm a k)
    (htempered :
      ∀ k, k ∈ positiveKRange a →
        ceilSqrt N < k →
          normalizedPositiveIfTerm a N k ≤ positiveTemperedMajorantTerm a k) :
    Unorm a N ≤ Xnorm N a + normalizedSoloTerm a N + positiveEdgeMajorantSum a := by
  rw [Unorm_eq_Xnorm_add_solo_add_retained_of_large_Xnorm_nonpos ha hN hlarge]
  have hsum := normalizedPositiveRetainedSum_le_edge_of_regime_bounds
    (a := a) (N := N) hrect hsmall htempered
  linarith

theorem Unorm_le_Xnorm_add_solo_add_edge_of_signLock_nonpos
    {a N : Nat} (ha : 401 ≤ a) (hrect : positiveRectangle a N)
    (hSL : ∀ k : Nat, 361 ≤ k →
      (N : ℚ) ≤ (40/3) * (k : ℚ) → Xnorm N k ≤ 0)
    (hsmall :
      ∀ k, k ∈ positiveKRange a →
        k ≤ ceilSqrt N →
          normalizedPositiveIfTerm a N k ≤ positiveSmallMajorantTerm a k)
    (htempered :
      ∀ k, k ∈ positiveKRange a →
        ceilSqrt N < k →
          normalizedPositiveIfTerm a N k ≤ positiveTemperedMajorantTerm a k) :
    Unorm a N ≤ Xnorm N a + normalizedSoloTerm a N + positiveEdgeMajorantSum a := by
  exact Unorm_le_Xnorm_add_solo_add_edge_of_large_Xnorm_nonpos
    (a := a) (N := N) (by omega : 1 ≤ a)
    (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect) hrect
    (large_Xnorm_nonpos_of_signLock_nonpos ha hrect hSL)
    hsmall htempered

theorem Unorm_le_Xnorm_add_positiveEnvelope_of_signLock_nonpos
    {a N : Nat} (ha : 401 ≤ a) (hrect : positiveRectangle a N)
    (hSL : ∀ k : Nat, 361 ≤ k →
      (N : ℚ) ≤ (40/3) * (k : ℚ) → Xnorm N k ≤ 0)
    (hsmall :
      ∀ k, k ∈ positiveKRange a →
        k ≤ ceilSqrt N →
          normalizedPositiveIfTerm a N k ≤ positiveSmallMajorantTerm a k)
    (htempered :
      ∀ k, k ∈ positiveKRange a →
        ceilSqrt N < k →
          normalizedPositiveIfTerm a N k ≤ positiveTemperedMajorantTerm a k) :
    Unorm a N ≤ Xnorm N a + positiveEnvelope a N := by
  have hU := Unorm_le_Xnorm_add_solo_add_edge_of_signLock_nonpos
    (a := a) (N := N) ha hrect hSL hsmall htempered
  unfold positiveEnvelope
  linarith

/-- Large-`a` assembly: a sign-lock lower bound for `-X_a`, the two
pointwise positive saddle estimates, and the `10^-8` positive-envelope
certificate imply `Unorm < 0`. -/
theorem Unorm_neg_of_signLockMargin_and_positiveEnvelope
    {a N : Nat} (ha : 401 ≤ a) (hrect : positiveRectangle a N)
    (hSLlarge : ∀ k : Nat, 361 ≤ k →
      (N : ℚ) ≤ (40/3) * (k : ℚ) → Xnorm N k ≤ 0)
    (hsmall :
      ∀ k, k ∈ positiveKRange a →
        k ≤ ceilSqrt N →
          normalizedPositiveIfTerm a N k ≤ positiveSmallMajorantTerm a k)
    (htempered :
      ∀ k, k ∈ positiveKRange a →
        ceilSqrt N < k →
          normalizedPositiveIfTerm a N k ≤ positiveTemperedMajorantTerm a k)
    (hXmain : Xnorm N a ≤ -signLockMargin a)
    (hpositive : positiveEnvelope a N ≤ positiveTarget) :
    Unorm a N < 0 := by
  have hU := Unorm_le_Xnorm_add_positiveEnvelope_of_signLock_nonpos
    (a := a) (N := N) ha hrect hSLlarge hsmall htempered
  have htarget := positiveTarget_lt_signLockMargin_of_ge_401 (m := a) ha
  linarith

/-- Large-`a` assembly from a single uniform sign-lock margin theorem.

This is the interface wanted by §5: the same `Xnorm N m ≤ -signLockMargin m`
statement handles the main `m = a` term and the discarded `k > 0.9a`
positive-part summands. -/
theorem Unorm_neg_of_uniform_signLockMargin_and_positiveEnvelope
    {a N : Nat} (ha : 401 ≤ a) (hrect : positiveRectangle a N)
    (hXbound : ∀ m : Nat, 361 ≤ m →
      (N : ℚ) ≤ (40/3) * (m : ℚ) → Xnorm N m ≤ -signLockMargin m)
    (hsmall :
      ∀ k, k ∈ positiveKRange a →
        k ≤ ceilSqrt N →
          normalizedPositiveIfTerm a N k ≤ positiveSmallMajorantTerm a k)
    (htempered :
      ∀ k, k ∈ positiveKRange a →
        ceilSqrt N < k →
          normalizedPositiveIfTerm a N k ≤ positiveTemperedMajorantTerm a k)
    (hpositive : positiveEnvelope a N ≤ positiveTarget) :
    Unorm a N < 0 := by
  refine Unorm_neg_of_signLockMargin_and_positiveEnvelope
    (a := a) (N := N) ha hrect ?hSLlarge hsmall htempered ?hXmain hpositive
  · intro k hk361 hNk
    exact Xnorm_nonpos_of_signLockMargin_bound hk361 (hXbound k hk361 hNk)
  · exact hXbound a (by omega : 361 ≤ a)
      (rectangle_N_le_signLock_range_self (a := a) (N := N) hrect)

/-- Large-`a` assembly from the remaining alternating-base lower bound in §5.

This is the current top-level bridge between the completed sign-lock error
audit and the positive-part reduction: once the alternating base sum is bounded
below uniformly in the sign-lock range, the `Unorm < 0` conclusion follows
from the same positive saddle obligations. -/
theorem Unorm_neg_of_uniform_signLockNearBase_and_positiveEnvelope
    {a N : Nat} (ha : 401 ≤ a) (hrect : positiveRectangle a N)
    (hbase : ∀ m : Nat, 361 ≤ m →
      (N : ℚ) ≤ (40/3) * (m : ℚ) →
        expNegLower50 * (1 - 2/(m : ℚ)) ≤ signLockNearBase N m)
    (hsmall :
      ∀ k, k ∈ positiveKRange a →
        k ≤ ceilSqrt N →
          normalizedPositiveIfTerm a N k ≤ positiveSmallMajorantTerm a k)
    (htempered :
      ∀ k, k ∈ positiveKRange a →
        ceilSqrt N < k →
          normalizedPositiveIfTerm a N k ≤ positiveTemperedMajorantTerm a k)
    (hpositive : positiveEnvelope a N ≤ positiveTarget) :
    Unorm a N < 0 := by
  have hN : 1 ≤ N := positiveRectangle_N_pos (by omega : 2 ≤ a) hrect
  refine Unorm_neg_of_uniform_signLockMargin_and_positiveEnvelope
    (a := a) (N := N) ha hrect ?hXbound hsmall htempered hpositive
  intro m hm hNm
  exact Xnorm_le_neg_signLockMargin_of_signLockNearBase
    (N := N) (m := m) hN hNm hm (hbase m hm hNm)

/-- Large-`a` assembly from the 12-term alternating-base prefix and paired
tail obligations in §5. -/
theorem Unorm_neg_of_uniform_signLockBasePrefix_tail_and_positiveEnvelope
    {a N : Nat} (ha : 401 ≤ a) (hrect : positiveRectangle a N)
    (hprefix : ∀ m : Nat, 361 ≤ m →
      (N : ℚ) ≤ (40/3) * (m : ℚ) →
        expNegLower50 * (1 - 2/(m : ℚ)) ≤ signLockBasePrefix N m 12)
    (htail : ∀ m : Nat, 361 ≤ m →
      (N : ℚ) ≤ (40/3) * (m : ℚ) →
        0 ≤ signLockBaseTailFrom12 N m)
    (hsmall :
      ∀ k, k ∈ positiveKRange a →
        k ≤ ceilSqrt N →
          normalizedPositiveIfTerm a N k ≤ positiveSmallMajorantTerm a k)
    (htempered :
      ∀ k, k ∈ positiveKRange a →
        ceilSqrt N < k →
          normalizedPositiveIfTerm a N k ≤ positiveTemperedMajorantTerm a k)
    (hpositive : positiveEnvelope a N ≤ positiveTarget) :
    Unorm a N < 0 := by
  refine Unorm_neg_of_uniform_signLockNearBase_and_positiveEnvelope
    (a := a) (N := N) ha hrect ?hbase hsmall htempered hpositive
  intro m hm hNm
  exact signLockNearBase_lower_of_prefix12_tail
    (N := N) (m := m) hm (hprefix m hm hNm) (htail m hm hNm)

/-- Large-`a` assembly after closing the paired alternating tail in §5.  The
remaining sign-lock input is the 12-term prefix inequality. -/
theorem Unorm_neg_of_uniform_signLockBasePrefix_and_positiveEnvelope
    {a N : Nat} (ha : 401 ≤ a) (hrect : positiveRectangle a N)
    (hprefix : ∀ m : Nat, 361 ≤ m →
      (N : ℚ) ≤ (40/3) * (m : ℚ) →
        expNegLower50 * (1 - 2/(m : ℚ)) ≤ signLockBasePrefix N m 12)
    (hsmall :
      ∀ k, k ∈ positiveKRange a →
        k ≤ ceilSqrt N →
          normalizedPositiveIfTerm a N k ≤ positiveSmallMajorantTerm a k)
    (htempered :
      ∀ k, k ∈ positiveKRange a →
        ceilSqrt N < k →
          normalizedPositiveIfTerm a N k ≤ positiveTemperedMajorantTerm a k)
    (hpositive : positiveEnvelope a N ≤ positiveTarget) :
    Unorm a N < 0 := by
  refine Unorm_neg_of_uniform_signLockBasePrefix_tail_and_positiveEnvelope
    (a := a) (N := N) ha hrect hprefix ?htail hsmall htempered hpositive
  intro m hm hNm
  exact signLockBaseTailFrom12_nonneg (N := N) (m := m) hNm hm

/-- Large-`a` assembly after the completed §5 sign-lock theorem.  The only
remaining inputs are the positive-saddle majorants and the positive-envelope
certificate. -/
theorem Unorm_neg_of_signLock_and_positiveEnvelope
    {a N : Nat} (ha : 401 ≤ a) (hrect : positiveRectangle a N)
    (hsmall :
      ∀ k, k ∈ positiveKRange a →
        k ≤ ceilSqrt N →
          normalizedPositiveIfTerm a N k ≤ positiveSmallMajorantTerm a k)
    (htempered :
      ∀ k, k ∈ positiveKRange a →
        ceilSqrt N < k →
          normalizedPositiveIfTerm a N k ≤ positiveTemperedMajorantTerm a k)
    (hpositive : positiveEnvelope a N ≤ positiveTarget) :
    Unorm a N < 0 := by
  have hN : 1 ≤ N := positiveRectangle_N_pos (by omega : 2 ≤ a) hrect
  refine Unorm_neg_of_uniform_signLockMargin_and_positiveEnvelope
    (a := a) (N := N) ha hrect ?hXbound hsmall htempered hpositive
  intro m hm hNm
  exact Xnorm_le_neg_signLockMargin (N := N) (m := m) hN hNm hm

/-- Same large-`a` assembly, but with the solo contribution already replaced
by an explicit upper bound.  This is the interface for the remaining
positive-envelope certificate. -/
theorem Unorm_neg_of_signLock_and_positiveEnvelopeBound
    {a N : Nat} {soloBound : ℚ}
    (ha : 401 ≤ a) (hrect : positiveRectangle a N)
    (hsmall :
      ∀ k, k ∈ positiveKRange a →
        k ≤ ceilSqrt N →
          normalizedPositiveIfTerm a N k ≤ positiveSmallMajorantTerm a k)
    (htempered :
      ∀ k, k ∈ positiveKRange a →
        ceilSqrt N < k →
          normalizedPositiveIfTerm a N k ≤ positiveTemperedMajorantTerm a k)
    (hsolo : normalizedSoloTerm a N ≤ soloBound)
    (hpositive : positiveEnvelopeBound a soloBound ≤ positiveTarget) :
    Unorm a N < 0 :=
  Unorm_neg_of_signLock_and_positiveEnvelope
    (a := a) (N := N) ha hrect hsmall htempered
    ((positiveEnvelope_le_bound_of_solo
      (a := a) (N := N) (soloBound := soloBound) hsolo).trans hpositive)

/-- Large-`a` assembly with custom retained-positive majorants.

This is the entropy-tail analogue of
`Unorm_neg_of_signLock_and_positiveEnvelopeBound`: it keeps the completed
sign-lock theorem and solo bookkeeping, but lets the small/tempered retained
summand majorants be supplied by a different rational tail estimate. -/
theorem Unorm_neg_of_signLock_and_customEnvelopeBound
    {smallTerm temperedTerm : Nat → Nat → ℚ}
    {a N : Nat} {soloBound : ℚ}
    (ha : 401 ≤ a) (hrect : positiveRectangle a N)
    (hsmall :
      ∀ k, k ∈ positiveKRange a →
        k ≤ ceilSqrt N →
          normalizedPositiveIfTerm a N k ≤ smallTerm a k)
    (htempered :
      ∀ k, k ∈ positiveKRange a →
        ceilSqrt N < k →
          normalizedPositiveIfTerm a N k ≤ temperedTerm a k)
    (hsolo : normalizedSoloTerm a N ≤ soloBound)
    (hpositive :
      positiveCustomEnvelopeBound smallTerm temperedTerm a soloBound ≤ positiveTarget) :
    Unorm a N < 0 := by
  have hN : 1 ≤ N := positiveRectangle_N_pos (by omega : 2 ≤ a) hrect
  have hSLlarge : ∀ k : Nat, 361 ≤ k →
      (N : ℚ) ≤ (40/3) * (k : ℚ) → Xnorm N k ≤ 0 := by
    intro k hk361 hNk
    exact Xnorm_nonpos_of_signLockMargin_bound hk361
      (Xnorm_le_neg_signLockMargin (N := N) (m := k) hN hNk hk361)
  have hU := Unorm_le_Xnorm_add_customEnvelope_of_signLock_nonpos
    (smallTerm := smallTerm) (temperedTerm := temperedTerm)
    (a := a) (N := N) ha hrect hSLlarge hsmall htempered
  have hXmain : Xnorm N a ≤ -signLockMargin a :=
    Xnorm_le_neg_signLockMargin
      (N := N) (m := a) hN
      (rectangle_N_le_signLock_range_self (a := a) (N := N) hrect)
      (by omega : 361 ≤ a)
  have hpositiveActual :
      positiveCustomEnvelope smallTerm temperedTerm a N ≤ positiveTarget :=
    (positiveCustomEnvelope_le_bound_of_solo
      (smallTerm := smallTerm) (temperedTerm := temperedTerm)
      (a := a) (N := N) (soloBound := soloBound) hsolo).trans hpositive
  have htarget := positiveTarget_lt_signLockMargin_of_ge_401 (m := a) ha
  linarith

/-- Packaged `a > 2000` positive-tail obligations for custom rational
small/tempered summand majorants.

This isolates the remaining entropy-tail work from the finite-window row
certificate.  A later proof can instantiate `smallTerm` and `temperedTerm`
with the entropy-shadow expressions, prove the pointwise saddle bounds and
the custom envelope budget, and obtain the old direct `entropyTail` field via
`PositiveSaddleCustomTailCertificate.entropyTail`. -/
structure PositiveSaddleCustomTailCertificate
    (smallTerm temperedTerm : Nat → Nat → ℚ) (soloBound : Nat → ℚ) : Prop where
  small :
    ∀ {a N k : Nat}, 2000 < a → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        normalizedPositiveIfTerm a N k ≤ smallTerm a k
  tempered :
    ∀ {a N k : Nat}, 2000 < a → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k →
        normalizedPositiveIfTerm a N k ≤ temperedTerm a k
  solo :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
      normalizedSoloTerm a N ≤ soloBound a
  envelope :
    ∀ {a : Nat}, 2000 < a →
      positiveCustomEnvelopeBound smallTerm temperedTerm a (soloBound a) ≤ positiveTarget

/-- Entropy-shadow specialization of the custom `a > 2000` positive-tail
certificate.  The remaining fields are exactly the analytic saddle bounds for
the entropy-shadow small/tempered shells, the solo bound, and the rational
custom-envelope budget. -/
structure PositiveSaddleEntropyShadowTailCertificate
    (soloBound : Nat → ℚ) : Prop where
  small :
    ∀ {a N k : Nat}, 2000 < a → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        normalizedPositiveIfTerm a N k ≤ positiveSmallEntropyShadowMajorantTerm a k
  tempered :
    ∀ {a N k : Nat}, 2000 < a → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k →
        normalizedPositiveIfTerm a N k ≤ positiveTemperedEntropyShadowMajorantTerm a k
  solo :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
      normalizedSoloTerm a N ≤ soloBound a
  envelope :
    ∀ {a : Nat}, 2000 < a →
      positiveEntropyShadowEnvelopeBound a (soloBound a) ≤ positiveTarget

theorem PositiveSaddleEntropyShadowTailCertificate.toCustomTailCertificate
    {soloBound : Nat → ℚ}
    (cert : PositiveSaddleEntropyShadowTailCertificate soloBound) :
    PositiveSaddleCustomTailCertificate
      positiveSmallEntropyShadowMajorantTerm
      positiveTemperedEntropyShadowMajorantTerm
      soloBound where
  small := cert.small
  tempered := cert.tempered
  solo := cert.solo
  envelope := by
    intro a ha
    simpa [positiveEntropyShadowEnvelopeBound] using cert.envelope (a := a) ha

theorem PositiveSaddleCustomTailCertificate.entropyTail
    {smallTerm temperedTerm : Nat → Nat → ℚ} {soloBound : Nat → ℚ}
    (cert : PositiveSaddleCustomTailCertificate smallTerm temperedTerm soloBound) :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0 := by
  intro a N ha2000 hrect
  exact Unorm_neg_of_signLock_and_customEnvelopeBound
    (smallTerm := smallTerm) (temperedTerm := temperedTerm)
    (a := a) (N := N) (soloBound := soloBound a)
    (by omega : 401 ≤ a) hrect
    (fun k hk hsmall => cert.small ha2000 hrect hk hsmall)
    (fun k hk htempered => cert.tempered ha2000 hrect hk htempered)
    (cert.solo ha2000 hrect)
    (cert.envelope ha2000)

theorem PositiveSaddleEntropyShadowTailCertificate.entropyTail
    {soloBound : Nat → ℚ}
    (cert : PositiveSaddleEntropyShadowTailCertificate soloBound) :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0 :=
  cert.toCustomTailCertificate.entropyTail

/-- Generic budget splitter for custom large-`a` positive envelopes. -/
theorem positiveCustomEnvelopeBound_le_target_of_budgets
    {smallTerm temperedTerm : Nat → Nat → ℚ} {a : Nat}
    {soloBound soloBudget edgeBudget : ℚ}
    (hsolo : soloBound ≤ soloBudget)
    (hedge : positiveCustomEdgeMajorantSum smallTerm temperedTerm a ≤ edgeBudget)
    (hbudget : soloBudget + edgeBudget ≤ positiveTarget) :
    positiveCustomEnvelopeBound smallTerm temperedTerm a soloBound ≤ positiveTarget := by
  unfold positiveCustomEnvelopeBound
  calc
    soloBound + positiveCustomEdgeMajorantSum smallTerm temperedTerm a
        ≤ soloBudget + edgeBudget := add_le_add hsolo hedge
    _ ≤ positiveTarget := hbudget

theorem positiveEntropyShadowEnvelopeBound_eq_solo_add_edge
    (a : Nat) (soloBound : ℚ) :
    positiveEntropyShadowEnvelopeBound a soloBound =
      soloBound + positiveEntropyShadowEdgeMajorantSum a := rfl

theorem positiveEntropyShadowEnvelope_le_bound_of_solo
    {a N : Nat} {soloBound : ℚ}
    (hsolo : normalizedSoloTerm a N ≤ soloBound) :
    positiveEntropyShadowEnvelope a N
      ≤ positiveEntropyShadowEnvelopeBound a soloBound :=
  positiveCustomEnvelope_le_bound_of_solo
    (smallTerm := positiveSmallEntropyShadowMajorantTerm)
    (temperedTerm := positiveTemperedEntropyShadowMajorantTerm)
    hsolo

/-- Entropy-shadow envelope budget after splitting the solo and retained-edge
allowances.  This is the same Lean bookkeeping split used on the finite
window; the TeX proof's sharper solo estimate can be inserted by proving
`soloBound ≤ positiveSoloBudget`. -/
theorem positiveEntropyShadowEnvelopeBound_le_target_of_budgets
    {a : Nat} {soloBound soloBudget edgeBudget : ℚ}
    (hsolo : soloBound ≤ soloBudget)
    (hedge : positiveEntropyShadowEdgeMajorantSum a ≤ edgeBudget)
    (hbudget : soloBudget + edgeBudget ≤ positiveTarget) :
    positiveEntropyShadowEnvelopeBound a soloBound ≤ positiveTarget :=
  positiveCustomEnvelopeBound_le_target_of_budgets
    (smallTerm := positiveSmallEntropyShadowMajorantTerm)
    (temperedTerm := positiveTemperedEntropyShadowMajorantTerm)
    hsolo hedge hbudget

theorem positiveEntropyShadowEnvelopeBound_le_target_of_standard_budgets
    {a : Nat} {soloBound : ℚ}
    (hsolo : soloBound ≤ positiveSoloBudget)
    (hedge : positiveEntropyShadowEdgeMajorantSum a ≤ positiveEdgeBudget) :
    positiveEntropyShadowEnvelopeBound a soloBound ≤ positiveTarget := by
  refine positiveEntropyShadowEnvelopeBound_le_target_of_budgets hsolo hedge ?_
  rw [positiveSoloBudget_add_edgeBudget]

theorem positiveEntropyShadowEdgeMajorantSum_le_edgeBudget_of_branch_budgets
    {a : Nat} {smallBudget temperedBudget edgeBudget : ℚ}
    (hsmall0 :
      ∀ k, k ∈ positiveKRange a →
        0 ≤ positiveSmallEntropyShadowMajorantTerm a k)
    (htempered0 :
      ∀ k, k ∈ positiveKRange a →
        0 ≤ positiveTemperedEntropyShadowMajorantTerm a k)
    (hsmall : positiveEntropyShadowSmallBranchSum a ≤ smallBudget)
    (htempered : positiveEntropyShadowTemperedBranchSum a ≤ temperedBudget)
    (hbudget : smallBudget + temperedBudget ≤ edgeBudget) :
    positiveEntropyShadowEdgeMajorantSum a ≤ edgeBudget :=
  positiveCustomEdgeMajorantSum_le_edgeBudget_of_branch_budgets
    (smallTerm := positiveSmallEntropyShadowMajorantTerm)
    (temperedTerm := positiveTemperedEntropyShadowMajorantTerm)
    hsmall0 htempered0 hsmall htempered hbudget

theorem positiveEntropyShadowEdgeMajorantSum_le_edgeBudget_of_half_branch_budgets
    {a : Nat}
    (hsmall0 :
      ∀ k, k ∈ positiveKRange a →
        0 ≤ positiveSmallEntropyShadowMajorantTerm a k)
    (htempered0 :
      ∀ k, k ∈ positiveKRange a →
        0 ≤ positiveTemperedEntropyShadowMajorantTerm a k)
    (hsmall : positiveEntropyShadowSmallBranchSum a ≤ positiveEdgeBudget / 2)
    (htempered :
      positiveEntropyShadowTemperedBranchSum a ≤ positiveEdgeBudget / 2) :
    positiveEntropyShadowEdgeMajorantSum a ≤ positiveEdgeBudget := by
  refine positiveEntropyShadowEdgeMajorantSum_le_edgeBudget_of_branch_budgets
    hsmall0 htempered0 hsmall htempered ?_
  norm_num [positiveEdgeBudget, positiveTarget]

/-- Budgeted entropy-shadow tail interface.

This is the large-`a` analogue of the finite-window budget certificates: the
analytic work proves pointwise small/tempered bounds, the solo term is placed
under the standard `positiveSoloBudget`, and the retained edge sum is placed
under `positiveEdgeBudget`. -/
structure PositiveSaddleEntropyShadowBudgetCertificate : Prop where
  small :
    ∀ {a N k : Nat}, 2000 < a → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        normalizedPositiveIfTerm a N k ≤ positiveSmallEntropyShadowMajorantTerm a k
  tempered :
    ∀ {a N k : Nat}, 2000 < a → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k →
        normalizedPositiveIfTerm a N k ≤ positiveTemperedEntropyShadowMajorantTerm a k
  soloBudget :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
      normalizedSoloTerm a N ≤ positiveSoloBudget
  edgeBudget :
    ∀ {a : Nat}, 2000 < a →
      positiveEntropyShadowEdgeMajorantSum a ≤ positiveEdgeBudget

theorem PositiveSaddleEntropyShadowBudgetCertificate.toTailCertificate
    (cert : PositiveSaddleEntropyShadowBudgetCertificate) :
    PositiveSaddleEntropyShadowTailCertificate (fun _ => positiveSoloBudget) where
  small := cert.small
  tempered := cert.tempered
  solo := cert.soloBudget
  envelope := by
    intro a ha
    exact positiveEntropyShadowEnvelopeBound_le_target_of_standard_budgets
      (soloBound := positiveSoloBudget) le_rfl (cert.edgeBudget ha)

theorem PositiveSaddleEntropyShadowBudgetCertificate.entropyTail
    (cert : PositiveSaddleEntropyShadowBudgetCertificate) :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0 :=
  cert.toTailCertificate.entropyTail

/-- Split-budget form of the entropy-shadow tail interface.

This matches the two-regime structure of the TeX proof more closely than the
single retained-edge budget: small and tempered branch sums are bounded
separately, and Lean combines them through the `max ≤ small + tempered`
branch-split lemma above. -/
structure PositiveSaddleEntropyShadowSplitBudgetCertificate : Prop where
  small :
    ∀ {a N k : Nat}, 2000 < a → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        normalizedPositiveIfTerm a N k ≤ positiveSmallEntropyShadowMajorantTerm a k
  tempered :
    ∀ {a N k : Nat}, 2000 < a → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k →
        normalizedPositiveIfTerm a N k ≤ positiveTemperedEntropyShadowMajorantTerm a k
  soloBudget :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
      normalizedSoloTerm a N ≤ positiveSoloBudget
  smallNonneg :
    ∀ {a k : Nat}, 2000 < a → k ∈ positiveKRange a →
      0 ≤ positiveSmallEntropyShadowMajorantTerm a k
  temperedNonneg :
    ∀ {a k : Nat}, 2000 < a → k ∈ positiveKRange a →
      0 ≤ positiveTemperedEntropyShadowMajorantTerm a k
  smallEdgeBudget :
    ∀ {a : Nat}, 2000 < a →
      positiveEntropyShadowSmallBranchSum a ≤ positiveEdgeBudget / 2
  temperedEdgeBudget :
    ∀ {a : Nat}, 2000 < a →
      positiveEntropyShadowTemperedBranchSum a ≤ positiveEdgeBudget / 2

theorem PositiveSaddleEntropyShadowSplitBudgetCertificate.toBudgetCertificate
    (cert : PositiveSaddleEntropyShadowSplitBudgetCertificate) :
    PositiveSaddleEntropyShadowBudgetCertificate where
  small := cert.small
  tempered := cert.tempered
  soloBudget := cert.soloBudget
  edgeBudget := by
    intro a ha
    exact positiveEntropyShadowEdgeMajorantSum_le_edgeBudget_of_half_branch_budgets
      (fun k hk => cert.smallNonneg (a := a) ha hk)
      (fun k hk => cert.temperedNonneg (a := a) ha hk)
      (cert.smallEdgeBudget ha)
      (cert.temperedEdgeBudget ha)

theorem PositiveSaddleEntropyShadowSplitBudgetCertificate.entropyTail
    (cert : PositiveSaddleEntropyShadowSplitBudgetCertificate) :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0 :=
  cert.toBudgetCertificate.entropyTail

/-- Entropy-shadow split-budget interface with externally supplied rational
exponential majorants.

Use this for the final `a > 2000` proof if the finite-window
`partialExpUpper` shell is replaced by a large-tail-specific exponential
bound.  The binomial entropy shadow and dyadic decay remain fixed; only the
last exponential factor is parameterized. -/
structure PositiveSaddleEntropyShadowExpSplitBudgetCertificate
    (smallExp temperedExp : Nat → Nat → ℚ) : Prop where
  small :
    ∀ {a N k : Nat}, 2000 < a → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        normalizedPositiveIfTerm a N k
          ≤ positiveSmallEntropyShadowExpMajorantTerm smallExp a k
  tempered :
    ∀ {a N k : Nat}, 2000 < a → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k →
        normalizedPositiveIfTerm a N k
          ≤ positiveTemperedEntropyShadowExpMajorantTerm temperedExp a k
  soloBudget :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
      normalizedSoloTerm a N ≤ positiveSoloBudget
  smallNonneg :
    ∀ {a k : Nat}, 2000 < a → k ∈ positiveKRange a →
      0 ≤ positiveSmallEntropyShadowExpMajorantTerm smallExp a k
  temperedNonneg :
    ∀ {a k : Nat}, 2000 < a → k ∈ positiveKRange a →
      0 ≤ positiveTemperedEntropyShadowExpMajorantTerm temperedExp a k
  smallEdgeBudget :
    ∀ {a : Nat}, 2000 < a →
      positiveEntropyShadowExpSmallBranchSum smallExp a ≤ positiveEdgeBudget / 2
  temperedEdgeBudget :
    ∀ {a : Nat}, 2000 < a →
      positiveEntropyShadowExpTemperedBranchSum temperedExp a ≤ positiveEdgeBudget / 2

theorem PositiveSaddleEntropyShadowExpSplitBudgetCertificate.toCustomTailCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    (cert : PositiveSaddleEntropyShadowExpSplitBudgetCertificate
      smallExp temperedExp) :
    PositiveSaddleCustomTailCertificate
      (positiveSmallEntropyShadowExpMajorantTerm smallExp)
      (positiveTemperedEntropyShadowExpMajorantTerm temperedExp)
      (fun _ => positiveSoloBudget) where
  small := cert.small
  tempered := cert.tempered
  solo := cert.soloBudget
  envelope := by
    intro a ha
    have hedge :
        positiveCustomEdgeMajorantSum
            (positiveSmallEntropyShadowExpMajorantTerm smallExp)
            (positiveTemperedEntropyShadowExpMajorantTerm temperedExp) a
          ≤ positiveEdgeBudget := by
      refine positiveCustomEdgeMajorantSum_le_edgeBudget_of_branch_budgets
        (smallTerm := positiveSmallEntropyShadowExpMajorantTerm smallExp)
        (temperedTerm := positiveTemperedEntropyShadowExpMajorantTerm temperedExp)
        (smallBudget := positiveEdgeBudget / 2)
        (temperedBudget := positiveEdgeBudget / 2)
        (edgeBudget := positiveEdgeBudget)
        ?hsmall0 ?htempered0 (cert.smallEdgeBudget ha)
        (cert.temperedEdgeBudget ha) ?hbudget
      · intro k hk
        exact cert.smallNonneg (a := a) ha hk
      · intro k hk
        exact cert.temperedNonneg (a := a) ha hk
      · norm_num [positiveEdgeBudget, positiveTarget]
    refine positiveCustomEnvelopeBound_le_target_of_budgets
      (smallTerm := positiveSmallEntropyShadowExpMajorantTerm smallExp)
      (temperedTerm := positiveTemperedEntropyShadowExpMajorantTerm temperedExp)
      (soloBound := positiveSoloBudget)
      le_rfl hedge ?_
    rw [positiveSoloBudget_add_edgeBudget]

theorem PositiveSaddleEntropyShadowExpSplitBudgetCertificate.entropyTail
    {smallExp temperedExp : Nat → Nat → ℚ}
    (cert : PositiveSaddleEntropyShadowExpSplitBudgetCertificate
      smallExp temperedExp) :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0 :=
  cert.toCustomTailCertificate.entropyTail

/-- First-term/ratio version of the parameterized entropy-shadow tail
certificate.

This is the form expected from a hand or generated rational entropy-tail
audit: for each branch, prove a nonnegative exponential factor, a uniform
successor ratio below `1`, and a first-term geometric tail budget.  Lean then
supplies the active-range arithmetic, branch-sum geometric bound, and final
positive-envelope assembly. -/
structure PositiveSaddleEntropyShadowExpGeometricBudgetCertificate
    (smallExp temperedExp : Nat → Nat → ℚ)
    (smallRatio temperedRatio : Nat → ℚ) : Prop where
  small :
    ∀ {a N k : Nat}, 2000 < a → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        normalizedPositiveIfTerm a N k
          ≤ positiveSmallEntropyShadowExpMajorantTerm smallExp a k
  tempered :
    ∀ {a N k : Nat}, 2000 < a → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k →
        normalizedPositiveIfTerm a N k
          ≤ positiveTemperedEntropyShadowExpMajorantTerm temperedExp a k
  soloBudget :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
      normalizedSoloTerm a N ≤ positiveSoloBudget
  smallExpNonneg :
    ∀ {a k : Nat}, 2000 < a → k ∈ positiveKRange a →
      0 ≤ smallExp a k
  temperedExpNonneg :
    ∀ {a k : Nat}, 2000 < a → k ∈ positiveKRange a →
      0 ≤ temperedExp a k
  smallRatioNonneg :
    ∀ {a : Nat}, 2000 < a → 0 ≤ smallRatio a
  smallRatioLtOne :
    ∀ {a : Nat}, 2000 < a → smallRatio a < 1
  smallStep :
    ∀ {a r : Nat}, 2000 < a → 1 ≤ r →
      r < min (posKmax a) (posSmallCutoff a) →
        positiveSmallEntropyShadowExpMajorantTerm smallExp a (r + 1)
          ≤ positiveSmallEntropyShadowExpMajorantTerm smallExp a r *
            smallRatio a
  smallFirstBudget :
    ∀ {a : Nat}, 2000 < a →
      positiveSmallEntropyShadowExpMajorantTerm smallExp a 1 *
        (1 / (1 - smallRatio a)) ≤ positiveEdgeBudget / 2
  temperedRatioNonneg :
    ∀ {a : Nat}, 2000 < a → 0 ≤ temperedRatio a
  temperedRatioLtOne :
    ∀ {a : Nat}, 2000 < a → temperedRatio a < 1
  temperedStep :
    ∀ {a r : Nat}, 2000 < a →
      max 1 (posTemperedCutoff a + 1) ≤ r → r < posKmax a →
        positiveTemperedEntropyShadowExpMajorantTerm temperedExp a (r + 1)
          ≤ positiveTemperedEntropyShadowExpMajorantTerm temperedExp a r *
            temperedRatio a
  temperedFirstBudget :
    ∀ {a : Nat}, 2000 < a →
      positiveTemperedEntropyShadowExpMajorantTerm temperedExp a
        (max 1 (posTemperedCutoff a + 1)) *
          (1 / (1 - temperedRatio a)) ≤ positiveEdgeBudget / 2

/-- Reserve form of
`PositiveSaddleEntropyShadowExpGeometricBudgetCertificate`.

The mathematical audit usually proves the first-term estimate after multiplying
by the geometric margin, `first ≤ budget * (1-ratio)`.  This wrapper records
that more direct inequality and converts it to the existing inverse-margin
budget internally. -/
structure PositiveSaddleEntropyShadowExpGeometricReserveCertificate
    (smallExp temperedExp : Nat → Nat → ℚ)
    (smallRatio temperedRatio : Nat → ℚ) : Prop where
  small :
    ∀ {a N k : Nat}, 2000 < a → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        normalizedPositiveIfTerm a N k
          ≤ positiveSmallEntropyShadowExpMajorantTerm smallExp a k
  tempered :
    ∀ {a N k : Nat}, 2000 < a → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k →
        normalizedPositiveIfTerm a N k
          ≤ positiveTemperedEntropyShadowExpMajorantTerm temperedExp a k
  soloBudget :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
      normalizedSoloTerm a N ≤ positiveSoloBudget
  smallExpNonneg :
    ∀ {a k : Nat}, 2000 < a → k ∈ positiveKRange a →
      0 ≤ smallExp a k
  temperedExpNonneg :
    ∀ {a k : Nat}, 2000 < a → k ∈ positiveKRange a →
      0 ≤ temperedExp a k
  smallRatioNonneg :
    ∀ {a : Nat}, 2000 < a → 0 ≤ smallRatio a
  smallRatioLtOne :
    ∀ {a : Nat}, 2000 < a → smallRatio a < 1
  smallStep :
    ∀ {a r : Nat}, 2000 < a → 1 ≤ r →
      r < min (posKmax a) (posSmallCutoff a) →
        positiveSmallEntropyShadowExpMajorantTerm smallExp a (r + 1)
          ≤ positiveSmallEntropyShadowExpMajorantTerm smallExp a r *
            smallRatio a
  smallFirstReserve :
    ∀ {a : Nat}, 2000 < a →
      positiveSmallEntropyShadowExpMajorantTerm smallExp a 1
        ≤ (positiveEdgeBudget / 2) * (1 - smallRatio a)
  temperedRatioNonneg :
    ∀ {a : Nat}, 2000 < a → 0 ≤ temperedRatio a
  temperedRatioLtOne :
    ∀ {a : Nat}, 2000 < a → temperedRatio a < 1
  temperedStep :
    ∀ {a r : Nat}, 2000 < a →
      max 1 (posTemperedCutoff a + 1) ≤ r → r < posKmax a →
        positiveTemperedEntropyShadowExpMajorantTerm temperedExp a (r + 1)
          ≤ positiveTemperedEntropyShadowExpMajorantTerm temperedExp a r *
            temperedRatio a
  temperedFirstReserve :
    ∀ {a : Nat}, 2000 < a →
      positiveTemperedEntropyShadowExpMajorantTerm temperedExp a
        (max 1 (posTemperedCutoff a + 1))
          ≤ (positiveEdgeBudget / 2) * (1 - temperedRatio a)

theorem PositiveSaddleEntropyShadowExpGeometricReserveCertificate.toGeometricBudgetCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleEntropyShadowExpGeometricReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleEntropyShadowExpGeometricBudgetCertificate
      smallExp temperedExp smallRatio temperedRatio where
  small := cert.small
  tempered := cert.tempered
  soloBudget := cert.soloBudget
  smallExpNonneg := cert.smallExpNonneg
  temperedExpNonneg := cert.temperedExpNonneg
  smallRatioNonneg := cert.smallRatioNonneg
  smallRatioLtOne := cert.smallRatioLtOne
  smallStep := cert.smallStep
  smallFirstBudget := by
    intro a ha
    exact mul_inv_one_sub_le_of_le_mul_one_sub
      (cert.smallRatioLtOne ha) (cert.smallFirstReserve ha)
  temperedRatioNonneg := cert.temperedRatioNonneg
  temperedRatioLtOne := cert.temperedRatioLtOne
  temperedStep := cert.temperedStep
  temperedFirstBudget := by
    intro a ha
    exact mul_inv_one_sub_le_of_le_mul_one_sub
      (cert.temperedRatioLtOne ha) (cert.temperedFirstReserve ha)

/-- Quotient-ratio form of the entropy-shadow reserve certificate.

This is convenient for generated rational checks: prove positivity of the
current summand and the adjacent quotient bound, and Lean converts it to the
successor-step inequality used by the geometric-tail machinery. -/
structure PositiveSaddleEntropyShadowExpQuotientReserveCertificate
    (smallExp temperedExp : Nat → Nat → ℚ)
    (smallRatio temperedRatio : Nat → ℚ) : Prop where
  small :
    ∀ {a N k : Nat}, 2000 < a → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        normalizedPositiveIfTerm a N k
          ≤ positiveSmallEntropyShadowExpMajorantTerm smallExp a k
  tempered :
    ∀ {a N k : Nat}, 2000 < a → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k →
        normalizedPositiveIfTerm a N k
          ≤ positiveTemperedEntropyShadowExpMajorantTerm temperedExp a k
  soloBudget :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
      normalizedSoloTerm a N ≤ positiveSoloBudget
  smallExpNonneg :
    ∀ {a k : Nat}, 2000 < a → k ∈ positiveKRange a →
      0 ≤ smallExp a k
  temperedExpNonneg :
    ∀ {a k : Nat}, 2000 < a → k ∈ positiveKRange a →
      0 ≤ temperedExp a k
  smallRatioNonneg :
    ∀ {a : Nat}, 2000 < a → 0 ≤ smallRatio a
  smallRatioLtOne :
    ∀ {a : Nat}, 2000 < a → smallRatio a < 1
  smallStepTermPos :
    ∀ {a r : Nat}, 2000 < a → 1 ≤ r →
      r < min (posKmax a) (posSmallCutoff a) →
        0 < positiveSmallEntropyShadowExpMajorantTerm smallExp a r
  smallStepQuotient :
    ∀ {a r : Nat}, 2000 < a → 1 ≤ r →
      r < min (posKmax a) (posSmallCutoff a) →
        positiveSmallEntropyShadowExpMajorantTerm smallExp a (r + 1) /
            positiveSmallEntropyShadowExpMajorantTerm smallExp a r
          ≤ smallRatio a
  smallFirstReserve :
    ∀ {a : Nat}, 2000 < a →
      positiveSmallEntropyShadowExpMajorantTerm smallExp a 1
        ≤ (positiveEdgeBudget / 2) * (1 - smallRatio a)
  temperedRatioNonneg :
    ∀ {a : Nat}, 2000 < a → 0 ≤ temperedRatio a
  temperedRatioLtOne :
    ∀ {a : Nat}, 2000 < a → temperedRatio a < 1
  temperedStepTermPos :
    ∀ {a r : Nat}, 2000 < a →
      max 1 (posTemperedCutoff a + 1) ≤ r → r < posKmax a →
        0 < positiveTemperedEntropyShadowExpMajorantTerm temperedExp a r
  temperedStepQuotient :
    ∀ {a r : Nat}, 2000 < a →
      max 1 (posTemperedCutoff a + 1) ≤ r → r < posKmax a →
        positiveTemperedEntropyShadowExpMajorantTerm temperedExp a (r + 1) /
            positiveTemperedEntropyShadowExpMajorantTerm temperedExp a r
          ≤ temperedRatio a
  temperedFirstReserve :
    ∀ {a : Nat}, 2000 < a →
      positiveTemperedEntropyShadowExpMajorantTerm temperedExp a
        (max 1 (posTemperedCutoff a + 1))
          ≤ (positiveEdgeBudget / 2) * (1 - temperedRatio a)

theorem PositiveSaddleEntropyShadowExpQuotientReserveCertificate.toGeometricReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleEntropyShadowExpQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleEntropyShadowExpGeometricReserveCertificate
      smallExp temperedExp smallRatio temperedRatio where
  small := cert.small
  tempered := cert.tempered
  soloBudget := cert.soloBudget
  smallExpNonneg := cert.smallExpNonneg
  temperedExpNonneg := cert.temperedExpNonneg
  smallRatioNonneg := cert.smallRatioNonneg
  smallRatioLtOne := cert.smallRatioLtOne
  smallStep := by
    intro a r ha hr1 hrhi
    exact positiveSmallEntropyShadowExp_step_of_div_step
      (cert.smallStepTermPos ha hr1 hrhi)
      (cert.smallStepQuotient ha hr1 hrhi)
  smallFirstReserve := cert.smallFirstReserve
  temperedRatioNonneg := cert.temperedRatioNonneg
  temperedRatioLtOne := cert.temperedRatioLtOne
  temperedStep := by
    intro a r ha hrlo hrhi
    exact positiveTemperedEntropyShadowExp_step_of_div_step
      (cert.temperedStepTermPos ha hrlo hrhi)
      (cert.temperedStepQuotient ha hrlo hrhi)
  temperedFirstReserve := cert.temperedFirstReserve

theorem PositiveSaddleEntropyShadowExpQuotientReserveCertificate.toGeometricBudgetCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleEntropyShadowExpQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleEntropyShadowExpGeometricBudgetCertificate
      smallExp temperedExp smallRatio temperedRatio :=
  cert.toGeometricReserveCertificate.toGeometricBudgetCertificate

/-- Raw-base quotient form of the entropy-shadow reserve certificate.

Compared with `PositiveSaddleEntropyShadowExpQuotientReserveCertificate`, the
successor check has already been reduced to the explicit rational base quotient
`positiveEntropyShadowBaseStepRawQuotient` times the externally supplied
exponential quotient.  This is the intended target for generated large-tail
ratio audits. -/
structure PositiveSaddleEntropyShadowExpRawQuotientReserveCertificate
    (smallExp temperedExp : Nat → Nat → ℚ)
    (smallRatio temperedRatio : Nat → ℚ) : Prop where
  small :
    ∀ {a N k : Nat}, 2000 < a → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        normalizedPositiveIfTerm a N k
          ≤ positiveSmallEntropyShadowExpMajorantTerm smallExp a k
  tempered :
    ∀ {a N k : Nat}, 2000 < a → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k →
        normalizedPositiveIfTerm a N k
          ≤ positiveTemperedEntropyShadowExpMajorantTerm temperedExp a k
  soloBudget :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N →
      normalizedSoloTerm a N ≤ positiveSoloBudget
  smallExpNonneg :
    ∀ {a k : Nat}, 2000 < a → k ∈ positiveKRange a →
      0 ≤ smallExp a k
  temperedExpNonneg :
    ∀ {a k : Nat}, 2000 < a → k ∈ positiveKRange a →
      0 ≤ temperedExp a k
  smallRatioNonneg :
    ∀ {a : Nat}, 2000 < a → 0 ≤ smallRatio a
  smallRatioLtOne :
    ∀ {a : Nat}, 2000 < a → smallRatio a < 1
  smallStepExpPos :
    ∀ {a r : Nat}, 2000 < a → 1 ≤ r →
      r < min (posKmax a) (posSmallCutoff a) →
        0 < smallExp a r
  smallRawStepQuotient :
    ∀ {a r : Nat}, 2000 < a → 1 ≤ r →
      r < min (posKmax a) (posSmallCutoff a) →
        positiveEntropyShadowBaseStepRawQuotient a r *
            (smallExp a (r + 1) / smallExp a r)
          ≤ smallRatio a
  smallFirstReserve :
    ∀ {a : Nat}, 2000 < a →
      positiveSmallEntropyShadowExpMajorantTerm smallExp a 1
        ≤ (positiveEdgeBudget / 2) * (1 - smallRatio a)
  temperedRatioNonneg :
    ∀ {a : Nat}, 2000 < a → 0 ≤ temperedRatio a
  temperedRatioLtOne :
    ∀ {a : Nat}, 2000 < a → temperedRatio a < 1
  temperedStepExpPos :
    ∀ {a r : Nat}, 2000 < a →
      max 1 (posTemperedCutoff a + 1) ≤ r → r < posKmax a →
        0 < temperedExp a r
  temperedRawStepQuotient :
    ∀ {a r : Nat}, 2000 < a →
      max 1 (posTemperedCutoff a + 1) ≤ r → r < posKmax a →
        positiveEntropyShadowBaseStepRawQuotient a r *
            (temperedExp a (r + 1) / temperedExp a r)
          ≤ temperedRatio a
  temperedFirstReserve :
    ∀ {a : Nat}, 2000 < a →
      positiveTemperedEntropyShadowExpMajorantTerm temperedExp a
        (max 1 (posTemperedCutoff a + 1))
          ≤ (positiveEdgeBudget / 2) * (1 - temperedRatio a)

theorem PositiveSaddleEntropyShadowExpRawQuotientReserveCertificate.toQuotientReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleEntropyShadowExpRawQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleEntropyShadowExpQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio where
  small := cert.small
  tempered := cert.tempered
  soloBudget := cert.soloBudget
  smallExpNonneg := cert.smallExpNonneg
  temperedExpNonneg := cert.temperedExpNonneg
  smallRatioNonneg := cert.smallRatioNonneg
  smallRatioLtOne := cert.smallRatioLtOne
  smallStepTermPos := by
    intro a r ha hr1 hrhi
    exact positiveSmallEntropyShadowExpMajorantTerm_pos_of_branch_step
      ha hr1 hrhi (cert.smallStepExpPos ha hr1 hrhi)
  smallStepQuotient := by
    intro a r ha hr1 hrhi
    rw [positiveSmallEntropyShadowExp_quotient_eq_raw_mul_exp_of_branch
      ha hr1 hrhi (cert.smallStepExpPos ha hr1 hrhi).ne']
    exact cert.smallRawStepQuotient ha hr1 hrhi
  smallFirstReserve := cert.smallFirstReserve
  temperedRatioNonneg := cert.temperedRatioNonneg
  temperedRatioLtOne := cert.temperedRatioLtOne
  temperedStepTermPos := by
    intro a r ha hrlo hrhi
    exact positiveTemperedEntropyShadowExpMajorantTerm_pos_of_branch_step
      ha hrlo hrhi (cert.temperedStepExpPos ha hrlo hrhi)
  temperedStepQuotient := by
    intro a r ha hrlo hrhi
    rw [positiveTemperedEntropyShadowExp_quotient_eq_raw_mul_exp_of_branch
      ha hrlo hrhi (cert.temperedStepExpPos ha hrlo hrhi).ne']
    exact cert.temperedRawStepQuotient ha hrlo hrhi
  temperedFirstReserve := cert.temperedFirstReserve

theorem PositiveSaddleEntropyShadowExpRawQuotientReserveCertificate.toGeometricReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleEntropyShadowExpRawQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleEntropyShadowExpGeometricReserveCertificate
      smallExp temperedExp smallRatio temperedRatio :=
  cert.toQuotientReserveCertificate.toGeometricReserveCertificate

theorem PositiveSaddleEntropyShadowExpRawQuotientReserveCertificate.toGeometricBudgetCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleEntropyShadowExpRawQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleEntropyShadowExpGeometricBudgetCertificate
      smallExp temperedExp smallRatio temperedRatio :=
  cert.toGeometricReserveCertificate.toGeometricBudgetCertificate

theorem one_mem_positiveKRange_of_large {a : Nat} (ha : 2 ≤ a) :
    1 ∈ positiveKRange a :=
  mem_positiveKRange.mpr ⟨le_rfl, one_le_posKmax ha⟩

theorem positiveTemperedBranch_start_mem_positiveKRange_of_large {a : Nat}
    (ha : 2000 < a) :
    max 1 (posTemperedCutoff a + 1) ∈ positiveKRange a :=
  mem_positiveKRange.mpr
    ⟨le_max_left _ _, positiveTemperedBranch_start_le_posKmax_of_large ha⟩

theorem PositiveSaddleEntropyShadowExpGeometricBudgetCertificate.toExpSplitBudgetCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleEntropyShadowExpGeometricBudgetCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleEntropyShadowExpSplitBudgetCertificate smallExp temperedExp where
  small := cert.small
  tempered := cert.tempered
  soloBudget := cert.soloBudget
  smallNonneg := by
    intro a k ha hk
    exact positiveSmallEntropyShadowExpMajorantTerm_nonneg
      (by omega : 20 ≤ a) hk (cert.smallExpNonneg ha hk)
  temperedNonneg := by
    intro a k ha hk
    exact positiveTemperedEntropyShadowExpMajorantTerm_nonneg
      (by omega : 20 ≤ a) hk (cert.temperedExpNonneg ha hk)
  smallEdgeBudget := by
    intro a ha
    have hF0 :
        0 ≤ positiveSmallEntropyShadowExpMajorantTerm smallExp a 1 :=
      positiveSmallEntropyShadowExpMajorantTerm_nonneg
        (by omega : 20 ≤ a)
        (one_mem_positiveKRange_of_large (by omega : 2 ≤ a))
        (cert.smallExpNonneg ha
          (one_mem_positiveKRange_of_large (by omega : 2 ≤ a)))
    exact positiveEntropyShadowExpSmallBranchSum_le_halfEdgeBudget_of_ratio_large
      ha hF0 (cert.smallRatioNonneg ha) (cert.smallRatioLtOne ha)
      (fun r hr1 hrhi => cert.smallStep ha hr1 hrhi)
      (cert.smallFirstBudget ha)
  temperedEdgeBudget := by
    intro a ha
    have hstart :
        max 1 (posTemperedCutoff a + 1) ∈ positiveKRange a :=
      positiveTemperedBranch_start_mem_positiveKRange_of_large ha
    have hF0 :
        0 ≤ positiveTemperedEntropyShadowExpMajorantTerm temperedExp a
          (max 1 (posTemperedCutoff a + 1)) :=
      positiveTemperedEntropyShadowExpMajorantTerm_nonneg
        (by omega : 20 ≤ a) hstart
        (cert.temperedExpNonneg ha hstart)
    exact positiveEntropyShadowExpTemperedBranchSum_le_halfEdgeBudget_of_ratio_large
      ha hF0 (cert.temperedRatioNonneg ha) (cert.temperedRatioLtOne ha)
      (fun r hrlo hrhi => cert.temperedStep ha hrlo hrhi)
      (cert.temperedFirstBudget ha)

theorem PositiveSaddleEntropyShadowExpGeometricBudgetCertificate.entropyTail
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleEntropyShadowExpGeometricBudgetCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0 :=
  cert.toExpSplitBudgetCertificate.entropyTail

theorem PositiveSaddleEntropyShadowExpGeometricReserveCertificate.entropyTail
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleEntropyShadowExpGeometricReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0 :=
  cert.toGeometricBudgetCertificate.entropyTail

theorem PositiveSaddleEntropyShadowExpQuotientReserveCertificate.entropyTail
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleEntropyShadowExpQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0 :=
  cert.toGeometricBudgetCertificate.entropyTail

/-! ## Packaged remaining §6 certificate interface -/

/-- The remaining positive-saddle obligations after the completed sign-lock
argument.  The four fields match the current proof split:

* small-regime pointwise saddle bound on the finite window `401 ≤ a ≤ 2000`;
* tempered-regime pointwise saddle bound on the same finite window;
* solo `Q_a` bound on the finite window;
* positive-envelope certificate after inserting the solo bound;
* entropy tail for `a > 2000`.

The `soloBound` parameter lets a later certificate use either the TeX-style
`exp(-0.49a)` surrogate or a sharper executable bound without changing the
assembly layer. -/
structure PositiveSaddleCertificate (soloBound : Nat → ℚ) : Prop where
  small :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        normalizedPositiveIfTerm a N k ≤ positiveSmallMajorantTerm a k
  tempered :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k →
        normalizedPositiveIfTerm a N k ≤ positiveTemperedMajorantTerm a k
  solo :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      normalizedSoloTerm a N ≤ soloBound a
  envelope :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEnvelopeBound a (soloBound a) ≤ positiveTarget
  entropyTail :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0

/-- A more convenient version of `PositiveSaddleCertificate` for the analytic
saddle work: the pointwise fields bound the raw product
`B_k Q_{a-k}/(N c_a)`.  The conversion below supplies the `B_k > 0` guard
automatically, using nonnegativity of the explicit majorants on the finite
window. -/
structure PositiveSaddleRawCertificate (soloBound : Nat → ℚ) : Prop where
  smallRaw :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        normalizedPositiveRawTerm a N k ≤ positiveSmallMajorantTerm a k
  temperedRaw :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k →
        normalizedPositiveRawTerm a N k ≤ positiveTemperedMajorantTerm a k
  solo :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      normalizedSoloTerm a N ≤ soloBound a
  envelope :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEnvelopeBound a (soloBound a) ≤ positiveTarget
  entropyTail :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0

/-- TeX-facing version of the remaining §6 certificate.  The pointwise
summand fields now use the exact factorized form
`(N/2) R_{k,a} 2^{-(a-k)} X_k(N)Y_{a-k}(N)` and only need to be proved when
`B_k(N)>0`; the conversion to raw summands handles the nonpositive `B_k`
case automatically.  The solo field is likewise stated in terms of
`2^{-a-1}Y_a(N)`. -/
structure PositiveSaddleFactorCertificate (soloBound : Nat → ℚ) : Prop where
  smallFactor :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N → 0 < Bq N k →
        positiveFactorizedRawTerm a N k ≤ positiveSmallMajorantTerm a k
  temperedFactor :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k → 0 < Bq N k →
        positiveFactorizedRawTerm a N k ≤ positiveTemperedMajorantTerm a k
  soloY :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      positiveDyadicDecay a / 2 * Ynorm N a ≤ soloBound a
  envelope :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEnvelopeBound a (soloBound a) ≤ positiveTarget
  entropyTail :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0

/-- Intermediate §6 interface after the coefficient-ratio and scalar-product
bookkeeping has been formalized.  The pointwise fields only need to prove the
factorized summand is below the explicit scalar products with constants
`8.9·14.5/2` and `7.3·14.5/2`; Lean then transports those bounds to the
executable small/tempered majorants. -/
structure PositiveSaddleScalarCertificate (soloBound : Nat → ℚ) : Prop where
  smallScalar :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N → 0 < Bq N k →
        positiveFactorizedRawTerm a N k ≤ positiveSmallScalarProductBound a k
  temperedScalar :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k → 0 < Bq N k →
        positiveFactorizedRawTerm a N k ≤ positiveTemperedScalarProductBound a N k
  soloY :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      positiveDyadicDecay a / 2 * Ynorm N a ≤ soloBound a
  envelope :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEnvelopeBound a (soloBound a) ≤ positiveTarget
  entropyTail :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0

/-- Budgeted scalar-product interface for the remaining §6 work.

Compared with `PositiveSaddleScalarCertificate`, this fixes the solo bound to
the deliberately loose half-target budget and replaces the finite envelope
field by the smaller corrected-edge scan obligation
`positiveEdgeMajorantSum a ≤ positiveEdgeBudget`. -/
structure PositiveSaddleScalarBudgetCertificate : Prop where
  smallScalar :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N → 0 < Bq N k →
        positiveFactorizedRawTerm a N k ≤ positiveSmallScalarProductBound a k
  temperedScalar :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k → 0 < Bq N k →
        positiveFactorizedRawTerm a N k ≤ positiveTemperedScalarProductBound a N k
  soloY :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget
  edgeBudget :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeMajorantSum a ≤ positiveEdgeBudget
  entropyTail :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0

/-- Combined-product version of the budgeted §6 interface.  Its analytic
fields ask directly for bounds on `X_k(N) * Y_{a-k}(N)` with the combined
exponents used by the executable majorants, avoiding the false
submultiplicativity requirement for independent `partialExpUpper` bounds. -/
structure PositiveSaddleCombinedProductBudgetCertificate : Prop where
  smallXY :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N → 0 < Bq N k →
        Xnorm N k * Ynorm N (posJ a k) ≤ positiveSmallXYProductBound a N k
  temperedXY :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k → 0 < Bq N k →
        Xnorm N k * Ynorm N (posJ a k) ≤ positiveTemperedXYProductBound a N k
  soloY :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget
  edgeBudget :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeMajorantSum a ≤ positiveEdgeBudget
  entropyTail :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0

/-- Corrected actual-`N` combined-product certificate for the small regime.

The small analytic field uses the rational tangent-line square-root surrogate
`positiveSmallXYProductTangentBound`; the separate `smallTangentEdge` field is
the finite comparison from that actual-`N` target to the executable upper-edge
majorant.  This preserves the monotonic slack of the paper's
`exp(1.139 sqrt N)/N` term, unlike the coarser `ceilSqrt N` target below. -/
structure PositiveSaddleTangentProductBudgetCertificate : Prop where
  smallXYTangent :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N → 0 < Bq N k →
        Xnorm N k * Ynorm N (posJ a k) ≤ positiveSmallXYProductTangentBound a N k
  smallTangentEdge :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        positiveSmallTangentExpEdgeGap a N k
  temperedXY :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k → 0 < Bq N k →
        Xnorm N k * Ynorm N (posJ a k) ≤ positiveTemperedXYProductBound a N k
  soloY :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget
  edgeBudget :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeMajorantSum a ≤ positiveEdgeBudget
  entropyTail :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0

/-- Row-checked version of the corrected tangent certificate.

This is meant for generated finite certificates: each generated row theorem can
prove the two booleans `checkPositiveSmallTangentExpEdgeRow a = true` and
`checkPositiveEdgeBudgetRow a = true`, while the analytic fields remain stated
as mathematical inequalities. -/
structure PositiveSaddleTangentCheckedRowsCertificate : Prop where
  smallXYTangent :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N → 0 < Bq N k →
        Xnorm N k * Ynorm N (posJ a k) ≤ positiveSmallXYProductTangentBound a N k
  smallTangentEdgeRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveSmallTangentExpEdgeRow a = true
  temperedXY :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k → 0 < Bq N k →
        Xnorm N k * Ynorm N (posJ a k) ≤ positiveTemperedXYProductBound a N k
  soloY :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget
  edgeBudgetRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveEdgeBudgetRow a = true
  entropyTail :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0

/-- Row-checked tangent certificate with the solo `Y_a` term also discharged
by the explicit `Eplus`/`Gcomp` finite row check.

The remaining analytic fields are the small and tempered `X*Y` saddle product
bounds and the entropy tail; all finite positive-envelope budget checks are
now represented by row booleans. -/
structure PositiveSaddleTangentFullyCheckedRowsCertificate : Prop where
  smallXYTangent :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N → 0 < Bq N k →
        Xnorm N k * Ynorm N (posJ a k) ≤ positiveSmallXYProductTangentBound a N k
  smallTangentEdgeRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveSmallTangentExpEdgeRow a = true
  temperedXY :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k → 0 < Bq N k →
        Xnorm N k * Ynorm N (posJ a k) ≤ positiveTemperedXYProductBound a N k
  soloGcompRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveSoloGcompRow a = true
  edgeBudgetRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveEdgeBudgetRow a = true
  entropyTail :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0

/-- `\overline B`/`Xplus` version of the row-checked tangent certificate.

The TeX proof estimates the positive side through the absolute majorant
`\overline B_k(N) = [X^k]C(X)^N`.  This interface records that route
explicitly: the remaining saddle product fields are stated for
`XplusNorm * Ynorm`, and Lean converts them back to the existing `Xnorm`
certificate using `Xnorm_mul_Ynorm_le_of_Xplus_mul_Ynorm`. -/
structure PositiveSaddleXplusTangentFullyCheckedRowsCertificate : Prop where
  smallXplusTangent :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        XplusNorm N k * Ynorm N (posJ a k)
          ≤ positiveSmallXYProductTangentBound a N k
  smallTangentEdgeRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveSmallTangentExpEdgeRow a = true
  temperedXplus :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k →
        XplusNorm N k * Ynorm N (posJ a k)
          ≤ positiveTemperedXYProductBound a N k
  soloGcompRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveSoloGcompRow a = true
  edgeBudgetRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveEdgeBudgetRow a = true
  entropyTail :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0

/-- Fully row-checked `Xplus`/`Gcomp` positive-saddle interface.

Compared with `PositiveSaddleXplusTangentFullyCheckedRowsCertificate`, the
small and tempered saddle-product fields are replaced by executable row
checks for the explicit `positiveXplusYProductGcompBound`.  The only
non-finite field left is the entropy tail for `a > 2000`. -/
structure PositiveSaddleXplusGcompTangentFullyCheckedRowsCertificate : Prop where
  smallXplusGcompRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveSmallXplusYProductGcompRow a = true
  temperedXplusGcompRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveTemperedXplusYProductGcompRow a = true
  smallTangentEdgeRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveSmallTangentExpEdgeRow a = true
  soloGcompRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveSoloGcompRow a = true
  edgeBudgetRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveEdgeBudgetRow a = true
  entropyTail :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0

/-- Fully row-checked finite-window certificate plus the first-term/ratio
geometric entropy-tail certificate for `a > 2000`.

This is the most concrete current end-to-end interface: all finite-window
positive-saddle obligations are executable row checks, and the remaining
large-`a` tail is the rational entropy-shadow geometric certificate. -/
structure PositiveSaddleXplusGcompTangentRowsEntropyGeometricCertificate
    (smallExp temperedExp : Nat → Nat → ℚ)
    (smallRatio temperedRatio : Nat → ℚ) : Prop where
  smallXplusGcompRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveSmallXplusYProductGcompRow a = true
  temperedXplusGcompRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveTemperedXplusYProductGcompRow a = true
  smallTangentEdgeRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveSmallTangentExpEdgeRow a = true
  soloGcompRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveSoloGcompRow a = true
  edgeBudgetRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveEdgeBudgetRow a = true
  entropyGeometric :
    PositiveSaddleEntropyShadowExpGeometricBudgetCertificate
      smallExp temperedExp smallRatio temperedRatio

/-- Row-checked finite-window certificate plus the reserve form of the
geometric entropy-shadow tail. -/
structure PositiveSaddleXplusGcompTangentRowsEntropyGeometricReserveCertificate
    (smallExp temperedExp : Nat → Nat → ℚ)
    (smallRatio temperedRatio : Nat → ℚ) : Prop where
  smallXplusGcompRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveSmallXplusYProductGcompRow a = true
  temperedXplusGcompRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveTemperedXplusYProductGcompRow a = true
  smallTangentEdgeRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveSmallTangentExpEdgeRow a = true
  soloGcompRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveSoloGcompRow a = true
  edgeBudgetRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveEdgeBudgetRow a = true
  entropyGeometricReserve :
    PositiveSaddleEntropyShadowExpGeometricReserveCertificate
      smallExp temperedExp smallRatio temperedRatio

/-- Row-checked finite-window certificate plus quotient-ratio reserve checks for
the large-`a` entropy-shadow tail. -/
structure PositiveSaddleXplusGcompTangentRowsEntropyQuotientReserveCertificate
    (smallExp temperedExp : Nat → Nat → ℚ)
    (smallRatio temperedRatio : Nat → ℚ) : Prop where
  smallXplusGcompRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveSmallXplusYProductGcompRow a = true
  temperedXplusGcompRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveTemperedXplusYProductGcompRow a = true
  smallTangentEdgeRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveSmallTangentExpEdgeRow a = true
  soloGcompRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveSoloGcompRow a = true
  edgeBudgetRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveEdgeBudgetRow a = true
  entropyQuotientReserve :
    PositiveSaddleEntropyShadowExpQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio

/-- Row-checked finite-window certificate plus raw-base quotient reserve checks
for the large-`a` entropy-shadow tail. -/
structure PositiveSaddleXplusGcompTangentRowsEntropyRawQuotientReserveCertificate
    (smallExp temperedExp : Nat → Nat → ℚ)
    (smallRatio temperedRatio : Nat → ℚ) : Prop where
  smallXplusGcompRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveSmallXplusYProductGcompRow a = true
  temperedXplusGcompRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveTemperedXplusYProductGcompRow a = true
  smallTangentEdgeRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveSmallTangentExpEdgeRow a = true
  soloGcompRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveSoloGcompRow a = true
  edgeBudgetRows :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      checkPositiveEdgeBudgetRow a = true
  entropyRawQuotientReserve :
    PositiveSaddleEntropyShadowExpRawQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio

/-- Fully range-checked `Xplus`/`Gcomp` positive-saddle interface.

This is the range-check analogue of
`PositiveSaddleXplusGcompTangentFullyCheckedRowsCertificate`: the finite window
`401 ≤ a ≤ 2000` is represented by five executable range booleans, while the
non-finite `a > 2000` entropy tail remains a mathematical field. -/
structure PositiveSaddleXplusGcompTangentFullyCheckedRangeCertificate : Prop where
  smallXplusGcompRange :
    checkPositiveSmallXplusYProductGcompRange 401 1600 = true
  temperedXplusGcompRange :
    checkPositiveTemperedXplusYProductGcompRange 401 1600 = true
  smallTangentEdgeRange :
    checkPositiveSmallTangentExpEdgeRange 401 1600 = true
  soloGcompRange :
    checkPositiveSoloGcompRange 401 1600 = true
  edgeBudgetRange :
    checkPositiveEdgeBudgetRange 401 1600 = true
  entropyTail :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0

/-- Range-checked finite-window certificate plus the geometric entropy-tail
certificate for `a > 2000`. -/
structure PositiveSaddleXplusGcompTangentRangeEntropyGeometricCertificate
    (smallExp temperedExp : Nat → Nat → ℚ)
    (smallRatio temperedRatio : Nat → ℚ) : Prop where
  smallXplusGcompRange :
    checkPositiveSmallXplusYProductGcompRange 401 1600 = true
  temperedXplusGcompRange :
    checkPositiveTemperedXplusYProductGcompRange 401 1600 = true
  smallTangentEdgeRange :
    checkPositiveSmallTangentExpEdgeRange 401 1600 = true
  soloGcompRange :
    checkPositiveSoloGcompRange 401 1600 = true
  edgeBudgetRange :
    checkPositiveEdgeBudgetRange 401 1600 = true
  entropyGeometric :
    PositiveSaddleEntropyShadowExpGeometricBudgetCertificate
      smallExp temperedExp smallRatio temperedRatio

/-- Range-checked finite-window certificate plus the reserve form of the
geometric entropy-tail certificate. -/
structure PositiveSaddleXplusGcompTangentRangeEntropyGeometricReserveCertificate
    (smallExp temperedExp : Nat → Nat → ℚ)
    (smallRatio temperedRatio : Nat → ℚ) : Prop where
  smallXplusGcompRange :
    checkPositiveSmallXplusYProductGcompRange 401 1600 = true
  temperedXplusGcompRange :
    checkPositiveTemperedXplusYProductGcompRange 401 1600 = true
  smallTangentEdgeRange :
    checkPositiveSmallTangentExpEdgeRange 401 1600 = true
  soloGcompRange :
    checkPositiveSoloGcompRange 401 1600 = true
  edgeBudgetRange :
    checkPositiveEdgeBudgetRange 401 1600 = true
  entropyGeometricReserve :
    PositiveSaddleEntropyShadowExpGeometricReserveCertificate
      smallExp temperedExp smallRatio temperedRatio

/-- Range-checked finite-window certificate plus quotient-ratio reserve checks
for the large-`a` entropy-shadow tail. -/
structure PositiveSaddleXplusGcompTangentRangeEntropyQuotientReserveCertificate
    (smallExp temperedExp : Nat → Nat → ℚ)
    (smallRatio temperedRatio : Nat → ℚ) : Prop where
  smallXplusGcompRange :
    checkPositiveSmallXplusYProductGcompRange 401 1600 = true
  temperedXplusGcompRange :
    checkPositiveTemperedXplusYProductGcompRange 401 1600 = true
  smallTangentEdgeRange :
    checkPositiveSmallTangentExpEdgeRange 401 1600 = true
  soloGcompRange :
    checkPositiveSoloGcompRange 401 1600 = true
  edgeBudgetRange :
    checkPositiveEdgeBudgetRange 401 1600 = true
  entropyQuotientReserve :
    PositiveSaddleEntropyShadowExpQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio

/-- Range-checked finite-window certificate plus raw-base quotient reserve
checks for the large-`a` entropy-shadow tail. -/
structure PositiveSaddleXplusGcompTangentRangeEntropyRawQuotientReserveCertificate
    (smallExp temperedExp : Nat → Nat → ℚ)
    (smallRatio temperedRatio : Nat → ℚ) : Prop where
  smallXplusGcompRange :
    checkPositiveSmallXplusYProductGcompRange 401 1600 = true
  temperedXplusGcompRange :
    checkPositiveTemperedXplusYProductGcompRange 401 1600 = true
  smallTangentEdgeRange :
    checkPositiveSmallTangentExpEdgeRange 401 1600 = true
  soloGcompRange :
    checkPositiveSoloGcompRange 401 1600 = true
  edgeBudgetRange :
    checkPositiveEdgeBudgetRange 401 1600 = true
  entropyRawQuotientReserve :
    PositiveSaddleEntropyShadowExpRawQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio

/-- Generated finite-window chunks for the most concrete §6 finite path.

Each chunk is a half-open interval `(lo, len)`.  The `cover` field records
that the chunk list covers every `a` in `401 ≤ a ≤ 2000`; the five boolean
fields can then be proved independently for each chunk, with chunk sizes
chosen to match `native_decide` performance. -/
structure PositiveSaddleXplusGcompTangentFiniteWindowChunks
    (chunks : List (Nat × Nat)) : Prop where
  cover : PositiveSaddleFiniteWindowChunkCover chunks
  smallXplusGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ chunks →
      checkPositiveSmallXplusYProductGcompRange chunk.1 chunk.2 = true
  temperedXplusGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ chunks →
      checkPositiveTemperedXplusYProductGcompRange chunk.1 chunk.2 = true
  smallTangentEdgeChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ chunks →
      checkPositiveSmallTangentExpEdgeRange chunk.1 chunk.2 = true
  soloGcompChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ chunks →
      checkPositiveSoloGcompRange chunk.1 chunk.2 = true
  edgeBudgetChunks :
    ∀ {chunk : Nat × Nat}, chunk ∈ chunks →
      checkPositiveEdgeBudgetRange chunk.1 chunk.2 = true

/-- Chunked finite-window certificate plus a direct entropy-tail field. -/
structure PositiveSaddleXplusGcompTangentChunkedRangeCertificate
    (chunks : List (Nat × Nat)) : Prop where
  finiteChunks :
    PositiveSaddleXplusGcompTangentFiniteWindowChunks chunks
  entropyTail :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0

/-- Chunked finite-window certificate plus the geometric entropy-tail
certificate for `a > 2000`. -/
structure PositiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricCertificate
    (chunks : List (Nat × Nat))
    (smallExp temperedExp : Nat → Nat → ℚ)
    (smallRatio temperedRatio : Nat → ℚ) : Prop where
  finiteChunks :
    PositiveSaddleXplusGcompTangentFiniteWindowChunks chunks
  entropyGeometric :
    PositiveSaddleEntropyShadowExpGeometricBudgetCertificate
      smallExp temperedExp smallRatio temperedRatio

/-- Chunked finite-window certificate plus the reserve form of the geometric
entropy-tail certificate. -/
structure PositiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricReserveCertificate
    (chunks : List (Nat × Nat))
    (smallExp temperedExp : Nat → Nat → ℚ)
    (smallRatio temperedRatio : Nat → ℚ) : Prop where
  finiteChunks :
    PositiveSaddleXplusGcompTangentFiniteWindowChunks chunks
  entropyGeometricReserve :
    PositiveSaddleEntropyShadowExpGeometricReserveCertificate
      smallExp temperedExp smallRatio temperedRatio

/-- Chunked finite-window certificate plus quotient-ratio reserve checks for
the large-`a` entropy-shadow tail. -/
structure PositiveSaddleXplusGcompTangentChunkedRangeEntropyQuotientReserveCertificate
    (chunks : List (Nat × Nat))
    (smallExp temperedExp : Nat → Nat → ℚ)
    (smallRatio temperedRatio : Nat → ℚ) : Prop where
  finiteChunks :
    PositiveSaddleXplusGcompTangentFiniteWindowChunks chunks
  entropyQuotientReserve :
    PositiveSaddleEntropyShadowExpQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio

/-- Chunked finite-window certificate plus raw-base quotient reserve checks for
the large-`a` entropy-shadow tail. -/
structure PositiveSaddleXplusGcompTangentChunkedRangeEntropyRawQuotientReserveCertificate
    (chunks : List (Nat × Nat))
    (smallExp temperedExp : Nat → Nat → ℚ)
    (smallRatio temperedRatio : Nat → ℚ) : Prop where
  finiteChunks :
    PositiveSaddleXplusGcompTangentFiniteWindowChunks chunks
  entropyRawQuotientReserve :
    PositiveSaddleEntropyShadowExpRawQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio

/-- Actual-`N` combined-product version of the budgeted §6 interface.  The
small-regime analytic estimate targets `positiveSmallXYProductAtBound`, and
the separate `smallEdge` field records the finite/monotone replacement by the
upper-edge bound used in the executable scan.

Audit note: with the current rational surrogate
`positiveSmallExponentAt`, which uses `ceilSqrt N`, this replacement is too
coarse on the top ceiling-square-root plateau.  The theorem
`positiveSmallExpEdgeGapAtCeil_topPlateau_not` records a concrete failing
finite cell.  The corrected actual-`N` interface is
`PositiveSaddleTangentProductBudgetCertificate`. -/
structure PositiveSaddleAtProductBudgetCertificate : Prop where
  smallXYAt :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N → 0 < Bq N k →
        Xnorm N k * Ynorm N (posJ a k) ≤ positiveSmallXYProductAtBound a N k
  smallEdge :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N → 0 < Bq N k →
        positiveSmallXYProductAtBound a N k ≤ positiveSmallXYProductBound a N k
  temperedXY :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k → 0 < Bq N k →
        Xnorm N k * Ynorm N (posJ a k) ≤ positiveTemperedXYProductBound a N k
  soloY :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget
  edgeBudget :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeMajorantSum a ≤ positiveEdgeBudget
  entropyTail :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0

/-- Audit/deprecated actual-`N` certificate with the small upper-edge
replacement reduced to the cancellable exponential-gap inequality
`positiveSmallExpEdgeGap`.

This records the natural but too-coarse `ceilSqrt N` attempt.  The concrete
counterexample `positiveSmallExpEdgeGapAtCeil_topPlateau_not` shows why this
is not the final certificate path; use
`PositiveSaddleTangentProductBudgetCertificate` instead. -/
structure PositiveSaddleAtExpBudgetCertificate : Prop where
  smallXYAt :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N → 0 < Bq N k →
        Xnorm N k * Ynorm N (posJ a k) ≤ positiveSmallXYProductAtBound a N k
  smallExpEdge :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N →
        positiveSmallExpEdgeGap a N k
  temperedXY :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k → 0 < Bq N k →
        Xnorm N k * Ynorm N (posJ a k) ≤ positiveTemperedXYProductBound a N k
  soloY :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget
  edgeBudget :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeMajorantSum a ≤ positiveEdgeBudget
  entropyTail :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0

/-- Audit/deprecated plateau-anchor version of the `ceilSqrt N`
positive-saddle certificate.

The `smallExpEdgeAnchor` field ranges over the possible values
`s = ceilSqrt N`, not over every `N` in the rectangle.  That reduction is
sound as a conditional theorem, but the associated finite condition is false
for the current `ceilSqrt` surrogate on the top plateau; see
`positiveSmallExpEdgeGapAtCeil_topPlateau_not`. -/
structure PositiveSaddleAtAnchorBudgetCertificate : Prop where
  smallXYAt :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N → 0 < Bq N k →
        Xnorm N k * Ynorm N (posJ a k) ≤ positiveSmallXYProductAtBound a N k
  smallExpEdgeAnchor :
    ∀ {a s k : Nat}, 401 ≤ a → a ≤ 2000 →
      s ∈ positiveSmallCeilRange a → k ∈ positiveKRange a → k ≤ s →
        positiveSmallExpEdgeGapAtCeil a s k
  temperedXY :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k → 0 < Bq N k →
        Xnorm N k * Ynorm N (posJ a k) ≤ positiveTemperedXYProductBound a N k
  soloY :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      positiveDyadicDecay a / 2 * Ynorm N a ≤ positiveSoloBudget
  edgeBudget :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEdgeMajorantSum a ≤ positiveEdgeBudget
  entropyTail :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0

theorem PositiveSaddleScalarCertificate.toFactorCertificate
    {soloBound : Nat → ℚ} (cert : PositiveSaddleScalarCertificate soloBound) :
    PositiveSaddleFactorCertificate soloBound where
  smallFactor := by
    intro a N k ha ha2000 hrect hk hsmall hB
    exact (cert.smallScalar ha ha2000 hrect hk hsmall hB).trans
      (positiveSmallScalarProductBound_le_majorant ha ha2000 hk)
  temperedFactor := by
    intro a N k ha ha2000 hrect hk htemp hB
    exact (cert.temperedScalar ha ha2000 hrect hk htemp hB).trans
      (positiveTemperedScalarProductBound_le_majorant ha ha2000 hrect hk
        (temperedRegime_of_rectangle hrect htemp))
  soloY := cert.soloY
  envelope := cert.envelope
  entropyTail := cert.entropyTail

theorem PositiveSaddleScalarBudgetCertificate.toScalarCertificate
    (cert : PositiveSaddleScalarBudgetCertificate) :
    PositiveSaddleScalarCertificate (fun _ => positiveSoloBudget) where
  smallScalar := cert.smallScalar
  temperedScalar := cert.temperedScalar
  soloY := cert.soloY
  envelope := by
    intro a ha ha2000
    exact positiveEnvelopeBound_le_target_of_edgeBudget
      (cert.edgeBudget ha ha2000)
  entropyTail := cert.entropyTail

theorem PositiveSaddleCombinedProductBudgetCertificate.toScalarBudgetCertificate
    (cert : PositiveSaddleCombinedProductBudgetCertificate) :
    PositiveSaddleScalarBudgetCertificate where
  smallScalar := by
    intro a N k ha ha2000 hrect hk hsmall hB
    exact positiveFactorizedRawTerm_le_smallScalar_of_XYProduct
      (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect) (by omega : 2 ≤ a)
      hk hB (cert.smallXY ha ha2000 hrect hk hsmall hB)
  temperedScalar := by
    intro a N k ha ha2000 hrect hk htemp hB
    exact positiveFactorizedRawTerm_le_temperedScalar_of_XYProduct
      (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect) (by omega : 2 ≤ a)
      hk hB (cert.temperedXY ha ha2000 hrect hk htemp hB)
  soloY := cert.soloY
  edgeBudget := cert.edgeBudget
  entropyTail := cert.entropyTail

theorem PositiveSaddleTangentProductBudgetCertificate.toCombinedProductBudgetCertificate
    (cert : PositiveSaddleTangentProductBudgetCertificate) :
    PositiveSaddleCombinedProductBudgetCertificate where
  smallXY := by
    intro a N k ha ha2000 hrect hk hsmall hB
    exact (cert.smallXYTangent ha ha2000 hrect hk hsmall hB).trans
      (positiveSmallXYProductTangentBound_le_bound_of_expGap
        (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect) (by omega : 1 ≤ a)
        (cert.smallTangentEdge ha ha2000 hrect hk hsmall))
  temperedXY := cert.temperedXY
  soloY := cert.soloY
  edgeBudget := cert.edgeBudget
  entropyTail := cert.entropyTail

theorem PositiveSaddleTangentCheckedRowsCertificate.toTangentProductBudgetCertificate
    (cert : PositiveSaddleTangentCheckedRowsCertificate) :
    PositiveSaddleTangentProductBudgetCertificate where
  smallXYTangent := cert.smallXYTangent
  smallTangentEdge := by
    intro a N k ha ha2000 hrect hk hsmall
    exact positiveSmallTangentExpEdgeGap_of_checkRow
      (cert.smallTangentEdgeRows ha ha2000) hrect hk hsmall
  temperedXY := cert.temperedXY
  soloY := cert.soloY
  edgeBudget := by
    intro a ha ha2000
    exact positiveEdgeBudget_of_checkPositiveEdgeBudgetRow
      (cert.edgeBudgetRows ha ha2000)
  entropyTail := cert.entropyTail

theorem PositiveSaddleTangentFullyCheckedRowsCertificate.toTangentCheckedRowsCertificate
    (cert : PositiveSaddleTangentFullyCheckedRowsCertificate) :
    PositiveSaddleTangentCheckedRowsCertificate where
  smallXYTangent := cert.smallXYTangent
  smallTangentEdgeRows := cert.smallTangentEdgeRows
  temperedXY := cert.temperedXY
  soloY := by
    intro a N ha ha2000 hrect
    exact dyadic_Ynorm_le_positiveSoloBudget_of_checkPositiveSoloGcompRow
      (cert.soloGcompRows ha ha2000) ha hrect
  edgeBudgetRows := cert.edgeBudgetRows
  entropyTail := cert.entropyTail

theorem PositiveSaddleXplusTangentFullyCheckedRowsCertificate.toTangentFullyCheckedRowsCertificate
    (cert : PositiveSaddleXplusTangentFullyCheckedRowsCertificate) :
    PositiveSaddleTangentFullyCheckedRowsCertificate where
  smallXYTangent := by
    intro a N k ha ha2000 hrect hk hsmall _hB
    exact Xnorm_mul_Ynorm_le_of_Xplus_mul_Ynorm
      (cert.smallXplusTangent ha ha2000 hrect hk hsmall)
  smallTangentEdgeRows := cert.smallTangentEdgeRows
  temperedXY := by
    intro a N k ha ha2000 hrect hk htemp _hB
    exact Xnorm_mul_Ynorm_le_of_Xplus_mul_Ynorm
      (cert.temperedXplus ha ha2000 hrect hk htemp)
  soloGcompRows := cert.soloGcompRows
  edgeBudgetRows := cert.edgeBudgetRows
  entropyTail := cert.entropyTail

theorem PositiveSaddleXplusGcompTangentFullyCheckedRowsCertificate.toXplusTangentFullyCheckedRowsCertificate
    (cert : PositiveSaddleXplusGcompTangentFullyCheckedRowsCertificate) :
    PositiveSaddleXplusTangentFullyCheckedRowsCertificate where
  smallXplusTangent := by
    intro a N k ha ha2000 hrect hk hsmall
    exact (XplusYnorm_le_positiveXplusYProductGcompBound a N k).trans
      (positiveSmallXplusYProductGcompBound_of_checkRow
        (cert.smallXplusGcompRows ha ha2000) hrect hk hsmall)
  smallTangentEdgeRows := cert.smallTangentEdgeRows
  temperedXplus := by
    intro a N k ha ha2000 hrect hk htempered
    exact (XplusYnorm_le_positiveXplusYProductGcompBound a N k).trans
      (positiveTemperedXplusYProductGcompBound_of_checkRow
        (cert.temperedXplusGcompRows ha ha2000) hrect hk htempered)
  soloGcompRows := cert.soloGcompRows
  edgeBudgetRows := cert.edgeBudgetRows
  entropyTail := cert.entropyTail

theorem PositiveSaddleXplusGcompTangentRowsEntropyGeometricCertificate.toXplusGcompTangentFullyCheckedRowsCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRowsEntropyGeometricCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentFullyCheckedRowsCertificate where
  smallXplusGcompRows := cert.smallXplusGcompRows
  temperedXplusGcompRows := cert.temperedXplusGcompRows
  smallTangentEdgeRows := cert.smallTangentEdgeRows
  soloGcompRows := cert.soloGcompRows
  edgeBudgetRows := cert.edgeBudgetRows
  entropyTail := cert.entropyGeometric.entropyTail

theorem PositiveSaddleXplusGcompTangentRowsEntropyGeometricReserveCertificate.toRowsEntropyGeometricCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRowsEntropyGeometricReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentRowsEntropyGeometricCertificate
      smallExp temperedExp smallRatio temperedRatio where
  smallXplusGcompRows := cert.smallXplusGcompRows
  temperedXplusGcompRows := cert.temperedXplusGcompRows
  smallTangentEdgeRows := cert.smallTangentEdgeRows
  soloGcompRows := cert.soloGcompRows
  edgeBudgetRows := cert.edgeBudgetRows
  entropyGeometric :=
    cert.entropyGeometricReserve.toGeometricBudgetCertificate

theorem PositiveSaddleXplusGcompTangentRowsEntropyGeometricReserveCertificate.toXplusGcompTangentFullyCheckedRowsCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRowsEntropyGeometricReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentFullyCheckedRowsCertificate :=
  cert.toRowsEntropyGeometricCertificate.toXplusGcompTangentFullyCheckedRowsCertificate

theorem PositiveSaddleXplusGcompTangentRowsEntropyQuotientReserveCertificate.toRowsEntropyGeometricReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRowsEntropyQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentRowsEntropyGeometricReserveCertificate
      smallExp temperedExp smallRatio temperedRatio where
  smallXplusGcompRows := cert.smallXplusGcompRows
  temperedXplusGcompRows := cert.temperedXplusGcompRows
  smallTangentEdgeRows := cert.smallTangentEdgeRows
  soloGcompRows := cert.soloGcompRows
  edgeBudgetRows := cert.edgeBudgetRows
  entropyGeometricReserve :=
    cert.entropyQuotientReserve.toGeometricReserveCertificate

theorem PositiveSaddleXplusGcompTangentRowsEntropyQuotientReserveCertificate.toRowsEntropyGeometricCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRowsEntropyQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentRowsEntropyGeometricCertificate
      smallExp temperedExp smallRatio temperedRatio :=
  cert.toRowsEntropyGeometricReserveCertificate.toRowsEntropyGeometricCertificate

theorem PositiveSaddleXplusGcompTangentRowsEntropyQuotientReserveCertificate.toXplusGcompTangentFullyCheckedRowsCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRowsEntropyQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentFullyCheckedRowsCertificate :=
  cert.toRowsEntropyGeometricCertificate.toXplusGcompTangentFullyCheckedRowsCertificate

theorem PositiveSaddleXplusGcompTangentRowsEntropyRawQuotientReserveCertificate.toRowsEntropyQuotientReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRowsEntropyRawQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentRowsEntropyQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio where
  smallXplusGcompRows := cert.smallXplusGcompRows
  temperedXplusGcompRows := cert.temperedXplusGcompRows
  smallTangentEdgeRows := cert.smallTangentEdgeRows
  soloGcompRows := cert.soloGcompRows
  edgeBudgetRows := cert.edgeBudgetRows
  entropyQuotientReserve :=
    cert.entropyRawQuotientReserve.toQuotientReserveCertificate

theorem PositiveSaddleXplusGcompTangentRowsEntropyRawQuotientReserveCertificate.toRowsEntropyGeometricCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRowsEntropyRawQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentRowsEntropyGeometricCertificate
      smallExp temperedExp smallRatio temperedRatio :=
  cert.toRowsEntropyQuotientReserveCertificate.toRowsEntropyGeometricCertificate

theorem PositiveSaddleXplusGcompTangentRowsEntropyRawQuotientReserveCertificate.toXplusGcompTangentFullyCheckedRowsCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRowsEntropyRawQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentFullyCheckedRowsCertificate :=
  cert.toRowsEntropyGeometricCertificate.toXplusGcompTangentFullyCheckedRowsCertificate

theorem PositiveSaddleXplusGcompTangentFullyCheckedRangeCertificate.toXplusGcompTangentFullyCheckedRowsCertificate
    (cert : PositiveSaddleXplusGcompTangentFullyCheckedRangeCertificate) :
    PositiveSaddleXplusGcompTangentFullyCheckedRowsCertificate where
  smallXplusGcompRows := by
    intro a ha h2000
    exact checkPositiveSmallXplusYProductGcompRow_of_checkRange
      cert.smallXplusGcompRange ha (by omega)
  temperedXplusGcompRows := by
    intro a ha h2000
    exact checkPositiveTemperedXplusYProductGcompRow_of_checkRange
      cert.temperedXplusGcompRange ha (by omega)
  smallTangentEdgeRows := by
    intro a ha h2000
    exact checkPositiveSmallTangentExpEdgeRow_of_checkRange
      cert.smallTangentEdgeRange ha (by omega)
  soloGcompRows := by
    intro a ha h2000
    exact checkPositiveSoloGcompRow_of_checkRange
      cert.soloGcompRange ha (by omega)
  edgeBudgetRows := by
    intro a ha h2000
    exact checkPositiveEdgeBudgetRow_of_checkPositiveEdgeBudgetRange
      cert.edgeBudgetRange ha (by omega)
  entropyTail := cert.entropyTail

theorem PositiveSaddleXplusGcompTangentRangeEntropyGeometricCertificate.toRowsEntropyGeometricCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRangeEntropyGeometricCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentRowsEntropyGeometricCertificate
      smallExp temperedExp smallRatio temperedRatio where
  smallXplusGcompRows := by
    intro a ha h2000
    exact checkPositiveSmallXplusYProductGcompRow_of_checkRange
      cert.smallXplusGcompRange ha (by omega)
  temperedXplusGcompRows := by
    intro a ha h2000
    exact checkPositiveTemperedXplusYProductGcompRow_of_checkRange
      cert.temperedXplusGcompRange ha (by omega)
  smallTangentEdgeRows := by
    intro a ha h2000
    exact checkPositiveSmallTangentExpEdgeRow_of_checkRange
      cert.smallTangentEdgeRange ha (by omega)
  soloGcompRows := by
    intro a ha h2000
    exact checkPositiveSoloGcompRow_of_checkRange
      cert.soloGcompRange ha (by omega)
  edgeBudgetRows := by
    intro a ha h2000
    exact checkPositiveEdgeBudgetRow_of_checkPositiveEdgeBudgetRange
      cert.edgeBudgetRange ha (by omega)
  entropyGeometric := cert.entropyGeometric

theorem PositiveSaddleXplusGcompTangentRangeEntropyGeometricCertificate.toXplusGcompTangentFullyCheckedRowsCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRangeEntropyGeometricCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentFullyCheckedRowsCertificate :=
  cert.toRowsEntropyGeometricCertificate.toXplusGcompTangentFullyCheckedRowsCertificate

theorem PositiveSaddleXplusGcompTangentRangeEntropyGeometricReserveCertificate.toRangeEntropyGeometricCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRangeEntropyGeometricReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentRangeEntropyGeometricCertificate
      smallExp temperedExp smallRatio temperedRatio where
  smallXplusGcompRange := cert.smallXplusGcompRange
  temperedXplusGcompRange := cert.temperedXplusGcompRange
  smallTangentEdgeRange := cert.smallTangentEdgeRange
  soloGcompRange := cert.soloGcompRange
  edgeBudgetRange := cert.edgeBudgetRange
  entropyGeometric :=
    cert.entropyGeometricReserve.toGeometricBudgetCertificate

theorem PositiveSaddleXplusGcompTangentRangeEntropyGeometricReserveCertificate.toRowsEntropyGeometricCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRangeEntropyGeometricReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentRowsEntropyGeometricCertificate
      smallExp temperedExp smallRatio temperedRatio :=
  cert.toRangeEntropyGeometricCertificate.toRowsEntropyGeometricCertificate

theorem PositiveSaddleXplusGcompTangentRangeEntropyGeometricReserveCertificate.toXplusGcompTangentFullyCheckedRowsCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRangeEntropyGeometricReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentFullyCheckedRowsCertificate :=
  cert.toRowsEntropyGeometricCertificate.toXplusGcompTangentFullyCheckedRowsCertificate

theorem PositiveSaddleXplusGcompTangentRangeEntropyQuotientReserveCertificate.toRangeEntropyGeometricReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRangeEntropyQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentRangeEntropyGeometricReserveCertificate
      smallExp temperedExp smallRatio temperedRatio where
  smallXplusGcompRange := cert.smallXplusGcompRange
  temperedXplusGcompRange := cert.temperedXplusGcompRange
  smallTangentEdgeRange := cert.smallTangentEdgeRange
  soloGcompRange := cert.soloGcompRange
  edgeBudgetRange := cert.edgeBudgetRange
  entropyGeometricReserve :=
    cert.entropyQuotientReserve.toGeometricReserveCertificate

theorem PositiveSaddleXplusGcompTangentRangeEntropyQuotientReserveCertificate.toRangeEntropyGeometricCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRangeEntropyQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentRangeEntropyGeometricCertificate
      smallExp temperedExp smallRatio temperedRatio :=
  cert.toRangeEntropyGeometricReserveCertificate.toRangeEntropyGeometricCertificate

theorem PositiveSaddleXplusGcompTangentRangeEntropyQuotientReserveCertificate.toRowsEntropyGeometricCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRangeEntropyQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentRowsEntropyGeometricCertificate
      smallExp temperedExp smallRatio temperedRatio :=
  cert.toRangeEntropyGeometricCertificate.toRowsEntropyGeometricCertificate

theorem PositiveSaddleXplusGcompTangentRangeEntropyQuotientReserveCertificate.toXplusGcompTangentFullyCheckedRowsCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRangeEntropyQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentFullyCheckedRowsCertificate :=
  cert.toRowsEntropyGeometricCertificate.toXplusGcompTangentFullyCheckedRowsCertificate

theorem PositiveSaddleXplusGcompTangentRangeEntropyRawQuotientReserveCertificate.toRangeEntropyQuotientReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRangeEntropyRawQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentRangeEntropyQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio where
  smallXplusGcompRange := cert.smallXplusGcompRange
  temperedXplusGcompRange := cert.temperedXplusGcompRange
  smallTangentEdgeRange := cert.smallTangentEdgeRange
  soloGcompRange := cert.soloGcompRange
  edgeBudgetRange := cert.edgeBudgetRange
  entropyQuotientReserve :=
    cert.entropyRawQuotientReserve.toQuotientReserveCertificate

theorem PositiveSaddleXplusGcompTangentRangeEntropyRawQuotientReserveCertificate.toRowsEntropyGeometricCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRangeEntropyRawQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentRowsEntropyGeometricCertificate
      smallExp temperedExp smallRatio temperedRatio :=
  cert.toRangeEntropyQuotientReserveCertificate.toRowsEntropyGeometricCertificate

theorem PositiveSaddleXplusGcompTangentRangeEntropyRawQuotientReserveCertificate.toXplusGcompTangentFullyCheckedRowsCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRangeEntropyRawQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentFullyCheckedRowsCertificate :=
  cert.toRowsEntropyGeometricCertificate.toXplusGcompTangentFullyCheckedRowsCertificate

theorem PositiveSaddleXplusGcompTangentFiniteWindowChunks.toXplusGcompTangentFullyCheckedRowsCertificate
    {chunks : List (Nat × Nat)}
    (finite : PositiveSaddleXplusGcompTangentFiniteWindowChunks chunks)
    (entropyTail :
      ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0) :
    PositiveSaddleXplusGcompTangentFullyCheckedRowsCertificate where
  smallXplusGcompRows := by
    intro a ha h2000
    exact checkPositiveSmallXplusYProductGcompRow_of_checkRangeChunks
      finite.smallXplusGcompChunks (finite.cover (a := a) ha h2000)
  temperedXplusGcompRows := by
    intro a ha h2000
    exact checkPositiveTemperedXplusYProductGcompRow_of_checkRangeChunks
      finite.temperedXplusGcompChunks (finite.cover (a := a) ha h2000)
  smallTangentEdgeRows := by
    intro a ha h2000
    exact checkPositiveSmallTangentExpEdgeRow_of_checkRangeChunks
      finite.smallTangentEdgeChunks (finite.cover (a := a) ha h2000)
  soloGcompRows := by
    intro a ha h2000
    exact checkPositiveSoloGcompRow_of_checkRangeChunks
      finite.soloGcompChunks (finite.cover (a := a) ha h2000)
  edgeBudgetRows := by
    intro a ha h2000
    exact checkPositiveEdgeBudgetRow_of_checkPositiveEdgeBudgetRangeChunks
      finite.edgeBudgetChunks (finite.cover (a := a) ha h2000)
  entropyTail := entropyTail

theorem PositiveSaddleXplusGcompTangentFiniteWindowChunks.toRowsEntropyGeometricCertificate
    {chunks : List (Nat × Nat)}
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (finite : PositiveSaddleXplusGcompTangentFiniteWindowChunks chunks)
    (entropyGeometric :
      PositiveSaddleEntropyShadowExpGeometricBudgetCertificate
        smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentRowsEntropyGeometricCertificate
      smallExp temperedExp smallRatio temperedRatio where
  smallXplusGcompRows := by
    intro a ha h2000
    exact checkPositiveSmallXplusYProductGcompRow_of_checkRangeChunks
      finite.smallXplusGcompChunks (finite.cover (a := a) ha h2000)
  temperedXplusGcompRows := by
    intro a ha h2000
    exact checkPositiveTemperedXplusYProductGcompRow_of_checkRangeChunks
      finite.temperedXplusGcompChunks (finite.cover (a := a) ha h2000)
  smallTangentEdgeRows := by
    intro a ha h2000
    exact checkPositiveSmallTangentExpEdgeRow_of_checkRangeChunks
      finite.smallTangentEdgeChunks (finite.cover (a := a) ha h2000)
  soloGcompRows := by
    intro a ha h2000
    exact checkPositiveSoloGcompRow_of_checkRangeChunks
      finite.soloGcompChunks (finite.cover (a := a) ha h2000)
  edgeBudgetRows := by
    intro a ha h2000
    exact checkPositiveEdgeBudgetRow_of_checkPositiveEdgeBudgetRangeChunks
      finite.edgeBudgetChunks (finite.cover (a := a) ha h2000)
  entropyGeometric := entropyGeometric

theorem PositiveSaddleXplusGcompTangentChunkedRangeCertificate.toXplusGcompTangentFullyCheckedRowsCertificate
    {chunks : List (Nat × Nat)}
    (cert : PositiveSaddleXplusGcompTangentChunkedRangeCertificate chunks) :
    PositiveSaddleXplusGcompTangentFullyCheckedRowsCertificate :=
  cert.finiteChunks.toXplusGcompTangentFullyCheckedRowsCertificate
    cert.entropyTail

theorem PositiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricCertificate.toRowsEntropyGeometricCertificate
    {chunks : List (Nat × Nat)}
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricCertificate
      chunks smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentRowsEntropyGeometricCertificate
      smallExp temperedExp smallRatio temperedRatio :=
  cert.finiteChunks.toRowsEntropyGeometricCertificate cert.entropyGeometric

theorem PositiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricCertificate.toXplusGcompTangentFullyCheckedRowsCertificate
    {chunks : List (Nat × Nat)}
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricCertificate
      chunks smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentFullyCheckedRowsCertificate :=
  cert.toRowsEntropyGeometricCertificate.toXplusGcompTangentFullyCheckedRowsCertificate

theorem PositiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricReserveCertificate.toChunkedRangeEntropyGeometricCertificate
    {chunks : List (Nat × Nat)}
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricReserveCertificate
      chunks smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricCertificate
      chunks smallExp temperedExp smallRatio temperedRatio where
  finiteChunks := cert.finiteChunks
  entropyGeometric :=
    cert.entropyGeometricReserve.toGeometricBudgetCertificate

theorem PositiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricReserveCertificate.toRowsEntropyGeometricCertificate
    {chunks : List (Nat × Nat)}
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricReserveCertificate
      chunks smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentRowsEntropyGeometricCertificate
      smallExp temperedExp smallRatio temperedRatio :=
  cert.toChunkedRangeEntropyGeometricCertificate.toRowsEntropyGeometricCertificate

theorem PositiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricReserveCertificate.toXplusGcompTangentFullyCheckedRowsCertificate
    {chunks : List (Nat × Nat)}
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricReserveCertificate
      chunks smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentFullyCheckedRowsCertificate :=
  cert.toRowsEntropyGeometricCertificate.toXplusGcompTangentFullyCheckedRowsCertificate

theorem PositiveSaddleXplusGcompTangentChunkedRangeEntropyQuotientReserveCertificate.toChunkedRangeEntropyGeometricReserveCertificate
    {chunks : List (Nat × Nat)}
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentChunkedRangeEntropyQuotientReserveCertificate
      chunks smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricReserveCertificate
      chunks smallExp temperedExp smallRatio temperedRatio where
  finiteChunks := cert.finiteChunks
  entropyGeometricReserve :=
    cert.entropyQuotientReserve.toGeometricReserveCertificate

theorem PositiveSaddleXplusGcompTangentChunkedRangeEntropyQuotientReserveCertificate.toChunkedRangeEntropyGeometricCertificate
    {chunks : List (Nat × Nat)}
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentChunkedRangeEntropyQuotientReserveCertificate
      chunks smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricCertificate
      chunks smallExp temperedExp smallRatio temperedRatio :=
  cert.toChunkedRangeEntropyGeometricReserveCertificate.toChunkedRangeEntropyGeometricCertificate

theorem PositiveSaddleXplusGcompTangentChunkedRangeEntropyQuotientReserveCertificate.toRowsEntropyGeometricCertificate
    {chunks : List (Nat × Nat)}
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentChunkedRangeEntropyQuotientReserveCertificate
      chunks smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentRowsEntropyGeometricCertificate
      smallExp temperedExp smallRatio temperedRatio :=
  cert.toChunkedRangeEntropyGeometricCertificate.toRowsEntropyGeometricCertificate

theorem PositiveSaddleXplusGcompTangentChunkedRangeEntropyQuotientReserveCertificate.toXplusGcompTangentFullyCheckedRowsCertificate
    {chunks : List (Nat × Nat)}
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentChunkedRangeEntropyQuotientReserveCertificate
      chunks smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentFullyCheckedRowsCertificate :=
  cert.toRowsEntropyGeometricCertificate.toXplusGcompTangentFullyCheckedRowsCertificate

theorem PositiveSaddleXplusGcompTangentChunkedRangeEntropyRawQuotientReserveCertificate.toChunkedRangeEntropyQuotientReserveCertificate
    {chunks : List (Nat × Nat)}
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentChunkedRangeEntropyRawQuotientReserveCertificate
      chunks smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentChunkedRangeEntropyQuotientReserveCertificate
      chunks smallExp temperedExp smallRatio temperedRatio where
  finiteChunks := cert.finiteChunks
  entropyQuotientReserve :=
    cert.entropyRawQuotientReserve.toQuotientReserveCertificate

theorem PositiveSaddleXplusGcompTangentChunkedRangeEntropyRawQuotientReserveCertificate.toRowsEntropyGeometricCertificate
    {chunks : List (Nat × Nat)}
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentChunkedRangeEntropyRawQuotientReserveCertificate
      chunks smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentRowsEntropyGeometricCertificate
      smallExp temperedExp smallRatio temperedRatio :=
  cert.toChunkedRangeEntropyQuotientReserveCertificate.toRowsEntropyGeometricCertificate

theorem PositiveSaddleXplusGcompTangentChunkedRangeEntropyRawQuotientReserveCertificate.toXplusGcompTangentFullyCheckedRowsCertificate
    {chunks : List (Nat × Nat)}
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentChunkedRangeEntropyRawQuotientReserveCertificate
      chunks smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleXplusGcompTangentFullyCheckedRowsCertificate :=
  cert.toRowsEntropyGeometricCertificate.toXplusGcompTangentFullyCheckedRowsCertificate

theorem PositiveSaddleAtProductBudgetCertificate.toCombinedProductBudgetCertificate
    (cert : PositiveSaddleAtProductBudgetCertificate) :
    PositiveSaddleCombinedProductBudgetCertificate where
  smallXY := by
    intro a N k ha ha2000 hrect hk hsmall hB
    exact (cert.smallXYAt ha ha2000 hrect hk hsmall hB).trans
      (cert.smallEdge ha ha2000 hrect hk hsmall hB)
  temperedXY := cert.temperedXY
  soloY := cert.soloY
  edgeBudget := cert.edgeBudget
  entropyTail := cert.entropyTail

theorem PositiveSaddleAtExpBudgetCertificate.toAtProductBudgetCertificate
    (cert : PositiveSaddleAtExpBudgetCertificate) :
    PositiveSaddleAtProductBudgetCertificate where
  smallXYAt := cert.smallXYAt
  smallEdge := by
    intro a N k ha ha2000 hrect hk hsmall _hB
    exact positiveSmallXYProductAtBound_le_bound_of_expGap
      (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect) (by omega : 1 ≤ a)
      (cert.smallExpEdge ha ha2000 hrect hk hsmall)
  temperedXY := cert.temperedXY
  soloY := cert.soloY
  edgeBudget := cert.edgeBudget
  entropyTail := cert.entropyTail

theorem PositiveSaddleAtAnchorBudgetCertificate.toAtExpBudgetCertificate
    (cert : PositiveSaddleAtAnchorBudgetCertificate) :
    PositiveSaddleAtExpBudgetCertificate where
  smallXYAt := cert.smallXYAt
  smallExpEdge := by
    intro a N k ha ha2000 hrect hk hsmall
    exact positiveSmallExpEdgeGap_of_anchor ha ha2000 hrect hk
      (cert.smallExpEdgeAnchor ha ha2000
        (ceilSqrt_mem_positiveSmallCeilRange_of_rectangle hrect) hk hsmall)
  temperedXY := cert.temperedXY
  soloY := cert.soloY
  edgeBudget := cert.edgeBudget
  entropyTail := cert.entropyTail

/-- A still more decomposed §6 interface: prove separate saddle bounds for
`X_k(N)` and `Y_{a-k}(N)`, plus a purely scalar comparison from their product
to the executable small/tempered majorant.  This matches the TeX proof split
after the coefficient-ratio estimate has been inserted. -/
structure PositiveSaddleXYCertificate
    (soloBound : Nat → ℚ)
    (smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ) : Prop where
  smallX :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N → 0 < Bq N k →
        Xnorm N k ≤ smallXBound a N k
  smallY :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N → 0 < Bq N k →
        Ynorm N (posJ a k) ≤ smallYBound a N k
  smallProduct :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → k ≤ ceilSqrt N → 0 < Bq N k →
        ((N : ℚ) / 2) * positiveBinomRatio a k *
            positiveDyadicDecay (posJ a k) *
            smallXBound a N k * smallYBound a N k
          ≤ positiveSmallMajorantTerm a k
  temperedX :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k → 0 < Bq N k →
        Xnorm N k ≤ temperedXBound a N k
  temperedY :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k → 0 < Bq N k →
        Ynorm N (posJ a k) ≤ temperedYBound a N k
  temperedProduct :
    ∀ {a N k : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      k ∈ positiveKRange a → ceilSqrt N < k → 0 < Bq N k →
        ((N : ℚ) / 2) * positiveBinomRatio a k *
            positiveDyadicDecay (posJ a k) *
            temperedXBound a N k * temperedYBound a N k
          ≤ positiveTemperedMajorantTerm a k
  soloY :
    ∀ {a N : Nat}, 401 ≤ a → a ≤ 2000 → positiveRectangle a N →
      positiveDyadicDecay a / 2 * Ynorm N a ≤ soloBound a
  envelope :
    ∀ {a : Nat}, 401 ≤ a → a ≤ 2000 →
      positiveEnvelopeBound a (soloBound a) ≤ positiveTarget
  entropyTail :
    ∀ {a N : Nat}, 2000 < a → positiveRectangle a N → Unorm a N < 0

theorem PositiveSaddleXYCertificate.toFactorCertificate
    {soloBound : Nat → ℚ}
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    (cert : PositiveSaddleXYCertificate soloBound
      smallXBound smallYBound temperedXBound temperedYBound) :
    PositiveSaddleFactorCertificate soloBound where
  smallFactor := by
    intro a N k ha ha2000 hrect hk hsmall hB
    have hN : 1 ≤ N := positiveRectangle_N_pos (by omega : 2 ≤ a) hrect
    exact (positiveFactorizedRawTerm_le_of_XY_bounds hN (by omega : 2 ≤ a)
      hk hB
      (cert.smallX ha ha2000 hrect hk hsmall hB)
      (cert.smallY ha ha2000 hrect hk hsmall hB)).trans
      (cert.smallProduct ha ha2000 hrect hk hsmall hB)
  temperedFactor := by
    intro a N k ha ha2000 hrect hk htemp hB
    have hN : 1 ≤ N := positiveRectangle_N_pos (by omega : 2 ≤ a) hrect
    exact (positiveFactorizedRawTerm_le_of_XY_bounds hN (by omega : 2 ≤ a)
      hk hB
      (cert.temperedX ha ha2000 hrect hk htemp hB)
      (cert.temperedY ha ha2000 hrect hk htemp hB)).trans
      (cert.temperedProduct ha ha2000 hrect hk htemp hB)
  soloY := cert.soloY
  envelope := cert.envelope
  entropyTail := cert.entropyTail

theorem PositiveSaddleFactorCertificate.toRawCertificate
    {soloBound : Nat → ℚ} (cert : PositiveSaddleFactorCertificate soloBound) :
    PositiveSaddleRawCertificate soloBound where
  smallRaw := by
    intro a N k ha ha2000 hrect hk hsmall
    exact normalizedPositiveRawTerm_le_smallMajorant_of_factorized_bound
      ha ha2000 hrect hk
      (fun hB => cert.smallFactor ha ha2000 hrect hk hsmall hB)
  temperedRaw := by
    intro a N k ha ha2000 hrect hk htemp
    exact normalizedPositiveRawTerm_le_temperedMajorant_of_factorized_bound
      ha ha2000 hrect hk htemp
      (fun hB => cert.temperedFactor ha ha2000 hrect hk htemp hB)
  solo := by
    intro a N ha ha2000 hrect
    rw [normalizedSoloTerm_eq_dyadic_Ynorm
      (positiveRectangle_N_pos (by omega : 2 ≤ a) hrect) (by omega : 1 ≤ a)]
    exact cert.soloY ha ha2000 hrect
  envelope := cert.envelope
  entropyTail := cert.entropyTail

theorem PositiveSaddleRawCertificate.toCertificate
    {soloBound : Nat → ℚ} (cert : PositiveSaddleRawCertificate soloBound) :
    PositiveSaddleCertificate soloBound where
  small := by
    intro a N k ha ha2000 hrect hk hsmall
    have hnonneg : 0 ≤ positiveSmallMajorantTerm a k :=
      positiveSmallMajorantTerm_nonneg ha ha2000 hk
    exact normalizedPositiveIfTerm_le_of_raw_le hnonneg
      (fun _ _ => cert.smallRaw ha ha2000 hrect hk hsmall)
  tempered := by
    intro a N k ha ha2000 hrect hk htemp
    have hcut : posTemperedCutoff a < k :=
      temperedRegime_of_rectangle hrect htemp
    have hnonneg : 0 ≤ positiveTemperedMajorantTerm a k :=
      positiveTemperedMajorantTerm_nonneg ha ha2000 hk hcut
    exact normalizedPositiveIfTerm_le_of_raw_le hnonneg
      (fun _ _ => cert.temperedRaw ha ha2000 hrect hk htemp)
  solo := cert.solo
  envelope := cert.envelope
  entropyTail := cert.entropyTail

theorem PositiveSaddleFactorCertificate.toCertificate
    {soloBound : Nat → ℚ} (cert : PositiveSaddleFactorCertificate soloBound) :
    PositiveSaddleCertificate soloBound :=
  cert.toRawCertificate.toCertificate

theorem PositiveSaddleScalarCertificate.toCertificate
    {soloBound : Nat → ℚ} (cert : PositiveSaddleScalarCertificate soloBound) :
    PositiveSaddleCertificate soloBound :=
  cert.toFactorCertificate.toCertificate

theorem PositiveSaddleScalarBudgetCertificate.toCertificate
    (cert : PositiveSaddleScalarBudgetCertificate) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toScalarCertificate.toCertificate

theorem PositiveSaddleCombinedProductBudgetCertificate.toCertificate
    (cert : PositiveSaddleCombinedProductBudgetCertificate) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toScalarBudgetCertificate.toCertificate

theorem PositiveSaddleTangentProductBudgetCertificate.toCertificate
    (cert : PositiveSaddleTangentProductBudgetCertificate) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toCombinedProductBudgetCertificate.toCertificate

theorem PositiveSaddleTangentCheckedRowsCertificate.toCertificate
    (cert : PositiveSaddleTangentCheckedRowsCertificate) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toTangentProductBudgetCertificate.toCertificate

theorem PositiveSaddleTangentFullyCheckedRowsCertificate.toCertificate
    (cert : PositiveSaddleTangentFullyCheckedRowsCertificate) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toTangentCheckedRowsCertificate.toCertificate

theorem PositiveSaddleXplusTangentFullyCheckedRowsCertificate.toCertificate
    (cert : PositiveSaddleXplusTangentFullyCheckedRowsCertificate) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toTangentFullyCheckedRowsCertificate.toCertificate

theorem PositiveSaddleXplusGcompTangentFullyCheckedRowsCertificate.toCertificate
    (cert : PositiveSaddleXplusGcompTangentFullyCheckedRowsCertificate) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusTangentFullyCheckedRowsCertificate.toCertificate

theorem PositiveSaddleXplusGcompTangentRowsEntropyGeometricCertificate.toCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRowsEntropyGeometricCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentFullyCheckedRowsCertificate.toCertificate

theorem PositiveSaddleXplusGcompTangentRowsEntropyGeometricReserveCertificate.toCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRowsEntropyGeometricReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentFullyCheckedRowsCertificate.toCertificate

theorem PositiveSaddleXplusGcompTangentRowsEntropyQuotientReserveCertificate.toCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRowsEntropyQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentFullyCheckedRowsCertificate.toCertificate

theorem PositiveSaddleXplusGcompTangentRowsEntropyRawQuotientReserveCertificate.toCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRowsEntropyRawQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentFullyCheckedRowsCertificate.toCertificate

theorem PositiveSaddleXplusGcompTangentFullyCheckedRangeCertificate.toCertificate
    (cert : PositiveSaddleXplusGcompTangentFullyCheckedRangeCertificate) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentFullyCheckedRowsCertificate.toCertificate

theorem PositiveSaddleXplusGcompTangentRangeEntropyGeometricCertificate.toCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRangeEntropyGeometricCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentFullyCheckedRowsCertificate.toCertificate

theorem PositiveSaddleXplusGcompTangentRangeEntropyGeometricReserveCertificate.toCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRangeEntropyGeometricReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentFullyCheckedRowsCertificate.toCertificate

theorem PositiveSaddleXplusGcompTangentRangeEntropyQuotientReserveCertificate.toCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRangeEntropyQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentFullyCheckedRowsCertificate.toCertificate

theorem PositiveSaddleXplusGcompTangentRangeEntropyRawQuotientReserveCertificate.toCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRangeEntropyRawQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentFullyCheckedRowsCertificate.toCertificate

theorem PositiveSaddleXplusGcompTangentChunkedRangeCertificate.toCertificate
    {chunks : List (Nat × Nat)}
    (cert : PositiveSaddleXplusGcompTangentChunkedRangeCertificate chunks) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentFullyCheckedRowsCertificate.toCertificate

theorem PositiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricCertificate.toCertificate
    {chunks : List (Nat × Nat)}
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricCertificate
      chunks smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentFullyCheckedRowsCertificate.toCertificate

theorem PositiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricReserveCertificate.toCertificate
    {chunks : List (Nat × Nat)}
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricReserveCertificate
      chunks smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentFullyCheckedRowsCertificate.toCertificate

theorem PositiveSaddleXplusGcompTangentChunkedRangeEntropyQuotientReserveCertificate.toCertificate
    {chunks : List (Nat × Nat)}
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentChunkedRangeEntropyQuotientReserveCertificate
      chunks smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentFullyCheckedRowsCertificate.toCertificate

theorem PositiveSaddleXplusGcompTangentChunkedRangeEntropyRawQuotientReserveCertificate.toCertificate
    {chunks : List (Nat × Nat)}
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentChunkedRangeEntropyRawQuotientReserveCertificate
      chunks smallExp temperedExp smallRatio temperedRatio) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toXplusGcompTangentFullyCheckedRowsCertificate.toCertificate

theorem PositiveSaddleAtProductBudgetCertificate.toCertificate
    (cert : PositiveSaddleAtProductBudgetCertificate) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toCombinedProductBudgetCertificate.toCertificate

theorem PositiveSaddleAtExpBudgetCertificate.toCertificate
    (cert : PositiveSaddleAtExpBudgetCertificate) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toAtProductBudgetCertificate.toCertificate

theorem PositiveSaddleAtAnchorBudgetCertificate.toCertificate
    (cert : PositiveSaddleAtAnchorBudgetCertificate) :
    PositiveSaddleCertificate (fun _ => positiveSoloBudget) :=
  cert.toAtExpBudgetCertificate.toCertificate

theorem PositiveSaddleXYCertificate.toCertificate
    {soloBound : Nat → ℚ}
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    (cert : PositiveSaddleXYCertificate soloBound
      smallXBound smallYBound temperedXBound temperedYBound) :
    PositiveSaddleCertificate soloBound :=
  cert.toFactorCertificate.toCertificate

theorem Unorm_neg_of_positiveSaddleCertificate_finite
    {soloBound : Nat → ℚ} (cert : PositiveSaddleCertificate soloBound)
    {a N : Nat} (ha : 401 ≤ a) (ha2000 : a ≤ 2000)
    (hrect : positiveRectangle a N) :
    Unorm a N < 0 :=
  Unorm_neg_of_signLock_and_positiveEnvelopeBound
    (a := a) (N := N) (soloBound := soloBound a)
    ha hrect
    (fun _ hk hsmall => cert.small ha ha2000 hrect hk hsmall)
    (fun _ hk htemp => cert.tempered ha ha2000 hrect hk htemp)
    (cert.solo ha ha2000 hrect)
    (cert.envelope ha ha2000)

/-- Rectangle form of the large-`a` tail theorem supplied by a completed
positive-saddle certificate. -/
theorem unorm_tail_of_positiveSaddleCertificate
    {soloBound : Nat → ℚ} (cert : PositiveSaddleCertificate soloBound) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 := by
  intro a ha N hlo hhi
  rcases le_or_gt a 2000 with ha2000 | ha2000
  · exact Unorm_neg_of_positiveSaddleCertificate_finite
      (soloBound := soloBound) cert ha ha2000 ⟨hlo, hhi⟩
  · exact cert.entropyTail ha2000 ⟨hlo, hhi⟩

theorem unorm_tail_of_positiveSaddleRawCertificate
    {soloBound : Nat → ℚ} (cert : PositiveSaddleRawCertificate soloBound) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleFactorCertificate
    {soloBound : Nat → ℚ} (cert : PositiveSaddleFactorCertificate soloBound) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleScalarCertificate
    {soloBound : Nat → ℚ} (cert : PositiveSaddleScalarCertificate soloBound) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleScalarBudgetCertificate
    (cert : PositiveSaddleScalarBudgetCertificate) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleCombinedProductBudgetCertificate
    (cert : PositiveSaddleCombinedProductBudgetCertificate) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleTangentProductBudgetCertificate
    (cert : PositiveSaddleTangentProductBudgetCertificate) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleTangentCheckedRowsCertificate
    (cert : PositiveSaddleTangentCheckedRowsCertificate) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleTangentFullyCheckedRowsCertificate
    (cert : PositiveSaddleTangentFullyCheckedRowsCertificate) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleXplusTangentFullyCheckedRowsCertificate
    (cert : PositiveSaddleXplusTangentFullyCheckedRowsCertificate) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleXplusGcompTangentFullyCheckedRowsCertificate
    (cert : PositiveSaddleXplusGcompTangentFullyCheckedRowsCertificate) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleXplusGcompTangentRowsEntropyGeometricCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRowsEntropyGeometricCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleXplusGcompTangentRowsEntropyGeometricReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRowsEntropyGeometricReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleXplusGcompTangentRowsEntropyQuotientReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRowsEntropyQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleXplusGcompTangentRowsEntropyRawQuotientReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRowsEntropyRawQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleXplusGcompTangentFullyCheckedRangeCertificate
    (cert : PositiveSaddleXplusGcompTangentFullyCheckedRangeCertificate) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleXplusGcompTangentRangeEntropyGeometricCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRangeEntropyGeometricCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleXplusGcompTangentRangeEntropyGeometricReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRangeEntropyGeometricReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleXplusGcompTangentRangeEntropyQuotientReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRangeEntropyQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleXplusGcompTangentRangeEntropyRawQuotientReserveCertificate
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentRangeEntropyRawQuotientReserveCertificate
      smallExp temperedExp smallRatio temperedRatio) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleXplusGcompTangentChunkedRangeCertificate
    {chunks : List (Nat × Nat)}
    (cert : PositiveSaddleXplusGcompTangentChunkedRangeCertificate chunks) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricCertificate
    {chunks : List (Nat × Nat)}
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricCertificate
      chunks smallExp temperedExp smallRatio temperedRatio) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricReserveCertificate
    {chunks : List (Nat × Nat)}
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentChunkedRangeEntropyGeometricReserveCertificate
      chunks smallExp temperedExp smallRatio temperedRatio) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleXplusGcompTangentChunkedRangeEntropyQuotientReserveCertificate
    {chunks : List (Nat × Nat)}
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentChunkedRangeEntropyQuotientReserveCertificate
      chunks smallExp temperedExp smallRatio temperedRatio) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleXplusGcompTangentChunkedRangeEntropyRawQuotientReserveCertificate
    {chunks : List (Nat × Nat)}
    {smallExp temperedExp : Nat → Nat → ℚ}
    {smallRatio temperedRatio : Nat → ℚ}
    (cert : PositiveSaddleXplusGcompTangentChunkedRangeEntropyRawQuotientReserveCertificate
      chunks smallExp temperedExp smallRatio temperedRatio) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleAtProductBudgetCertificate
    (cert : PositiveSaddleAtProductBudgetCertificate) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleAtExpBudgetCertificate
    (cert : PositiveSaddleAtExpBudgetCertificate) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleAtAnchorBudgetCertificate
    (cert : PositiveSaddleAtAnchorBudgetCertificate) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

theorem unorm_tail_of_positiveSaddleXYCertificate
    {soloBound : Nat → ℚ}
    {smallXBound smallYBound temperedXBound temperedYBound :
      Nat → Nat → Nat → ℚ}
    (cert : PositiveSaddleXYCertificate soloBound
      smallXBound smallYBound temperedXBound temperedYBound) :
    ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 :=
  unorm_tail_of_positiveSaddleCertificate cert.toCertificate

/-! ## Numerical anchors for the first post-certificate row -/

theorem posNlo_401 : posNlo 401 = 2399 := by
  native_decide

theorem posNhi_401 : posNhi 401 = 4804 := by
  native_decide

theorem posSmallCutoff_401 : posSmallCutoff 401 = 70 := by
  native_decide

theorem posTemperedCutoff_401 : posTemperedCutoff 401 = 49 := by
  native_decide

end Prop51
