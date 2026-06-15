/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Positive-part saddle setup (paper §6)

This file records the integer bookkeeping for the repaired positive-part
estimate.  The analytic saddle majorants and the rational certificate are
added later; the goal here is to make the corrected two-edge rectangle scan a
Lean interface rather than an informal convention in the Python script.
-/

import Mathlib.Data.Nat.Sqrt
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

/-- The largest cutoff at which the small-`k` saddle regime can occur anywhere
in the rectangle.  This is the corrected `ceil(sqrt(12a-8))` edge from
`scripts/positive_saddle_scan.py`. -/
def posSmallCutoff (a : Nat) : Nat := ceilSqrt (posNhi a)

/-- The smallest cutoff at which the tempered saddle regime can occur anywhere
in the rectangle.  This is the corrected `ceil(sqrt(6a-7))` edge from
`scripts/positive_saddle_scan.py`. -/
def posTemperedCutoff (a : Nat) : Nat := ceilSqrt (posNlo a)

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

/-- In the retained range, `j=a-k` still has size at least `a/10`. -/
theorem self_le_ten_mul_posJ_of_le_posKmax {a k : Nat}
    (hk : k ≤ posKmax a) :
    a ≤ 10 * posJ a k := by
  unfold posJ
  have h10 : 10*k ≤ 9*a := ten_mul_le_nine_mul_of_le_posKmax hk
  omega

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

/-! ## Executable rational summand majorants -/

/-- The finite-window partial-exp cutoff for the §6 scan.  On
`401 ≤ a ≤ 2000`, both rationalized edge exponents are `< 800`; see
`positiveSmallExponentUpper_lt_expCutoff` and
`positiveTemperedExponentUpper_lt_expCutoff`. -/
def positiveExpCutoff : Nat := 800

/-- The binomial denominator retained in paper §6:
`\binom{a-2}{k-1}`. -/
def positiveBinomDen (a k : Nat) : Nat := Nat.choose (a-2) (k-1)

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

/-- The rationalized small-regime edge majorant for one summand. -/
def positiveSmallMajorantTerm (a k : Nat) : ℚ :=
  positivePrefactor 65 a (posNhi a) k
    * partialExpUpper (positiveSmallExponentUpper a k) positiveExpCutoff

/-- The rationalized tempered-regime edge majorant for one summand. -/
def positiveTemperedMajorantTerm (a k : Nat) : ℚ :=
  positivePrefactor 96 a (posNlo a) k
    * partialExpUpper (positiveTemperedExponentUpper a k) positiveExpCutoff

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

/-! ## Raw normalized positive contribution -/

/-- The normalized solo `Q_a` contribution in `Unorm`.  In the paper's
notation this is the term written as `2^{-a-1}Y_a(N)`. -/
def normalizedSoloTerm (a N : Nat) : ℚ :=
  Qq N a / ((N : ℚ) * c a)

/-- One normalized raw positive summand from `Unorm_eq`, without the positivity
guard. -/
def normalizedPositiveRawTerm (a N k : Nat) : ℚ :=
  Bq N k * Qq N (a-k) / ((N : ℚ) * c a)

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

theorem Unorm_eq_Xnorm_add_solo_add_retained_of_large_Xnorm_nonpos
    {a N : Nat} (ha : 1 ≤ a) (hN : 1 ≤ N)
    (hlarge : ∀ k, k < a → posKmax a < k → 1 ≤ k → Xnorm N k ≤ 0) :
    Unorm a N =
      Xnorm N a + normalizedSoloTerm a N + normalizedPositiveRetainedSum a N := by
  rw [Unorm_eq_Xnorm_add_solo_add_positive,
    normalizedPositiveRangeSum_eq_retained_of_large_Xnorm_nonpos ha hN hlarge]

theorem positiveBinomDen_pos {a k : Nat} (ha : 2 ≤ a) (hk1 : 1 ≤ k)
    (hkmax : k ≤ posKmax a) :
    0 < positiveBinomDen a k := by
  unfold positiveBinomDen
  have hka : k < a := lt_self_of_le_posKmax (by omega : 1 ≤ a) hkmax
  exact Nat.choose_pos (by omega : k - 1 ≤ a - 2)

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

theorem positiveSmallExponentUpper_nonneg {a k : Nat}
    (hj : 0 < posJ a k) :
    0 ≤ positiveSmallExponentUpper a k := by
  unfold positiveSmallExponentUpper
  have hjQ : (0 : ℚ) < (posJ a k : ℚ) := by exact_mod_cast hj
  positivity

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
