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

theorem positiveEnvelope_le_bound_of_solo
    {a N : Nat} {soloBound : ℚ}
    (hsolo : normalizedSoloTerm a N ≤ soloBound) :
    positiveEnvelope a N ≤ positiveEnvelopeBound a soloBound := by
  unfold positiveEnvelope positiveEnvelopeBound
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
