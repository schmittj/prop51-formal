/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Soundness of the dyadic interval arithmetic (Layer B infrastructure)

Enclosure semantics for the executable kernel `Prop51Kernel.lean`.  A `DF`
`(m, e)` denotes the rational `DF.val = m · 2^e`; the single soundness
notion is

  `DI.mem x I ↔ I.lo.val ≤ x ∧ x ≤ I.hi.val`,

and every kernel operation comes with a `mem`-preservation lemma
(`mem_add`, `mem_mul`, `mem_divNat`, …).  Everything is stated over `ℚ`
(the problem statement is pure `ℚ`; no real numbers appear anywhere).

Only *enclosure* is proved — never tightness.  In particular the rounding
soundness (`rdn_le`, `le_rup`) reduces to floor/ceil facts
(`Nat.shiftRight_eq_div_pow`, `Int.fmod` positivity), and would remain
sound under any choice of shift amounts.
-/

import Prop51Kernel
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

namespace Prop51

/-! ## Shift semantics -/

theorem shl_spec (m : Int) (k : Nat) : shl m k = m * (2:Int)^k := by
  cases m with
  | ofNat n =>
      show ((n <<< k : Nat) : Int) = ((n : Nat) : Int) * (2:Int)^k
      rw [Nat.shiftLeft_eq]
      push_cast
      ring
  | negSucc n =>
      show Int.negSucc ((n+1) <<< k - 1) = Int.negSucc n * (2:Int)^k
      rw [Nat.shiftLeft_eq]
      have h2 : 0 < (n+1) * 2^k := Nat.mul_pos (Nat.succ_pos n) (Nat.two_pow_pos k)
      rw [Int.negSucc_eq, Int.negSucc_eq]
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring

/-- The floor bound: `floorShr m k · 2^k ≤ m`. -/
theorem floorShr_mul_le (m : Int) (k : Nat) : floorShr m k * (2:Int)^k ≤ m := by
  cases m with
  | ofNat n =>
      show ((n >>> k : Nat) : Int) * (2:Int)^k ≤ ((n : Nat) : Int)
      rw [Nat.shiftRight_eq_div_pow]
      have h := Nat.div_mul_le_self n (2^k)
      exact_mod_cast h
  | negSucc n =>
      show Int.negSucc (n >>> k) * (2:Int)^k ≤ Int.negSucc n
      rw [Nat.shiftRight_eq_div_pow, Int.negSucc_eq, Int.negSucc_eq]
      have hdm : (2:ℤ)^k * ((n / 2^k : Nat) : ℤ) + ((n % 2^k : Nat) : ℤ)
          = (n : ℤ) := by exact_mod_cast Nat.div_add_mod n (2^k)
      have hlt : ((n % 2^k : Nat) : ℤ) < (2:ℤ)^k := by
        exact_mod_cast Nat.mod_lt n (Nat.two_pow_pos k)
      nlinarith [hdm, hlt]

theorem le_ceilShr_mul (m : Int) (k : Nat) : m ≤ ceilShr m k * (2:Int)^k := by
  have h := floorShr_mul_le (-m) k
  unfold ceilShr
  nlinarith [h]

namespace DF

/-- The rational value of a dyadic float. -/
def val (f : DF) : ℚ := (f.m : ℚ) * (2:ℚ) ^ f.e

theorem val_mk (m e : Int) : val ⟨m, e⟩ = (m : ℚ) * (2:ℚ)^e := rfl

theorem two_zpow_pos (e : Int) : (0:ℚ) < (2:ℚ) ^ e :=
  zpow_pos (by norm_num) e

/-- Mantissa monotonicity at a fixed exponent. -/
theorem val_le_val_of_m_le {m m' : Int} (e : Int) (h : m ≤ m') :
    val ⟨m, e⟩ ≤ val ⟨m', e⟩ :=
  mul_le_mul_of_nonneg_right (by exact_mod_cast h) (le_of_lt (two_zpow_pos e))

theorem val_neg_of_m_neg {f : DF} (h : f.m < 0) : f.val < 0 :=
  mul_neg_of_neg_of_pos (by exact_mod_cast h) (two_zpow_pos f.e)

theorem val_nonneg_of_m_nonneg {f : DF} (h : 0 ≤ f.m) : 0 ≤ f.val :=
  mul_nonneg (by exact_mod_cast h) (le_of_lt (two_zpow_pos f.e))

theorem val_nonpos_of_m_nonpos {f : DF} (h : f.m ≤ 0) : f.val ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h)
    (le_of_lt (two_zpow_pos f.e))

/-- Exact re-alignment: shifting the mantissa left while lowering the
exponent preserves the value. -/
theorem val_align (m e emin : Int) (h : emin ≤ e) :
    val ⟨shl m (e - emin).toNat, emin⟩ = val ⟨m, e⟩ := by
  rw [val_mk, val_mk, shl_spec]
  push_cast
  rw [mul_assoc]
  congr 1
  rw [← zpow_natCast (2:ℚ) (e - emin).toNat,
    ← zpow_add₀ (by norm_num : (2:ℚ) ≠ 0)]
  congr 1
  omega

/-- Exact `PREC`-bit mantissa boost: `(m·2^PREC) · 2^(e-PREC) = m · 2^e`. -/
theorem val_shl_PREC (m e : Int) :
    val ⟨shl m PREC, e - (PREC : Int)⟩ = val ⟨m, e⟩ := by
  have h := val_align m e (e - (PREC : Int)) (by omega)
  have hk : (e - (e - (PREC : Int))).toNat = PREC := by omega
  rwa [hk] at h

private theorem val_floorShr_le (m e : Int) (k : Nat) :
    val ⟨floorShr m k, e + (k : Int)⟩ ≤ val ⟨m, e⟩ := by
  rw [val_mk, val_mk, zpow_add₀ (by norm_num : (2:ℚ) ≠ 0), zpow_natCast]
  have h : ((floorShr m k * 2^k : ℤ) : ℚ) ≤ ((m : ℤ) : ℚ) :=
    Int.cast_le.mpr (floorShr_mul_le m k)
  push_cast at h
  calc (floorShr m k : ℚ) * ((2:ℚ)^e * (2:ℚ)^k)
      = ((floorShr m k : ℚ) * (2:ℚ)^k) * (2:ℚ)^e := by ring
    _ ≤ (m : ℚ) * (2:ℚ)^e :=
        mul_le_mul_of_nonneg_right h (le_of_lt (two_zpow_pos e))

private theorem le_val_ceilShr (m e : Int) (k : Nat) :
    val ⟨m, e⟩ ≤ val ⟨ceilShr m k, e + (k : Int)⟩ := by
  rw [val_mk, val_mk, zpow_add₀ (by norm_num : (2:ℚ) ≠ 0), zpow_natCast]
  have h : ((m : ℤ) : ℚ) ≤ ((ceilShr m k * 2^k : ℤ) : ℚ) :=
    Int.cast_le.mpr (le_ceilShr_mul m k)
  push_cast at h
  calc (m : ℚ) * (2:ℚ)^e
      ≤ ((ceilShr m k : ℚ) * (2:ℚ)^k) * (2:ℚ)^e :=
        mul_le_mul_of_nonneg_right h (le_of_lt (two_zpow_pos e))
    _ = (ceilShr m k : ℚ) * ((2:ℚ)^e * (2:ℚ)^k) := by ring

theorem rdn_le (f : DF) : (rdn f).val ≤ f.val := by
  unfold rdn
  dsimp only
  split
  · exact le_refl _
  · exact val_floorShr_le f.m f.e _

theorem le_rup (f : DF) : f.val ≤ (rup f).val := by
  unfold rup
  dsimp only
  split
  · exact le_refl _
  · exact le_val_ceilShr f.m f.e _

theorem val_neg (f : DF) : f.neg.val = -f.val := by
  rw [neg, val]
  show ((-f.m : ℤ) : ℚ) * (2:ℚ)^f.e = -((f.m : ℚ) * (2:ℚ)^f.e)
  push_cast
  ring

theorem val_addE (a b : DF) : (a.addE b).val = a.val + b.val := by
  unfold addE
  dsimp only
  rw [val_mk]
  push_cast
  rw [add_mul]
  have h1 := val_align a.m a.e (min a.e b.e) (min_le_left _ _)
  have h2 := val_align b.m b.e (min a.e b.e) (min_le_right _ _)
  rw [val_mk, val_mk] at h1 h2
  rw [h1, h2]
  rfl

theorem val_mulE (a b : DF) : (a.mulE b).val = a.val * b.val := by
  rw [mulE, val, val, val]
  show ((a.m * b.m : ℤ) : ℚ) * (2:ℚ)^(a.e + b.e) = _
  rw [zpow_add₀ (by norm_num : (2:ℚ) ≠ 0)]
  push_cast
  ring

end DF

/-! ## Soundness of `hull4` -/

/-- The lower endpoint of `hull4` is below each of the four inputs, and the
upper endpoint above. -/
theorem hull4_spec (p1 p2 p3 p4 : DF) :
    ((hull4 p1 p2 p3 p4).lo.val ≤ p1.val ∧ (hull4 p1 p2 p3 p4).lo.val ≤ p2.val
      ∧ (hull4 p1 p2 p3 p4).lo.val ≤ p3.val
      ∧ (hull4 p1 p2 p3 p4).lo.val ≤ p4.val)
    ∧ (p1.val ≤ (hull4 p1 p2 p3 p4).hi.val ∧ p2.val ≤ (hull4 p1 p2 p3 p4).hi.val
      ∧ p3.val ≤ (hull4 p1 p2 p3 p4).hi.val
      ∧ p4.val ≤ (hull4 p1 p2 p3 p4).hi.val) := by
  unfold hull4
  dsimp only
  set e := min (min p1.e p2.e) (min p3.e p4.e) with he
  have he1 : e ≤ p1.e := le_trans (min_le_left _ _) (min_le_left _ _)
  have he2 : e ≤ p2.e := le_trans (min_le_left _ _) (min_le_right _ _)
  have he3 : e ≤ p3.e := le_trans (min_le_right _ _) (min_le_left _ _)
  have he4 : e ≤ p4.e := le_trans (min_le_right _ _) (min_le_right _ _)
  have ha1 := DF.val_align p1.m p1.e e he1
  have ha2 := DF.val_align p2.m p2.e e he2
  have ha3 := DF.val_align p3.m p3.e e he3
  have ha4 := DF.val_align p4.m p4.e e he4
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact le_trans (DF.rdn_le _) (le_trans (DF.val_le_val_of_m_le e
      (le_trans (min_le_left _ _) (min_le_left _ _))) (le_of_eq ha1))
  · exact le_trans (DF.rdn_le _) (le_trans (DF.val_le_val_of_m_le e
      (le_trans (min_le_left _ _) (min_le_right _ _))) (le_of_eq ha2))
  · exact le_trans (DF.rdn_le _) (le_trans (DF.val_le_val_of_m_le e
      (le_trans (min_le_right _ _) (min_le_left _ _))) (le_of_eq ha3))
  · exact le_trans (DF.rdn_le _) (le_trans (DF.val_le_val_of_m_le e
      (le_trans (min_le_right _ _) (min_le_right _ _))) (le_of_eq ha4))
  · exact le_trans (le_trans (le_of_eq ha1.symm) (DF.val_le_val_of_m_le e
      (le_trans (le_max_left _ _) (le_max_left _ _)))) (DF.le_rup _)
  · exact le_trans (le_trans (le_of_eq ha2.symm) (DF.val_le_val_of_m_le e
      (le_trans (le_max_right _ _) (le_max_left _ _)))) (DF.le_rup _)
  · exact le_trans (le_trans (le_of_eq ha3.symm) (DF.val_le_val_of_m_le e
      (le_trans (le_max_left _ _) (le_max_right _ _)))) (DF.le_rup _)
  · exact le_trans (le_trans (le_of_eq ha4.symm) (DF.val_le_val_of_m_le e
      (le_trans (le_max_right _ _) (le_max_right _ _)))) (DF.le_rup _)

/-! ## The four-corner product bounds over `ℚ` -/

private theorem four_min_le_mul {x y a b c d : ℚ} (h1 : a ≤ x) (h2 : x ≤ b)
    (h3 : c ≤ y) (h4 : y ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ x * y := by
  rcases le_total 0 y with hy | hy
  · have hxy : a * y ≤ x * y := mul_le_mul_of_nonneg_right h1 hy
    rcases le_total 0 a with ha | ha
    · have hc : a * c ≤ a * y := mul_le_mul_of_nonneg_left h3 ha
      exact le_trans (le_trans (min_le_left _ _) (min_le_left _ _))
        (le_trans hc hxy)
    · have hd : a * d ≤ a * y := mul_le_mul_of_nonpos_left h4 ha
      exact le_trans (le_trans (min_le_left _ _) (min_le_right _ _))
        (le_trans hd hxy)
  · have hxy : b * y ≤ x * y := mul_le_mul_of_nonpos_right h2 hy
    rcases le_total 0 b with hb | hb
    · have hc : b * c ≤ b * y := mul_le_mul_of_nonneg_left h3 hb
      exact le_trans (le_trans (min_le_right _ _) (min_le_left _ _))
        (le_trans hc hxy)
    · have hd : b * d ≤ b * y := mul_le_mul_of_nonpos_left h4 hb
      exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _))
        (le_trans hd hxy)

private theorem mul_le_four_max {x y a b c d : ℚ} (h1 : a ≤ x) (h2 : x ≤ b)
    (h3 : c ≤ y) (h4 : y ≤ d) :
    x * y ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  rcases le_total 0 y with hy | hy
  · have hxy : x * y ≤ b * y := mul_le_mul_of_nonneg_right h2 hy
    rcases le_total 0 b with hb | hb
    · have hd : b * y ≤ b * d := mul_le_mul_of_nonneg_left h4 hb
      exact le_trans (le_trans hxy hd)
        (le_trans (le_max_right _ _) (le_max_right _ _))
    · have hc : b * y ≤ b * c := mul_le_mul_of_nonpos_left h3 hb
      exact le_trans (le_trans hxy hc)
        (le_trans (le_max_left _ _) (le_max_right _ _))
  · have hxy : x * y ≤ a * y := mul_le_mul_of_nonpos_right h1 hy
    rcases le_total 0 a with ha | ha
    · have hd : a * y ≤ a * d := mul_le_mul_of_nonneg_left h4 ha
      exact le_trans (le_trans hxy hd)
        (le_trans (le_max_right _ _) (le_max_left _ _))
    · have hc : a * y ≤ a * c := mul_le_mul_of_nonpos_left h3 ha
      exact le_trans (le_trans hxy hc)
        (le_trans (le_max_left _ _) (le_max_left _ _))

namespace DI

/-- `x` is enclosed by the interval `I`. -/
def mem (x : ℚ) (I : DI) : Prop := I.lo.val ≤ x ∧ x ≤ I.hi.val

theorem mem_zero : mem 0 zero := by
  constructor <;> simp [zero, DF.val_mk]

theorem mem_one : mem 1 one := by
  constructor <;> simp [one, DF.val_mk]

theorem mem_exact (n : Nat) : mem (n : ℚ) (exact n) := by
  constructor <;> simp [exact, DF.val_mk]

theorem mem_add {x y : ℚ} {I J : DI} (hx : mem x I) (hy : mem y J) :
    mem (x + y) (I.add J) := by
  constructor
  · calc (DF.rdn (I.lo.addE J.lo)).val
        ≤ (I.lo.addE J.lo).val := DF.rdn_le _
      _ = I.lo.val + J.lo.val := DF.val_addE _ _
      _ ≤ x + y := add_le_add hx.1 hy.1
  · calc x + y
        ≤ I.hi.val + J.hi.val := add_le_add hx.2 hy.2
      _ = (I.hi.addE J.hi).val := (DF.val_addE _ _).symm
      _ ≤ (DF.rup (I.hi.addE J.hi)).val := DF.le_rup _

theorem mem_neg {x : ℚ} {I : DI} (hx : mem x I) : mem (-x) I.neg := by
  constructor
  · rw [show I.neg.lo = I.hi.neg from rfl, DF.val_neg]
    linarith [hx.2]
  · rw [show I.neg.hi = I.lo.neg from rfl, DF.val_neg]
    linarith [hx.1]

theorem mem_nsmul (n : Nat) {x : ℚ} {I : DI} (hx : mem x I) :
    mem ((n : ℚ) * x) (nsmul n I) := by
  have hval : ∀ (m : Int) (e : Int),
      DF.val ⟨(n : Int) * m, e⟩ = (n : ℚ) * DF.val ⟨m, e⟩ := by
    intro m e
    rw [DF.val_mk, DF.val_mk]
    push_cast
    ring
  constructor
  · calc (DF.rdn ⟨(n : Int) * I.lo.m, I.lo.e⟩).val
        ≤ DF.val ⟨(n : Int) * I.lo.m, I.lo.e⟩ := DF.rdn_le _
      _ = (n : ℚ) * I.lo.val := hval _ _
      _ ≤ (n : ℚ) * x :=
          mul_le_mul_of_nonneg_left hx.1 (Nat.cast_nonneg n)
  · calc (n : ℚ) * x
        ≤ (n : ℚ) * I.hi.val :=
          mul_le_mul_of_nonneg_left hx.2 (Nat.cast_nonneg n)
      _ = DF.val ⟨(n : Int) * I.hi.m, I.hi.e⟩ := (hval _ _).symm
      _ ≤ (DF.rup ⟨(n : Int) * I.hi.m, I.hi.e⟩).val := DF.le_rup _

private theorem div_le_div_right' {x y : ℚ} (h : x ≤ y) {c : ℚ} (hc : 0 < c) :
    x / c ≤ y / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h (le_of_lt (inv_pos.mpr hc))

theorem mem_shr (k : Nat) {x : ℚ} {I : DI} (hx : mem x I) :
    mem (x / 2^k) (shr k I) := by
  have hval : ∀ (m : Int) (e : Int),
      DF.val ⟨m, e - (k : Int)⟩ = DF.val ⟨m, e⟩ / 2^k := by
    intro m e
    rw [DF.val_mk, DF.val_mk, zpow_sub₀ (by norm_num : (2:ℚ) ≠ 0),
      zpow_natCast]
    ring
  have h2k : (0:ℚ) < 2^k := by positivity
  constructor
  · rw [show (shr k I).lo = ⟨I.lo.m, I.lo.e - (k : Int)⟩ from rfl, hval]
    exact div_le_div_right' hx.1 h2k
  · rw [show (shr k I).hi = ⟨I.hi.m, I.hi.e - (k : Int)⟩ from rfl, hval]
    exact div_le_div_right' hx.2 h2k

/-- Floor division bound over `ℤ`: `(a.fdiv n) * n ≤ a` for `0 < n`. -/
private theorem fdiv_mul_le (a : Int) {n : Int} (hn : 0 < n) :
    a.fdiv n * n ≤ a := by
  have h := Int.fmod_add_fdiv_mul a n
  have h2 := Int.fmod_nonneg_of_pos a hn
  linarith

theorem mem_divNat {x : ℚ} {I : DI} (n : Nat) (hn : 0 < n) (hx : mem x I) :
    mem (x / (n : ℚ)) (I.divNat n) := by
  have hnQ : (0:ℚ) < (n : ℚ) := by exact_mod_cast hn
  have hnZ : (0:Int) < (n : Int) := by exact_mod_cast hn
  constructor
  · have hfd : (((shl I.lo.m PREC).fdiv (n : Int) : ℤ) : ℚ)
        ≤ ((shl I.lo.m PREC : ℤ) : ℚ) / (n : ℚ) := by
      rw [le_div_iff₀ hnQ]
      exact_mod_cast fdiv_mul_le (shl I.lo.m PREC) hnZ
    calc (DF.rdn ⟨(shl I.lo.m PREC).fdiv (n : Int), I.lo.e - (PREC : Int)⟩).val
        ≤ DF.val ⟨(shl I.lo.m PREC).fdiv (n : Int), I.lo.e - (PREC : Int)⟩ :=
          DF.rdn_le _
      _ = (((shl I.lo.m PREC).fdiv (n : Int) : ℤ) : ℚ)
          * (2:ℚ)^(I.lo.e - (PREC : Int)) := DF.val_mk _ _
      _ ≤ (((shl I.lo.m PREC : ℤ) : ℚ) / (n : ℚ))
          * (2:ℚ)^(I.lo.e - (PREC : Int)) :=
          mul_le_mul_of_nonneg_right hfd (le_of_lt (DF.two_zpow_pos _))
      _ = (((shl I.lo.m PREC : ℤ) : ℚ)
          * (2:ℚ)^(I.lo.e - (PREC : Int))) / (n : ℚ) := by ring
      _ = DF.val ⟨shl I.lo.m PREC, I.lo.e - (PREC : Int)⟩ / (n : ℚ) := by
          rw [DF.val_mk]
      _ = I.lo.val / (n : ℚ) := by rw [DF.val_shl_PREC]
      _ ≤ x / (n : ℚ) := div_le_div_right' hx.1 hnQ
  · have hfd : ((shl I.hi.m PREC : ℤ) : ℚ) / (n : ℚ)
        ≤ ((-((-(shl I.hi.m PREC)).fdiv (n : Int)) : ℤ) : ℚ) := by
      rw [div_le_iff₀ hnQ]
      have h := fdiv_mul_le (-(shl I.hi.m PREC)) hnZ
      have : (shl I.hi.m PREC : ℤ)
          ≤ -((-(shl I.hi.m PREC)).fdiv (n : Int)) * (n : Int) := by linarith
      exact_mod_cast this
    calc x / (n : ℚ)
        ≤ I.hi.val / (n : ℚ) := div_le_div_right' hx.2 hnQ
      _ = DF.val ⟨shl I.hi.m PREC, I.hi.e - (PREC : Int)⟩ / (n : ℚ) := by
          rw [DF.val_shl_PREC]
      _ = (((shl I.hi.m PREC : ℤ) : ℚ) / (n : ℚ))
          * (2:ℚ)^(I.hi.e - (PREC : Int)) := by
          rw [DF.val_mk]; ring
      _ ≤ ((-((-(shl I.hi.m PREC)).fdiv (n : Int)) : ℤ) : ℚ)
          * (2:ℚ)^(I.hi.e - (PREC : Int)) :=
          mul_le_mul_of_nonneg_right hfd (le_of_lt (DF.two_zpow_pos _))
      _ = DF.val ⟨-((-(shl I.hi.m PREC)).fdiv (n : Int)),
            I.hi.e - (PREC : Int)⟩ := (DF.val_mk _ _).symm
      _ ≤ (DF.rup ⟨-((-(shl I.hi.m PREC)).fdiv (n : Int)),
            I.hi.e - (PREC : Int)⟩).val := DF.le_rup _

theorem mem_mul {x y : ℚ} {I J : DI} (hx : mem x I) (hy : mem y J) :
    mem (x * y) (I.mul J) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  obtain ⟨⟨l1, l2, l3, l4⟩, u1, u2, u3, u4⟩ :=
    hull4_spec (I.lo.mulE J.lo) (I.lo.mulE J.hi) (I.hi.mulE J.lo)
      (I.hi.mulE J.hi)
  rw [DF.val_mulE] at l1 l2 l3 l4 u1 u2 u3 u4
  constructor
  · have hmin := four_min_le_mul h1 h2 h3 h4
    have : (I.mul J).lo.val
        ≤ min (min (I.lo.val * J.lo.val) (I.lo.val * J.hi.val))
            (min (I.hi.val * J.lo.val) (I.hi.val * J.hi.val)) :=
      le_min (le_min l1 l2) (le_min l3 l4)
    exact le_trans this hmin
  · have hmax := mul_le_four_max h1 h2 h3 h4
    have : max (max (I.lo.val * J.lo.val) (I.lo.val * J.hi.val))
            (max (I.hi.val * J.lo.val) (I.hi.val * J.hi.val))
        ≤ (I.mul J).hi.val :=
      max_le (max_le u1 u2) (max_le u3 u4)
    exact le_trans hmax this

theorem val_zero_mk : DF.val ⟨0, 0⟩ = 0 := by simp [DF.val_mk]

theorem mem_hull0_of_mem {x : ℚ} {I : DI} (hx : mem x I) : mem x (hull0 I) := by
  constructor
  · show (if I.lo.m < 0 then I.lo else ⟨0, 0⟩ : DF).val ≤ x
    split
    · exact hx.1
    · rename_i h
      rw [val_zero_mk]
      exact le_trans (DF.val_nonneg_of_m_nonneg (by omega)) hx.1
  · show x ≤ (if 0 < I.hi.m then I.hi else ⟨0, 0⟩ : DF).val
    split
    · exact hx.2
    · rename_i h
      rw [val_zero_mk]
      exact le_trans hx.2 (DF.val_nonpos_of_m_nonpos (by omega))

theorem zero_mem_hull0 (I : DI) : mem 0 (hull0 I) := by
  constructor
  · show (if I.lo.m < 0 then I.lo else ⟨0, 0⟩ : DF).val ≤ 0
    split
    · exact le_of_lt (DF.val_neg_of_m_neg ‹_›)
    · rw [val_zero_mk]
  · show (0:ℚ) ≤ (if 0 < I.hi.m then I.hi else ⟨0, 0⟩ : DF).val
    split
    · exact DF.val_nonneg_of_m_nonneg (le_of_lt ‹_›)
    · rw [val_zero_mk]

end DI

end Prop51
