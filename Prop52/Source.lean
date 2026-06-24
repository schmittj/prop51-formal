/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Source coefficient for the corrected Chen--Larson Proposition 5.2

The certificate core proves non-vanishing for the marked coefficient
`correctedCoeff a μ = [t^a] B_μ(t) * (M a - K_μ(t))`.  The corrected geometric
identity in Proposition 5.2 produces instead the source coefficient
`[t^a] B_μ(t) * D^cor_μ(t)`.  This file defines that source coefficient and
proves the degree-`a` source--marked bridge used by the paper.

The bridge is not a numerical certificate: it is a formal rational identity.
The `native_decide` examples at the bottom are only small executable sanity
checks.
-/

import Prop52.Assembly

namespace Prop52

/-- The coefficient of the corrected source factor
`D^cor_{μ,lead}(t)`.

For the corrected Proposition 5.2 coefficient the leading term is `lead = M a`;
for the printed coefficient it is `lead = 1`. -/
def sourceFactorCoeff (lead : ℚ) (μ : List Nat) : Nat → ℚ
  | 0 => lead
  | 1 => -2 * ((N μ : ℚ) - sPower μ 1)
  | r + 2 =>
      -12 * ((r + 1 : Nat) : ℚ) * Prop51.c (r + 1) *
        ((N μ : ℚ) - sPower μ (r + 2))

/-- The source coefficient `[t^a] B_μ(t) * D^cor_{μ,lead}(t)`. -/
def sourceCoeff (lead : ℚ) (μ : List Nat) (a : Nat) : ℚ :=
  ∑ r ∈ Finset.range (a + 1),
    sourceFactorCoeff lead μ r * Prop51.bCoeff μ (a - r)

/-- The marked factor whose convolution is `lead * b_a - markedConvolution`. -/
def markedFactorCoeff (lead : ℚ) (μ : List Nat) : Nat → ℚ
  | 0 => lead
  | r + 1 => -markedCoeff μ (r + 1)

/-- The defect between the source and marked factors. -/
def sourceBridgeFactorCoeff (μ : List Nat) : Nat → ℚ
  | 0 => 0
  | 1 => -2 * (μ.sum : ℚ)
  | r + 2 => -12 * ((r + 1 : Nat) : ℚ) * hCoeff μ (r + 1)

/-- The marked coefficient with an arbitrary leading constant. -/
def markedProxyCoeff (lead : ℚ) (μ : List Nat) (a : Nat) : ℚ :=
  lead * Prop51.bCoeff μ a - markedConvolution μ a

private theorem markedWeight_succ_eq_sPower_sub (μ : List Nat) (r : Nat) :
    markedWeight μ (r + 1) = sPower μ r - sPower μ (r + 1) := by
  induction μ with
  | nil =>
      simp [markedWeight, sPower]
  | cons mi μ ih =>
      unfold markedWeight sPower at ih ⊢
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      have hq : (((mi + 1 : Nat) : ℚ) ≠ 0) := by positivity
      have hterm :
          (mi : ℚ) / ((mi + 1 : Nat) : ℚ) ^ (r + 1) =
            1 / ((mi + 1 : Nat) : ℚ) ^ r -
              1 / ((mi + 1 : Nat) : ℚ) ^ (r + 1) := by
        field_simp [hq, pow_ne_zero _ hq]
        norm_num
        ring_nf
      rw [hterm]
      ring

private theorem sPower_zero_eq_length (μ : List Nat) :
    sPower μ 0 = (μ.length : ℚ) := by
  induction μ with
  | nil =>
      simp [sPower]
  | cons mi μ ih =>
    simp [sPower]
    ring

private theorem N_sub_sPower_zero_eq_sum (μ : List Nat) :
    (N μ : ℚ) - sPower μ 0 = (μ.sum : ℚ) := by
  have hN : N μ = μ.sum + μ.length := by
    unfold N
    rw [Prop51.sum_map_add_one]
  have hNq : (N μ : ℚ) = (μ.sum : ℚ) + (μ.length : ℚ) := by
    exact_mod_cast hN
  rw [hNq, sPower_zero_eq_length]
  ring

private theorem sourceFactorCoeff_eq_marked_add_bridge
    (lead : ℚ) (μ : List Nat) (r : Nat) :
    sourceFactorCoeff lead μ r =
      markedFactorCoeff lead μ r + sourceBridgeFactorCoeff μ r := by
  cases r with
  | zero =>
      simp [sourceFactorCoeff, markedFactorCoeff, sourceBridgeFactorCoeff]
  | succ r =>
      cases r with
      | zero =>
          have hmw := markedWeight_succ_eq_sPower_sub μ 0
          have hN := N_sub_sPower_zero_eq_sum μ
          have hN' : (N μ : ℚ) = (μ.sum : ℚ) + sPower μ 0 := by
            linarith
          simp [sourceFactorCoeff, markedFactorCoeff, sourceBridgeFactorCoeff,
            markedCoeff, phiCoeff, hmw, hN']
          ring
      | succ r =>
          have hmw := markedWeight_succ_eq_sPower_sub μ (r + 1)
          simp [sourceFactorCoeff, markedFactorCoeff, sourceBridgeFactorCoeff,
            markedCoeff, phiCoeff, hCoeff, hmw]
          ring

private theorem markedFactorCoeff_sum_eq_markedProxy
    (lead : ℚ) (μ : List Nat) (a : Nat) :
    (∑ r ∈ Finset.range (a + 1),
        markedFactorCoeff lead μ r * Prop51.bCoeff μ (a - r))
      = markedProxyCoeff lead μ a := by
  rw [Finset.sum_range_succ']
  simp [markedFactorCoeff, markedProxyCoeff, markedConvolution,
    Prop51.list_range_map_sum]
  ring

private theorem hCoeff_bCoeff_recurrence (μ : List Nat) :
    ∀ n : Nat,
      (∑ t ∈ Finset.range n,
          ((t + 1 : Nat) : ℚ) * hCoeff μ (t + 1) *
            Prop51.bCoeff μ (n - (t + 1)))
        = -((n : ℚ) * Prop51.bCoeff μ n)
  | 0 => by
      simp
  | n + 1 => by
      let L : Nat → ℚ := fun r => -hCoeff μ r
      have hrec := Prop51.expCoeff_succ_mul L n
      have hrec_b :
          ((n + 1 : Nat) : ℚ) * Prop51.bCoeff μ (n + 1)
            =
          ∑ t ∈ Finset.range (n + 1),
            ((t + 1 : Nat) : ℚ) * (-hCoeff μ (t + 1)) *
              Prop51.bCoeff μ (n - t) := by
        simpa [L, fCoeff, bCoeff_eq_fCoeff] using hrec
      have hneg :
          (∑ t ∈ Finset.range (n + 1),
            ((t + 1 : Nat) : ℚ) * (-hCoeff μ (t + 1)) *
              Prop51.bCoeff μ (n - t))
            =
          - (∑ t ∈ Finset.range (n + 1),
            ((t + 1 : Nat) : ℚ) * hCoeff μ (t + 1) *
              Prop51.bCoeff μ (n - t)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun t ht => ?_
        ring
      rw [hneg] at hrec_b
      have htarget :
          (∑ t ∈ Finset.range (n + 1),
              ((t + 1 : Nat) : ℚ) * hCoeff μ (t + 1) *
                Prop51.bCoeff μ (n - t))
            = -(((n + 1 : Nat) : ℚ) * Prop51.bCoeff μ (n + 1)) := by
        linarith
      simpa [Nat.succ_sub_succ_eq_sub, neg_mul] using htarget

private theorem sourceBridgeFactorCoeff_convolution
    (μ : List Nat) {a : Nat} (ha : 1 ≤ a) :
    (∑ r ∈ Finset.range (a + 1),
        sourceBridgeFactorCoeff μ r * Prop51.bCoeff μ (a - r))
      =
        (12 * ((a : ℚ) - 1) - 2 * (μ.sum : ℚ)) *
          Prop51.bCoeff μ (a - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n : Nat, a = n + 1 := ⟨a - 1, by omega⟩
  rw [Finset.sum_range_succ']
  simp only [sourceBridgeFactorCoeff, zero_mul, add_zero]
  rw [Finset.sum_range_succ']
  have htail :
      (∑ t ∈ Finset.range n,
          (-12 * ((t + 1 : Nat) : ℚ) * hCoeff μ (t + 1)) *
            Prop51.bCoeff μ (n + 1 - (t + 2)))
        =
      12 * (n : ℚ) * Prop51.bCoeff μ n := by
    have hrec := hCoeff_bCoeff_recurrence μ n
    calc
      (∑ t ∈ Finset.range n,
          (-12 * ((t + 1 : Nat) : ℚ) * hCoeff μ (t + 1)) *
            Prop51.bCoeff μ (n + 1 - (t + 2)))
          =
        -12 *
          (∑ t ∈ Finset.range n,
            ((t + 1 : Nat) : ℚ) * hCoeff μ (t + 1) *
              Prop51.bCoeff μ (n - (t + 1))) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun t ht => ?_
            have htlt : t < n := Finset.mem_range.mp ht
            have hsub : n + 1 - (t + 2) = n - (t + 1) := by omega
            rw [hsub]
            ring
      _ = 12 * (n : ℚ) * Prop51.bCoeff μ n := by
            rw [hrec]
            ring
  rw [htail]
  simp
  ring

/-- General source--marked bridge.

For any list `μ`, leading constant `lead`, and degree `a >= 1`, the source
coefficient equals the marked coefficient plus the single recurrence correction
shown here.  This is the formal version of the paper's source--marked bridge. -/
theorem sourceCoeff_sub_marked (lead : ℚ) (μ : List Nat) {a : Nat} (ha : 1 ≤ a) :
    sourceCoeff lead μ a =
      lead * Prop51.bCoeff μ a - markedConvolution μ a
        + (12 * ((a : ℚ) - 1) - 2 * (μ.sum : ℚ)) *
          Prop51.bCoeff μ (a - 1) := by
  unfold sourceCoeff
  calc
    (∑ r ∈ Finset.range (a + 1),
        sourceFactorCoeff lead μ r * Prop51.bCoeff μ (a - r))
        =
      (∑ r ∈ Finset.range (a + 1),
        (markedFactorCoeff lead μ r + sourceBridgeFactorCoeff μ r) *
          Prop51.bCoeff μ (a - r)) := by
          refine Finset.sum_congr rfl fun r hr => ?_
          rw [sourceFactorCoeff_eq_marked_add_bridge]
    _ =
      (∑ r ∈ Finset.range (a + 1),
        markedFactorCoeff lead μ r * Prop51.bCoeff μ (a - r))
        +
      (∑ r ∈ Finset.range (a + 1),
        sourceBridgeFactorCoeff μ r * Prop51.bCoeff μ (a - r)) := by
          simp [add_mul, Finset.sum_add_distrib]
    _ = markedProxyCoeff lead μ a
        + (12 * ((a : ℚ) - 1) - 2 * (μ.sum : ℚ)) *
          Prop51.bCoeff μ (a - 1) := by
          rw [markedFactorCoeff_sum_eq_markedProxy,
            sourceBridgeFactorCoeff_convolution μ ha]
    _ =
      lead * Prop51.bCoeff μ a - markedConvolution μ a
        + (12 * ((a : ℚ) - 1) - 2 * (μ.sum : ℚ)) *
          Prop51.bCoeff μ (a - 1) := by
          rfl

/-- For positive partitions of `M a`, the source coefficient with leading term
`M a` is exactly the corrected marked coefficient in degree `a`. -/
theorem sourceCorrectedCoeff_eq {a : Nat} (ha : 1 ≤ a) {μ : List Nat}
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    sourceCoeff (M a) μ a = correctedCoeff a μ := by
  obtain ⟨hsum, _hpos⟩ := hμ
  rw [sourceCoeff_sub_marked (lead := (M a : ℚ)) (μ := μ) ha]
  unfold correctedCoeff
  have hM : (M a : ℚ) = 6 * (a : ℚ) - 6 := by
    unfold M
    rw [Nat.cast_sub (by omega : 6 ≤ 6 * a)]
    norm_num
  have hsumq : (μ.sum : ℚ) = (M a : ℚ) := by exact_mod_cast hsum
  have hcorr :
      12 * ((a : ℚ) - 1) - 2 * (μ.sum : ℚ) = 0 := by
    rw [hsumq, hM]
    ring
  rw [hcorr]
  ring

/-- The printed source coefficient also agrees with the printed marked
coefficient in degree `a` when `μ` partitions `M a`.  The same bridge correction
vanishes because `M a = μ.sum = 6a - 6`. -/
theorem sourcePrintedCoeff_eq {a : Nat} (ha : 1 ≤ a) {μ : List Nat}
    (hμ : Prop51.IsPartitionOf μ (M a)) :
    sourceCoeff 1 μ a = printedCoeff μ a := by
  obtain ⟨hsum, _hpos⟩ := hμ
  rw [sourceCoeff_sub_marked (lead := (1 : ℚ)) (μ := μ) ha]
  unfold printedCoeff
  have hM : (M a : ℚ) = 6 * (a : ℚ) - 6 := by
    unfold M
    rw [Nat.cast_sub (by omega : 6 ≤ 6 * a)]
    norm_num
  have hsumq : (μ.sum : ℚ) = (M a : ℚ) := by exact_mod_cast hsum
  have hcorr :
      12 * ((a : ℚ) - 1) - 2 * (μ.sum : ℚ) = 0 := by
    rw [hsumq, hM]
    ring
  rw [hcorr]
  ring

/-- Source-shaped corrected Proposition 5.2: non-vanishing. -/
theorem sourceCorrectedCoeff_nonvanishing :
    ∀ a : Nat, 2 ≤ a →
      ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
        sourceCoeff (M a) μ a ≠ 0 := by
  intro a ha μ hμ
  rw [sourceCorrectedCoeff_eq (a := a) (ha := by omega) hμ]
  exact correctedCoeff_nonvanishing a ha μ hμ

/-- Source-shaped corrected Proposition 5.2: strict negativity for `a >= 14`. -/
theorem sourceCorrectedCoeff_neg {a : Nat} (ha : 14 ≤ a)
    {μ : List Nat} (hμ : Prop51.IsPartitionOf μ (M a)) :
    sourceCoeff (M a) μ a < 0 := by
  rw [sourceCorrectedCoeff_eq (a := a) (ha := by omega) hμ]
  exact correctedCoeff_neg ha hμ

/-! ## Executable checks for the smallest corrected example

For `g = 4` (`a = 2`) and `μ = (1^6)`, the corrected note records
`[t^2]B_μ = -195/8`, printed coefficient `45/8`, corrected coefficient
`-465/4`; the final two checks verify that the source coefficient has the same
degree-two value as the corrected marked coefficient. -/

example : Prop51.bCoeff [1, 1, 1, 1, 1, 1] 2 = -195 / 8 := by native_decide

example : printedCoeff [1, 1, 1, 1, 1, 1] 2 = 45 / 8 := by native_decide

example : correctedCoeff 2 [1, 1, 1, 1, 1, 1] = -465 / 4 := by native_decide

example : sourceCoeff (M 2) [1, 1, 1, 1, 1, 1] 2 = -465 / 4 := by
  native_decide

example :
    sourceCoeff (M 2) [1, 1, 1, 1, 1, 1] 2 =
      correctedCoeff 2 [1, 1, 1, 1, 1, 1] := by
  native_decide

end Prop52
