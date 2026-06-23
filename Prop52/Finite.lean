/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Exact finite checks for corrected Proposition 5.2

This module starts the corrected finite range by checking the exact rational
recurrence for `2 <= a <= 8`, the range independently spot-checked in the
Prop52 bundle.  The remaining finite degrees `9 <= a <= 13` are larger and
will use either a scaled exact check or the modular-certificate bridge.
-/

import Prop52.Theorem
import Prop51.PartitionsComplete

namespace Prop52

/-! ## Permutation invariance -/

theorem markedWeight_perm {μ ν : List Nat} (h : μ.Perm ν) (r : Nat) :
    markedWeight μ r = markedWeight ν r :=
  (h.map _).sum_eq

theorem markedCoeff_perm {μ ν : List Nat} (h : μ.Perm ν) (r : Nat) :
    markedCoeff μ r = markedCoeff ν r := by
  simp [markedCoeff, markedWeight_perm h r]

theorem markedConvolution_perm {μ ν : List Nat} (h : μ.Perm ν) (a : Nat) :
    markedConvolution μ a = markedConvolution ν a := by
  unfold markedConvolution
  congr 1
  refine List.map_congr_left fun k _hk => ?_
  rw [markedCoeff_perm h, Prop51.bCoeff_perm h]

theorem printedCoeff_perm {μ ν : List Nat} (h : μ.Perm ν) (a : Nat) :
    printedCoeff μ a = printedCoeff ν a := by
  simp [printedCoeff, Prop51.bCoeff_perm h, markedConvolution_perm h]

theorem correctedCoeff_perm {μ ν : List Nat} (h : μ.Perm ν) (a : Nat) :
    correctedCoeff a μ = correctedCoeff a ν := by
  simp [correctedCoeff, Prop51.bCoeff_perm h, markedConvolution_perm h]

/-! ## Exact generated-partition check through `a = 8` -/

/-- Exact rational nonvanishing for every generated partition in the range
`2 <= a <= 8`. -/
theorem correctedCoeff_ne_2_8_generated :
    ∀ a : Nat, 2 ≤ a → a ≤ 8 →
      ∀ μ ∈ Prop51.partitions (M a), correctedCoeff a μ ≠ 0 := by
  native_decide

/-- Predicate-form exact rational nonvanishing for `2 <= a <= 8`, upgraded
from the generated weakly-decreasing partitions by generator completeness and
permutation invariance. -/
theorem correctedCoeff_ne_2_8 :
    ∀ a : Nat, 2 ≤ a → a ≤ 8 →
      ∀ μ : List Nat, Prop51.IsPartitionOf μ (M a) →
        correctedCoeff a μ ≠ 0 := by
  intro a ha h8 μ hμ
  obtain ⟨hsum, hpos⟩ := hμ
  obtain ⟨μ', hperm, hpair⟩ := Prop51.exists_sorted_perm μ
  have hmem : μ' ∈ Prop51.partitions (M a) := by
    rw [Prop51.mem_partitions_iff]
    refine ⟨by rw [← hperm.sum_eq]; exact hsum, hpair, ?_⟩
    exact fun x hx => hpos x (hperm.mem_iff.mpr hx)
  rw [correctedCoeff_perm hperm]
  exact correctedCoeff_ne_2_8_generated a ha h8 μ' hmem

end Prop52
