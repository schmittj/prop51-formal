/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Main statements

This file isolates the target theorem of the project and records exactly
what is proved so far.  It deliberately imports only the definition layer and
the finite certificates.

## The target

`CoefficientNegativity` is the full Chen–Larson Proposition 5.1 coefficient
statement (arXiv:2603.23850): for every genus `g ≥ 2` with `g ≡ 0, 2 (mod 3)`
and every positive partition `μ` of `2g - 2`, the coefficient
`b_{⌊g/3⌋+1}(μ)` is negative (in particular nonzero, which is the hypothesis
of Proposition 5.1 there).

## Status

* `coefficientNegativity_of_g_le_1199` : proved — the enumeration (`g ≤ 23`),
  the exact-rational certificate (`9 ≤ a ≤ 60`), the verified dyadic
  interval certificate (`61 ≤ a ≤ 400`, Layer B), and the Layer A majorant
  bridge `b_a(μ) ≤ U_a(N)` (paper eq. 8) together cover every relevant
  genus `g ≤ 1199` and every positive partition.
* `a ≥ 401` (effective analytic bound): not yet formalized — Layer C of the
  roadmap; it would upgrade the capstone to full `CoefficientNegativity`.
-/
import Prop51.Defs
import Prop51.Partitions
import Prop51.CertificateSmall
import Prop51.CertificateExact
import Prop51.PartitionsComplete
import Prop51.Majorant
import Prop51.CertificateInterval
import Prop51.PositiveSaddle

namespace Prop51

/-- `μ` is a positive partition of `n`: a list of positive parts summing to
`n`.  (Order is irrelevant to `bCoeff`, which only uses the multiset of
parts; we do not impose sortedness.) -/
def IsPartitionOf (μ : List Nat) (n : Nat) : Prop :=
  μ.sum = n ∧ ∀ m ∈ μ, 1 ≤ m

/-- **The target statement.**  Negativity of the Chen–Larson Proposition 5.1
coefficient for all relevant genera and all positive partitions.  Proving
this proposition (sorry-free, with the power-series bridge of Layer A) is the
goal of this repository. -/
def CoefficientNegativity : Prop :=
  ∀ g : Nat, 2 ≤ g → g % 3 ≠ 1 →
    ∀ μ : List Nat, IsPartitionOf μ (2*g - 2) →
      bCoeff μ (g/3 + 1) < 0

/-- What is currently machine-checked towards `CoefficientNegativity` for
small genus: every *generated* partition for every relevant `g ≤ 23`.
Upgrading `∀ μ ∈ partitions (2g-2)` to `∀ μ, IsPartitionOf μ (2g-2)` needs
the generator-completeness lemma plus permutation-invariance of `bCoeff`
(ROADMAP, Layer A′). -/
theorem coefficientNegativity_of_g_le_23 :
    ∀ g < 24, 2 ≤ g → g % 3 ≠ 1 →
      ∀ μ ∈ partitions (2*g - 2), bCoeff μ (g/3 + 1) < 0 :=
  bCoeff_neg_g_le_23

/-- **Small-genus case of the target, in full generality**: for every
relevant `g ≤ 23` and *every* positive partition `μ` of `2g-2` (arbitrary
order, arbitrary list representation), the Chen–Larson coefficient is
negative.  Combines the machine-checked enumeration with generator
completeness (`mem_partitions_iff`) and permutation-invariance of `bCoeff`. -/
theorem coefficientNegativity_of_g_le_23' :
    ∀ g < 24, 2 ≤ g → g % 3 ≠ 1 →
      ∀ μ : List Nat, IsPartitionOf μ (2*g - 2) →
        bCoeff μ (g/3 + 1) < 0 := by
  intro g hg h2 hres μ hμ
  obtain ⟨hsum, hpos⟩ := hμ
  obtain ⟨μ', hperm, hpair⟩ := exists_sorted_perm μ
  have hmem : μ' ∈ partitions (2*g - 2) := by
    rw [mem_partitions_iff]
    refine ⟨by rw [← hperm.sum_eq]; exact hsum, hpair, ?_⟩
    exact fun x hx => hpos x (hperm.mem_iff.mpr hx)
  rw [bCoeff_perm hperm]
  exact bCoeff_neg_g_le_23 g hg h2 hres μ' hmem

/-- **The capstone of Layers 0+A**: for every genus `2 ≤ g ≤ 179` with
`g ≡ 0, 2 (mod 3)` and *every* positive partition `μ` of `2g-2`, the
Chen–Larson Proposition 5.1 coefficient is negative.

Combines: the small-genus enumeration (`g ≤ 23`), the exact-rational
majorant certificate (`9 ≤ a ≤ 60`, i.e. `24 ≤ g ≤ 179`), and the majorant
inequality `b_a(μ) ≤ N c_a · Unorm a N` of `Prop51.Majorant`.  The
quantification over `μ` is the honest predicate form (`IsPartitionOf`). -/
theorem coefficientNegativity_of_g_le_179 :
    ∀ g, 2 ≤ g → g ≤ 179 → g % 3 ≠ 1 →
      ∀ μ : List Nat, IsPartitionOf μ (2*g - 2) →
        bCoeff μ (g/3 + 1) < 0 := by
  intro g h2 h179 hres μ hμp
  obtain ⟨hsum, hpos⟩ := hμp
  rcases Nat.lt_or_ge g 24 with hg | hg
  · exact coefficientNegativity_of_g_le_23' g hg h2 hres μ ⟨hsum, hpos⟩
  · have hmap := sum_map_add_one μ
    have hlen := length_le_sum μ hpos
    have hne : 1 ≤ μ.length := by
      rcases μ with - | ⟨x, l⟩
      · exfalso; simp at hsum; omega
      · simp
    have hNval : (μ.map (· + 1)).sum = (2*g - 2) + μ.length := by
      rw [hmap, hsum]
    refine bCoeff_neg_of_unorm μ (g/3 + 1) ((μ.map (· + 1)).sum)
      hpos rfl (by omega) (by omega) ?_
    exact unorm_neg_9_60 (g/3 + 1) (by omega) (by omega)
      ((μ.map (· + 1)).sum) (by omega) (by omega)

/-- **The capstone of Layers 0+A+B**: for every genus `2 ≤ g ≤ 1199` with
`g ≡ 0, 2 (mod 3)` and *every* positive partition `μ` of `2g-2`, the
Chen–Larson Proposition 5.1 coefficient is negative.

Extends `coefficientNegativity_of_g_le_179` with the verified dyadic
interval certificate `unorm_neg_61_400` (`61 ≤ a ≤ 400`, i.e.
`180 ≤ g ≤ 1199`); the partition-to-rectangle bookkeeping
(`N = 2g-2+n`, `6a-7 ≤ N ≤ 12a-8`) is the same `omega` argument. -/
theorem coefficientNegativity_of_g_le_1199 :
    ∀ g, 2 ≤ g → g ≤ 1199 → g % 3 ≠ 1 →
      ∀ μ : List Nat, IsPartitionOf μ (2*g - 2) →
        bCoeff μ (g/3 + 1) < 0 := by
  intro g h2 h1199 hres μ hμp
  rcases Nat.lt_or_ge g 180 with hg | hg
  · exact coefficientNegativity_of_g_le_179 g h2 (by omega) hres μ hμp
  · obtain ⟨hsum, hpos⟩ := hμp
    have hmap := sum_map_add_one μ
    have hlen := length_le_sum μ hpos
    have hne : 1 ≤ μ.length := by
      rcases μ with - | ⟨x, l⟩
      · exfalso; simp at hsum; omega
      · simp
    have hNval : (μ.map (· + 1)).sum = (2*g - 2) + μ.length := by
      rw [hmap, hsum]
    refine bCoeff_neg_of_unorm μ (g/3 + 1) ((μ.map (· + 1)).sum)
      hpos rfl (by omega) (by omega) ?_
    exact unorm_neg_61_400 (g/3 + 1) (by omega) (by omega)
      ((μ.map (· + 1)).sum) (by omega) (by omega)

/-- Conditional large-genus capstone: once Layer C proves `Unorm a N < 0`
throughout the post-certificate rectangle `a ≥ 401`, the Chen–Larson
coefficient is negative for every relevant `g ≥ 1200`. -/
theorem coefficientNegativity_of_g_ge_1200_of_unorm_tail
    (htail :
      ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0) :
    ∀ g, 1200 ≤ g → g % 3 ≠ 1 →
      ∀ μ : List Nat, IsPartitionOf μ (2*g - 2) →
        bCoeff μ (g/3 + 1) < 0 := by
  intro g hg1200 hres μ hμp
  obtain ⟨hsum, hpos⟩ := hμp
  have hmap := sum_map_add_one μ
  have hlen := length_le_sum μ hpos
  have hne : 1 ≤ μ.length := by
    rcases μ with - | ⟨x, l⟩
    · exfalso; simp at hsum; omega
    · simp
  have hNval : (μ.map (· + 1)).sum = (2*g - 2) + μ.length := by
    rw [hmap, hsum]
  refine bCoeff_neg_of_unorm μ (g/3 + 1) ((μ.map (· + 1)).sum)
    hpos rfl (by omega) (by omega) ?_
  exact htail (g/3 + 1) (by omega) ((μ.map (· + 1)).sum)
    (by omega) (by omega)

/-- Conditional final theorem: the only remaining input is the large-`a`
majorant negativity statement. -/
theorem coefficientNegativity_of_unorm_tail
    (htail :
      ∀ a, 401 ≤ a → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0) :
    CoefficientNegativity := by
  intro g h2 hres μ hμp
  rcases Nat.lt_or_ge g 1200 with hg | hg
  · exact coefficientNegativity_of_g_le_1199 g h2 (by omega) hres μ hμp
  · exact coefficientNegativity_of_g_ge_1200_of_unorm_tail htail
      g hg hres μ hμp

/-- Final assembly from the packaged §6 positive-saddle certificate. -/
theorem coefficientNegativity_of_positiveSaddleCertificate
    {soloBound : Nat → ℚ} (cert : PositiveSaddleCertificate soloBound) :
    CoefficientNegativity :=
  coefficientNegativity_of_unorm_tail
    (unorm_tail_of_positiveSaddleCertificate cert)

end Prop51
