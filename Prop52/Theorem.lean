/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Public facade for the corrected Chen--Larson Proposition 5.2

This file is the human-facing checkpoint for the `g ≡ 1 (mod 3)` case.  It
contains only the final source-shaped theorems.

Notation matched to the paper:

* `Prop51.chenLarsonC` is the hypergeometric series
  `C(t) = Σ_k (6k)! / ((3k)!(2k)! 72^k) t^k`;
* `Prop51.chenLarsonSeries_spec` pins `Prop51.bCoeff μ a` as the coefficient
  `b_a` of the Proposition 5.1 quotient
  `B_μ(t) = ∏_i C(t/(m_i+1)) / C(t)^N`;
* `Prop52.sourceCoeff (M a) μ a` is `[t^a] B_μ(t) * D^cor_μ(t)`, where
  `D^cor_μ` is the corrected source factor of the corrected Proposition 5.2
  identity;
* `M a = 6a - 6`; when `g % 3 = 1` and `a = g / 3 + 1`, this is
  `M a = 2g - 2`;
* `Prop51.IsPartitionOf μ (2 * g - 2)` says that `μ` is a positive partition of
  the geometric degree `2g - 2`;
* the target coefficient degree is `a = g / 3 + 1`.

Thus the theorems below state exactly that the corrected Proposition 5.2 source
coefficient is nonzero for all `g ≥ 2`, `g ≡ 1 (mod 3)`, and is strictly
negative in the large range used by the proof.
-/

import Prop52.Source

namespace Prop52

/-- Corrected Chen--Larson Proposition 5.2 source coefficient: non-vanishing
for every genus `g ≥ 2` with `g ≡ 1 (mod 3)`. -/
theorem chenLarsonProp52Coefficient_nonvanishing
    {g : Nat} (hg : 2 ≤ g) (hmod : g % 3 = 1)
    {μ : List Nat} (hμ : Prop51.IsPartitionOf μ (2 * g - 2)) :
    sourceCoeff (M (g / 3 + 1)) μ (g / 3 + 1) ≠ 0 := by
  have hdecomp : g = 3 * (g / 3) + 1 := by
    have h := Nat.mod_add_div g 3
    omega
  have hM : M (g / 3 + 1) = 2 * g - 2 := by
    simp [M]
    omega
  have ha : 2 ≤ g / 3 + 1 := by
    omega
  have hμ' : Prop51.IsPartitionOf μ (M (g / 3 + 1)) := by
    simpa [hM] using hμ
  exact sourceCorrectedCoeff_nonvanishing (g / 3 + 1) ha μ hμ'

/-- Corrected Chen--Larson Proposition 5.2 source coefficient: strict
negativity in the large range `g ≥ 40`, `g ≡ 1 (mod 3)`. -/
theorem chenLarsonProp52Coefficient_neg
    {g : Nat} (hg : 40 ≤ g) (hmod : g % 3 = 1)
    {μ : List Nat} (hμ : Prop51.IsPartitionOf μ (2 * g - 2)) :
    sourceCoeff (M (g / 3 + 1)) μ (g / 3 + 1) < 0 := by
  have hdecomp : g = 3 * (g / 3) + 1 := by
    have h := Nat.mod_add_div g 3
    omega
  have hM : M (g / 3 + 1) = 2 * g - 2 := by
    simp [M]
    omega
  have ha : 14 ≤ g / 3 + 1 := by
    omega
  have hμ' : Prop51.IsPartitionOf μ (M (g / 3 + 1)) := by
    simpa [hM] using hμ
  exact sourceCorrectedCoeff_neg ha hμ'

end Prop52
