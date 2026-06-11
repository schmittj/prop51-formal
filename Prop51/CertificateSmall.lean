/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Small-genus certificate: `b_a(μ) < 0` for all `g ≤ 23`, `g ≡ 0,2 (mod 3)`

These are the genera with `a = ⌊g/3⌋ + 1 ≤ 8`, where the partition-free
majorant is too weak and the paper (tenth revision, §7/§8) enumerates the
finitely many partitions instead.  This file machine-checks that enumeration:
about 150,000 partitions in total, the largest case being the 75,175
partitions of 44 (g = 23).

The cardinality theorems cross-check the generator against the known
partition numbers p(2g-2), matching the table in the paper and OEIS A000041.

Trust note: `native_decide` adds the axiom `Lean.ofReduceBool` (it evaluates
via the compiler).  See `scripts/AxiomsReport.lean` and README §Trust.
-/
import Prop51.Defs
import Prop51.Partitions

namespace Prop51

/-- The Chen–Larson coefficient is negative for every positive partition in
every relevant genus `g ≤ 23` (residues `g ≡ 0, 2 mod 3`, `a = g/3 + 1 ≤ 8`).
This is Theorem 8.1 of the paper restricted to `a ≤ 8`, with partitions
ranging over the generator. -/
theorem bCoeff_neg_g_le_23 :
    ∀ g < 24, 2 ≤ g → g % 3 ≠ 1 →
      ∀ μ ∈ partitions (2*g - 2), bCoeff μ (g/3 + 1) < 0 := by
  native_decide

/-- Generator cardinality cross-checks: `p(n)` for the relevant `n = 2g-2`,
matching the paper's table (g = 23: 75175 partitions of 44). -/
theorem partitions_card_checks :
    (partitions 2).length = 2 ∧
    (partitions 10).length = 42 ∧
    (partitions 16).length = 231 ∧
    (partitions 28).length = 3718 ∧
    (partitions 40).length = 37338 ∧
    (partitions 44).length = 75175 := by
  native_decide

/-- Spot anchor from the paper's table: the one-part partition `(2)` of
`g = 2` has `b_1((2)) = -20/9 = -2.22…`. -/
theorem bCoeff_anchor_g2 : bCoeff [2] 1 = -20/9 := by native_decide

end Prop51
