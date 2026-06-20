/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Public statement of the Chen--Larson coefficient theorem

This file contains only the definitions needed to state the final theorem.
The coefficient `bCoeff` itself is defined in `Prop51.Defs`; the official
power-series characterization is exposed in `Prop51.Theorem`.
-/

import Prop51.Defs

namespace Prop51

/-- `μ` is a positive partition of `n`: a list of positive parts summing to
`n`.  Order is irrelevant to `bCoeff`, which only uses the multiset of parts;
we do not impose sortedness. -/
def IsPartitionOf (μ : List Nat) (n : Nat) : Prop :=
  μ.sum = n ∧ ∀ m ∈ μ, 1 ≤ m

/-- Negativity of the Chen--Larson Proposition 5.1 coefficient for all
relevant genera and all positive partitions. -/
def CoefficientNegativity : Prop :=
  ∀ g : Nat, 2 ≤ g → g % 3 ≠ 1 →
    ∀ μ : List Nat, IsPartitionOf μ (2*g - 2) →
      bCoeff μ (g/3 + 1) < 0

end Prop51
