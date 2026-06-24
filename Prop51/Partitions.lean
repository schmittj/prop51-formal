/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Partition enumeration

A standard descending-parts partition generator, used by the small-genus
certificate (`Prop51/CertificateSmall.lean`).  The small-genus certificates use
only the *membership* direction (`mem_partitions_iff`, since they quantify over
the generated list); the converse *completeness* of the generator — every
weakly-decreasing positive list summing to `n` occurs — is proved in
`Prop51/PartitionsComplete.lean` and is what lifts the certificates to the
arbitrary-partition public theorems.  The cardinality cross-checks below tie the
generator to the known partition numbers p(n).
-/

namespace Prop51

/-- Partitions of `n` into parts of size at most `p`, as weakly decreasing
lists of positive parts. -/
def partitionsLe : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | (_+1), 0 => []
  | (n+1), (p+1) =>
    (if p + 1 ≤ n + 1 then
      (partitionsLe (n+1-(p+1)) (p+1)).map (fun μ => (p+1) :: μ)
    else []) ++ partitionsLe (n+1) p
  termination_by n p => (n, p)
  decreasing_by
    · exact Prod.Lex.left _ _ (by omega)
    · exact Prod.Lex.right _ (by omega)

/-- All partitions of `n` (weakly decreasing lists of positive parts). -/
def partitions (n : Nat) : List (List Nat) := partitionsLe n n

example : partitions 2 = [[2], [1, 1]] := by native_decide
example : partitions 4 = [[4], [3,1], [2,2], [2,1,1], [1,1,1,1]] := by
  native_decide

end Prop51
