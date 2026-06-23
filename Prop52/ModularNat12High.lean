/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Fast Nat-residue certificates for corrected Proposition 5.2, `a = 12`

This shard checks first parts `56 <= first <= 66`.
-/

import Prop52.ModularNat

namespace Prop52

theorem checkGeneratedModNat_12_prime1_firstPartRange_56_11 :
    checkGeneratedModNatFirstPartRange finitePrime1 12 56 11 = true := by
  native_decide

end Prop52
