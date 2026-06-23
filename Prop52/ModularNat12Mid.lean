/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Fast Nat-residue certificates for corrected Proposition 5.2, `a = 12`

This shard checks first parts `30 <= first <= 33`.
-/

import Prop52.ModularNat

namespace Prop52

theorem checkGeneratedModNat_12_prime1_firstPartRange_30_4 :
    checkGeneratedModNatFirstPartRange finitePrime1 12 30 4 = true := by
  native_decide

end Prop52
