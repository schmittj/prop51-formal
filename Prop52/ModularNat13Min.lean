/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Fast Nat-residue certificates for corrected Proposition 5.2, `a = 13`

This shard checks first parts `1 <= first <= 2`.
-/

import Prop52.ModularNat

namespace Prop52

theorem checkGeneratedModNat_13_prime1_firstPartRange_1_2 :
    checkGeneratedModNatFirstPartRange finitePrime1 13 1 2 = true := by
  native_decide

end Prop52
