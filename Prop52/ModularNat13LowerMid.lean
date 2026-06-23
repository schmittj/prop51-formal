/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Fast Nat-residue certificates for corrected Proposition 5.2, `a = 13`

This shard checks first part `19`.
-/

import Prop52.ModularNat

namespace Prop52

theorem checkGeneratedModNat_13_prime1_firstPartRange_19_1 :
    checkGeneratedModNatFirstPartRange finitePrime1 13 19 1 = true := by
  native_decide

end Prop52
