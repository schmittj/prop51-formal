/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Fast Nat-residue certificates for corrected Proposition 5.2, `a = 11`

The certificates in this file are chunked so that each `native_decide` proof has
a bounded evaluation cost and can be cached independently of the `a = 9,10`
certificates in `Prop52.ModularNat`.
-/

import Prop52.ModularNat

namespace Prop52

/-- Fast Nat-residue certificate for the first `a = 11` chunk. -/
theorem checkGeneratedModNat_11_prime1_chunk_0 :
    checkGeneratedModNatChunk finitePrime1 11 0 50000 = true := by
  native_decide

end Prop52
