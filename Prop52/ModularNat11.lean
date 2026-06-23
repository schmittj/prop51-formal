/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Fast Nat-residue certificates for corrected Proposition 5.2, `a = 11`

The certificates in this file are chunked so that each `native_decide` proof has
a bounded evaluation cost and can be cached independently of the `a = 9,10`
certificates in `Prop52.ModularNat`.
-/

import Prop52.ModularNat
import Mathlib.Tactic.IntervalCases

namespace Prop52

/-- Fast Nat-residue certificate for the first `a = 11` chunk. -/
theorem checkGeneratedModNat_11_prime1_chunk_0 :
    checkGeneratedModNatChunk finitePrime1 11 0 50000 = true := by
  native_decide

theorem checkGeneratedModNat_11_prime1_chunk_1 :
    checkGeneratedModNatChunk finitePrime1 11 50000 50000 = true := by
  native_decide

theorem checkGeneratedModNat_11_prime1_chunk_2 :
    checkGeneratedModNatChunk finitePrime1 11 100000 50000 = true := by
  native_decide

theorem checkGeneratedModNat_11_prime1_chunk_3 :
    checkGeneratedModNatChunk finitePrime1 11 150000 50000 = true := by
  native_decide

theorem checkGeneratedModNat_11_prime1_chunk_4 :
    checkGeneratedModNatChunk finitePrime1 11 200000 50000 = true := by
  native_decide

theorem checkGeneratedModNat_11_prime1_chunk_5 :
    checkGeneratedModNatChunk finitePrime1 11 250000 50000 = true := by
  native_decide

theorem checkGeneratedModNat_11_prime1_chunk_6 :
    checkGeneratedModNatChunk finitePrime1 11 300000 50000 = true := by
  native_decide

theorem checkGeneratedModNat_11_prime1_chunk_7 :
    checkGeneratedModNatChunk finitePrime1 11 350000 50000 = true := by
  native_decide

theorem checkGeneratedModNat_11_prime1_chunk_8 :
    checkGeneratedModNatChunk finitePrime1 11 400000 50000 = true := by
  native_decide

theorem checkGeneratedModNat_11_prime1_chunk_9 :
    checkGeneratedModNatChunk finitePrime1 11 450000 50000 = true := by
  native_decide

theorem checkGeneratedModNat_11_prime1_chunk_10 :
    checkGeneratedModNatChunk finitePrime1 11 500000 50000 = true := by
  native_decide

theorem checkGeneratedModNat_11_prime1_chunk_11 :
    checkGeneratedModNatChunk finitePrime1 11 550000 50000 = true := by
  native_decide

theorem checkGeneratedModNat_11_prime1_chunk_12 :
    checkGeneratedModNatChunk finitePrime1 11 600000 50000 = true := by
  native_decide

theorem checkGeneratedModNat_11_prime1_chunk_13 :
    checkGeneratedModNatChunk finitePrime1 11 650000 50000 = true := by
  native_decide

theorem checkGeneratedModNat_11_prime1_chunk_14 :
    checkGeneratedModNatChunk finitePrime1 11 700000 50000 = true := by
  native_decide

theorem checkGeneratedModNat_11_prime1_chunk_15 :
    checkGeneratedModNatChunk finitePrime1 11 750000 50000 = true := by
  native_decide

theorem checkGeneratedModNat_11_prime1_chunk_16 :
    checkGeneratedModNatChunk finitePrime1 11 800000 50000 = true := by
  native_decide

theorem checkGeneratedModNat_11_prime1_chunk_17 :
    checkGeneratedModNatChunk finitePrime1 11 850000 50000 = true := by
  native_decide

theorem checkGeneratedModNat_11_prime1_chunk_18 :
    checkGeneratedModNatChunk finitePrime1 11 900000 50000 = true := by
  native_decide

/-- Final `a = 11` chunk.  The generated list has fewer than one million
entries; this covers the tail after index `950000`. -/
theorem checkGeneratedModNat_11_prime1_chunk_19 :
    checkGeneratedModNatChunk finitePrime1 11 950000 50000 = true := by
  native_decide

/-- The chunk certificates cover all indices used for the `a = 11` scan. -/
theorem checkGeneratedModNat_11_prime1_chunks
    (j : Nat) (hj : j < 20) :
    checkGeneratedModNatChunk finitePrime1 11 (j * 50000) 50000 = true := by
  interval_cases j <;>
    simp [checkGeneratedModNat_11_prime1_chunk_0,
      checkGeneratedModNat_11_prime1_chunk_1,
      checkGeneratedModNat_11_prime1_chunk_2,
      checkGeneratedModNat_11_prime1_chunk_3,
      checkGeneratedModNat_11_prime1_chunk_4,
      checkGeneratedModNat_11_prime1_chunk_5,
      checkGeneratedModNat_11_prime1_chunk_6,
      checkGeneratedModNat_11_prime1_chunk_7,
      checkGeneratedModNat_11_prime1_chunk_8,
      checkGeneratedModNat_11_prime1_chunk_9,
      checkGeneratedModNat_11_prime1_chunk_10,
      checkGeneratedModNat_11_prime1_chunk_11,
      checkGeneratedModNat_11_prime1_chunk_12,
      checkGeneratedModNat_11_prime1_chunk_13,
      checkGeneratedModNat_11_prime1_chunk_14,
      checkGeneratedModNat_11_prime1_chunk_15,
      checkGeneratedModNat_11_prime1_chunk_16,
      checkGeneratedModNat_11_prime1_chunk_17,
      checkGeneratedModNat_11_prime1_chunk_18,
      checkGeneratedModNat_11_prime1_chunk_19]

end Prop52
