/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# The assembled interval certificate: `61 ≤ a ≤ 400`

Combines the eight `native_decide` chunks
(`Prop51/CertificateInterval1.lean` … `…8.lean`) with the soundness theorem
`checkRange_sound` of `Prop51/IntervalCert.lean` into the Layer B
certificate: the normalized majorant `Unorm a N` is negative on the whole
rectangle `61 ≤ a ≤ 400`, `6a-7 ≤ N ≤ 12a-8` (i.e. `359 ≤ N ≤ 4792`;
480,984 − 10,764 = 470,220 pairs beyond the exact certificate).

Together with `unorm_neg_9_60` (`Prop51/CertificateExact.lean`) this gives
`Unorm a N < 0` on the full certified range `9 ≤ a ≤ 400`.
-/

import Prop51.IntervalCert
import Prop51.CertificateExact
import Prop51.CertificateInterval1
import Prop51.CertificateInterval2
import Prop51.CertificateInterval3
import Prop51.CertificateInterval4
import Prop51.CertificateInterval5
import Prop51.CertificateInterval6
import Prop51.CertificateInterval7
import Prop51.CertificateInterval8

namespace Prop51

/-- **The Layer B interval certificate**: the normalized majorant is
negative for every `61 ≤ a ≤ 400` and every `N` in the rectangle
`6a-7 ≤ N ≤ 12a-8`. -/
theorem unorm_neg_61_400 :
    ∀ a, 61 ≤ a → a ≤ 400 → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 →
      Unorm a N < 0 := by
  intro a h61 h400 N hlo hhi
  have h359 : 359 ≤ N := by omega
  have h4792 : N ≤ 4792 := by omega
  rcases Nat.lt_or_ge N 1846 with h | h
  · exact checkRange_sound 359 1487 checkRange_chunk1 a N h61 h400 hlo hhi
      (by omega) (by omega)
  rcases Nat.lt_or_ge N 2324 with h2 | h2
  · exact checkRange_sound 1846 478 checkRange_chunk2 a N h61 h400 hlo hhi
      (by omega) (by omega)
  rcases Nat.lt_or_ge N 2693 with h3 | h3
  · exact checkRange_sound 2324 369 checkRange_chunk3 a N h61 h400 hlo hhi
      (by omega) (by omega)
  rcases Nat.lt_or_ge N 3072 with h4 | h4
  · exact checkRange_sound 2693 379 checkRange_chunk4 a N h61 h400 hlo hhi
      (by omega) (by omega)
  rcases Nat.lt_or_ge N 3466 with h5 | h5
  · exact checkRange_sound 3072 394 checkRange_chunk5 a N h61 h400 hlo hhi
      (by omega) (by omega)
  rcases Nat.lt_or_ge N 3880 with h6 | h6
  · exact checkRange_sound 3466 414 checkRange_chunk6 a N h61 h400 hlo hhi
      (by omega) (by omega)
  rcases Nat.lt_or_ge N 4320 with h7 | h7
  · exact checkRange_sound 3880 440 checkRange_chunk7 a N h61 h400 hlo hhi
      (by omega) (by omega)
  · exact checkRange_sound 4320 473 checkRange_chunk8 a N h61 h400 hlo hhi
      (by omega) (by omega)

/-- The combined certificate, `9 ≤ a ≤ 400`: exact rationals for
`a ≤ 60` (`unorm_neg_9_60`), verified dyadic intervals beyond. -/
theorem unorm_neg_9_400 :
    ∀ a, 9 ≤ a → a ≤ 400 → ∀ N, 6*a - 7 ≤ N → N ≤ 12*a - 8 →
      Unorm a N < 0 := by
  intro a h9 h400 N hlo hhi
  rcases Nat.lt_or_ge a 61 with h | h
  · exact unorm_neg_9_60 a (by omega) h9 N (by omega) (by omega)
  · exact unorm_neg_61_400 a h h400 N hlo hhi

end Prop51
