/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Interval certificate, chunk 2/8: columns `N ∈ [1846, 2323]`

`native_decide` evaluation of the verified interval checker
(`Prop51/IntervalCert.lean`) on one slice of the `N`-range; the slices are
sized for roughly equal work and combined in
`Prop51/CertificateInterval.lean`.  Trusts the Lean compiler
(`Lean.ofReduceBool`), like the finite certificates of Layer 0.
-/

import Prop51.IntervalCert

namespace Prop51

theorem checkRange_chunk2 : checkRange 1846 478 = true := by native_decide

end Prop51
