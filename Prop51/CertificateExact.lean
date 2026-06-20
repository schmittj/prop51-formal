/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Exact majorant certificate: `U_a(N) < 0` for `9 ≤ a ≤ 60`

Machine-checked exact-rational negativity of the normalized partition-free
majorant `Unorm a N = U_a(N)/(N c_a)` on the full rectangle
`9 ≤ a ≤ 60`, `6a-7 ≤ N ≤ 12a-8` — all 10,764 pairs.  This reproduces, inside
Lean, the exact certificate layer of the paper (`paper/prop51.tex`, finite
verification §4), and via
the majorant inequality (paper eq. 8, Layer A of the roadmap) covers every
positive partition for all relevant `9 ≤ a ≤ 60`, i.e. all `24 ≤ g ≤ 179`
with `g ≡ 0, 2 (mod 3)`.

The corner theorem pins the *exact rational value* at the least-negative pair
`(a, N) = (9, 100)`, matching the paper and the independent Arb certificate
enclosure.

Trust note: `native_decide` adds the axiom `Lean.ofReduceBool`.
-/
import Prop51.Defs

namespace Prop51

/-- The least-negative corner of the certified rectangle, as an exact
rational: `U_9(100)/(100 c_9) = -13391635371339739/213818836571652096
≈ -0.0626`. -/
theorem unorm_corner_9_100 :
    Unorm 9 100 = -(13391635371339739 : ℚ) / 213818836571652096 := by
  native_decide

/-- Exact-rational negativity of the majorant on the full rectangle
`9 ≤ a ≤ 60`, `6a-7 ≤ N ≤ 12a-8` (10,764 pairs). -/
theorem unorm_neg_9_60 :
    ∀ a < 61, 9 ≤ a → ∀ N < 12*a - 7, 6*a - 7 ≤ N → Unorm a N < 0 := by
  native_decide

end Prop51
