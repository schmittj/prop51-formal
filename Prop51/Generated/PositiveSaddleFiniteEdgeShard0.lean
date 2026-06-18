import Prop51.Main

namespace Prop51

/-
Generated finite-window positive-saddle certificate.

This proves only the finite Boolean checks.  Combine it with a
`PositiveSaddleLargeTailAuditCertificate` for the final theorem.
Pass `--final-tail-parts` to target the split large-tail interface.
Pass `--final-tail-bounds-parts` for product/solo bound splits.
Pass `--final-tail-atomic-parts` for the atomic large-tail interface.
Pass `--final-tail-atomic-bounds` for bound-split atomic tails.
Pass `--final-tail-raw-cleared-unit-bounds` for grouped raw-cleared
unit-reserve tails with product/solo bound splits.
Pass `--final-tail-refined-atomic-bounds` for the refined raw-exp
ratio step atoms with product/solo bound splits.
Pass `--final-tail-closed-factorial-block-sum` for the factorial-only
closed block-sum product/solo large-tail interface.
Pass `--final-tail-closed-factorial-split-block-sum` for the
split-final-term factorial-only product/solo block-sum interface.
Pass `--final-tail-closed-factorial-split-block-sum-fast` for the
same split interface with fast rational exponential evaluators.
Pass `--final-tail-closed-factorial-split-block-sum-fast-product-solo-envelope`
when only the product side uses the fast split target and the solo
side is supplied directly as the `(10/7)^a` envelope.
Pass `--final-tail-closed-factorial-split-block-sum-fast-product-solo-ten-sevenths`
when the product side uses the fast split target and the solo side
uses the split-final-term target cleared directly against `(10/7)^a`.
Pass `--final-tail-closed-factorial-split-block-sum-fast-product-solo-ten-sevenths-upper-edge`
for the same route with the solo target supplied only at `N = posNhi a`.
Pass `--final-tail-tempered-raw-exp-ratio-reserve-bounds` after
the small step is filled by Lean's raw-base half certificate.
Pass `--final-tail-tempered-raw-exp-ratio-tempered-reserve-bounds`
after the small first reserve is also filled by Lean.
Pass `--final-tail-tempered-raw-exp-ratio-reserve-envelope-bounds`
to split those reserve atoms through explicit exp envelopes.
Pass `--final-tail-tempered-raw-exp-ratio-tempered-reserve-envelope-bounds`
to split only the remaining tempered reserve atoms.
Pass `--final-tail-tempered-raw-exp-ratio-ten-sevenths-reserve-envelope-bounds`
to use the concrete `(10/7)^a` tempered endpoint envelope.
Pass `--final-tail-tempered-raw-exp-ratio-ten-sevenths-closed-reserve-bounds`
after the concrete `(10/7)^a` endpoint reserve budgets are closed.
Pass `--final-tail-tempered-raw-exp-ratio-ten-sevenths-closed-reserve-solo-envelope-bounds`
after the concrete endpoint reserves and solo scalar budget are closed.
Pass `--final-tail-tempered-raw-exp-crossmul-tempered-reserve-bounds`
for denominator-cleared tempered step atoms and direct reserve atoms.
Pass `--final-tail-tempered-raw-exp-crossmul-tempered-reserve-envelope-bounds`
for denominator-cleared tempered step atoms and reserve envelopes.
Pass `--final-tail-tempered-raw-exp-crossmul-ten-sevenths-reserve-envelope-bounds`
for denominator-cleared tempered step atoms and concrete `(10/7)^a`
endpoint reserve budgets.
Pass `--final-tail-tempered-raw-exp-crossmul-ten-sevenths-closed-reserve-bounds`
after the concrete `(10/7)^a` endpoint reserves are closed.
Pass `--final-tail-tempered-raw-exp-crossmul-ten-sevenths-closed-reserve-solo-envelope-bounds`
after the concrete endpoint reserves and solo scalar budget are closed.
Pass `--final-tail-tempered-sharp-top-offset-exp-target-tempered-reserve-bounds`
for the ten-offset lower sharp top-strip exp target, upper reverse
exp target, and direct tempered reserve atoms.
Pass `--final-tail-tempered-sharp-top-offset-exp-target-tempered-reserve-envelope-bounds`
for those exp targets and reserve envelopes.
Pass `--final-tail-tempered-sharp-top-offset-exp-target-ten-sevenths-reserve-envelope-bounds`
for those exp targets and concrete `(10/7)^a` endpoint reserves.
Pass `--final-tail-tempered-sharp-top-offset-exp-target-ten-sevenths-closed-reserve-bounds`
after the concrete endpoint reserves are closed for those exp targets.
Pass `--final-tail-tempered-sharp-top-offset-exp-target-ten-sevenths-closed-reserve-solo-envelope-bounds`
after the endpoint reserves and solo scalar budget are closed for
those exp targets.
Pass `--final-tail-tempered-sharp-top-offset-upper-middle-exp-target-tempered-reserve-bounds`
or its envelope, concrete `(10/7)^a`, closed-reserve, or solo-envelope
variants when the upper reverse exp target only covers the middle band.
Pass `--final-tail-tempered-sharp-top-offset-hybrid-raw-exp-upper-middle-exp-target-ten-sevenths-closed-reserve-solo-envelope-bounds`
when the lower sharp top strip keeps the raw-exp product combined
on the finite prefix before using the upper-middle route.
Use the `...-hybrid-raw-exp-chunked-upper-middle-...` variant when
that finite prefix is supplied through explicit `(a,t)` chunks.
Use the `...-hybrid-ratio-chunked-upper-middle-...` variant when
the prefix is split into raw-budget and exp-ratio chunk certificates.
Use the `...-hybrid-ratio-chunked-product-bound-solo-bound` variant
when the final product and solo split sums are supplied through
separate rational surrogate-bound hybrid certificates.
Use the `...-hybrid-ratio-chunked-xy-bound-solo-bound` variant
when the final product factors have separate rational surrogate
bounds `xBound` and `yBound` before multiplying in the scalar
budget chunks.
Use the `...-hybrid-ratio-chunked-xy-bound-full-solo-bound-full`
variant when those surrogate bounds and the scalar budgets are both
supplied through finite-prefix Boolean chunks.
-/

/-
Individual finite-window atom shard.
Shard 1 of 8752; balanced by atoms; atoms 0 <= i < 1 out of 8752.
Fields: ['edge-fixed'].
-/

theorem positiveSaddleFiniteEdgeShard_edge_fixed_r0_k0 :
    checkPositiveEdgeMajorantKChunkUnitRowRange
      401 10 1 20
      (fun _ => positiveEdgeFixedKScaleUpTo 20 (posKmax 411)) = true := by
  exact
    checkPositiveEdgeMajorantKChunkUnitRowRange_of_checkPositiveEdgeMajorantKChunkUnitRowRangeFast
      (by native_decide)

end Prop51
