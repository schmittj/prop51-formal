#!/usr/bin/env python3
"""Emit a Lean template for the fixed finite-window positive-saddle audit.

The generated theorem only proves the finite `401 <= a <= 2000` Boolean
checks.  The large-`a` product/solo and split-tempered reserve inputs are
supplied separately as a `PositiveSaddleLargeTailAuditCertificate`, or as one
of the split large-tail interfaces when requested for the final theorem.

Strategies include:
  * all-chunks: one Boolean per finite family, targeting
    `PositiveSaddleFixedFiniteWindowAllChunksAuditCertificate`;
  * split-fields: dispatch each finite field by fixed row and edge chunk
    indices, targeting `PositiveSaddleFixedFiniteWindowAuditCertificate`.
  * cell-tangent: same fixed product/solo/edge dispatch, but tangent is a
    theorem argument over `checkPositiveSmallTangentExpEdgeCell`.
  * chunked-tangent: product/solo/edge use fixed row chunks, and tangent is
    split by fixed row, `N`, and small-regime `k` chunks.
  * product-n-chunked-tangent: product is additionally split by fixed
    row, uniform product `N`-chunk index, and retained `k` chunk.
  * product-tangent-solo-n-chunked: product, tangent, and displayed-solo
    checks are all split by fixed row and uniform `N`-chunk index.
  * product-nk-tangent-solo-n-chunked: as above, but product checks are also
    split by a separate fixed-width retained-`k` cover.
  * combined-product-nk-tangent-solo-n-chunked: as above, but each product
    atom checks the small/tempered split in one shared-table pass.
  * --emit-single-chunk FIELD: emit one cacheable `native_decide` theorem for
    a concrete product, tangent, solo, or edge chunk.
  * --emit-single-chunk-suite: emit all single-chunk theorems for a concrete
    product-n-chunked-tangent certificate, followed by the assembled finite
    certificate.
  * --emit-single-chunk-shard: emit one balanced shard of the atom theorem
    list, for independent Lean modules in large proof-production runs.
  * --emit-single-chunk-manifest: emit the same atom list as JSON for batch
    proof production; pass --manifest-shard-count to include the balanced
    shard plan in the JSON.
  * --dry-run-counts: emit formula-based atom counts as JSON, without
    materializing the full atom manifest.
  * --use-single-chunk-theorems: assemble the product-n-chunked certificate
    from previously emitted single-chunk theorem names.

Example:
  scripts/positive_saddle_fixed_finite_template.py \
    --product-row-len 1 --tangent-row-len 10 \
    --solo-saddle-row-len 100 --solo-budget-row-len 100 \
    --edge-row-len 10 --n-len 1 \
    --name positiveSaddleFiniteWindow \
    --strategy split-fields

  scripts/positive_saddle_fixed_finite_template.py \
    --product-row-len 1 --solo-saddle-row-len 1 --solo-budget-row-len 1 \
    --edge-row-len 1 --n-len 1 \
    --emit-single-chunk product-small --row-index 0 --n-index 0 --k-index 0
"""

from __future__ import annotations

import argparse
import json
import re
import sys


LEAN_IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
LEAN_MODULE_RE = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*$"
)


def positive_nat(text: str) -> int:
    try:
        value = int(text)
    except ValueError as exc:
        raise argparse.ArgumentTypeError(f"{text!r} is not an integer") from exc
    if value <= 0:
        raise argparse.ArgumentTypeError(f"{text!r} is not positive")
    return value


def nonnegative_nat(text: str) -> int:
    try:
        value = int(text)
    except ValueError as exc:
        raise argparse.ArgumentTypeError(f"{text!r} is not an integer") from exc
    if value < 0:
        raise argparse.ArgumentTypeError(f"{text!r} is negative")
    return value


def lean_ident(text: str) -> str:
    if not LEAN_IDENT_RE.match(text):
        raise argparse.ArgumentTypeError(f"{text!r} is not a Lean identifier")
    return text


def lean_module(text: str) -> str:
    if not LEAN_MODULE_RE.match(text):
        raise argparse.ArgumentTypeError(f"{text!r} is not a Lean module name")
    return text


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="emit a Lean finite-window positive-saddle certificate template",
    )
    parser.add_argument("--product-row-len", type=positive_nat, required=True)
    parser.add_argument(
        "--tangent-row-len",
        type=positive_nat,
        help="required except for cell-tangent",
    )
    parser.add_argument(
        "--tangent-n-len",
        type=positive_nat,
        help="fixed N-chunk length for --strategy chunked-tangent",
    )
    parser.add_argument(
        "--tangent-k-len",
        type=positive_nat,
        help="fixed k-chunk length for --strategy chunked-tangent",
    )
    parser.add_argument(
        "--solo-saddle-n-len",
        type=positive_nat,
        help=(
            "fixed N-chunk length for displayed-solo saddle checks; "
            "defaults to --n-len when needed"
        ),
    )
    parser.add_argument(
        "--solo-budget-n-len",
        type=positive_nat,
        help=(
            "fixed N-chunk length for displayed-solo budget checks; "
            "defaults to --n-len when needed"
        ),
    )
    parser.add_argument("--solo-saddle-row-len", type=positive_nat, required=True)
    parser.add_argument("--solo-budget-row-len", type=positive_nat, required=True)
    parser.add_argument("--edge-row-len", type=positive_nat, required=True)
    parser.add_argument("--n-len", type=positive_nat, required=True)
    parser.add_argument(
        "--product-k-len",
        type=positive_nat,
        help=(
            "fixed retained-k chunk length for product checks under "
            "--strategy product-nk-tangent-solo-n-chunked or "
            "--strategy combined-product-nk-tangent-solo-n-chunked"
        ),
    )
    parser.add_argument(
        "--edge-k-len",
        type=positive_nat,
        help=(
            "fixed retained-k chunk length for fine edge checks under "
            "--strategy combined-product-nk-tangent-solo-n-fixed-edge-k-chunked"
        ),
    )
    parser.add_argument(
        "--name",
        type=lean_ident,
        default=None,
        help="Lean theorem name for the generated finite certificate",
    )
    parser.add_argument(
        "--extra-import",
        action="append",
        default=[],
        type=lean_module,
        help=(
            "additional Lean module to import in generated output; repeat for "
            "assembled certificates that depend on separately built atom files"
        ),
    )
    parser.add_argument(
        "--emit-final",
        action="store_true",
        help="also emit a theorem taking a large-tail certificate to CoefficientNegativity",
    )
    parser.add_argument(
        "--final-tail-parts",
        action="store_true",
        help=(
            "with --emit-final, make the final theorem take the split "
            "PositiveSaddleLargeTailPartsAuditCertificate interface"
        ),
    )
    parser.add_argument(
        "--final-tail-bounds-parts",
        action="store_true",
        help=(
            "with --emit-final, make the final theorem take the product/solo "
            "bound-split PositiveSaddleLargeTailBoundsPartsAuditCertificate "
            "interface"
        ),
    )
    parser.add_argument(
        "--final-tail-atomic-parts",
        action="store_true",
        help=(
            "with --emit-final, make the final theorem take the atomic "
            "PositiveSaddleLargeTailAtomicPartsAuditCertificate interface"
        ),
    )
    parser.add_argument(
        "--final-tail-atomic-bounds",
        action="store_true",
        help=(
            "with --emit-final, make the final theorem take the product/solo "
            "bound-split and candidate-atomic "
            "PositiveSaddleLargeTailAtomicBoundsAuditCertificate interface"
        ),
    )
    parser.add_argument(
        "--final-tail-raw-cleared-unit-bounds",
        action="store_true",
        help=(
            "with --emit-final, make the final theorem take the product/solo "
            "bound-split and grouped raw-cleared unit-reserve "
            "PositiveSaddleLargeTailRawClearedUnitBoundsAuditCertificate "
            "interface"
        ),
    )
    parser.add_argument(
        "--final-tail-refined-atomic-bounds",
        action="store_true",
        help=(
            "with --emit-final, make the final theorem take the product/solo "
            "bound-split and refined candidate-atomic "
            "PositiveSaddleLargeTailRefinedAtomicBoundsAuditCertificate "
            "interface"
        ),
    )
    parser.add_argument(
        "--final-tail-tempered-raw-exp-ratio-reserve-bounds",
        action="store_true",
        help=(
            "with --emit-final, make the final theorem take the product/solo "
            "bound-split interface whose live candidate fields are the two "
            "tempered raw-exp ratio atoms and the three reserve atoms"
        ),
    )
    parser.add_argument(
        "--final-tail-tempered-raw-exp-ratio-tempered-reserve-bounds",
        action="store_true",
        help=(
            "with --emit-final, make the final theorem take the product/solo "
            "bound-split interface whose live candidate fields are the two "
            "tempered raw-exp ratio atoms and the two tempered reserve atoms"
        ),
    )
    parser.add_argument(
        "--final-tail-tempered-raw-exp-ratio-reserve-envelope-bounds",
        action="store_true",
        help=(
            "with --emit-final, make the final theorem take the product/solo "
            "bound-split interface whose reserve atoms are supplied through "
            "explicit large-exp envelope bounds"
        ),
    )
    parser.add_argument(
        "--final-tail-tempered-raw-exp-ratio-tempered-reserve-envelope-bounds",
        action="store_true",
        help=(
            "with --emit-final, make the final theorem take the product/solo "
            "bound-split interface whose remaining tempered reserve atoms "
            "are supplied through explicit large-exp envelope bounds"
        ),
    )
    parser.add_argument(
        "--single-chunk-prefix",
        type=lean_ident,
        default="positiveSaddleGeneratedChunk",
        help="prefix for generated/referenced single-chunk theorem names",
    )
    parser.add_argument(
        "--use-single-chunk-theorems",
        action="store_true",
        help="assemble product-n-chunked-tangent from single-chunk theorem names",
    )
    parser.add_argument(
        "--emit-single-chunk-suite",
        action="store_true",
        help=(
            "emit all single-chunk theorems and assemble the "
            "product-n-chunked-tangent certificate"
        ),
    )
    parser.add_argument(
        "--emit-single-chunk-shard",
        action="store_true",
        help="emit one balanced shard of the required single-chunk theorems",
    )
    parser.add_argument(
        "--shard-index",
        type=nonnegative_nat,
        help="zero-based shard index for --emit-single-chunk-shard",
    )
    parser.add_argument(
        "--shard-count",
        type=positive_nat,
        help="total number of shards for --emit-single-chunk-shard",
    )
    parser.add_argument(
        "--emit-single-chunk-manifest",
        action="store_true",
        help=(
            "emit a JSON manifest of all required single-chunk theorem names "
            "and indices instead of Lean code"
        ),
    )
    parser.add_argument(
        "--dry-run-counts",
        action="store_true",
        help=(
            "emit formula-based JSON atom counts and exit without "
            "materializing the full manifest or any Lean code"
        ),
    )
    parser.add_argument(
        "--manifest-shard-count",
        type=positive_nat,
        help=(
            "with --emit-single-chunk-manifest, include balanced shard "
            "start/stop metadata for this many shards"
        ),
    )
    parser.add_argument(
        "--strategy",
        choices=(
            "all-chunks",
            "split-fields",
            "cell-tangent",
            "chunked-tangent",
            "product-n-chunked-tangent",
            "product-tangent-solo-n-chunked",
            "product-nk-tangent-solo-n-chunked",
            "combined-product-nk-tangent-solo-n-chunked",
            "combined-product-nk-tangent-solo-n-fixed-edge-k-chunked",
        ),
        default="all-chunks",
        help="finite certificate shape to emit",
    )
    parser.add_argument(
        "--emit-single-chunk",
        choices=(
            "product-small",
            "product-tempered",
            "product-combined",
            "tangent",
            "tangent-n",
            "solo-saddle",
            "solo-saddle-n",
            "solo-budget",
            "solo-budget-n",
            "edge",
            "edge-fixed",
        ),
        help="emit one concrete chunk theorem instead of a full certificate",
    )
    parser.add_argument(
        "--row-index",
        type=nonnegative_nat,
        help="fixed row chunk index for --emit-single-chunk",
    )
    parser.add_argument(
        "--n-index",
        type=nonnegative_nat,
        help="fixed product N-chunk index for product single chunks",
    )
    parser.add_argument(
        "--k-index",
        type=nonnegative_nat,
        help="fixed retained-k/tangent-k chunk index for single chunks",
    )
    args = parser.parse_args(argv)
    if args.solo_saddle_n_len is None:
        args.solo_saddle_n_len = args.n_len
    if args.solo_budget_n_len is None:
        args.solo_budget_n_len = args.n_len
    if args.product_k_len is None:
        args.product_k_len = 20
    if args.edge_k_len is None:
        args.edge_k_len = 20
    if args.emit_single_chunk_suite and args.emit_single_chunk is not None:
        parser.error("--emit-single-chunk-suite cannot be combined with --emit-single-chunk")
    if args.emit_single_chunk_shard and args.emit_single_chunk is not None:
        parser.error("--emit-single-chunk-shard cannot be combined with --emit-single-chunk")
    if args.emit_single_chunk_manifest and args.emit_single_chunk is not None:
        parser.error(
            "--emit-single-chunk-manifest cannot be combined with --emit-single-chunk"
        )
    if args.emit_single_chunk_shard and args.emit_single_chunk_suite:
        parser.error(
            "--emit-single-chunk-shard cannot be combined with "
            "--emit-single-chunk-suite"
        )
    if args.emit_single_chunk_shard and args.emit_single_chunk_manifest:
        parser.error(
            "--emit-single-chunk-shard cannot be combined with "
            "--emit-single-chunk-manifest"
        )
    if args.emit_single_chunk_manifest and args.emit_single_chunk_suite:
        parser.error(
            "--emit-single-chunk-manifest cannot be combined with "
            "--emit-single-chunk-suite"
        )
    if args.dry_run_counts and (
        args.emit_single_chunk is not None
        or args.emit_single_chunk_suite
        or args.emit_single_chunk_shard
        or args.emit_single_chunk_manifest
    ):
        parser.error(
            "--dry-run-counts cannot be combined with single-chunk, suite, "
            "shard, or manifest emission"
        )
    final_tail_selectors = (
        args.final_tail_parts,
        args.final_tail_bounds_parts,
        args.final_tail_atomic_parts,
        args.final_tail_atomic_bounds,
        args.final_tail_raw_cleared_unit_bounds,
        args.final_tail_refined_atomic_bounds,
        args.final_tail_tempered_raw_exp_ratio_reserve_bounds,
        args.final_tail_tempered_raw_exp_ratio_tempered_reserve_bounds,
        args.final_tail_tempered_raw_exp_ratio_reserve_envelope_bounds,
        args.final_tail_tempered_raw_exp_ratio_tempered_reserve_envelope_bounds,
    )
    if sum(bool(selector) for selector in final_tail_selectors) > 1:
        parser.error("--final-tail-* options cannot be combined")
    if args.emit_single_chunk_suite and args.use_single_chunk_theorems:
        parser.error(
            "--emit-single-chunk-suite cannot be combined with "
            "--use-single-chunk-theorems"
        )
    if args.emit_single_chunk_shard and args.use_single_chunk_theorems:
        parser.error(
            "--emit-single-chunk-shard cannot be combined with "
            "--use-single-chunk-theorems"
        )
    if args.emit_single_chunk_shard:
        if args.shard_index is None or args.shard_count is None:
            parser.error(
                "--shard-index and --shard-count are required with "
                "--emit-single-chunk-shard"
            )
        if args.shard_count <= args.shard_index:
            parser.error("--shard-index must be smaller than --shard-count")
    elif args.shard_index is not None or args.shard_count is not None:
        parser.error(
            "--shard-index/--shard-count require --emit-single-chunk-shard"
        )
    if args.manifest_shard_count is not None and not args.emit_single_chunk_manifest:
        parser.error(
            "--manifest-shard-count requires --emit-single-chunk-manifest"
        )
    if args.emit_single_chunk_suite and args.strategy not in (
        "product-n-chunked-tangent",
        "product-tangent-solo-n-chunked",
        "product-nk-tangent-solo-n-chunked",
        "combined-product-nk-tangent-solo-n-chunked",
        "combined-product-nk-tangent-solo-n-fixed-edge-k-chunked",
    ):
        parser.error(
            "--emit-single-chunk-suite is only supported for "
            "--strategy product-n-chunked-tangent or "
            "--strategy product-tangent-solo-n-chunked or "
            "--strategy product-nk-tangent-solo-n-chunked or "
            "--strategy combined-product-nk-tangent-solo-n-chunked"
            " or --strategy combined-product-nk-tangent-solo-n-fixed-edge-k-chunked"
        )
    if args.emit_single_chunk_shard and args.strategy not in (
        "product-n-chunked-tangent",
        "product-tangent-solo-n-chunked",
        "product-nk-tangent-solo-n-chunked",
        "combined-product-nk-tangent-solo-n-chunked",
        "combined-product-nk-tangent-solo-n-fixed-edge-k-chunked",
    ):
        parser.error(
            "--emit-single-chunk-shard is only supported for "
            "--strategy product-n-chunked-tangent or "
            "--strategy product-tangent-solo-n-chunked or "
            "--strategy product-nk-tangent-solo-n-chunked or "
            "--strategy combined-product-nk-tangent-solo-n-chunked"
            " or --strategy combined-product-nk-tangent-solo-n-fixed-edge-k-chunked"
        )
    if args.emit_single_chunk_manifest and args.strategy not in (
        "product-n-chunked-tangent",
        "product-tangent-solo-n-chunked",
        "product-nk-tangent-solo-n-chunked",
        "combined-product-nk-tangent-solo-n-chunked",
        "combined-product-nk-tangent-solo-n-fixed-edge-k-chunked",
    ):
        parser.error(
            "--emit-single-chunk-manifest is only supported for "
            "--strategy product-n-chunked-tangent or "
            "--strategy product-tangent-solo-n-chunked or "
            "--strategy product-nk-tangent-solo-n-chunked or "
            "--strategy combined-product-nk-tangent-solo-n-chunked"
            " or --strategy combined-product-nk-tangent-solo-n-fixed-edge-k-chunked"
        )
    if args.dry_run_counts and args.strategy not in (
        "product-n-chunked-tangent",
        "product-tangent-solo-n-chunked",
        "product-nk-tangent-solo-n-chunked",
        "combined-product-nk-tangent-solo-n-chunked",
        "combined-product-nk-tangent-solo-n-fixed-edge-k-chunked",
    ):
        parser.error(
            "--dry-run-counts is only supported for "
            "--strategy product-n-chunked-tangent or "
            "--strategy product-tangent-solo-n-chunked or "
            "--strategy product-nk-tangent-solo-n-chunked or "
            "--strategy combined-product-nk-tangent-solo-n-chunked"
            " or --strategy combined-product-nk-tangent-solo-n-fixed-edge-k-chunked"
        )
    if args.use_single_chunk_theorems and args.emit_single_chunk is not None:
        parser.error("--use-single-chunk-theorems cannot be combined with --emit-single-chunk")
    if args.use_single_chunk_theorems and args.strategy not in (
        "product-n-chunked-tangent",
        "product-tangent-solo-n-chunked",
        "product-nk-tangent-solo-n-chunked",
        "combined-product-nk-tangent-solo-n-chunked",
        "combined-product-nk-tangent-solo-n-fixed-edge-k-chunked",
    ):
        parser.error(
            "--use-single-chunk-theorems is only supported for "
            "--strategy product-n-chunked-tangent or "
            "--strategy product-tangent-solo-n-chunked or "
            "--strategy product-nk-tangent-solo-n-chunked or "
            "--strategy combined-product-nk-tangent-solo-n-chunked"
            " or --strategy combined-product-nk-tangent-solo-n-fixed-edge-k-chunked"
        )
    if args.emit_single_chunk is not None:
        if args.row_index is None:
            parser.error("--row-index is required with --emit-single-chunk")
        if args.emit_single_chunk in (
            "product-small",
            "product-tempered",
            "product-combined",
            "edge",
            "edge-fixed",
        ):
            if args.k_index is None:
                parser.error("--k-index is required for product/edge single chunks")
        if args.emit_single_chunk in (
            "product-small",
            "product-tempered",
            "product-combined",
        ):
            if args.n_index is None:
                parser.error("--n-index is required for product single chunks")
        if args.emit_single_chunk in ("tangent", "tangent-n"):
            if args.tangent_row_len is None:
                parser.error("--tangent-row-len is required for tangent single chunks")
            if args.tangent_n_len is None:
                parser.error("--tangent-n-len is required for tangent single chunks")
            if args.tangent_k_len is None:
                parser.error("--tangent-k-len is required for tangent single chunks")
            if args.k_index is None:
                parser.error("--k-index is required for tangent single chunks")
        if args.emit_single_chunk == "tangent-n" and args.n_index is None:
            parser.error("--n-index is required for tangent-n single chunks")
        if args.emit_single_chunk in ("solo-saddle-n", "solo-budget-n"):
            if args.n_index is None:
                parser.error("--n-index is required for solo N-index single chunks")
        validate_single_chunk_indices(parser, args)
    else:
        if args.strategy != "cell-tangent" and args.tangent_row_len is None:
            parser.error("--tangent-row-len is required unless --strategy cell-tangent")
        if args.strategy in (
            "chunked-tangent",
            "product-n-chunked-tangent",
            "product-tangent-solo-n-chunked",
            "product-nk-tangent-solo-n-chunked",
            "combined-product-nk-tangent-solo-n-chunked",
            "combined-product-nk-tangent-solo-n-fixed-edge-k-chunked",
        ):
            if args.tangent_n_len is None:
                parser.error(f"--tangent-n-len is required for --strategy {args.strategy}")
            if args.tangent_k_len is None:
                parser.error(f"--tangent-k-len is required for --strategy {args.strategy}")
    if args.name is None:
        if args.emit_single_chunk is not None:
            args.name = single_chunk_default_name(args)
        elif args.strategy == "all-chunks":
            args.name = "positiveSaddleGeneratedFixedFiniteWindowAllChunksCertificate"
        elif args.strategy == "split-fields":
            args.name = "positiveSaddleGeneratedFixedFiniteWindowCertificate"
        elif args.strategy == "cell-tangent":
            args.name = "positiveSaddleGeneratedFixedFiniteWindowCellTangentCertificate"
        elif args.strategy == "chunked-tangent":
            args.name = "positiveSaddleGeneratedFixedFiniteWindowChunkedTangentCertificate"
        elif args.strategy == "product-n-chunked-tangent":
            args.name = (
                "positiveSaddleGeneratedFixedFiniteWindowProductNChunkedTangentCertificate"
            )
        elif args.strategy == "product-tangent-solo-n-chunked":
            args.name = (
                "positiveSaddleGeneratedFixedFiniteWindowProductTangentSoloNChunkedCertificate"
            )
        elif args.strategy == "product-nk-tangent-solo-n-chunked":
            args.name = (
                "positiveSaddleGeneratedFixedFiniteWindowProductNKChunkedTangentSoloNChunkedCertificate"
            )
        elif args.strategy == "combined-product-nk-tangent-solo-n-chunked":
            args.name = (
                "positiveSaddleGeneratedFixedFiniteWindowCombinedProductNKChunkedTangentSoloNChunkedCertificate"
            )
        else:
            args.name = (
                "positiveSaddleGeneratedFixedFiniteWindowCombinedProductNKChunkedTangentSoloNFixedEdgeKChunkedCertificate"
            )
    return args


def validate_lt(
    parser: argparse.ArgumentParser,
    option: str,
    value: int,
    bound: int,
) -> None:
    if value >= bound:
        parser.error(f"{option} must be < {bound}, got {value}")


def validate_single_chunk_indices(
    parser: argparse.ArgumentParser, args: argparse.Namespace
) -> None:
    field = args.emit_single_chunk
    if field in ("product-small", "product-tempered", "product-combined"):
        validate_lt(parser, "--row-index", args.row_index, row_count(args.product_row_len))
        validate_lt(
            parser,
            "--n-index",
            args.n_index,
            product_n_index_count(args.product_row_len, args.n_len),
        )
        validate_lt(parser, "--k-index", args.k_index, active_product_k_count(args))
    elif field == "tangent":
        validate_lt(parser, "--row-index", args.row_index, row_count(args.tangent_row_len))
        validate_lt(parser, "--k-index", args.k_index, tangent_k_count(args.tangent_k_len))
    elif field == "tangent-n":
        validate_lt(parser, "--row-index", args.row_index, row_count(args.tangent_row_len))
        validate_lt(
            parser,
            "--n-index",
            args.n_index,
            product_n_index_count(args.tangent_row_len, args.tangent_n_len),
        )
        validate_lt(parser, "--k-index", args.k_index, tangent_k_count(args.tangent_k_len))
    elif field == "solo-saddle":
        validate_lt(
            parser,
            "--row-index",
            args.row_index,
            row_count(args.solo_saddle_row_len),
        )
    elif field == "solo-saddle-n":
        validate_lt(
            parser,
            "--row-index",
            args.row_index,
            row_count(args.solo_saddle_row_len),
        )
        validate_lt(
            parser,
            "--n-index",
            args.n_index,
            product_n_index_count(args.solo_saddle_row_len, args.solo_saddle_n_len),
        )
    elif field == "solo-budget":
        validate_lt(
            parser,
            "--row-index",
            args.row_index,
            row_count(args.solo_budget_row_len),
        )
    elif field == "solo-budget-n":
        validate_lt(
            parser,
            "--row-index",
            args.row_index,
            row_count(args.solo_budget_row_len),
        )
        validate_lt(
            parser,
            "--n-index",
            args.n_index,
            product_n_index_count(args.solo_budget_row_len, args.solo_budget_n_len),
        )
    elif field == "edge":
        validate_lt(parser, "--row-index", args.row_index, row_count(args.edge_row_len))
        validate_lt(parser, "--k-index", args.k_index, 90)
    elif field == "edge-fixed":
        validate_lt(parser, "--row-index", args.row_index, row_count(args.edge_row_len))
        validate_lt(parser, "--k-index", args.k_index, edge_k_count(args.edge_k_len))
    else:
        raise AssertionError(f"unhandled single chunk field {field!r}")


def single_chunk_default_name(args: argparse.Namespace) -> str:
    return single_chunk_name(
        args.single_chunk_prefix,
        args.emit_single_chunk,
        args.row_index,
        args.n_index,
        args.k_index,
    )


def single_chunk_name(
    prefix: str,
    field: str,
    row_index: int,
    n_index: int | None = None,
    k_index: int | None = None,
) -> str:
    field = field.replace("-", "_")
    pieces = [field, f"r{row_index}"]
    if n_index is not None:
        pieces.append(f"n{n_index}")
    if k_index is not None:
        pieces.append(f"k{k_index}")
    return prefix + "_" + "_".join(pieces)


def row_count(row_len: int) -> int:
    return (1600 + row_len - 1) // row_len


def tangent_k_count(k_len: int) -> int:
    return (155 + k_len - 1) // k_len


def product_k_count(k_len: int) -> int:
    return (1800 + k_len - 1) // k_len


def edge_k_count(k_len: int) -> int:
    return (1800 + k_len - 1) // k_len


def active_product_k_len(args: argparse.Namespace) -> int:
    if args.strategy in (
        "product-nk-tangent-solo-n-chunked",
        "combined-product-nk-tangent-solo-n-chunked",
        "combined-product-nk-tangent-solo-n-fixed-edge-k-chunked",
    ):
        return args.product_k_len
    return 20


def active_product_k_count(args: argparse.Namespace) -> int:
    return product_k_count(active_product_k_len(args))


def product_n_index_count(row_len: int, n_len: int) -> int:
    return (6 * (2000 + row_len) + n_len - 1) // n_len


def exact_case_tree_lines(
    variables: list[tuple[str, int]],
    name_for_indices,
    indices: tuple[int, ...] = (),
    indent: str = "    ",
) -> list[str]:
    if not variables:
        return [f"{indent}exact {name_for_indices(*indices)}"]
    var_name, count = variables[0]
    lines = [f"{indent}interval_cases {var_name}"]
    for index in range(count):
        next_indices = (*indices, index)
        if len(variables) == 1:
            lines.append(f"{indent}next => exact {name_for_indices(*next_indices)}")
        else:
            lines.append(f"{indent}next =>")
            lines.extend(
                exact_case_tree_lines(
                    variables[1:],
                    name_for_indices,
                    next_indices,
                    indent + "  ",
                )
            )
    return lines


def emit_header(args: argparse.Namespace | None = None) -> list[str]:
    imports = ["Prop51.Main"]
    if args is not None:
        for module in args.extra_import:
            if module not in imports:
                imports.append(module)
    return [
        *(f"import {module}" for module in imports),
        "",
        "namespace Prop51",
        "",
        "/-",
        "Generated finite-window positive-saddle certificate.",
        "",
        "This proves only the finite Boolean checks.  Combine it with a",
        "`PositiveSaddleLargeTailAuditCertificate` for the final theorem.",
        "Pass `--final-tail-parts` to target the split large-tail interface.",
        "Pass `--final-tail-bounds-parts` for product/solo bound splits.",
        "Pass `--final-tail-atomic-parts` for the atomic large-tail interface.",
        "Pass `--final-tail-atomic-bounds` for bound-split atomic tails.",
        "Pass `--final-tail-raw-cleared-unit-bounds` for grouped raw-cleared",
        "unit-reserve tails with product/solo bound splits.",
        "Pass `--final-tail-refined-atomic-bounds` for the refined raw-exp",
        "ratio step atoms with product/solo bound splits.",
        "Pass `--final-tail-tempered-raw-exp-ratio-reserve-bounds` after",
        "the small step is filled by Lean's raw-base half certificate.",
        "Pass `--final-tail-tempered-raw-exp-ratio-tempered-reserve-bounds`",
        "after the small first reserve is also filled by Lean.",
        "Pass `--final-tail-tempered-raw-exp-ratio-reserve-envelope-bounds`",
        "to split those reserve atoms through explicit exp envelopes.",
        "Pass `--final-tail-tempered-raw-exp-ratio-tempered-reserve-envelope-bounds`",
        "to split only the remaining tempered reserve atoms.",
        "-/",
    ]


def final_tail_type(args: argparse.Namespace) -> str:
    if args.final_tail_tempered_raw_exp_ratio_reserve_envelope_bounds:
        return (
            "PositiveSaddleLargeTailTemperedRawExpRatioReserveEnvelopeBoundsAuditCertificate"
        )
    if args.final_tail_tempered_raw_exp_ratio_tempered_reserve_envelope_bounds:
        return (
            "PositiveSaddleLargeTailTemperedRawExpRatioTemperedReserveEnvelopeBoundsAuditCertificate"
        )
    if args.final_tail_tempered_raw_exp_ratio_reserve_bounds:
        return (
            "PositiveSaddleLargeTailTemperedRawExpRatioReserveBoundsAuditCertificate"
        )
    if args.final_tail_tempered_raw_exp_ratio_tempered_reserve_bounds:
        return (
            "PositiveSaddleLargeTailTemperedRawExpRatioTemperedReserveBoundsAuditCertificate"
        )
    if args.final_tail_refined_atomic_bounds:
        return "PositiveSaddleLargeTailRefinedAtomicBoundsAuditCertificate"
    if args.final_tail_atomic_bounds:
        return "PositiveSaddleLargeTailAtomicBoundsAuditCertificate"
    if args.final_tail_raw_cleared_unit_bounds:
        return "PositiveSaddleLargeTailRawClearedUnitBoundsAuditCertificate"
    if args.final_tail_atomic_parts:
        return "PositiveSaddleLargeTailAtomicPartsAuditCertificate"
    if args.final_tail_bounds_parts:
        return "PositiveSaddleLargeTailBoundsPartsAuditCertificate"
    if args.final_tail_parts:
        return "PositiveSaddleLargeTailPartsAuditCertificate"
    return "PositiveSaddleLargeTailAuditCertificate"


def final_tail_binder_lines(args: argparse.Namespace) -> list[str]:
    if (
        args.final_tail_bounds_parts
        or args.final_tail_atomic_bounds
        or args.final_tail_raw_cleared_unit_bounds
        or args.final_tail_refined_atomic_bounds
        or args.final_tail_tempered_raw_exp_ratio_reserve_bounds
        or args.final_tail_tempered_raw_exp_ratio_tempered_reserve_bounds
        or args.final_tail_tempered_raw_exp_ratio_reserve_envelope_bounds
        or args.final_tail_tempered_raw_exp_ratio_tempered_reserve_envelope_bounds
    ):
        lines = [
            "    {smallXBound smallYBound temperedXBound temperedYBound :",
            "      Nat → Nat → Nat → ℚ}",
            "    {soloYBound : Nat → Nat → ℚ}",
        ]
        if args.final_tail_tempered_raw_exp_ratio_reserve_envelope_bounds:
            lines.extend(
                [
                    "    {smallFirstExpBound temperedLowerFirstExpBound",
                    "      temperedUpperLastExpBound : Nat → ℚ}",
                    f"    (tail : {final_tail_type(args)}",
                    "      smallXBound smallYBound temperedXBound temperedYBound soloYBound",
                    "      smallFirstExpBound temperedLowerFirstExpBound",
                    "      temperedUpperLastExpBound) :",
                ]
            )
        elif args.final_tail_tempered_raw_exp_ratio_tempered_reserve_envelope_bounds:
            lines.extend(
                [
                    "    {temperedLowerFirstExpBound",
                    "      temperedUpperLastExpBound : Nat → ℚ}",
                    f"    (tail : {final_tail_type(args)}",
                    "      smallXBound smallYBound temperedXBound temperedYBound soloYBound",
                    "      temperedLowerFirstExpBound",
                    "      temperedUpperLastExpBound) :",
                ]
            )
        else:
            lines.extend(
                [
                    f"    (tail : {final_tail_type(args)}",
                    "      smallXBound smallYBound temperedXBound temperedYBound soloYBound) :",
                ]
            )
        return lines
    return [f"    (tail : {final_tail_type(args)}) :"]


def final_tail_arg(args: argparse.Namespace) -> str:
    if (
        args.final_tail_atomic_bounds
        or args.final_tail_raw_cleared_unit_bounds
        or args.final_tail_refined_atomic_bounds
        or args.final_tail_tempered_raw_exp_ratio_reserve_bounds
        or args.final_tail_tempered_raw_exp_ratio_tempered_reserve_bounds
        or args.final_tail_tempered_raw_exp_ratio_reserve_envelope_bounds
        or args.final_tail_tempered_raw_exp_ratio_tempered_reserve_envelope_bounds
        or args.final_tail_atomic_parts
        or args.final_tail_bounds_parts
        or args.final_tail_parts
    ):
        return "tail.toLargeTailAuditCertificate"
    return "tail"


def single_chunk_theorem_lines(
    args: argparse.Namespace,
    field: str,
    name: str,
    row_index: int,
    n_index: int | None = None,
    k_index: int | None = None,
) -> list[str]:
    if field == "product-small":
        row_lo = 401 + args.product_row_len * row_index
        product_k = active_product_k_len(args)
        k_lo = 1 + product_k * k_index
        return [
            f"theorem {name} :",
            "    checkPositiveSmallXYProductRawClearedTableFixedNIndexRowRangeKChunk",
            f"      {args.n_len} {row_lo} {args.product_row_len}",
            f"      {n_index} {k_lo} {product_k} = true := by",
            "  native_decide",
        ]
    if field == "product-tempered":
        row_lo = 401 + args.product_row_len * row_index
        product_k = active_product_k_len(args)
        k_lo = 1 + product_k * k_index
        return [
            f"theorem {name} :",
            "    checkPositiveTemperedXYProductRawClearedTableFixedNIndexRowRangeKChunk",
            f"      {args.n_len} {row_lo} {args.product_row_len}",
            f"      {n_index} {k_lo} {product_k} = true := by",
            "  native_decide",
        ]
    if field == "product-combined":
        row_lo = 401 + args.product_row_len * row_index
        product_k = active_product_k_len(args)
        k_lo = 1 + product_k * k_index
        return [
            f"theorem {name} :",
            "    checkPositiveXYProductRawClearedTableFixedNIndexRowRangeKChunk",
            f"      {args.n_len} {row_lo} {args.product_row_len}",
            f"      {n_index} {k_lo} {product_k} = true := by",
            "  native_decide",
        ]
    if field == "tangent":
        row_lo = 401 + args.tangent_row_len * row_index
        k_lo = 1 + args.tangent_k_len * k_index
        return [
            f"theorem {name} :",
            "    checkPositiveSmallTangentExpEdgeFixedNChunksRowRangeKChunk",
            f"      {args.tangent_n_len} {row_lo} {args.tangent_row_len}",
            f"      {k_lo} {args.tangent_k_len} = true := by",
            "  native_decide",
        ]
    if field == "tangent-n":
        row_lo = 401 + args.tangent_row_len * row_index
        k_lo = 1 + args.tangent_k_len * k_index
        return [
            f"theorem {name} :",
            "    checkPositiveSmallTangentExpEdgeFixedNIndexRowRangeKChunk",
            f"      {args.tangent_n_len} {row_lo} {args.tangent_row_len}",
            f"      {n_index} {k_lo} {args.tangent_k_len} = true := by",
            "  native_decide",
        ]
    if field == "solo-saddle":
        row_lo = 401 + args.solo_saddle_row_len * row_index
        return [
            f"theorem {name} :",
            "    checkPositiveSoloDisplayedYSaddleClearedRange",
            f"      {row_lo} {args.solo_saddle_row_len} = true := by",
            "  native_decide",
        ]
    if field == "solo-saddle-n":
        row_lo = 401 + args.solo_saddle_row_len * row_index
        return [
            f"theorem {name} :",
            "    checkPositiveSoloDisplayedYSaddleClearedFixedNIndexRowRange",
            f"      {args.solo_saddle_n_len} {row_lo} {args.solo_saddle_row_len}",
            f"      {n_index} = true := by",
            "  native_decide",
        ]
    if field == "solo-budget":
        row_lo = 401 + args.solo_budget_row_len * row_index
        return [
            f"theorem {name} :",
            "    checkPositiveSoloDisplayedYBoundUnitRange",
            f"      {row_lo} {args.solo_budget_row_len} = true := by",
            "  native_decide",
        ]
    if field == "solo-budget-n":
        row_lo = 401 + args.solo_budget_row_len * row_index
        return [
            f"theorem {name} :",
            "    checkPositiveSoloDisplayedYBoundUnitFixedNIndexRowRange",
            f"      {args.solo_budget_n_len} {row_lo} {args.solo_budget_row_len}",
            f"      {n_index} = true := by",
            "  native_decide",
        ]
    if field == "edge":
        row_lo = 401 + args.edge_row_len * row_index
        k_lo = 1 + 20 * k_index
        return [
            f"theorem {name} :",
            "    checkPositiveEdgeMajorantKChunkUnitRowRange",
            f"      {row_lo} {args.edge_row_len} {k_lo} 20",
            "      (fun _ => positiveEdgeUniformScaleMin) = true := by",
            "  native_decide",
        ]
    if field == "edge-fixed":
        row_lo = 401 + args.edge_row_len * row_index
        k_lo = 1 + args.edge_k_len * k_index
        return [
            f"theorem {name} :",
            "    checkPositiveEdgeMajorantKChunkUnitRowRange",
            f"      {row_lo} {args.edge_row_len} {k_lo} {args.edge_k_len}",
            f"      (fun _ => positiveEdgeFixedKScale {args.edge_k_len}) = true := by",
            "  native_decide",
        ]
    raise AssertionError(f"unhandled single chunk field {field!r}")


def emit_single_chunk(args: argparse.Namespace) -> str:
    lines = emit_header(args)
    lines.extend(
        single_chunk_theorem_lines(
            args,
            args.emit_single_chunk,
            args.name,
            args.row_index,
            args.n_index,
            args.k_index,
        )
    )

    lines.extend(["", "end Prop51", ""])
    return "\n".join(lines)


def single_chunk_specs(
    args: argparse.Namespace,
) -> list[tuple[str, int, int | None, int | None, str]]:
    specs = []
    product_fields = (
        ("product-combined",)
        if args.strategy in (
            "combined-product-nk-tangent-solo-n-chunked",
            "combined-product-nk-tangent-solo-n-fixed-edge-k-chunked",
        )
        else ("product-small", "product-tempered")
    )
    for field in product_fields:
        for i in range(row_count(args.product_row_len)):
            for n in range(product_n_index_count(args.product_row_len, args.n_len)):
                for j in range(active_product_k_count(args)):
                    specs.append(
                        (
                            field,
                            i,
                            n,
                            j,
                            single_chunk_name(args.single_chunk_prefix, field, i, n, j),
                        )
                    )
    if args.strategy in (
        "product-tangent-solo-n-chunked",
        "product-nk-tangent-solo-n-chunked",
        "combined-product-nk-tangent-solo-n-chunked",
        "combined-product-nk-tangent-solo-n-fixed-edge-k-chunked",
    ):
        for i in range(row_count(args.tangent_row_len)):
            for n in range(product_n_index_count(args.tangent_row_len, args.tangent_n_len)):
                for j in range(tangent_k_count(args.tangent_k_len)):
                    specs.append(
                        (
                            "tangent-n",
                            i,
                            n,
                            j,
                            single_chunk_name(
                                args.single_chunk_prefix, "tangent-n", i, n, j
                            ),
                        )
                    )
        for field, row_len, n_len in (
            ("solo-saddle-n", args.solo_saddle_row_len, args.solo_saddle_n_len),
            ("solo-budget-n", args.solo_budget_row_len, args.solo_budget_n_len),
        ):
            for i in range(row_count(row_len)):
                for n in range(product_n_index_count(row_len, n_len)):
                    specs.append(
                        (
                            field,
                            i,
                            n,
                            None,
                            single_chunk_name(args.single_chunk_prefix, field, i, n),
                        )
                    )
    else:
        for i in range(row_count(args.tangent_row_len)):
            for j in range(tangent_k_count(args.tangent_k_len)):
                specs.append(
                    (
                        "tangent",
                        i,
                        None,
                        j,
                        single_chunk_name(
                            args.single_chunk_prefix, "tangent", i, None, j
                        ),
                    )
                )
        for field, row_len in (
            ("solo-saddle", args.solo_saddle_row_len),
            ("solo-budget", args.solo_budget_row_len),
        ):
            for i in range(row_count(row_len)):
                specs.append(
                    (
                        field,
                        i,
                        None,
                        None,
                        single_chunk_name(args.single_chunk_prefix, field, i),
                    )
                )
    edge_field = (
        "edge-fixed"
        if args.strategy
        == "combined-product-nk-tangent-solo-n-fixed-edge-k-chunked"
        else "edge"
    )
    edge_count = edge_k_count(args.edge_k_len) if edge_field == "edge-fixed" else 90
    for i in range(row_count(args.edge_row_len)):
        for j in range(edge_count):
            specs.append(
                (
                    edge_field,
                    i,
                    None,
                    j,
                    single_chunk_name(args.single_chunk_prefix, edge_field, i, None, j),
                )
            )
    return specs


def common_finite_emit_args(args: argparse.Namespace) -> list[str]:
    emit_args = [
        "--strategy",
        args.strategy,
        "--product-row-len",
        str(args.product_row_len),
        "--tangent-row-len",
        str(args.tangent_row_len),
        "--solo-saddle-row-len",
        str(args.solo_saddle_row_len),
        "--solo-budget-row-len",
        str(args.solo_budget_row_len),
        "--edge-row-len",
        str(args.edge_row_len),
        "--n-len",
        str(args.n_len),
        "--tangent-n-len",
        str(args.tangent_n_len),
        "--tangent-k-len",
        str(args.tangent_k_len),
        "--solo-saddle-n-len",
        str(args.solo_saddle_n_len),
        "--solo-budget-n-len",
        str(args.solo_budget_n_len),
        "--product-k-len",
        str(args.product_k_len),
        "--edge-k-len",
        str(args.edge_k_len),
    ]
    for module in args.extra_import:
        emit_args.extend(["--extra-import", module])
    if args.final_tail_parts:
        emit_args.append("--final-tail-parts")
    if args.final_tail_bounds_parts:
        emit_args.append("--final-tail-bounds-parts")
    if args.final_tail_atomic_parts:
        emit_args.append("--final-tail-atomic-parts")
    if args.final_tail_atomic_bounds:
        emit_args.append("--final-tail-atomic-bounds")
    if args.final_tail_raw_cleared_unit_bounds:
        emit_args.append("--final-tail-raw-cleared-unit-bounds")
    if args.final_tail_refined_atomic_bounds:
        emit_args.append("--final-tail-refined-atomic-bounds")
    if args.final_tail_tempered_raw_exp_ratio_reserve_bounds:
        emit_args.append("--final-tail-tempered-raw-exp-ratio-reserve-bounds")
    if args.final_tail_tempered_raw_exp_ratio_tempered_reserve_bounds:
        emit_args.append(
            "--final-tail-tempered-raw-exp-ratio-tempered-reserve-bounds"
        )
    if args.final_tail_tempered_raw_exp_ratio_reserve_envelope_bounds:
        emit_args.append(
            "--final-tail-tempered-raw-exp-ratio-reserve-envelope-bounds"
        )
    if args.final_tail_tempered_raw_exp_ratio_tempered_reserve_envelope_bounds:
        emit_args.append(
            "--final-tail-tempered-raw-exp-ratio-tempered-reserve-envelope-bounds"
        )
    return emit_args


def single_chunk_emit_args(
    args: argparse.Namespace,
    field: str,
    row_index: int,
    n_index: int | None,
    k_index: int | None,
    name: str,
) -> list[str]:
    emit_args = [
        *common_finite_emit_args(args),
        "--emit-single-chunk",
        field,
        "--row-index",
        str(row_index),
        "--name",
        name,
    ]
    if n_index is not None:
        emit_args.extend(["--n-index", str(n_index)])
    if k_index is not None:
        emit_args.extend(["--k-index", str(k_index)])
    return emit_args


def single_chunk_shard_emit_args(
    args: argparse.Namespace, shard_index: int, shard_count: int
) -> list[str]:
    return [
        *common_finite_emit_args(args),
        "--single-chunk-prefix",
        args.single_chunk_prefix,
        "--emit-single-chunk-shard",
        "--shard-index",
        str(shard_index),
        "--shard-count",
        str(shard_count),
    ]


def emit_single_chunk_manifest(args: argparse.Namespace) -> str:
    specs = single_chunk_specs(args)
    counts: dict[str, int] = {}
    chunks = []
    for index, (field, row_index, n_index, k_index, name) in enumerate(specs):
        counts[field] = counts.get(field, 0) + 1
        chunks.append(
            {
                "index": index,
                "field": field,
                "row_index": row_index,
                "n_index": n_index,
                "k_index": k_index,
                "theorem": name,
                "emit_args": single_chunk_emit_args(
                    args, field, row_index, n_index, k_index, name
                ),
            }
        )
    manifest = {
        "strategy": args.strategy,
        "certificate_theorem": args.name,
        "single_chunk_prefix": args.single_chunk_prefix,
        "extra_imports": args.extra_import,
        "total": len(specs),
        "counts": counts,
        "chunks": chunks,
    }
    if args.manifest_shard_count is not None:
        shard_count = args.manifest_shard_count
        manifest["shards"] = [
            {
                "shard_index": shard_index,
                "shard_count": shard_count,
                "start": start,
                "stop": stop,
                "count": stop - start,
                "emit_args": single_chunk_shard_emit_args(
                    args, shard_index, shard_count
                ),
            }
            for shard_index in range(shard_count)
            for start, stop in [shard_bounds(len(specs), shard_index, shard_count)]
        ]
    return json.dumps(manifest, indent=2, sort_keys=True) + "\n"


def count_product_atoms(args: argparse.Namespace) -> tuple[dict[str, int], dict[str, int]]:
    product_rows = row_count(args.product_row_len)
    product_n = product_n_index_count(args.product_row_len, args.n_len)
    product_k = active_product_k_count(args)
    product_fields = (
        ("product-combined",)
        if args.strategy in (
            "combined-product-nk-tangent-solo-n-chunked",
            "combined-product-nk-tangent-solo-n-fixed-edge-k-chunked",
        )
        else ("product-small", "product-tempered")
    )
    per_field = product_rows * product_n * product_k
    counts = {field: per_field for field in product_fields}
    dimensions = {
        "product_rows": product_rows,
        "product_n_indices": product_n,
        "product_k_chunks": product_k,
        "product_k_len": active_product_k_len(args),
    }
    return counts, dimensions


def count_tangent_solo_atoms(args: argparse.Namespace) -> tuple[dict[str, int], dict[str, int]]:
    counts: dict[str, int] = {}
    dimensions: dict[str, int] = {}
    tangent_rows = row_count(args.tangent_row_len)
    tangent_k = tangent_k_count(args.tangent_k_len)
    dimensions["tangent_rows"] = tangent_rows
    dimensions["tangent_k_chunks"] = tangent_k
    if args.strategy in (
        "product-tangent-solo-n-chunked",
        "product-nk-tangent-solo-n-chunked",
        "combined-product-nk-tangent-solo-n-chunked",
        "combined-product-nk-tangent-solo-n-fixed-edge-k-chunked",
    ):
        tangent_n = product_n_index_count(args.tangent_row_len, args.tangent_n_len)
        dimensions["tangent_n_indices"] = tangent_n
        counts["tangent-n"] = tangent_rows * tangent_n * tangent_k
        for field, row_len, n_len in (
            ("solo-saddle-n", args.solo_saddle_row_len, args.solo_saddle_n_len),
            ("solo-budget-n", args.solo_budget_row_len, args.solo_budget_n_len),
        ):
            rows = row_count(row_len)
            n_indices = product_n_index_count(row_len, n_len)
            dimensions[f"{field}_rows"] = rows
            dimensions[f"{field}_n_indices"] = n_indices
            counts[field] = rows * n_indices
    else:
        counts["tangent"] = tangent_rows * tangent_k
        for field, row_len in (
            ("solo-saddle", args.solo_saddle_row_len),
            ("solo-budget", args.solo_budget_row_len),
        ):
            rows = row_count(row_len)
            dimensions[f"{field}_rows"] = rows
            counts[field] = rows
    return counts, dimensions


def count_edge_atoms(args: argparse.Namespace) -> tuple[dict[str, int], dict[str, int]]:
    edge_rows = row_count(args.edge_row_len)
    if args.strategy == "combined-product-nk-tangent-solo-n-fixed-edge-k-chunked":
        edge_chunks = edge_k_count(args.edge_k_len)
        return (
            {"edge-fixed": edge_rows * edge_chunks},
            {
                "edge_rows": edge_rows,
                "edge_k_chunks": edge_chunks,
                "edge_k_len": args.edge_k_len,
            },
        )
    return (
        {"edge": edge_rows * 90},
        {"edge_rows": edge_rows, "edge_k_chunks": 90, "edge_k_len": 20},
    )


def emit_dry_run_counts(args: argparse.Namespace) -> str:
    counts: dict[str, int] = {}
    dimensions: dict[str, int] = {}
    for next_counts, next_dimensions in (
        count_product_atoms(args),
        count_tangent_solo_atoms(args),
        count_edge_atoms(args),
    ):
        counts.update(next_counts)
        dimensions.update(next_dimensions)
    total = sum(counts.values())
    payload = {
        "strategy": args.strategy,
        "certificate_theorem": args.name,
        "single_chunk_prefix": args.single_chunk_prefix,
        "chunk_lengths": {
            "product_row_len": args.product_row_len,
            "product_n_len": args.n_len,
            "product_k_len": active_product_k_len(args),
            "tangent_row_len": args.tangent_row_len,
            "tangent_n_len": args.tangent_n_len,
            "tangent_k_len": args.tangent_k_len,
            "solo_saddle_row_len": args.solo_saddle_row_len,
            "solo_saddle_n_len": args.solo_saddle_n_len,
            "solo_budget_row_len": args.solo_budget_row_len,
            "solo_budget_n_len": args.solo_budget_n_len,
            "edge_row_len": args.edge_row_len,
            "edge_k_len": args.edge_k_len
            if args.strategy
            == "combined-product-nk-tangent-solo-n-fixed-edge-k-chunked"
            else 20,
        },
        "dimensions": dimensions,
        "counts": counts,
        "total": total,
        "materialized_chunks": False,
    }
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"


def shard_bounds(total: int, shard_index: int, shard_count: int) -> tuple[int, int]:
    start = total * shard_index // shard_count
    stop = total * (shard_index + 1) // shard_count
    return start, stop


def emit_single_chunk_shard(args: argparse.Namespace) -> str:
    specs = single_chunk_specs(args)
    start, stop = shard_bounds(len(specs), args.shard_index, args.shard_count)
    lines = emit_header(args)
    lines.extend(
        [
            "",
            "/-",
            "Individual finite-window atom shard.",
            f"Shard {args.shard_index + 1} of {args.shard_count}; "
            f"atoms {start} <= i < {stop} out of {len(specs)}.",
            "-/",
            "",
        ]
    )
    for field, row_index, n_index, k_index, name in specs[start:stop]:
        lines.extend(
            single_chunk_theorem_lines(
                args, field, name, row_index, n_index, k_index
            )
        )
        lines.append("")
    lines.extend(["end Prop51", ""])
    return "\n".join(lines)


def emit_single_chunk_suite(args: argparse.Namespace) -> str:
    lines = emit_header(args)
    lines.extend(
        [
            "",
            "/-",
            "Individual finite-window atoms.  These theorem statements are",
            "cache-friendly: each one can also be emitted independently with",
            "`--emit-single-chunk`, using the theorem names below.",
            "-/",
            "",
        ]
    )
    for field, row_index, n_index, k_index, name in single_chunk_specs(args):
        lines.extend(
            single_chunk_theorem_lines(
                args, field, name, row_index, n_index, k_index
            )
        )
        lines.append("")

    assembly_args = argparse.Namespace(**vars(args))
    assembly_args.use_single_chunk_theorems = True
    if args.strategy == "product-tangent-solo-n-chunked":
        lines.extend(product_tangent_solo_n_chunked_theorem_lines(assembly_args))
    elif args.strategy == "product-nk-tangent-solo-n-chunked":
        lines.extend(product_nk_tangent_solo_n_chunked_theorem_lines(assembly_args))
    elif args.strategy == "combined-product-nk-tangent-solo-n-chunked":
        lines.extend(
            combined_product_nk_tangent_solo_n_chunked_theorem_lines(assembly_args)
        )
    elif args.strategy == "combined-product-nk-tangent-solo-n-fixed-edge-k-chunked":
        lines.extend(
            combined_product_nk_tangent_solo_n_fixed_edge_k_chunked_theorem_lines(
                assembly_args
            )
        )
    else:
        lines.extend(product_n_chunked_tangent_theorem_lines(assembly_args))
    lines.extend(["", "end Prop51", ""])
    return "\n".join(lines)


def add_positive_fields(lines: list[str]) -> None:
    lines.extend(
        [
            "  productRowLenPos := by norm_num",
            "  tangentRowLenPos := by norm_num",
            "  soloSaddleRowLenPos := by norm_num",
            "  soloBudgetRowLenPos := by norm_num",
            "  edgeRowLenPos := by norm_num",
            "  nLenPos := by norm_num",
        ]
    )


def add_row_edge_dispatch_field(
    lines: list[str], field_name: str, row_len: int, row_bound: int
) -> None:
    lines.extend(
        [
            f"  {field_name} := by",
            "    intro rowChunk hrowChunk edgeChunk hedgeChunk",
            "    rcases (mem_positiveSaddleFixedRowChunks_iff",
            f"        (by norm_num : 0 < {row_len})).1 hrowChunk with",
            "      \u27e8i, hi, rfl\u27e9",
            f"    have hi' : i < {row_bound} := by simpa using hi",
            "    clear hi",
            "    rcases (mem_positiveEdgeDefaultKChunks_iff).1 hedgeChunk with",
            "      \u27e8j, hj, rfl\u27e9",
            "    have hj' : j < 90 := by simpa using hj",
            "    clear hj",
            "    interval_cases i; interval_cases j; native_decide",
        ]
    )


def add_row_edge_dispatch_field_from_single_chunks(
    lines: list[str],
    field_name: str,
    row_len: int,
    chunk_field: str,
    theorem_prefix: str,
) -> None:
    lines.extend(
        [
            f"  {field_name} := by",
            "    intro rowChunk hrowChunk edgeChunk hedgeChunk",
            "    rcases (mem_positiveSaddleFixedRowChunks_iff",
            f"        (by norm_num : 0 < {row_len})).1 hrowChunk with",
            "      ⟨i, hi, rfl⟩",
            f"    have hi' : i < {row_count(row_len)} := by simpa using hi",
            "    clear hi",
            "    rcases (mem_positiveEdgeDefaultKChunks_iff).1 hedgeChunk with",
            "      ⟨j, hj, rfl⟩",
            "    have hj' : j < 90 := by simpa using hj",
            "    clear hj",
        ]
    )
    lines.extend(
        exact_case_tree_lines(
            [("i", row_count(row_len)), ("j", 90)],
            lambda i, j: single_chunk_name(theorem_prefix, chunk_field, i, None, j),
        )
    )


def add_row_fixed_edge_dispatch_field_from_single_chunks(
    lines: list[str],
    field_name: str,
    row_len: int,
    edge_k_len: int,
    theorem_prefix: str,
) -> None:
    lines.extend(
        [
            f"  {field_name} := by",
            "    intro rowChunk hrowChunk edgeChunk hedgeChunk",
            "    rcases (mem_positiveSaddleFixedRowChunks_iff",
            f"        (by norm_num : 0 < {row_len})).1 hrowChunk with",
            "      ⟨i, hi, rfl⟩",
            f"    have hi' : i < {row_count(row_len)} := by simpa using hi",
            "    clear hi",
            "    rcases (mem_positiveEdgeFixedKChunks_iff",
            f"        (by norm_num : 0 < {edge_k_len})).1 hedgeChunk with",
            "      ⟨j, hj, rfl⟩",
            f"    have hj' : j < {edge_k_count(edge_k_len)} := by simpa using hj",
            "    clear hj",
        ]
    )
    lines.extend(
        exact_case_tree_lines(
            [("i", row_count(row_len)), ("j", edge_k_count(edge_k_len))],
            lambda i, j: single_chunk_name(
                theorem_prefix, "edge-fixed", i, None, j
            ),
        )
    )


def add_row_fixed_edge_dispatch_field(
    lines: list[str], field_name: str, row_len: int, edge_k_len: int
) -> None:
    lines.extend(
        [
            f"  {field_name} := by",
            "    intro rowChunk hrowChunk edgeChunk hedgeChunk",
            "    rcases (mem_positiveSaddleFixedRowChunks_iff",
            f"        (by norm_num : 0 < {row_len})).1 hrowChunk with",
            "      ⟨i, hi, rfl⟩",
            f"    have hi' : i < {row_count(row_len)} := by simpa using hi",
            "    clear hi",
            "    rcases (mem_positiveEdgeFixedKChunks_iff",
            f"        (by norm_num : 0 < {edge_k_len})).1 hedgeChunk with",
            "      ⟨j, hj, rfl⟩",
            f"    have hj' : j < {edge_k_count(edge_k_len)} := by simpa using hj",
            "    clear hj",
            "    interval_cases i; interval_cases j; native_decide",
        ]
    )


def add_row_dispatch_field(
    lines: list[str], field_name: str, row_len: int, row_bound: int
) -> None:
    lines.extend(
        [
            f"  {field_name} := by",
            "    intro rowChunk hrowChunk",
            "    rcases (mem_positiveSaddleFixedRowChunks_iff",
            f"        (by norm_num : 0 < {row_len})).1 hrowChunk with",
            "      \u27e8i, hi, rfl\u27e9",
            f"    have hi' : i < {row_bound} := by simpa using hi",
            "    clear hi",
            "    interval_cases i; native_decide",
        ]
    )


def add_row_dispatch_field_from_single_chunks(
    lines: list[str],
    field_name: str,
    row_len: int,
    chunk_field: str,
    theorem_prefix: str,
) -> None:
    lines.extend(
        [
            f"  {field_name} := by",
            "    intro rowChunk hrowChunk",
            "    rcases (mem_positiveSaddleFixedRowChunks_iff",
            f"        (by norm_num : 0 < {row_len})).1 hrowChunk with",
            "      ⟨i, hi, rfl⟩",
            f"    have hi' : i < {row_count(row_len)} := by simpa using hi",
            "    clear hi",
        ]
    )
    lines.extend(
        exact_case_tree_lines(
            [("i", row_count(row_len))],
            lambda i: single_chunk_name(theorem_prefix, chunk_field, i),
        )
    )


def add_tangent_row_k_dispatch_field(
    lines: list[str], field_name: str, row_len: int, k_len: int
) -> None:
    lines.extend(
        [
            f"  {field_name} := by",
            "    intro rowChunk hrowChunk kChunk hkChunk",
            "    rcases (mem_positiveSaddleFixedRowChunks_iff",
            f"        (by norm_num : 0 < {row_len})).1 hrowChunk with",
            "      \u27e8i, hi, rfl\u27e9",
            f"    have hi' : i < {row_count(row_len)} := by simpa using hi",
            "    clear hi",
            "    rcases (mem_positiveTangentFixedKChunks_iff",
            f"        (by norm_num : 0 < {k_len})).1 hkChunk with",
            "      \u27e8j, hj, rfl\u27e9",
            f"    have hj' : j < {tangent_k_count(k_len)} := by simpa using hj",
            "    clear hj",
            "    interval_cases i; interval_cases j; native_decide",
        ]
    )


def add_tangent_row_k_dispatch_field_from_single_chunks(
    lines: list[str],
    field_name: str,
    row_len: int,
    k_len: int,
    theorem_prefix: str,
) -> None:
    lines.extend(
        [
            f"  {field_name} := by",
            "    intro rowChunk hrowChunk kChunk hkChunk",
            "    rcases (mem_positiveSaddleFixedRowChunks_iff",
            f"        (by norm_num : 0 < {row_len})).1 hrowChunk with",
            "      ⟨i, hi, rfl⟩",
            f"    have hi' : i < {row_count(row_len)} := by simpa using hi",
            "    clear hi",
            "    rcases (mem_positiveTangentFixedKChunks_iff",
            f"        (by norm_num : 0 < {k_len})).1 hkChunk with",
            "      ⟨j, hj, rfl⟩",
            f"    have hj' : j < {tangent_k_count(k_len)} := by simpa using hj",
            "    clear hj",
        ]
    )
    lines.extend(
        exact_case_tree_lines(
            [("i", row_count(row_len)), ("j", tangent_k_count(k_len))],
            lambda i, j: single_chunk_name(theorem_prefix, "tangent", i, None, j),
        )
    )


def add_tangent_row_n_k_dispatch_field(
    lines: list[str], field_name: str, row_len: int, n_len: int, k_len: int
) -> None:
    lines.extend(
        [
            f"  {field_name} := by",
            "    intro rowChunk hrowChunk nIndex hnIndex kChunk hkChunk",
            "    rcases (mem_positiveSaddleFixedRowChunks_iff",
            f"        (by norm_num : 0 < {row_len})).1 hrowChunk with",
            "      ⟨i, hi, rfl⟩",
            f"    have hi' : i < {row_count(row_len)} := by simpa using hi",
            "    clear hi",
            "    have hnIndex' :",
            f"        nIndex < {product_n_index_count(row_len, n_len)} := by",
            "      simpa using",
            "        (mem_positiveProductFixedNChunkIndices_iff",
            f"          (by norm_num : 0 < {n_len})).1 hnIndex",
            "    clear hnIndex",
            "    rcases (mem_positiveTangentFixedKChunks_iff",
            f"        (by norm_num : 0 < {k_len})).1 hkChunk with",
            "      ⟨j, hj, rfl⟩",
            f"    have hj' : j < {tangent_k_count(k_len)} := by simpa using hj",
            "    clear hj",
            "    interval_cases i; interval_cases nIndex; interval_cases j; native_decide",
        ]
    )


def add_tangent_row_n_k_dispatch_field_from_single_chunks(
    lines: list[str],
    field_name: str,
    row_len: int,
    n_len: int,
    k_len: int,
    theorem_prefix: str,
) -> None:
    lines.extend(
        [
            f"  {field_name} := by",
            "    intro rowChunk hrowChunk nIndex hnIndex kChunk hkChunk",
            "    rcases (mem_positiveSaddleFixedRowChunks_iff",
            f"        (by norm_num : 0 < {row_len})).1 hrowChunk with",
            "      ⟨i, hi, rfl⟩",
            f"    have hi' : i < {row_count(row_len)} := by simpa using hi",
            "    clear hi",
            "    have hnIndex' :",
            f"        nIndex < {product_n_index_count(row_len, n_len)} := by",
            "      simpa using",
            "        (mem_positiveProductFixedNChunkIndices_iff",
            f"          (by norm_num : 0 < {n_len})).1 hnIndex",
            "    clear hnIndex",
            "    rcases (mem_positiveTangentFixedKChunks_iff",
            f"        (by norm_num : 0 < {k_len})).1 hkChunk with",
            "      ⟨j, hj, rfl⟩",
            f"    have hj' : j < {tangent_k_count(k_len)} := by simpa using hj",
            "    clear hj",
        ]
    )
    lines.extend(
        exact_case_tree_lines(
            [
                ("i", row_count(row_len)),
                ("nIndex", product_n_index_count(row_len, n_len)),
                ("j", tangent_k_count(k_len)),
            ],
            lambda i, n, j: single_chunk_name(
                theorem_prefix, "tangent-n", i, n, j
            ),
        )
    )


def add_solo_row_n_dispatch_field(
    lines: list[str], field_name: str, row_len: int, n_len: int
) -> None:
    lines.extend(
        [
            f"  {field_name} := by",
            "    intro rowChunk hrowChunk nIndex hnIndex",
            "    rcases (mem_positiveSaddleFixedRowChunks_iff",
            f"        (by norm_num : 0 < {row_len})).1 hrowChunk with",
            "      ⟨i, hi, rfl⟩",
            f"    have hi' : i < {row_count(row_len)} := by simpa using hi",
            "    clear hi",
            "    have hnIndex' :",
            f"        nIndex < {product_n_index_count(row_len, n_len)} := by",
            "      simpa using",
            "        (mem_positiveProductFixedNChunkIndices_iff",
            f"          (by norm_num : 0 < {n_len})).1 hnIndex",
            "    clear hnIndex",
            "    interval_cases i; interval_cases nIndex; native_decide",
        ]
    )


def add_solo_row_n_dispatch_field_from_single_chunks(
    lines: list[str],
    field_name: str,
    row_len: int,
    n_len: int,
    chunk_field: str,
    theorem_prefix: str,
) -> None:
    lines.extend(
        [
            f"  {field_name} := by",
            "    intro rowChunk hrowChunk nIndex hnIndex",
            "    rcases (mem_positiveSaddleFixedRowChunks_iff",
            f"        (by norm_num : 0 < {row_len})).1 hrowChunk with",
            "      ⟨i, hi, rfl⟩",
            f"    have hi' : i < {row_count(row_len)} := by simpa using hi",
            "    clear hi",
            "    have hnIndex' :",
            f"        nIndex < {product_n_index_count(row_len, n_len)} := by",
            "      simpa using",
            "        (mem_positiveProductFixedNChunkIndices_iff",
            f"          (by norm_num : 0 < {n_len})).1 hnIndex",
            "    clear hnIndex",
        ]
    )
    lines.extend(
        exact_case_tree_lines(
            [("i", row_count(row_len)), ("nIndex", product_n_index_count(row_len, n_len))],
            lambda i, n: single_chunk_name(theorem_prefix, chunk_field, i, n),
        )
    )


def add_product_row_n_edge_dispatch_field(
    lines: list[str], field_name: str, row_len: int, n_len: int
) -> None:
    lines.extend(
        [
            f"  {field_name} := by",
            "    intro rowChunk hrowChunk nIndex hnIndex edgeChunk hedgeChunk",
            "    rcases (mem_positiveSaddleFixedRowChunks_iff",
            f"        (by norm_num : 0 < {row_len})).1 hrowChunk with",
            "      ⟨i, hi, rfl⟩",
            f"    have hi' : i < {row_count(row_len)} := by simpa using hi",
            "    clear hi",
            "    have hnIndex' :",
            f"        nIndex < {product_n_index_count(row_len, n_len)} := by",
            "      simpa using",
            "        (mem_positiveProductFixedNChunkIndices_iff",
            f"          (by norm_num : 0 < {n_len})).1 hnIndex",
            "    clear hnIndex",
            "    rcases (mem_positiveEdgeDefaultKChunks_iff).1 hedgeChunk with",
            "      ⟨j, hj, rfl⟩",
            "    have hj' : j < 90 := by simpa using hj",
            "    clear hj",
            "    interval_cases i; interval_cases nIndex; interval_cases j; native_decide",
        ]
    )


def add_product_row_n_edge_dispatch_field_from_single_chunks(
    lines: list[str],
    field_name: str,
    row_len: int,
    n_len: int,
    chunk_field: str,
    theorem_prefix: str,
) -> None:
    lines.extend(
        [
            f"  {field_name} := by",
            "    intro rowChunk hrowChunk nIndex hnIndex edgeChunk hedgeChunk",
            "    rcases (mem_positiveSaddleFixedRowChunks_iff",
            f"        (by norm_num : 0 < {row_len})).1 hrowChunk with",
            "      ⟨i, hi, rfl⟩",
            f"    have hi' : i < {row_count(row_len)} := by simpa using hi",
            "    clear hi",
            "    have hnIndex' :",
            f"        nIndex < {product_n_index_count(row_len, n_len)} := by",
            "      simpa using",
            "        (mem_positiveProductFixedNChunkIndices_iff",
            f"          (by norm_num : 0 < {n_len})).1 hnIndex",
            "    clear hnIndex",
            "    rcases (mem_positiveEdgeDefaultKChunks_iff).1 hedgeChunk with",
            "      ⟨j, hj, rfl⟩",
            "    have hj' : j < 90 := by simpa using hj",
            "    clear hj",
        ]
    )
    lines.extend(
        exact_case_tree_lines(
            [
                ("i", row_count(row_len)),
                ("nIndex", product_n_index_count(row_len, n_len)),
                ("j", 90),
            ],
            lambda i, n, j: single_chunk_name(
                theorem_prefix, chunk_field, i, n, j
            ),
        )
    )


def add_product_row_n_product_k_dispatch_field(
    lines: list[str],
    field_name: str,
    row_len: int,
    n_len: int,
    product_k_len: int,
) -> None:
    lines.extend(
        [
            f"  {field_name} := by",
            "    intro rowChunk hrowChunk nIndex hnIndex productKChunk hproductKChunk",
            "    rcases (mem_positiveSaddleFixedRowChunks_iff",
            f"        (by norm_num : 0 < {row_len})).1 hrowChunk with",
            "      ⟨i, hi, rfl⟩",
            f"    have hi' : i < {row_count(row_len)} := by simpa using hi",
            "    clear hi",
            "    have hnIndex' :",
            f"        nIndex < {product_n_index_count(row_len, n_len)} := by",
            "      simpa using",
            "        (mem_positiveProductFixedNChunkIndices_iff",
            f"          (by norm_num : 0 < {n_len})).1 hnIndex",
            "    clear hnIndex",
            "    rcases (mem_positiveProductFixedKChunks_iff",
            f"        (by norm_num : 0 < {product_k_len})).1 hproductKChunk with",
            "      ⟨j, hj, rfl⟩",
            f"    have hj' : j < {product_k_count(product_k_len)} := by simpa using hj",
            "    clear hj",
            "    interval_cases i; interval_cases nIndex; interval_cases j; native_decide",
        ]
    )


def add_product_row_n_product_k_dispatch_field_from_single_chunks(
    lines: list[str],
    field_name: str,
    row_len: int,
    n_len: int,
    product_k_len: int,
    chunk_field: str,
    theorem_prefix: str,
) -> None:
    lines.extend(
        [
            f"  {field_name} := by",
            "    intro rowChunk hrowChunk nIndex hnIndex productKChunk hproductKChunk",
            "    rcases (mem_positiveSaddleFixedRowChunks_iff",
            f"        (by norm_num : 0 < {row_len})).1 hrowChunk with",
            "      ⟨i, hi, rfl⟩",
            f"    have hi' : i < {row_count(row_len)} := by simpa using hi",
            "    clear hi",
            "    have hnIndex' :",
            f"        nIndex < {product_n_index_count(row_len, n_len)} := by",
            "      simpa using",
            "        (mem_positiveProductFixedNChunkIndices_iff",
            f"          (by norm_num : 0 < {n_len})).1 hnIndex",
            "    clear hnIndex",
            "    rcases (mem_positiveProductFixedKChunks_iff",
            f"        (by norm_num : 0 < {product_k_len})).1 hproductKChunk with",
            "      ⟨j, hj, rfl⟩",
            f"    have hj' : j < {product_k_count(product_k_len)} := by simpa using hj",
            "    clear hj",
        ]
    )
    lines.extend(
        exact_case_tree_lines(
            [
                ("i", row_count(row_len)),
                ("nIndex", product_n_index_count(row_len, n_len)),
                ("j", product_k_count(product_k_len)),
            ],
            lambda i, n, j: single_chunk_name(
                theorem_prefix, chunk_field, i, n, j
            ),
        )
    )


def tangent_cell_provider_binder(with_colon: bool) -> list[str]:
    last = (
        "          checkPositiveSmallTangentExpEdgeCell a N k = true) :"
        if with_colon
        else "          checkPositiveSmallTangentExpEdgeCell a N k = true)"
    )
    return [
        "    (htangent :",
        "      \u2200 {a N k : Nat}, 401 \u2264 a \u2192 a \u2264 2000 \u2192 positiveRectangle a N \u2192",
        "        k \u2208 positiveKRange a \u2192 k \u2264 ceilSqrt N \u2192",
        last,
    ]


def emit_all_chunks(args: argparse.Namespace) -> str:
    p = args.product_row_len
    t = args.tangent_row_len
    ss = args.solo_saddle_row_len
    sb = args.solo_budget_row_len
    e = args.edge_row_len
    n = args.n_len
    name = args.name
    final_name = f"coefficientNegativity_of_{name}"

    lines = emit_header(args)
    lines.extend(
        [
            f"theorem {name} :",
            "    PositiveSaddleFixedFiniteWindowAllChunksAuditCertificate",
            f"      {p} {t} {ss} {sb} {e} {n} where",
        ]
    )
    add_positive_fields(lines)
    lines.extend(
        [
            "  smallXYProductRawClearedTableFixedRowKChunks := by",
            "    native_decide",
            "  temperedXYProductRawClearedTableFixedRowKChunks := by",
            "    native_decide",
            "  smallTangentExpEdgeFixedRows := by",
            "    native_decide",
            "  soloYSaddleClearedFixedRows := by",
            "    native_decide",
            "  soloYBudgetFixedRows := by",
            "    native_decide",
            "  edgeKChunkUnitFixedRowKChunks := by",
            "    native_decide",
        ]
    )

    if args.emit_final:
        lines.extend(
            [
                "",
                f"theorem {final_name}",
                *final_tail_binder_lines(args),
                "    CoefficientNegativity :=",
                "  coefficientNegativity_of_positiveSaddleFixedFiniteWindowAllChunksAuditCertificate",
                f"    {name} {final_tail_arg(args)}",
            ]
        )

    lines.extend(["", "end Prop51", ""])
    return "\n".join(lines)


def emit_split_fields(args: argparse.Namespace) -> str:
    p = args.product_row_len
    t = args.tangent_row_len
    ss = args.solo_saddle_row_len
    sb = args.solo_budget_row_len
    e = args.edge_row_len
    n = args.n_len
    name = args.name
    final_name = f"coefficientNegativity_of_{name}"

    lines = emit_header(args)
    lines.extend(
        [
            f"theorem {name} :",
            "    PositiveSaddleFixedFiniteWindowAuditCertificate",
            f"      {p} {t} {ss} {sb} {e} {n} where",
        ]
    )
    add_positive_fields(lines)
    add_row_edge_dispatch_field(
        lines,
        "smallXYProductRawClearedTableProductRowRangeKChunks",
        p,
        row_count(p),
    )
    add_row_edge_dispatch_field(
        lines,
        "temperedXYProductRawClearedTableProductRowRangeKChunks",
        p,
        row_count(p),
    )
    add_row_dispatch_field(
        lines,
        "smallTangentExpEdgeRowRangeChunks",
        t,
        row_count(t),
    )
    add_row_dispatch_field(
        lines,
        "soloYSaddleClearedRowRangeChunks",
        ss,
        row_count(ss),
    )
    add_row_dispatch_field(
        lines,
        "soloYBudgetRowRangeChunks",
        sb,
        row_count(sb),
    )
    add_row_edge_dispatch_field(
        lines,
        "edgeKChunkUnitRowRanges",
        e,
        row_count(e),
    )

    if args.emit_final:
        lines.extend(
            [
                "",
                f"theorem {final_name}",
                *final_tail_binder_lines(args),
                "    CoefficientNegativity :=",
                "  coefficientNegativity_of_positiveSaddleFixedFiniteWindowAuditCertificate",
                f"    {name} {final_tail_arg(args)}",
            ]
        )

    lines.extend(["", "end Prop51", ""])
    return "\n".join(lines)


def emit_cell_tangent(args: argparse.Namespace) -> str:
    p = args.product_row_len
    ss = args.solo_saddle_row_len
    sb = args.solo_budget_row_len
    e = args.edge_row_len
    n = args.n_len
    name = args.name
    final_name = f"coefficientNegativity_of_{name}"

    lines = emit_header(args)
    lines.extend(
        [
            f"theorem {name}",
            *tangent_cell_provider_binder(with_colon=True),
            "    PositiveSaddleFixedFiniteWindowCellTangentAuditCertificate",
            f"      {p} {ss} {sb} {e} {n} where",
            "  productRowLenPos := by norm_num",
            "  soloSaddleRowLenPos := by norm_num",
            "  soloBudgetRowLenPos := by norm_num",
            "  edgeRowLenPos := by norm_num",
            "  nLenPos := by norm_num",
        ]
    )
    add_row_edge_dispatch_field(
        lines,
        "smallXYProductRawClearedTableProductRowRangeKChunks",
        p,
        row_count(p),
    )
    add_row_edge_dispatch_field(
        lines,
        "temperedXYProductRawClearedTableProductRowRangeKChunks",
        p,
        row_count(p),
    )
    lines.append("  smallTangentExpEdgeCells := htangent")
    add_row_dispatch_field(
        lines,
        "soloYSaddleClearedRowRangeChunks",
        ss,
        row_count(ss),
    )
    add_row_dispatch_field(
        lines,
        "soloYBudgetRowRangeChunks",
        sb,
        row_count(sb),
    )
    add_row_edge_dispatch_field(
        lines,
        "edgeKChunkUnitRowRanges",
        e,
        row_count(e),
    )

    if args.emit_final:
        lines.extend(
            [
                "",
                f"theorem {final_name}",
                *tangent_cell_provider_binder(with_colon=False),
                *final_tail_binder_lines(args),
                "    CoefficientNegativity :=",
                "  coefficientNegativity_of_positiveSaddleFixedFiniteWindowCellTangentAuditCertificate",
                f"    ({name} htangent) {final_tail_arg(args)}",
            ]
        )

    lines.extend(["", "end Prop51", ""])
    return "\n".join(lines)


def emit_chunked_tangent(args: argparse.Namespace) -> str:
    p = args.product_row_len
    t = args.tangent_row_len
    ss = args.solo_saddle_row_len
    sb = args.solo_budget_row_len
    e = args.edge_row_len
    product_n = args.n_len
    tangent_n = args.tangent_n_len
    tangent_k = args.tangent_k_len
    name = args.name
    final_name = f"coefficientNegativity_of_{name}"

    lines = emit_header(args)
    lines.extend(
        [
            f"theorem {name} :",
            "    PositiveSaddleFixedFiniteWindowChunkedTangentAuditCertificate",
            f"      {p} {t} {ss} {sb} {e}",
            f"      {product_n} {tangent_n} {tangent_k} where",
            "  productRowLenPos := by norm_num",
            "  tangentRowLenPos := by norm_num",
            "  soloSaddleRowLenPos := by norm_num",
            "  soloBudgetRowLenPos := by norm_num",
            "  edgeRowLenPos := by norm_num",
            "  productNLenPos := by norm_num",
            "  tangentNLenPos := by norm_num",
            "  tangentKLenPos := by norm_num",
        ]
    )
    add_row_edge_dispatch_field(
        lines,
        "smallXYProductRawClearedTableProductRowRangeKChunks",
        p,
        row_count(p),
    )
    add_row_edge_dispatch_field(
        lines,
        "temperedXYProductRawClearedTableProductRowRangeKChunks",
        p,
        row_count(p),
    )
    add_tangent_row_k_dispatch_field(
        lines,
        "smallTangentExpEdgeRowRangeNChunksKChunks",
        t,
        tangent_k,
    )
    add_row_dispatch_field(
        lines,
        "soloYSaddleClearedRowRangeChunks",
        ss,
        row_count(ss),
    )
    add_row_dispatch_field(
        lines,
        "soloYBudgetRowRangeChunks",
        sb,
        row_count(sb),
    )
    add_row_edge_dispatch_field(
        lines,
        "edgeKChunkUnitRowRanges",
        e,
        row_count(e),
    )

    if args.emit_final:
        lines.extend(
            [
                "",
                f"theorem {final_name}",
                *final_tail_binder_lines(args),
                "    CoefficientNegativity :=",
                "  coefficientNegativity_of_positiveSaddleFixedFiniteWindowChunkedTangentAuditCertificate",
                f"    {name} {final_tail_arg(args)}",
            ]
        )

    lines.extend(["", "end Prop51", ""])
    return "\n".join(lines)


def product_n_chunked_tangent_theorem_lines(args: argparse.Namespace) -> list[str]:
    p = args.product_row_len
    t = args.tangent_row_len
    ss = args.solo_saddle_row_len
    sb = args.solo_budget_row_len
    e = args.edge_row_len
    product_n = args.n_len
    tangent_n = args.tangent_n_len
    tangent_k = args.tangent_k_len
    name = args.name
    final_name = f"coefficientNegativity_of_{name}"

    lines = [
        f"theorem {name} :",
        "    PositiveSaddleFixedFiniteWindowProductNChunkedTangentAuditCertificate",
        f"      {p} {t} {ss} {sb} {e}",
        f"      {product_n} {tangent_n} {tangent_k} where",
        "  productRowLenPos := by norm_num",
        "  tangentRowLenPos := by norm_num",
        "  soloSaddleRowLenPos := by norm_num",
        "  soloBudgetRowLenPos := by norm_num",
        "  edgeRowLenPos := by norm_num",
        "  productNLenPos := by norm_num",
        "  tangentNLenPos := by norm_num",
        "  tangentKLenPos := by norm_num",
    ]
    if args.use_single_chunk_theorems:
        add_product_row_n_edge_dispatch_field_from_single_chunks(
            lines,
            "smallXYProductRawClearedTableProductRowRangeNIndexKChunks",
            p,
            product_n,
            "product-small",
            args.single_chunk_prefix,
        )
        add_product_row_n_edge_dispatch_field_from_single_chunks(
            lines,
            "temperedXYProductRawClearedTableProductRowRangeNIndexKChunks",
            p,
            product_n,
            "product-tempered",
            args.single_chunk_prefix,
        )
        add_tangent_row_k_dispatch_field_from_single_chunks(
            lines,
            "smallTangentExpEdgeRowRangeNChunksKChunks",
            t,
            tangent_k,
            args.single_chunk_prefix,
        )
        add_row_dispatch_field_from_single_chunks(
            lines,
            "soloYSaddleClearedRowRangeChunks",
            ss,
            "solo-saddle",
            args.single_chunk_prefix,
        )
        add_row_dispatch_field_from_single_chunks(
            lines,
            "soloYBudgetRowRangeChunks",
            sb,
            "solo-budget",
            args.single_chunk_prefix,
        )
        add_row_edge_dispatch_field_from_single_chunks(
            lines,
            "edgeKChunkUnitRowRanges",
            e,
            "edge",
            args.single_chunk_prefix,
        )
    else:
        add_product_row_n_edge_dispatch_field(
            lines,
            "smallXYProductRawClearedTableProductRowRangeNIndexKChunks",
            p,
            product_n,
        )
        add_product_row_n_edge_dispatch_field(
            lines,
            "temperedXYProductRawClearedTableProductRowRangeNIndexKChunks",
            p,
            product_n,
        )
        add_tangent_row_k_dispatch_field(
            lines,
            "smallTangentExpEdgeRowRangeNChunksKChunks",
            t,
            tangent_k,
        )
        add_row_dispatch_field(
            lines,
            "soloYSaddleClearedRowRangeChunks",
            ss,
            row_count(ss),
        )
        add_row_dispatch_field(
            lines,
            "soloYBudgetRowRangeChunks",
            sb,
            row_count(sb),
        )
        add_row_edge_dispatch_field(
            lines,
            "edgeKChunkUnitRowRanges",
            e,
            row_count(e),
        )

    if args.emit_final:
        lines.extend(
            [
                "",
                f"theorem {final_name}",
                *final_tail_binder_lines(args),
                "    CoefficientNegativity :=",
                "  coefficientNegativity_of_positiveSaddleFixedFiniteWindowProductNChunkedTangentAuditCertificate",
                f"    {name} {final_tail_arg(args)}",
            ]
        )

    return lines


def emit_product_n_chunked_tangent(args: argparse.Namespace) -> str:
    lines = emit_header(args)
    lines.extend(product_n_chunked_tangent_theorem_lines(args))
    lines.extend(["", "end Prop51", ""])
    return "\n".join(lines)


def product_tangent_solo_n_chunked_theorem_lines(args: argparse.Namespace) -> list[str]:
    p = args.product_row_len
    t = args.tangent_row_len
    ss = args.solo_saddle_row_len
    sb = args.solo_budget_row_len
    e = args.edge_row_len
    product_n = args.n_len
    tangent_n = args.tangent_n_len
    solo_saddle_n = args.solo_saddle_n_len
    solo_budget_n = args.solo_budget_n_len
    tangent_k = args.tangent_k_len
    name = args.name
    final_name = f"coefficientNegativity_of_{name}"

    lines = [
        f"theorem {name} :",
        "    PositiveSaddleFixedFiniteWindowProductTangentSoloNChunkedAuditCertificate",
        f"      {p} {t} {ss} {sb} {e}",
        f"      {product_n} {tangent_n} {solo_saddle_n} {solo_budget_n} {tangent_k} where",
        "  productRowLenPos := by norm_num",
        "  tangentRowLenPos := by norm_num",
        "  soloSaddleRowLenPos := by norm_num",
        "  soloBudgetRowLenPos := by norm_num",
        "  edgeRowLenPos := by norm_num",
        "  productNLenPos := by norm_num",
        "  tangentNLenPos := by norm_num",
        "  soloSaddleNLenPos := by norm_num",
        "  soloBudgetNLenPos := by norm_num",
        "  tangentKLenPos := by norm_num",
    ]
    if args.use_single_chunk_theorems:
        add_product_row_n_edge_dispatch_field_from_single_chunks(
            lines,
            "smallXYProductRawClearedTableProductRowRangeNIndexKChunks",
            p,
            product_n,
            "product-small",
            args.single_chunk_prefix,
        )
        add_product_row_n_edge_dispatch_field_from_single_chunks(
            lines,
            "temperedXYProductRawClearedTableProductRowRangeNIndexKChunks",
            p,
            product_n,
            "product-tempered",
            args.single_chunk_prefix,
        )
        add_tangent_row_n_k_dispatch_field_from_single_chunks(
            lines,
            "smallTangentExpEdgeRowRangeNIndexKChunks",
            t,
            tangent_n,
            tangent_k,
            args.single_chunk_prefix,
        )
        add_solo_row_n_dispatch_field_from_single_chunks(
            lines,
            "soloYSaddleClearedRowRangeNIndexChunks",
            ss,
            solo_saddle_n,
            "solo-saddle-n",
            args.single_chunk_prefix,
        )
        add_solo_row_n_dispatch_field_from_single_chunks(
            lines,
            "soloYBudgetRowRangeNIndexChunks",
            sb,
            solo_budget_n,
            "solo-budget-n",
            args.single_chunk_prefix,
        )
        add_row_edge_dispatch_field_from_single_chunks(
            lines,
            "edgeKChunkUnitRowRanges",
            e,
            "edge",
            args.single_chunk_prefix,
        )
    else:
        add_product_row_n_edge_dispatch_field(
            lines,
            "smallXYProductRawClearedTableProductRowRangeNIndexKChunks",
            p,
            product_n,
        )
        add_product_row_n_edge_dispatch_field(
            lines,
            "temperedXYProductRawClearedTableProductRowRangeNIndexKChunks",
            p,
            product_n,
        )
        add_tangent_row_n_k_dispatch_field(
            lines,
            "smallTangentExpEdgeRowRangeNIndexKChunks",
            t,
            tangent_n,
            tangent_k,
        )
        add_solo_row_n_dispatch_field(
            lines,
            "soloYSaddleClearedRowRangeNIndexChunks",
            ss,
            solo_saddle_n,
        )
        add_solo_row_n_dispatch_field(
            lines,
            "soloYBudgetRowRangeNIndexChunks",
            sb,
            solo_budget_n,
        )
        add_row_edge_dispatch_field(
            lines,
            "edgeKChunkUnitRowRanges",
            e,
            row_count(e),
        )

    if args.emit_final:
        lines.extend(
            [
                "",
                f"theorem {final_name}",
                *final_tail_binder_lines(args),
                "    CoefficientNegativity :=",
                "  coefficientNegativity_of_positiveSaddleFixedFiniteWindowProductTangentSoloNChunkedAuditCertificate",
                f"    {name} {final_tail_arg(args)}",
            ]
        )

    return lines


def product_nk_tangent_solo_n_chunked_theorem_lines(
    args: argparse.Namespace,
) -> list[str]:
    p = args.product_row_len
    t = args.tangent_row_len
    ss = args.solo_saddle_row_len
    sb = args.solo_budget_row_len
    e = args.edge_row_len
    product_n = args.n_len
    product_k = args.product_k_len
    tangent_n = args.tangent_n_len
    solo_saddle_n = args.solo_saddle_n_len
    solo_budget_n = args.solo_budget_n_len
    tangent_k = args.tangent_k_len
    name = args.name
    final_name = f"coefficientNegativity_of_{name}"

    lines = [
        f"theorem {name} :",
        "    PositiveSaddleFixedFiniteWindowProductNKChunkedTangentSoloNChunkedAuditCertificate",
        f"      {p} {t} {ss} {sb} {e}",
        f"      {product_n} {product_k} {tangent_n} {solo_saddle_n} {solo_budget_n}",
        f"      {tangent_k} where",
        "  productRowLenPos := by norm_num",
        "  tangentRowLenPos := by norm_num",
        "  soloSaddleRowLenPos := by norm_num",
        "  soloBudgetRowLenPos := by norm_num",
        "  edgeRowLenPos := by norm_num",
        "  productNLenPos := by norm_num",
        "  productKLenPos := by norm_num",
        "  tangentNLenPos := by norm_num",
        "  soloSaddleNLenPos := by norm_num",
        "  soloBudgetNLenPos := by norm_num",
        "  tangentKLenPos := by norm_num",
    ]
    if args.use_single_chunk_theorems:
        add_product_row_n_product_k_dispatch_field_from_single_chunks(
            lines,
            "smallXYProductRawClearedTableProductRowRangeNIndexKChunks",
            p,
            product_n,
            product_k,
            "product-small",
            args.single_chunk_prefix,
        )
        add_product_row_n_product_k_dispatch_field_from_single_chunks(
            lines,
            "temperedXYProductRawClearedTableProductRowRangeNIndexKChunks",
            p,
            product_n,
            product_k,
            "product-tempered",
            args.single_chunk_prefix,
        )
        add_tangent_row_n_k_dispatch_field_from_single_chunks(
            lines,
            "smallTangentExpEdgeRowRangeNIndexKChunks",
            t,
            tangent_n,
            tangent_k,
            args.single_chunk_prefix,
        )
        add_solo_row_n_dispatch_field_from_single_chunks(
            lines,
            "soloYSaddleClearedRowRangeNIndexChunks",
            ss,
            solo_saddle_n,
            "solo-saddle-n",
            args.single_chunk_prefix,
        )
        add_solo_row_n_dispatch_field_from_single_chunks(
            lines,
            "soloYBudgetRowRangeNIndexChunks",
            sb,
            solo_budget_n,
            "solo-budget-n",
            args.single_chunk_prefix,
        )
        add_row_edge_dispatch_field_from_single_chunks(
            lines,
            "edgeKChunkUnitRowRanges",
            e,
            "edge",
            args.single_chunk_prefix,
        )
    else:
        add_product_row_n_product_k_dispatch_field(
            lines,
            "smallXYProductRawClearedTableProductRowRangeNIndexKChunks",
            p,
            product_n,
            product_k,
        )
        add_product_row_n_product_k_dispatch_field(
            lines,
            "temperedXYProductRawClearedTableProductRowRangeNIndexKChunks",
            p,
            product_n,
            product_k,
        )
        add_tangent_row_n_k_dispatch_field(
            lines,
            "smallTangentExpEdgeRowRangeNIndexKChunks",
            t,
            tangent_n,
            tangent_k,
        )
        add_solo_row_n_dispatch_field(
            lines,
            "soloYSaddleClearedRowRangeNIndexChunks",
            ss,
            solo_saddle_n,
        )
        add_solo_row_n_dispatch_field(
            lines,
            "soloYBudgetRowRangeNIndexChunks",
            sb,
            solo_budget_n,
        )
        add_row_edge_dispatch_field(
            lines,
            "edgeKChunkUnitRowRanges",
            e,
            row_count(e),
        )

    if args.emit_final:
        lines.extend(
            [
                "",
                f"theorem {final_name}",
                *final_tail_binder_lines(args),
                "    CoefficientNegativity :=",
                "  coefficientNegativity_of_positiveSaddleFixedFiniteWindowProductNKChunkedTangentSoloNChunkedAuditCertificate",
                f"    {name} {final_tail_arg(args)}",
            ]
        )

    return lines


def combined_product_nk_tangent_solo_n_chunked_theorem_lines(
    args: argparse.Namespace,
) -> list[str]:
    p = args.product_row_len
    t = args.tangent_row_len
    ss = args.solo_saddle_row_len
    sb = args.solo_budget_row_len
    e = args.edge_row_len
    product_n = args.n_len
    product_k = args.product_k_len
    tangent_n = args.tangent_n_len
    solo_saddle_n = args.solo_saddle_n_len
    solo_budget_n = args.solo_budget_n_len
    tangent_k = args.tangent_k_len
    name = args.name
    final_name = f"coefficientNegativity_of_{name}"

    lines = [
        f"theorem {name} :",
        "    PositiveSaddleFixedFiniteWindowCombinedProductNKChunkedTangentSoloNChunkedAuditCertificate",
        f"      {p} {t} {ss} {sb} {e}",
        f"      {product_n} {product_k} {tangent_n} {solo_saddle_n} {solo_budget_n}",
        f"      {tangent_k} where",
        "  productRowLenPos := by norm_num",
        "  tangentRowLenPos := by norm_num",
        "  soloSaddleRowLenPos := by norm_num",
        "  soloBudgetRowLenPos := by norm_num",
        "  edgeRowLenPos := by norm_num",
        "  productNLenPos := by norm_num",
        "  productKLenPos := by norm_num",
        "  tangentNLenPos := by norm_num",
        "  soloSaddleNLenPos := by norm_num",
        "  soloBudgetNLenPos := by norm_num",
        "  tangentKLenPos := by norm_num",
    ]
    if args.use_single_chunk_theorems:
        add_product_row_n_product_k_dispatch_field_from_single_chunks(
            lines,
            "xyProductRawClearedTableProductRowRangeNIndexKChunks",
            p,
            product_n,
            product_k,
            "product-combined",
            args.single_chunk_prefix,
        )
        add_tangent_row_n_k_dispatch_field_from_single_chunks(
            lines,
            "smallTangentExpEdgeRowRangeNIndexKChunks",
            t,
            tangent_n,
            tangent_k,
            args.single_chunk_prefix,
        )
        add_solo_row_n_dispatch_field_from_single_chunks(
            lines,
            "soloYSaddleClearedRowRangeNIndexChunks",
            ss,
            solo_saddle_n,
            "solo-saddle-n",
            args.single_chunk_prefix,
        )
        add_solo_row_n_dispatch_field_from_single_chunks(
            lines,
            "soloYBudgetRowRangeNIndexChunks",
            sb,
            solo_budget_n,
            "solo-budget-n",
            args.single_chunk_prefix,
        )
        add_row_edge_dispatch_field_from_single_chunks(
            lines,
            "edgeKChunkUnitRowRanges",
            e,
            "edge",
            args.single_chunk_prefix,
        )
    else:
        add_product_row_n_product_k_dispatch_field(
            lines,
            "xyProductRawClearedTableProductRowRangeNIndexKChunks",
            p,
            product_n,
            product_k,
        )
        add_tangent_row_n_k_dispatch_field(
            lines,
            "smallTangentExpEdgeRowRangeNIndexKChunks",
            t,
            tangent_n,
            tangent_k,
        )
        add_solo_row_n_dispatch_field(
            lines,
            "soloYSaddleClearedRowRangeNIndexChunks",
            ss,
            solo_saddle_n,
        )
        add_solo_row_n_dispatch_field(
            lines,
            "soloYBudgetRowRangeNIndexChunks",
            sb,
            solo_budget_n,
        )
        add_row_edge_dispatch_field(
            lines,
            "edgeKChunkUnitRowRanges",
            e,
            row_count(e),
        )

    if args.emit_final:
        lines.extend(
            [
                "",
                f"theorem {final_name}",
                *final_tail_binder_lines(args),
                "    CoefficientNegativity :=",
                "  coefficientNegativity_of_positiveSaddleFixedFiniteWindowCombinedProductNKChunkedTangentSoloNChunkedAuditCertificate",
                f"    {name} {final_tail_arg(args)}",
            ]
        )

    return lines


def combined_product_nk_tangent_solo_n_fixed_edge_k_chunked_theorem_lines(
    args: argparse.Namespace,
) -> list[str]:
    p = args.product_row_len
    t = args.tangent_row_len
    ss = args.solo_saddle_row_len
    sb = args.solo_budget_row_len
    e = args.edge_row_len
    product_n = args.n_len
    product_k = args.product_k_len
    tangent_n = args.tangent_n_len
    solo_saddle_n = args.solo_saddle_n_len
    solo_budget_n = args.solo_budget_n_len
    tangent_k = args.tangent_k_len
    edge_k = args.edge_k_len
    name = args.name
    final_name = f"coefficientNegativity_of_{name}"

    lines = [
        f"theorem {name} :",
        "    PositiveSaddleFixedFiniteWindowCombinedProductNKChunkedTangentSoloNFixedEdgeKChunkedAuditCertificate",
        f"      {p} {t} {ss} {sb} {e}",
        f"      {product_n} {product_k} {tangent_n} {solo_saddle_n} {solo_budget_n}",
        f"      {tangent_k} {edge_k} where",
        "  productRowLenPos := by norm_num",
        "  tangentRowLenPos := by norm_num",
        "  soloSaddleRowLenPos := by norm_num",
        "  soloBudgetRowLenPos := by norm_num",
        "  edgeRowLenPos := by norm_num",
        "  productNLenPos := by norm_num",
        "  productKLenPos := by norm_num",
        "  tangentNLenPos := by norm_num",
        "  soloSaddleNLenPos := by norm_num",
        "  soloBudgetNLenPos := by norm_num",
        "  tangentKLenPos := by norm_num",
        "  edgeKLenPos := by norm_num",
    ]
    if args.use_single_chunk_theorems:
        add_product_row_n_product_k_dispatch_field_from_single_chunks(
            lines,
            "xyProductRawClearedTableProductRowRangeNIndexKChunks",
            p,
            product_n,
            product_k,
            "product-combined",
            args.single_chunk_prefix,
        )
        add_tangent_row_n_k_dispatch_field_from_single_chunks(
            lines,
            "smallTangentExpEdgeRowRangeNIndexKChunks",
            t,
            tangent_n,
            tangent_k,
            args.single_chunk_prefix,
        )
        add_solo_row_n_dispatch_field_from_single_chunks(
            lines,
            "soloYSaddleClearedRowRangeNIndexChunks",
            ss,
            solo_saddle_n,
            "solo-saddle-n",
            args.single_chunk_prefix,
        )
        add_solo_row_n_dispatch_field_from_single_chunks(
            lines,
            "soloYBudgetRowRangeNIndexChunks",
            sb,
            solo_budget_n,
            "solo-budget-n",
            args.single_chunk_prefix,
        )
        add_row_fixed_edge_dispatch_field_from_single_chunks(
            lines,
            "edgeKChunkUnitRowRanges",
            e,
            edge_k,
            args.single_chunk_prefix,
        )
    else:
        add_product_row_n_product_k_dispatch_field(
            lines,
            "xyProductRawClearedTableProductRowRangeNIndexKChunks",
            p,
            product_n,
            product_k,
        )
        add_tangent_row_n_k_dispatch_field(
            lines,
            "smallTangentExpEdgeRowRangeNIndexKChunks",
            t,
            tangent_n,
            tangent_k,
        )
        add_solo_row_n_dispatch_field(
            lines,
            "soloYSaddleClearedRowRangeNIndexChunks",
            ss,
            solo_saddle_n,
        )
        add_solo_row_n_dispatch_field(
            lines,
            "soloYBudgetRowRangeNIndexChunks",
            sb,
            solo_budget_n,
        )
        add_row_fixed_edge_dispatch_field(
            lines,
            "edgeKChunkUnitRowRanges",
            e,
            edge_k,
        )

    if args.emit_final:
        if args.final_tail_tempered_raw_exp_ratio_reserve_envelope_bounds:
            final_theorem = (
                "coefficientNegativity_of_positiveSaddleFixedFiniteWindowCombinedProductNKChunkedTangentSoloNFixedEdgeKChunkedTemperedRawExpRatioReserveEnvelopeBoundsAuditCertificate"
            )
            final_arg = "tail"
        elif args.final_tail_tempered_raw_exp_ratio_reserve_bounds:
            final_theorem = (
                "coefficientNegativity_of_positiveSaddleFixedFiniteWindowCombinedProductNKChunkedTangentSoloNFixedEdgeKChunkedTemperedRawExpRatioReserveBoundsAuditCertificate"
            )
            final_arg = "tail"
        elif args.final_tail_refined_atomic_bounds:
            final_theorem = (
                "coefficientNegativity_of_positiveSaddleFixedFiniteWindowCombinedProductNKChunkedTangentSoloNFixedEdgeKChunkedRefinedAtomicBoundsAuditCertificate"
            )
            final_arg = "tail"
        else:
            final_theorem = (
                "coefficientNegativity_of_positiveSaddleFixedFiniteWindowCombinedProductNKChunkedTangentSoloNFixedEdgeKChunkedAuditCertificate"
            )
            final_arg = final_tail_arg(args)
        lines.extend(
            [
                "",
                f"theorem {final_name}",
                *final_tail_binder_lines(args),
                "    CoefficientNegativity :=",
                f"  {final_theorem}",
                f"    {name} {final_arg}",
            ]
        )

    return lines


def emit_product_tangent_solo_n_chunked(args: argparse.Namespace) -> str:
    lines = emit_header(args)
    lines.extend(product_tangent_solo_n_chunked_theorem_lines(args))
    lines.extend(["", "end Prop51", ""])
    return "\n".join(lines)


def emit_product_nk_tangent_solo_n_chunked(args: argparse.Namespace) -> str:
    lines = emit_header(args)
    lines.extend(product_nk_tangent_solo_n_chunked_theorem_lines(args))
    lines.extend(["", "end Prop51", ""])
    return "\n".join(lines)


def emit_combined_product_nk_tangent_solo_n_chunked(
    args: argparse.Namespace,
) -> str:
    lines = emit_header(args)
    lines.extend(combined_product_nk_tangent_solo_n_chunked_theorem_lines(args))
    lines.extend(["", "end Prop51", ""])
    return "\n".join(lines)


def emit_combined_product_nk_tangent_solo_n_fixed_edge_k_chunked(
    args: argparse.Namespace,
) -> str:
    lines = emit_header(args)
    lines.extend(
        combined_product_nk_tangent_solo_n_fixed_edge_k_chunked_theorem_lines(args)
    )
    lines.extend(["", "end Prop51", ""])
    return "\n".join(lines)


def emit(args: argparse.Namespace) -> str:
    if args.dry_run_counts:
        return emit_dry_run_counts(args)
    if args.emit_single_chunk is not None:
        return emit_single_chunk(args)
    if args.emit_single_chunk_manifest:
        return emit_single_chunk_manifest(args)
    if args.emit_single_chunk_shard:
        return emit_single_chunk_shard(args)
    if args.emit_single_chunk_suite:
        return emit_single_chunk_suite(args)
    if args.strategy == "all-chunks":
        return emit_all_chunks(args)
    if args.strategy == "split-fields":
        return emit_split_fields(args)
    if args.strategy == "cell-tangent":
        return emit_cell_tangent(args)
    if args.strategy == "chunked-tangent":
        return emit_chunked_tangent(args)
    if args.strategy == "product-n-chunked-tangent":
        return emit_product_n_chunked_tangent(args)
    if args.strategy == "product-tangent-solo-n-chunked":
        return emit_product_tangent_solo_n_chunked(args)
    if args.strategy == "product-nk-tangent-solo-n-chunked":
        return emit_product_nk_tangent_solo_n_chunked(args)
    if args.strategy == "combined-product-nk-tangent-solo-n-chunked":
        return emit_combined_product_nk_tangent_solo_n_chunked(args)
    return emit_combined_product_nk_tangent_solo_n_fixed_edge_k_chunked(args)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    sys.stdout.write(emit(args))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
