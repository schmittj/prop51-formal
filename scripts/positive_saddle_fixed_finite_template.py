#!/usr/bin/env python3
"""Emit a Lean template for the fixed finite-window positive-saddle audit.

The generated theorem only proves the finite `401 <= a <= 2000` Boolean
checks.  The large-`a` product/solo and split-tempered reserve inputs are
supplied separately as a `PositiveSaddleLargeTailAuditCertificate`.

Two strategies are available:
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
  * --emit-single-chunk FIELD: emit one cacheable `native_decide` theorem for
    a concrete product, tangent, solo, or edge chunk.
  * --emit-single-chunk-suite: emit all single-chunk theorems for a concrete
    product-n-chunked-tangent certificate, followed by the assembled finite
    certificate.
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
import re
import sys


LEAN_IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")


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
    parser.add_argument("--solo-saddle-row-len", type=positive_nat, required=True)
    parser.add_argument("--solo-budget-row-len", type=positive_nat, required=True)
    parser.add_argument("--edge-row-len", type=positive_nat, required=True)
    parser.add_argument("--n-len", type=positive_nat, required=True)
    parser.add_argument(
        "--name",
        type=lean_ident,
        default=None,
        help="Lean theorem name for the generated finite certificate",
    )
    parser.add_argument(
        "--emit-final",
        action="store_true",
        help="also emit a theorem taking a large-tail certificate to CoefficientNegativity",
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
        "--strategy",
        choices=(
            "all-chunks",
            "split-fields",
            "cell-tangent",
            "chunked-tangent",
            "product-n-chunked-tangent",
        ),
        default="all-chunks",
        help="finite certificate shape to emit",
    )
    parser.add_argument(
        "--emit-single-chunk",
        choices=(
            "product-small",
            "product-tempered",
            "tangent",
            "solo-saddle",
            "solo-budget",
            "edge",
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
    if args.emit_single_chunk_suite and args.emit_single_chunk is not None:
        parser.error("--emit-single-chunk-suite cannot be combined with --emit-single-chunk")
    if args.emit_single_chunk_suite and args.use_single_chunk_theorems:
        parser.error(
            "--emit-single-chunk-suite cannot be combined with "
            "--use-single-chunk-theorems"
        )
    if args.emit_single_chunk_suite and args.strategy != "product-n-chunked-tangent":
        parser.error(
            "--emit-single-chunk-suite is only supported for "
            "--strategy product-n-chunked-tangent"
        )
    if args.use_single_chunk_theorems and args.emit_single_chunk is not None:
        parser.error("--use-single-chunk-theorems cannot be combined with --emit-single-chunk")
    if args.use_single_chunk_theorems and args.strategy != "product-n-chunked-tangent":
        parser.error(
            "--use-single-chunk-theorems is only supported for "
            "--strategy product-n-chunked-tangent"
        )
    if args.emit_single_chunk is not None:
        if args.row_index is None:
            parser.error("--row-index is required with --emit-single-chunk")
        if args.emit_single_chunk in ("product-small", "product-tempered", "edge"):
            if args.k_index is None:
                parser.error("--k-index is required for product/edge single chunks")
        if args.emit_single_chunk in ("product-small", "product-tempered"):
            if args.n_index is None:
                parser.error("--n-index is required for product single chunks")
        if args.emit_single_chunk == "tangent":
            if args.tangent_row_len is None:
                parser.error("--tangent-row-len is required for tangent single chunks")
            if args.tangent_n_len is None:
                parser.error("--tangent-n-len is required for tangent single chunks")
            if args.tangent_k_len is None:
                parser.error("--tangent-k-len is required for tangent single chunks")
            if args.k_index is None:
                parser.error("--k-index is required for tangent single chunks")
        validate_single_chunk_indices(parser, args)
    else:
        if args.strategy != "cell-tangent" and args.tangent_row_len is None:
            parser.error("--tangent-row-len is required unless --strategy cell-tangent")
        if args.strategy in ("chunked-tangent", "product-n-chunked-tangent"):
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
        else:
            args.name = (
                "positiveSaddleGeneratedFixedFiniteWindowProductNChunkedTangentCertificate"
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
    if field in ("product-small", "product-tempered"):
        validate_lt(parser, "--row-index", args.row_index, row_count(args.product_row_len))
        validate_lt(
            parser,
            "--n-index",
            args.n_index,
            product_n_index_count(args.product_row_len, args.n_len),
        )
        validate_lt(parser, "--k-index", args.k_index, 90)
    elif field == "tangent":
        validate_lt(parser, "--row-index", args.row_index, row_count(args.tangent_row_len))
        validate_lt(parser, "--k-index", args.k_index, tangent_k_count(args.tangent_k_len))
    elif field == "solo-saddle":
        validate_lt(
            parser,
            "--row-index",
            args.row_index,
            row_count(args.solo_saddle_row_len),
        )
    elif field == "solo-budget":
        validate_lt(
            parser,
            "--row-index",
            args.row_index,
            row_count(args.solo_budget_row_len),
        )
    elif field == "edge":
        validate_lt(parser, "--row-index", args.row_index, row_count(args.edge_row_len))
        validate_lt(parser, "--k-index", args.k_index, 90)
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


def emit_header() -> list[str]:
    return [
        "import Prop51.Main",
        "",
        "namespace Prop51",
        "",
        "/-",
        "Generated finite-window positive-saddle certificate.",
        "",
        "This proves only the finite Boolean checks.  Combine it with a",
        "`PositiveSaddleLargeTailAuditCertificate` for the final theorem.",
        "-/",
    ]


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
        k_lo = 1 + 20 * k_index
        return [
            f"theorem {name} :",
            "    checkPositiveSmallXYProductRawClearedTableFixedNIndexRowRangeKChunk",
            f"      {args.n_len} {row_lo} {args.product_row_len}",
            f"      {n_index} {k_lo} 20 = true := by",
            "  native_decide",
        ]
    if field == "product-tempered":
        row_lo = 401 + args.product_row_len * row_index
        k_lo = 1 + 20 * k_index
        return [
            f"theorem {name} :",
            "    checkPositiveTemperedXYProductRawClearedTableFixedNIndexRowRangeKChunk",
            f"      {args.n_len} {row_lo} {args.product_row_len}",
            f"      {n_index} {k_lo} 20 = true := by",
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
    if field == "solo-saddle":
        row_lo = 401 + args.solo_saddle_row_len * row_index
        return [
            f"theorem {name} :",
            "    checkPositiveSoloDisplayedYSaddleClearedRange",
            f"      {row_lo} {args.solo_saddle_row_len} = true := by",
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
    raise AssertionError(f"unhandled single chunk field {field!r}")


def emit_single_chunk(args: argparse.Namespace) -> str:
    lines = emit_header()
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
    for field in ("product-small", "product-tempered"):
        for i in range(row_count(args.product_row_len)):
            for n in range(product_n_index_count(args.product_row_len, args.n_len)):
                for j in range(90):
                    specs.append(
                        (
                            field,
                            i,
                            n,
                            j,
                            single_chunk_name(args.single_chunk_prefix, field, i, n, j),
                        )
                    )
    for i in range(row_count(args.tangent_row_len)):
        for j in range(tangent_k_count(args.tangent_k_len)):
            specs.append(
                (
                    "tangent",
                    i,
                    None,
                    j,
                    single_chunk_name(args.single_chunk_prefix, "tangent", i, None, j),
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
    for i in range(row_count(args.edge_row_len)):
        for j in range(90):
            specs.append(
                (
                    "edge",
                    i,
                    None,
                    j,
                    single_chunk_name(args.single_chunk_prefix, "edge", i, None, j),
                )
            )
    return specs


def emit_single_chunk_suite(args: argparse.Namespace) -> str:
    lines = emit_header()
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

    lines = emit_header()
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
                "    (tail : PositiveSaddleLargeTailAuditCertificate) :",
                "    CoefficientNegativity :=",
                "  coefficientNegativity_of_positiveSaddleFixedFiniteWindowAllChunksAuditCertificate",
                f"    {name} tail",
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

    lines = emit_header()
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
                "    (tail : PositiveSaddleLargeTailAuditCertificate) :",
                "    CoefficientNegativity :=",
                "  coefficientNegativity_of_positiveSaddleFixedFiniteWindowAuditCertificate",
                f"    {name} tail",
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

    lines = emit_header()
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
                "    (tail : PositiveSaddleLargeTailAuditCertificate) :",
                "    CoefficientNegativity :=",
                "  coefficientNegativity_of_positiveSaddleFixedFiniteWindowCellTangentAuditCertificate",
                f"    ({name} htangent) tail",
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

    lines = emit_header()
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
                "    (tail : PositiveSaddleLargeTailAuditCertificate) :",
                "    CoefficientNegativity :=",
                "  coefficientNegativity_of_positiveSaddleFixedFiniteWindowChunkedTangentAuditCertificate",
                f"    {name} tail",
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
                "    (tail : PositiveSaddleLargeTailAuditCertificate) :",
                "    CoefficientNegativity :=",
                "  coefficientNegativity_of_positiveSaddleFixedFiniteWindowProductNChunkedTangentAuditCertificate",
                f"    {name} tail",
            ]
        )

    return lines


def emit_product_n_chunked_tangent(args: argparse.Namespace) -> str:
    lines = emit_header()
    lines.extend(product_n_chunked_tangent_theorem_lines(args))
    lines.extend(["", "end Prop51", ""])
    return "\n".join(lines)


def emit(args: argparse.Namespace) -> str:
    if args.emit_single_chunk is not None:
        return emit_single_chunk(args)
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
    return emit_product_n_chunked_tangent(args)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    sys.stdout.write(emit(args))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
