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

Example:
  scripts/positive_saddle_fixed_finite_template.py \
    --product-row-len 1 --tangent-row-len 10 \
    --solo-saddle-row-len 100 --solo-budget-row-len 100 \
    --edge-row-len 10 --n-len 1 \
    --name positiveSaddleFiniteWindow \
    --strategy split-fields
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
    args = parser.parse_args(argv)
    if args.strategy != "cell-tangent" and args.tangent_row_len is None:
        parser.error("--tangent-row-len is required unless --strategy cell-tangent")
    if args.strategy in ("chunked-tangent", "product-n-chunked-tangent"):
        if args.tangent_n_len is None:
            parser.error(f"--tangent-n-len is required for --strategy {args.strategy}")
        if args.tangent_k_len is None:
            parser.error(f"--tangent-k-len is required for --strategy {args.strategy}")
    if args.name is None:
        if args.strategy == "all-chunks":
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


def row_count(row_len: int) -> int:
    return (1600 + row_len - 1) // row_len


def tangent_k_count(k_len: int) -> int:
    return (155 + k_len - 1) // k_len


def product_n_index_count(row_len: int, n_len: int) -> int:
    return (6 * (2000 + row_len) + n_len - 1) // n_len


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


def emit_product_n_chunked_tangent(args: argparse.Namespace) -> str:
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
    )
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

    lines.extend(["", "end Prop51", ""])
    return "\n".join(lines)


def emit(args: argparse.Namespace) -> str:
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
