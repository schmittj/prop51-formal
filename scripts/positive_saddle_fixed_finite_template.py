#!/usr/bin/env python3
"""Emit a Lean template for the fixed finite-window positive-saddle audit.

The generated theorem targets
`PositiveSaddleFixedFiniteWindowAllChunksAuditCertificate`, so it only proves
the finite `401 <= a <= 2000` Boolean checks.  The large-`a` product/solo and
split-tempered reserve inputs are supplied separately as a
`PositiveSaddleLargeTailAuditCertificate`.

Example:
  scripts/positive_saddle_fixed_finite_template.py \
    --product-row-len 1 --tangent-row-len 10 \
    --solo-saddle-row-len 100 --solo-budget-row-len 100 \
    --edge-row-len 10 --n-len 1 \
    --name positiveSaddleFiniteWindow
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
    parser.add_argument("--tangent-row-len", type=positive_nat, required=True)
    parser.add_argument("--solo-saddle-row-len", type=positive_nat, required=True)
    parser.add_argument("--solo-budget-row-len", type=positive_nat, required=True)
    parser.add_argument("--edge-row-len", type=positive_nat, required=True)
    parser.add_argument("--n-len", type=positive_nat, required=True)
    parser.add_argument(
        "--name",
        type=lean_ident,
        default="positiveSaddleFixedFiniteWindowAllChunksAuditCertificate",
        help="Lean theorem name for the generated finite certificate",
    )
    parser.add_argument(
        "--emit-final",
        action="store_true",
        help="also emit a theorem taking a large-tail certificate to CoefficientNegativity",
    )
    return parser.parse_args(argv)


def emit(args: argparse.Namespace) -> str:
    p = args.product_row_len
    t = args.tangent_row_len
    ss = args.solo_saddle_row_len
    sb = args.solo_budget_row_len
    e = args.edge_row_len
    n = args.n_len
    name = args.name
    final_name = f"coefficientNegativity_of_{name}"

    lines = [
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
        f"theorem {name} :",
        "    PositiveSaddleFixedFiniteWindowAllChunksAuditCertificate",
        f"      {p} {t} {ss} {sb} {e} {n} where",
        "  productRowLenPos := by norm_num",
        "  tangentRowLenPos := by norm_num",
        "  soloSaddleRowLenPos := by norm_num",
        "  soloBudgetRowLenPos := by norm_num",
        "  edgeRowLenPos := by norm_num",
        "  nLenPos := by norm_num",
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


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    sys.stdout.write(emit(args))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
