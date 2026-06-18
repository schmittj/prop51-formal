#!/usr/bin/env python3
"""Emit Lean templates for large-tail positive-saddle prefix chunks.

This generator covers only the finite lower-prefix strip

    2000 < a < 3000.

It targets the prefix chunk inputs used by the full-hybrid large-tail route:

* product factor bounds:
  PositiveSaddleLargeTailProductFastUpperEdgeLowerNXYBoundPrefixBoundChunksCertificate
* product scalar budgets against xBound*yBound:
  PositiveSaddleLargeTailProductFastUpperEdgeLowerNProductBoundPrefixChunksCertificate
* solo bound:
  PositiveSaddleLargeTailSoloFastUpperEdgeBoundPrefixBoundChunksCertificate
* solo scalar budget:
  PositiveSaddleLargeTailSoloFastUpperEdgeBoundPrefixChunksCertificate

The analytic fields for 3000 <= a are intentionally not generated here.
Those remain ordinary Lean theorem arguments in the final full-hybrid
certificate.  The `exact-bound-full-hybrid` certificate profile uses the
exact upper-edge split sums for xBound/yBound/soloBound, so Lean closes the
prefix-bound fields and generated proof production only needs scalar prefix
atoms.  Those scalar atoms still expand the exact split sums, so use
`--shard-balance native-work` and inspect `native_work_estimates` before
attempting large exact-bound shards.
"""

from __future__ import annotations

import argparse
import json
import re
import shlex
import subprocess
import sys
from pathlib import Path
from typing import Callable, Iterable, NamedTuple


LEAN_IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
LEAN_QUALIFIED_IDENT_RE = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*$"
)
PROJECT_ROOT = Path(__file__).resolve().parents[1]

PREFIX_START = 2001
PREFIX_ROWS = 999

PRODUCT_FIELDS = (
    "product-x-bound",
    "product-y-bound",
    "product-small-scalar",
    "product-tempered-scalar",
)
SOLO_FIELDS = ("solo-bound", "solo-scalar")
SINGLE_CHUNK_FIELDS = (*PRODUCT_FIELDS, *SOLO_FIELDS)

CERTIFICATES = (
    "all-prefixes",
    "exact-bound-full-hybrid",
    "product-bound-prefix",
    "product-scalar-prefix",
    "solo-bound-prefix",
    "solo-scalar-prefix",
)

EXACT_X_BOUND = "positiveLargeTailProductXUpperEdgeExactBound"
EXACT_Y_BOUND = "positiveLargeTailProductYUpperEdgeExactBound"
EXACT_SOLO_BOUND = "positiveLargeTailSoloUpperEdgeExactBound"


class ChunkSpec(NamedTuple):
    field: str
    a_index: int
    k_index: int | None
    name: str


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


def lean_qualified_ident(text: str) -> str:
    if not LEAN_QUALIFIED_IDENT_RE.match(text):
        raise argparse.ArgumentTypeError(
            f"{text!r} is not a Lean qualified identifier"
        )
    return text


def ceil_div(num: int, den: int) -> int:
    return 0 if num <= 0 else (num + den - 1) // den


def pos_kmax(a: int) -> int:
    return 9 * a // 10


def pos_nhi(a: int) -> int:
    return 12 * a - 8


def a_chunk_count(a_len: int) -> int:
    return ceil_div(PREFIX_ROWS, a_len)


def a_lo(args: argparse.Namespace, a_index: int) -> int:
    return PREFIX_START + args.a_len * a_index


def a_bound(args: argparse.Namespace, a_index: int) -> int:
    return a_lo(args, a_index) + args.a_len


def k_chunk_count(args: argparse.Namespace, a_index: int) -> int:
    return ceil_div(pos_kmax(a_bound(args, a_index)), args.k_len)


def k_lo(args: argparse.Namespace, k_index: int) -> int:
    return 1 + args.k_len * k_index


def slug(field: str) -> str:
    return field.replace("-", "_")


def single_chunk_name(
    prefix: str, field: str, a_index: int, k_index: int | None = None
) -> str:
    if k_index is None:
        return f"{prefix}_{slug(field)}_a{a_index}"
    return f"{prefix}_{slug(field)}_a{a_index}_k{k_index}"


def selected_fields(args: argparse.Namespace) -> set[str]:
    if args.single_chunk_field is None:
        if args.certificate == "exact-bound-full-hybrid":
            return certificate_fields(args.certificate)
        return set(SINGLE_CHUNK_FIELDS)
    return set(args.single_chunk_field)


def selected_field_payload(args: argparse.Namespace) -> list[str] | str:
    if args.single_chunk_field is None:
        return "all"
    return sorted(selected_fields(args))


def field_requires_x(field: str) -> bool:
    return field in {
        "product-x-bound",
        "product-small-scalar",
        "product-tempered-scalar",
    }


def field_requires_y(field: str) -> bool:
    return field in {
        "product-y-bound",
        "product-small-scalar",
        "product-tempered-scalar",
    }


def field_requires_solo(field: str) -> bool:
    return field in SOLO_FIELDS


def certificate_fields(certificate: str) -> set[str]:
    if certificate == "all-prefixes":
        return set(SINGLE_CHUNK_FIELDS)
    if certificate == "exact-bound-full-hybrid":
        return {
            "product-small-scalar",
            "product-tempered-scalar",
            "solo-scalar",
        }
    if certificate == "product-bound-prefix":
        return {"product-x-bound", "product-y-bound"}
    if certificate == "product-scalar-prefix":
        return {"product-small-scalar", "product-tempered-scalar"}
    if certificate == "solo-bound-prefix":
        return {"solo-bound"}
    if certificate == "solo-scalar-prefix":
        return {"solo-scalar"}
    raise AssertionError(f"unknown certificate {certificate!r}")


def required_fields(args: argparse.Namespace) -> set[str]:
    if args.emit_single_chunk is not None:
        return {args.emit_single_chunk}
    if (
        args.emit_single_chunk_manifest
        or args.emit_single_chunk_shard
        or (args.dry_run_counts and args.dry_run_shard_count is not None)
    ):
        return selected_fields(args)
    if args.dry_run_counts:
        return set()
    return certificate_fields(args.certificate)


def validate_bound_args(parser: argparse.ArgumentParser, args: argparse.Namespace) -> None:
    fields = required_fields(args)
    if any(field_requires_x(field) for field in fields) and args.x_bound is None:
        parser.error("--x-bound is required for selected product X/scalar fields")
    if any(field_requires_y(field) for field in fields) and args.y_bound is None:
        parser.error("--y-bound is required for selected product Y/scalar fields")
    if any(field_requires_solo(field) for field in fields) and args.solo_bound is None:
        parser.error("--solo-bound is required for selected solo fields")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="emit large-tail positive-saddle prefix chunk certificates",
    )
    parser.add_argument("--a-len", type=positive_nat, required=True)
    parser.add_argument("--k-len", type=positive_nat, required=True)
    parser.add_argument(
        "--x-bound",
        type=lean_qualified_ident,
        help="Lean identifier for xBound : Nat -> Nat -> Rat",
    )
    parser.add_argument(
        "--y-bound",
        type=lean_qualified_ident,
        help="Lean identifier for yBound : Nat -> Nat -> Rat",
    )
    parser.add_argument(
        "--solo-bound",
        type=lean_qualified_ident,
        help="Lean identifier for soloBound : Nat -> Rat",
    )
    parser.add_argument(
        "--name",
        type=lean_ident,
        default="positiveSaddleLargeTailPrefix",
        help="base Lean theorem name for assembled prefix certificates",
    )
    parser.add_argument(
        "--certificate",
        choices=CERTIFICATES,
        default="all-prefixes",
        help="which assembled prefix certificate theorem(s) to emit",
    )
    parser.add_argument(
        "--extra-import",
        action="append",
        default=[],
        type=lean_qualified_ident,
        help="additional Lean module import; repeat for generated atom shards",
    )
    parser.add_argument(
        "--single-chunk-prefix",
        type=lean_ident,
        default="positiveSaddleLargeTailGeneratedChunk",
        help="prefix for generated/referenced single-chunk theorem names",
    )
    parser.add_argument(
        "--use-single-chunk-theorems",
        action="store_true",
        help="assemble prefix certificates from imported single-chunk theorems",
    )
    parser.add_argument(
        "--emit-single-chunk",
        choices=SINGLE_CHUNK_FIELDS,
        help="emit one concrete native_decide prefix atom theorem",
    )
    parser.add_argument(
        "--a-index",
        type=nonnegative_nat,
        help="zero-based a-chunk index for --emit-single-chunk",
    )
    parser.add_argument(
        "--k-index",
        type=nonnegative_nat,
        help="zero-based k-chunk index for product --emit-single-chunk",
    )
    parser.add_argument(
        "--emit-single-chunk-shard",
        action="store_true",
        help="emit one balanced shard of single-chunk theorem declarations",
    )
    parser.add_argument(
        "--shard-index",
        type=nonnegative_nat,
        help="zero-based shard index for --emit-single-chunk-shard",
    )
    parser.add_argument(
        "--shard-count",
        type=positive_nat,
        help="total shard count for --emit-single-chunk-shard",
    )
    parser.add_argument(
        "--emit-single-chunk-manifest",
        action="store_true",
        help="emit a JSON manifest for all selected single-chunk theorems",
    )
    parser.add_argument(
        "--manifest-shard-count",
        type=positive_nat,
        help="with --emit-single-chunk-manifest, include shard metadata",
    )
    parser.add_argument(
        "--dry-run-counts",
        action="store_true",
        help="emit formula-based JSON counts without materializing the manifest",
    )
    parser.add_argument(
        "--dry-run-shard-count",
        type=positive_nat,
        help="with --dry-run-counts, include shard summaries",
    )
    parser.add_argument(
        "--shard-balance",
        choices=("atoms", "cells", "native-work"),
        default="atoms",
        help=(
            "balance shards by atom count, flat loop-cell estimate, or "
            "native-work estimate including exact-bound split sums"
        ),
    )
    parser.add_argument(
        "--single-chunk-field",
        action="append",
        choices=SINGLE_CHUNK_FIELDS,
        help=(
            "restrict dry-run, manifest, or shard output to one atom family; "
            "repeat for several families"
        ),
    )
    args = parser.parse_args(argv)
    if args.certificate == "exact-bound-full-hybrid":
        if args.x_bound is None:
            args.x_bound = EXACT_X_BOUND
        if args.y_bound is None:
            args.y_bound = EXACT_Y_BOUND
        if args.solo_bound is None:
            args.solo_bound = EXACT_SOLO_BOUND

    if args.emit_single_chunk is not None:
        if args.a_index is None:
            parser.error("--a-index is required with --emit-single-chunk")
        if args.a_index >= a_chunk_count(args.a_len):
            parser.error("--a-index is outside positiveLargeTailLowerPrefixAChunks")
        if args.emit_single_chunk in PRODUCT_FIELDS:
            if args.k_index is None:
                parser.error("--k-index is required for product single chunks")
            if args.k_index >= k_chunk_count(args, args.a_index):
                parser.error("--k-index is outside this a-chunk's k cover")
        elif args.k_index is not None:
            parser.error("--k-index is only valid for product single chunks")
    elif args.a_index is not None or args.k_index is not None:
        parser.error("--a-index/--k-index require --emit-single-chunk")

    if args.emit_single_chunk_shard:
        if args.shard_index is None or args.shard_count is None:
            parser.error(
                "--shard-index and --shard-count are required with "
                "--emit-single-chunk-shard"
            )
        if args.shard_count <= args.shard_index:
            parser.error("--shard-index must be smaller than --shard-count")
    elif args.shard_index is not None or args.shard_count is not None:
        parser.error("--shard-index/--shard-count require --emit-single-chunk-shard")

    if args.manifest_shard_count is not None and not args.emit_single_chunk_manifest:
        parser.error("--manifest-shard-count requires --emit-single-chunk-manifest")

    if args.dry_run_shard_count is not None and not args.dry_run_counts:
        parser.error("--dry-run-shard-count requires --dry-run-counts")

    output_modes = sum(
        bool(mode)
        for mode in (
            args.emit_single_chunk is not None,
            args.emit_single_chunk_shard,
            args.emit_single_chunk_manifest,
            args.dry_run_counts,
        )
    )
    if output_modes > 1:
        parser.error("single-chunk, shard, manifest, and dry-run modes are exclusive")

    if args.single_chunk_field is not None:
        if not (
            args.emit_single_chunk_manifest
            or args.emit_single_chunk_shard
            or args.dry_run_counts
        ):
            parser.error(
                "--single-chunk-field is only supported with dry runs, "
                "manifests, or shard emission"
            )

    validate_bound_args(parser, args)
    return args


def git_output(*args: str) -> str | None:
    try:
        result = subprocess.run(
            ["git", *args],
            cwd=PROJECT_ROOT,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            text=True,
        )
    except (OSError, subprocess.CalledProcessError):
        return None
    return result.stdout.strip()


def reproducibility_metadata() -> dict[str, object]:
    status = git_output("status", "--porcelain")
    try:
        script_path = str(Path(sys.argv[0]).resolve().relative_to(PROJECT_ROOT))
    except ValueError:
        script_path = sys.argv[0]
    return {
        "argv": sys.argv[:],
        "command": shlex.join(sys.argv),
        "script": script_path,
        "git_commit": git_output("rev-parse", "HEAD"),
        "git_dirty": None if status is None else bool(status),
        "git_status_porcelain": None if status is None else status.splitlines(),
    }


def common_emit_args(args: argparse.Namespace) -> list[str]:
    emit_args = [
        "--a-len",
        str(args.a_len),
        "--k-len",
        str(args.k_len),
    ]
    if args.certificate != "all-prefixes":
        emit_args.extend(["--certificate", args.certificate])
    if args.x_bound is not None:
        emit_args.extend(["--x-bound", args.x_bound])
    if args.y_bound is not None:
        emit_args.extend(["--y-bound", args.y_bound])
    if args.solo_bound is not None:
        emit_args.extend(["--solo-bound", args.solo_bound])
    for module in args.extra_import:
        emit_args.extend(["--extra-import", module])
    return emit_args


def single_chunk_emit_args(args: argparse.Namespace, spec: ChunkSpec) -> list[str]:
    emit_args = [
        *common_emit_args(args),
        "--emit-single-chunk",
        spec.field,
        "--a-index",
        str(spec.a_index),
        "--name",
        spec.name,
    ]
    if spec.k_index is not None:
        emit_args.extend(["--k-index", str(spec.k_index)])
    return emit_args


def shard_emit_args(
    args: argparse.Namespace, shard_index: int, shard_count: int
) -> list[str]:
    emit_args = [
        *common_emit_args(args),
        "--single-chunk-prefix",
        args.single_chunk_prefix,
        "--emit-single-chunk-shard",
        "--shard-index",
        str(shard_index),
        "--shard-count",
        str(shard_count),
    ]
    if args.shard_balance != "atoms":
        emit_args.extend(["--shard-balance", args.shard_balance])
    if args.single_chunk_field is not None:
        for field in args.single_chunk_field:
            emit_args.extend(["--single-chunk-field", field])
    return emit_args


def field_shapes(args: argparse.Namespace) -> Iterable[tuple[str, int, int]]:
    selected = selected_fields(args)
    for field in SINGLE_CHUNK_FIELDS:
        if field not in selected:
            continue
        start = 0
        if field in PRODUCT_FIELDS:
            for a_index in range(a_chunk_count(args.a_len)):
                stop = start + k_chunk_count(args, a_index)
                yield field, start, stop
                start = stop
        else:
            count = a_chunk_count(args.a_len)
            yield field, 0, count


def single_chunk_shape_ranges(args: argparse.Namespace) -> list[tuple[str, int, int]]:
    ranges = []
    offset = 0
    for field in SINGLE_CHUNK_FIELDS:
        if field not in selected_fields(args):
            continue
        if field in PRODUCT_FIELDS:
            count = product_atom_count(args)
        else:
            count = a_chunk_count(args.a_len)
        ranges.append((field, offset, offset + count))
        offset += count
    return ranges


def single_chunk_total_count(args: argparse.Namespace) -> int:
    return sum(stop - start for _, start, stop in single_chunk_shape_ranges(args))


def product_atom_count(args: argparse.Namespace) -> int:
    return sum(
        k_chunk_count(args, a_index) for a_index in range(a_chunk_count(args.a_len))
    )


def spec_for_field_local_index(
    args: argparse.Namespace, field: str, local_index: int
) -> ChunkSpec:
    if field in SOLO_FIELDS:
        a_index = local_index
        return ChunkSpec(
            field,
            a_index,
            None,
            single_chunk_name(args.single_chunk_prefix, field, a_index),
        )

    remaining = local_index
    for a_index in range(a_chunk_count(args.a_len)):
        count = k_chunk_count(args, a_index)
        if remaining < count:
            return ChunkSpec(
                field,
                a_index,
                remaining,
                single_chunk_name(
                    args.single_chunk_prefix, field, a_index, remaining
                ),
            )
        remaining -= count
    raise AssertionError(f"local index {local_index} outside {field}")


def single_chunk_specs_slice(
    args: argparse.Namespace, start: int, stop: int
) -> Iterable[ChunkSpec]:
    offset = 0
    for field, shape_start, shape_stop in single_chunk_shape_ranges(args):
        local_start = max(0, start - shape_start)
        local_stop = min(shape_stop - shape_start, stop - shape_start)
        if local_start < local_stop:
            if field in PRODUCT_FIELDS:
                local_offset = 0
                for a_index in range(a_chunk_count(args.a_len)):
                    count = k_chunk_count(args, a_index)
                    k_start = max(0, local_start - local_offset)
                    k_stop = min(count, local_stop - local_offset)
                    for k_index in range(k_start, k_stop):
                        yield ChunkSpec(
                            field,
                            a_index,
                            k_index,
                            single_chunk_name(
                                args.single_chunk_prefix, field, a_index, k_index
                            ),
                        )
                    local_offset += count
            else:
                for local_index in range(local_start, local_stop):
                    yield ChunkSpec(
                        field,
                        local_index,
                        None,
                        single_chunk_name(
                            args.single_chunk_prefix, field, local_index
                        ),
                    )
        offset = shape_stop
    assert offset == single_chunk_total_count(args)


def single_chunk_specs(args: argparse.Namespace) -> list[ChunkSpec]:
    return list(single_chunk_specs_slice(args, 0, single_chunk_total_count(args)))


def field_cell_weight(args: argparse.Namespace, field: str) -> int:
    if field in PRODUCT_FIELDS:
        return args.a_len * args.k_len
    return args.a_len


def split_factorial_sum_work(degree: int) -> int:
    """Conservative term count for one split-final-term closed block sum."""
    if degree <= 0:
        return 1
    inner_terms = (degree // 2) * ((degree + 1) // 2)
    return 1 + degree + inner_terms


def spec_flat_cell_weight(args: argparse.Namespace, spec: ChunkSpec) -> int:
    return field_cell_weight(args, spec.field)


def product_chunk_active_bounds(
    args: argparse.Namespace, a_index: int, k_index: int
) -> tuple[int, int, int, int] | None:
    alo = a_lo(args, a_index)
    ahi = min(PREFIX_START + PREFIX_ROWS - 1, alo + args.a_len - 1)
    if ahi < alo:
        return None
    klo = k_lo(args, k_index)
    khi = min(klo + args.k_len - 1, pos_kmax(ahi))
    if khi < klo:
        return None
    return alo, ahi, klo, khi


def spec_native_work_weight(args: argparse.Namespace, spec: ChunkSpec) -> int:
    """Conservative native_decide work units for one generated atom.

    The ordinary flat cell count is accurate for cheap rational surrogate
    atoms.  In the exact-bound profile, scalar atoms expand the upper-edge
    split-final-term block sums inside each Boolean cell, so we account for
    that hidden quadratic work separately.
    """
    flat = spec_flat_cell_weight(args, spec)
    if args.certificate != "exact-bound-full-hybrid":
        return flat
    if spec.field in ("product-x-bound", "product-y-bound", "solo-bound"):
        return flat
    if spec.field == "solo-scalar":
        alo = a_lo(args, spec.a_index)
        ahi = min(PREFIX_START + PREFIX_ROWS - 1, alo + args.a_len - 1)
        if ahi < alo:
            return 0
        row_count = ahi - alo + 1
        return row_count * split_factorial_sum_work(pos_nhi(ahi))
    if spec.field in ("product-small-scalar", "product-tempered-scalar"):
        assert spec.k_index is not None
        bounds = product_chunk_active_bounds(args, spec.a_index, spec.k_index)
        if bounds is None:
            return 0
        alo, ahi, klo, khi = bounds
        row_count = ahi - alo + 1
        k_count = khi - klo + 1
        # `X` depends on `k`, while `Y` depends on `j = a-k`.  The same cell
        # cannot maximize both simultaneously, but using both maxima keeps the
        # estimate safely conservative for shard planning.
        max_j = max(0, ahi - klo)
        return row_count * k_count * (
            split_factorial_sum_work(khi) + split_factorial_sum_work(max_j)
        )
    return flat


def single_chunk_specs_iter(args: argparse.Namespace) -> Iterable[ChunkSpec]:
    return single_chunk_specs_slice(args, 0, single_chunk_total_count(args))


def single_chunk_weight_ranges(
    args: argparse.Namespace,
    weight_of: Callable[[argparse.Namespace, ChunkSpec], int],
) -> list[tuple[int, int, int, int, int]]:
    ranges = []
    offset = 0
    weight_offset = 0
    current_weight: int | None = None
    run_start = 0
    run_weight_start = 0
    for spec in single_chunk_specs_iter(args):
        weight = weight_of(args, spec)
        if current_weight is None:
            current_weight = weight
            run_start = offset
            run_weight_start = weight_offset
        elif weight != current_weight:
            ranges.append((run_start, offset, current_weight, run_weight_start))
            run_start = offset
            run_weight_start = weight_offset
            current_weight = weight
        offset += 1
        weight_offset += weight
    if current_weight is not None:
        ranges.append((run_start, offset, current_weight, run_weight_start))
    return [
        (start, stop, weight, weight_start, weight_start + (stop - start) * weight)
        for start, stop, weight, weight_start in ranges
    ]


def cell_weight_ranges(args: argparse.Namespace) -> list[tuple[str, int, int, int, int, int]]:
    ranges = []
    cell_offset = 0
    for field, start, stop in single_chunk_shape_ranges(args):
        weight = field_cell_weight(args, field)
        cell_stop = cell_offset + (stop - start) * weight
        ranges.append((field, start, stop, weight, cell_offset, cell_stop))
        cell_offset = cell_stop
    return ranges


def atom_index_for_cell_target(
    ranges: list[tuple[str, int, int, int, int, int]], target: int
) -> int:
    if target <= 0:
        return 0
    for _field, start, stop, weight, cell_start, cell_stop in ranges:
        if target <= cell_start:
            return start
        if target <= cell_stop:
            local = target - cell_start
            return min(stop, start + ceil_div(local, weight))
    return ranges[-1][2] if ranges else 0


def atom_index_for_weight_target(
    ranges: list[tuple[int, int, int, int, int]], target: int
) -> int:
    if target <= 0:
        return 0
    for start, stop, weight, weight_start, weight_stop in ranges:
        if target <= weight_start:
            return start
        if target <= weight_stop:
            local = target - weight_start
            return min(stop, start + ceil_div(local, weight))
    return ranges[-1][1] if ranges else 0


def shard_bounds(
    args: argparse.Namespace, shard_index: int, shard_count: int
) -> tuple[int, int]:
    total = single_chunk_total_count(args)
    if args.shard_balance == "atoms":
        return total * shard_index // shard_count, total * (shard_index + 1) // shard_count
    if args.shard_balance == "cells":
        ranges = cell_weight_ranges(args)
        if not ranges:
            return 0, 0
        total_weight = ranges[-1][5]
        start_target = total_weight * shard_index // shard_count
        stop_target = total_weight * (shard_index + 1) // shard_count
        return (
            atom_index_for_cell_target(ranges, start_target),
            atom_index_for_cell_target(ranges, stop_target),
        )
    ranges = single_chunk_weight_ranges(args, spec_native_work_weight)
    if not ranges:
        return 0, 0
    total_weight = ranges[-1][4]
    start_target = total_weight * shard_index // shard_count
    stop_target = total_weight * (shard_index + 1) // shard_count
    return (
        atom_index_for_weight_target(ranges, start_target),
        atom_index_for_weight_target(ranges, stop_target),
    )


def count_by_field(args: argparse.Namespace) -> dict[str, int]:
    counts: dict[str, int] = {}
    for field, start, stop in single_chunk_shape_ranges(args):
        counts[field] = stop - start
    return counts


def cell_estimates(args: argparse.Namespace, counts: dict[str, int]) -> dict[str, object]:
    by_field = {
        field: {
            "atoms": count,
            "max_cells_per_atom": field_cell_weight(args, field),
            "max_total_cells": count * field_cell_weight(args, field),
        }
        for field, count in counts.items()
    }
    return {
        "by_field": by_field,
        "max_total_cells": sum(
            field_payload["max_total_cells"] for field_payload in by_field.values()
        ),
    }


def native_work_estimates(
    args: argparse.Namespace,
    start: int = 0,
    stop: int | None = None,
) -> dict[str, object]:
    if stop is None:
        stop = single_chunk_total_count(args)
    by_field: dict[str, dict[str, int]] = {}
    for spec in single_chunk_specs_slice(args, start, stop):
        payload = by_field.setdefault(
            spec.field,
            {"atoms": 0, "max_work_per_atom": 0, "max_total_work": 0},
        )
        weight = spec_native_work_weight(args, spec)
        payload["atoms"] += 1
        payload["max_work_per_atom"] = max(payload["max_work_per_atom"], weight)
        payload["max_total_work"] += weight
    return {
        "by_field": by_field,
        "max_total_work": sum(
            field_payload["max_total_work"] for field_payload in by_field.values()
        ),
    }


def shard_summaries(
    args: argparse.Namespace, shard_count: int
) -> list[dict[str, object]]:
    shape_ranges = single_chunk_shape_ranges(args)
    summaries = []
    for shard_index in range(shard_count):
        start, stop = shard_bounds(args, shard_index, shard_count)
        counts: dict[str, int] = {}
        for field, shape_start, shape_stop in shape_ranges:
            overlap = min(stop, shape_stop) - max(start, shape_start)
            if overlap > 0:
                counts[field] = counts.get(field, 0) + overlap
        summaries.append(
            {
                "shard_index": shard_index,
                "shard_count": shard_count,
                "start": start,
                "stop": stop,
                "count": stop - start,
                "shard_balance": args.shard_balance,
                "counts": counts,
                "cell_estimates": cell_estimates(args, counts),
                "native_work_estimates": native_work_estimates(args, start, stop),
                "emit_args": shard_emit_args(args, shard_index, shard_count),
            }
        )
    return summaries


def chunk_lengths(args: argparse.Namespace) -> dict[str, int]:
    return {"a_len": args.a_len, "k_len": args.k_len}


def dry_run_dimensions(args: argparse.Namespace) -> dict[str, object]:
    a_count = a_chunk_count(args.a_len)
    k_counts = [k_chunk_count(args, a_index) for a_index in range(a_count)]
    return {
        "a_chunk_count": a_count,
        "product_k_chunk_counts": {
            "min": min(k_counts) if k_counts else 0,
            "max": max(k_counts) if k_counts else 0,
            "total": sum(k_counts),
        },
        "prefix_rows": PREFIX_ROWS,
        "prefix_start": PREFIX_START,
    }


def manifest_payload(args: argparse.Namespace) -> dict[str, object]:
    specs = single_chunk_specs(args)
    counts: dict[str, int] = {}
    chunks = []
    for index, spec in enumerate(specs):
        counts[spec.field] = counts.get(spec.field, 0) + 1
        chunk: dict[str, object] = {
            "index": index,
            "field": spec.field,
            "a_index": spec.a_index,
            "a_lo": a_lo(args, spec.a_index),
            "a_len": args.a_len,
            "theorem": spec.name,
            "emit_args": single_chunk_emit_args(args, spec),
            "max_cells": field_cell_weight(args, spec.field),
            "native_work": spec_native_work_weight(args, spec),
        }
        if spec.k_index is not None:
            chunk.update(
                {
                    "k_index": spec.k_index,
                    "k_lo": k_lo(args, spec.k_index),
                    "k_len": args.k_len,
                }
            )
        chunks.append(chunk)
    payload: dict[str, object] = {
        "strategy": "large-tail-prefix",
        "certificate": args.certificate,
        "certificate_theorem": args.name,
        "single_chunk_prefix": args.single_chunk_prefix,
        "single_chunk_fields": selected_field_payload(args),
        "bounds": {
            "x_bound": args.x_bound,
            "y_bound": args.y_bound,
            "solo_bound": args.solo_bound,
        },
        "chunk_lengths": chunk_lengths(args),
        "dimensions": dry_run_dimensions(args),
        "extra_imports": args.extra_import,
        "reproducibility": reproducibility_metadata(),
        "total": len(specs),
        "counts": counts,
        "cell_estimates": cell_estimates(args, counts),
        "native_work_estimates": native_work_estimates(args),
        "chunks": chunks,
    }
    if args.manifest_shard_count is not None:
        payload["shards"] = shard_summaries(args, args.manifest_shard_count)
    return payload


def emit_manifest(args: argparse.Namespace) -> str:
    return json.dumps(manifest_payload(args), indent=2, sort_keys=True) + "\n"


def emit_dry_run_counts(args: argparse.Namespace) -> str:
    counts = count_by_field(args)
    payload: dict[str, object] = {
        "strategy": "large-tail-prefix",
        "certificate": args.certificate,
        "certificate_theorem": args.name,
        "single_chunk_prefix": args.single_chunk_prefix,
        "single_chunk_fields": selected_field_payload(args),
        "chunk_lengths": chunk_lengths(args),
        "dimensions": dry_run_dimensions(args),
        "reproducibility": reproducibility_metadata(),
        "counts": counts,
        "cell_estimates": cell_estimates(args, counts),
        "native_work_estimates": native_work_estimates(args),
        "total": sum(counts.values()),
        "materialized_chunks": False,
    }
    if args.dry_run_shard_count is not None:
        payload["shards"] = shard_summaries(args, args.dry_run_shard_count)
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"


def xy_bound_expr(args: argparse.Namespace) -> str:
    return f"(fun a k => {args.x_bound} a k * {args.y_bound} a k)"


def emit_header(args: argparse.Namespace) -> list[str]:
    imports = ["Prop51.PositiveSaddleChunks"]
    for module in args.extra_import:
        if module not in imports:
            imports.append(module)
    return [
        *(f"import {module}" for module in imports),
        "",
        "namespace Prop51",
        "",
        "/-",
        "Generated large-tail positive-saddle prefix certificate.",
        "",
        "This covers only the lower-prefix strip 2000 < a < 3000.",
        "The analytic fields for 3000 <= a remain separate Lean inputs.",
        "-/",
        "",
    ]


def single_chunk_theorem_lines(args: argparse.Namespace, spec: ChunkSpec) -> list[str]:
    alo = a_lo(args, spec.a_index)
    if spec.field == "product-x-bound":
        assert spec.k_index is not None
        return [
            f"theorem {spec.name} :",
            "    checkPositiveLargeTailProductXUpperEdgeBoundChunk",
            f"      {args.x_bound} {alo} {args.a_len} {k_lo(args, spec.k_index)}",
            f"      {args.k_len} = true := by",
            "  native_decide",
        ]
    if spec.field == "product-y-bound":
        assert spec.k_index is not None
        return [
            f"theorem {spec.name} :",
            "    checkPositiveLargeTailProductYUpperEdgeBoundChunk",
            f"      {args.y_bound} {alo} {args.a_len} {k_lo(args, spec.k_index)}",
            f"      {args.k_len} = true := by",
            "  native_decide",
        ]
    if spec.field == "product-small-scalar":
        assert spec.k_index is not None
        return [
            f"theorem {spec.name} :",
            "    checkPositiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundChunk",
            f"      {xy_bound_expr(args)} {alo} {args.a_len}",
            f"      {k_lo(args, spec.k_index)} {args.k_len} = true := by",
            "  native_decide",
        ]
    if spec.field == "product-tempered-scalar":
        assert spec.k_index is not None
        return [
            f"theorem {spec.name} :",
            "    checkPositiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundChunk",
            f"      {xy_bound_expr(args)} {alo} {args.a_len}",
            f"      {k_lo(args, spec.k_index)} {args.k_len} = true := by",
            "  native_decide",
        ]
    if spec.field == "solo-bound":
        return [
            f"theorem {spec.name} :",
            "    checkPositiveLargeTailSoloUpperEdgeBoundChunk",
            f"      {args.solo_bound} {alo} {args.a_len} = true := by",
            "  native_decide",
        ]
    if spec.field == "solo-scalar":
        return [
            f"theorem {spec.name} :",
            "    checkPositiveLargeTailSoloFastUpperEdgeBoundChunk",
            f"      {args.solo_bound} {alo} {args.a_len} = true := by",
            "  native_decide",
        ]
    raise AssertionError(f"unhandled field {spec.field!r}")


def emit_single_chunk(args: argparse.Namespace) -> str:
    assert args.emit_single_chunk is not None
    spec = ChunkSpec(
        args.emit_single_chunk,
        args.a_index,
        args.k_index,
        args.name
        if args.name != "positiveSaddleLargeTailPrefix"
        else single_chunk_name(
            args.single_chunk_prefix,
            args.emit_single_chunk,
            args.a_index,
            args.k_index,
        ),
    )
    lines = emit_header(args)
    lines.extend(single_chunk_theorem_lines(args, spec))
    lines.extend(["", "end Prop51", ""])
    return "\n".join(lines)


def exact_case_tree_lines(
    variables: list[tuple[str, int]],
    name_for_indices: Callable[..., str],
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


def add_product_chunk_dispatch_field(
    lines: list[str], field_name: str, atom_field: str, args: argparse.Namespace
) -> None:
    lines.extend(
        [
            f"  {field_name} := by",
            "    intro aChunk kChunk haChunk hkChunk",
            "    rcases (mem_positiveLargeTailLowerPrefixAChunks_iff",
            f"        (by norm_num : 0 < {args.a_len})).1 haChunk with",
            "      ⟨i, hi, rfl⟩",
        ]
    )
    a_count = a_chunk_count(args.a_len)
    lines.append(f"    have hi' : i < {a_count} := by")
    lines.append("      norm_num at hi")
    lines.append("      omega")
    lines.append("    clear hi")
    lines.append("    interval_cases i")
    for a_index in range(a_count):
        count = k_chunk_count(args, a_index)
        lines.append("    next =>")
        lines.extend(
            [
                "      rcases (mem_positiveProductFixedKChunksUpTo_iff",
                f"          (by norm_num : 0 < {args.k_len})).1 hkChunk with",
                "        ⟨j, hj, rfl⟩",
                f"      have hj' : j < {count} := by",
                "        norm_num [posKmax] at hj",
                "        omega",
                "      clear hj",
            ]
        )
        if args.use_single_chunk_theorems:
            lines.extend(
                exact_case_tree_lines(
                    [("j", count)],
                    lambda j, a_index=a_index: single_chunk_name(
                        args.single_chunk_prefix, atom_field, a_index, j
                    ),
                    indent="      ",
                )
            )
        else:
            lines.append("      interval_cases j <;> native_decide")


def add_solo_chunk_dispatch_field(
    lines: list[str], field_name: str, atom_field: str, args: argparse.Namespace
) -> None:
    lines.extend(
        [
            f"  {field_name} := by",
            "    intro aChunk haChunk",
            "    rcases (mem_positiveLargeTailLowerPrefixAChunks_iff",
            f"        (by norm_num : 0 < {args.a_len})).1 haChunk with",
            "      ⟨i, hi, rfl⟩",
        ]
    )
    a_count = a_chunk_count(args.a_len)
    lines.append(f"    have hi' : i < {a_count} := by")
    lines.append("      norm_num at hi")
    lines.append("      omega")
    lines.append("    clear hi")
    if args.use_single_chunk_theorems:
        lines.extend(
            exact_case_tree_lines(
                [("i", a_count)],
                lambda i: single_chunk_name(args.single_chunk_prefix, atom_field, i),
                indent="    ",
            )
        )
    else:
        lines.append("    interval_cases i <;> native_decide")


def product_bound_theorem_name(args: argparse.Namespace) -> str:
    return f"{args.name}_productBoundPrefixChunks"


def product_scalar_theorem_name(args: argparse.Namespace) -> str:
    return f"{args.name}_productScalarPrefixChunks"


def solo_bound_theorem_name(args: argparse.Namespace) -> str:
    return f"{args.name}_soloBoundPrefixChunks"


def solo_scalar_theorem_name(args: argparse.Namespace) -> str:
    return f"{args.name}_soloScalarPrefixChunks"


def emit_product_bound_prefix(args: argparse.Namespace) -> list[str]:
    lines = [
        f"theorem {product_bound_theorem_name(args)} :",
        "    PositiveSaddleLargeTailProductFastUpperEdgeLowerNXYBoundPrefixBoundChunksCertificate",
        f"      {args.x_bound} {args.y_bound} {args.a_len} {args.k_len} where",
        "  aLenPos := by norm_num",
        "  kLenPos := by norm_num",
    ]
    add_product_chunk_dispatch_field(lines, "xBoundChunk", "product-x-bound", args)
    add_product_chunk_dispatch_field(lines, "yBoundChunk", "product-y-bound", args)
    return lines


def emit_product_scalar_prefix(args: argparse.Namespace) -> list[str]:
    lines = [
        f"theorem {product_scalar_theorem_name(args)} :",
        "    PositiveSaddleLargeTailProductFastUpperEdgeLowerNProductBoundPrefixChunksCertificate",
        f"      {xy_bound_expr(args)} {args.a_len} {args.k_len} where",
        "  aLenPos := by norm_num",
        "  kLenPos := by norm_num",
    ]
    add_product_chunk_dispatch_field(
        lines, "smallProductChunk", "product-small-scalar", args
    )
    add_product_chunk_dispatch_field(
        lines, "temperedProductChunk", "product-tempered-scalar", args
    )
    return lines


def emit_solo_bound_prefix(args: argparse.Namespace) -> list[str]:
    lines = [
        f"theorem {solo_bound_theorem_name(args)} :",
        "    PositiveSaddleLargeTailSoloFastUpperEdgeBoundPrefixBoundChunksCertificate",
        f"      {args.solo_bound} {args.a_len} where",
        "  aLenPos := by norm_num",
    ]
    add_solo_chunk_dispatch_field(lines, "soloBoundChunk", "solo-bound", args)
    return lines


def emit_solo_scalar_prefix(args: argparse.Namespace) -> list[str]:
    lines = [
        f"theorem {solo_scalar_theorem_name(args)} :",
        "    PositiveSaddleLargeTailSoloFastUpperEdgeBoundPrefixChunksCertificate",
        f"      {args.solo_bound} {args.a_len} where",
        "  aLenPos := by norm_num",
    ]
    add_solo_chunk_dispatch_field(lines, "soloChunk", "solo-scalar", args)
    return lines


def product_full_hybrid_theorem_name(args: argparse.Namespace) -> str:
    return f"{args.name}_productFullHybrid"


def solo_full_hybrid_theorem_name(args: argparse.Namespace) -> str:
    return f"{args.name}_soloFullHybrid"


def emit_product_full_hybrid_wrapper(args: argparse.Namespace) -> list[str]:
    xy = xy_bound_expr(args)
    return [
        f"theorem {product_full_hybrid_theorem_name(args)}",
        "    (largeXBound :",
        "      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →",
        "        positiveLargeTailProductXClosedFactorialSplitBlockBound",
        f"            a (posNhi a) k ≤ {args.x_bound} a k)",
        "    (largeYBound :",
        "      ∀ {a k : Nat}, 3000 ≤ a → k ∈ positiveKRange a →",
        "        positiveLargeTailProductYClosedFactorialSplitBlockBound",
        f"            a (posNhi a) k ≤ {args.y_bound} a k)",
        "    (largeSmall :",
        "      ∀ {a k : Nat}, 3000 ≤ a →",
        "        k ∈ positiveKRange a → k ≤ ceilSqrt (posNhi a) →",
        "          positiveLargeTailSmallProductFastUpperEdgeLowerNProductBoundScalar",
        f"            {xy} a k)",
        "    (largeTempered :",
        "      ∀ {a k : Nat}, 3000 ≤ a →",
        "        k ∈ positiveKRange a → ceilSqrt (posNlo a) < k →",
        "          positiveLargeTailTemperedProductFastUpperEdgeLowerNProductBoundScalar",
        f"            {xy} a k) :",
        "    PositiveSaddleLargeTailProductFastUpperEdgeLowerNXYBoundFullHybridCertificate",
        f"      {args.x_bound} {args.y_bound} {args.a_len} {args.k_len} where",
        f"  boundPrefixChunks := {product_bound_theorem_name(args)}",
        f"  scalarPrefixChunks := {product_scalar_theorem_name(args)}",
        "  largeXBound := largeXBound",
        "  largeYBound := largeYBound",
        "  largeSmall := largeSmall",
        "  largeTempered := largeTempered",
    ]


def emit_solo_full_hybrid_wrapper(args: argparse.Namespace) -> list[str]:
    return [
        f"theorem {solo_full_hybrid_theorem_name(args)}",
        "    (largeBound :",
        "      ∀ {a : Nat}, 3000 ≤ a →",
        "        positiveLargeTailSoloGcompClosedFactorialSplitBlockSum a (posNhi a)",
        f"          ≤ {args.solo_bound} a)",
        "    (largeSolo :",
        "      ∀ {a : Nat}, 3000 ≤ a →",
        f"        positiveLargeTailSoloFastUpperEdgeBoundScalar {args.solo_bound} a) :",
        "    PositiveSaddleLargeTailSoloFastUpperEdgeBoundFullHybridCertificate",
        f"      {args.solo_bound} {args.a_len} where",
        f"  boundPrefixChunks := {solo_bound_theorem_name(args)}",
        f"  scalarPrefixChunks := {solo_scalar_theorem_name(args)}",
        "  largeBound := largeBound",
        "  largeSolo := largeSolo",
    ]


def emit_exact_product_full_hybrid_wrapper(args: argparse.Namespace) -> list[str]:
    return [
        f"theorem {product_full_hybrid_theorem_name(args)}",
        "    (large :",
        "      PositiveSaddleLargeTailProductClosedFactorialSplitBlockSumScalarFastExpUpperEdgeLowerNCertificate) :",
        "    PositiveSaddleLargeTailProductFastUpperEdgeLowerNXYBoundFullHybridCertificate",
        f"      {EXACT_X_BOUND} {EXACT_Y_BOUND} {args.a_len} {args.k_len} :=",
        f"  {product_scalar_theorem_name(args)}.toExactXYBoundFullHybridCertificate large",
    ]


def emit_exact_solo_full_hybrid_wrapper(args: argparse.Namespace) -> list[str]:
    return [
        f"theorem {solo_full_hybrid_theorem_name(args)}",
        "    (largeSolo :",
        "      ∀ {a : Nat}, 3000 ≤ a →",
        "        positiveLargeTailSoloGcompClosedFactorialSplitBlockSumFastCleared",
        "          a (posNhi a)) :",
        "    PositiveSaddleLargeTailSoloFastUpperEdgeBoundFullHybridCertificate",
        f"      {EXACT_SOLO_BOUND} {args.a_len} :=",
        f"  {solo_scalar_theorem_name(args)}.toExactBoundFullHybridCertificate_of_fastCleared",
        "    largeSolo",
    ]


def emit_prefix_certificates(args: argparse.Namespace) -> str:
    lines = emit_header(args)
    blocks: list[list[str]] = []
    if args.certificate == "exact-bound-full-hybrid":
        blocks.append(emit_product_scalar_prefix(args))
        blocks.append(emit_solo_scalar_prefix(args))
        blocks.append(emit_exact_product_full_hybrid_wrapper(args))
        blocks.append(emit_exact_solo_full_hybrid_wrapper(args))
        for index, block in enumerate(blocks):
            if index:
                lines.append("")
            lines.extend(block)
        lines.extend(["", "end Prop51", ""])
        return "\n".join(lines)
    if args.certificate in ("all-prefixes", "product-bound-prefix"):
        blocks.append(emit_product_bound_prefix(args))
    if args.certificate in ("all-prefixes", "product-scalar-prefix"):
        blocks.append(emit_product_scalar_prefix(args))
    if args.certificate in ("all-prefixes", "solo-bound-prefix"):
        blocks.append(emit_solo_bound_prefix(args))
    if args.certificate in ("all-prefixes", "solo-scalar-prefix"):
        blocks.append(emit_solo_scalar_prefix(args))
    if args.certificate == "all-prefixes":
        blocks.append(emit_product_full_hybrid_wrapper(args))
        blocks.append(emit_solo_full_hybrid_wrapper(args))
    for index, block in enumerate(blocks):
        if index:
            lines.append("")
        lines.extend(block)
    lines.extend(["", "end Prop51", ""])
    return "\n".join(lines)


def emit_single_chunk_shard(args: argparse.Namespace) -> str:
    start, stop = shard_bounds(args, args.shard_index, args.shard_count)
    lines = emit_header(args)
    field_note = selected_field_payload(args)
    lines.extend(
        [
            "/-",
            f"Shard {args.shard_index + 1}/{args.shard_count}, atoms [{start}, {stop}),",
            f"balanced by {args.shard_balance}.",
            f"Selected fields: {field_note}.",
            "-/",
            "",
        ]
    )
    for index, spec in enumerate(single_chunk_specs_slice(args, start, stop)):
        if index:
            lines.append("")
        lines.extend(single_chunk_theorem_lines(args, spec))
    lines.extend(["", "end Prop51", ""])
    return "\n".join(lines)


def emit(args: argparse.Namespace) -> str:
    if args.dry_run_counts:
        return emit_dry_run_counts(args)
    if args.emit_single_chunk_manifest:
        return emit_manifest(args)
    if args.emit_single_chunk_shard:
        return emit_single_chunk_shard(args)
    if args.emit_single_chunk is not None:
        return emit_single_chunk(args)
    return emit_prefix_certificates(args)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    sys.stdout.write(emit(args))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
