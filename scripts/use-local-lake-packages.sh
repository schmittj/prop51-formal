#!/usr/bin/env bash
set -euo pipefail

target="${1:?usage: bash scripts/use-local-lake-packages.sh /path/to/existing/.lake/packages}"

if [ ! -d "$target" ]; then
  echo "Lake package directory does not exist: $target" >&2
  exit 1
fi

mkdir -p .lake

if [ -e .lake/packages ] && [ ! -L .lake/packages ]; then
  echo ".lake/packages already exists and is not a symlink." >&2
  echo "Move or remove it first, then rerun this script." >&2
  exit 1
fi

rm -f .lake/packages
ln -s "$target" .lake/packages

echo "Using Lake packages from $target"
