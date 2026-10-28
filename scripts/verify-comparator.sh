#!/usr/bin/env bash
set -euo pipefail

# Adapted from PalomarRegistry/PalomarTemplate (Apache-2.0).
repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"

if [[ $(uname -s) != Linux ]]; then
  echo "error: Palomar Comparator checks need Linux and bubblewrap; use CI" >&2
  exit 1
fi
for command_name in bwrap lake lean python3; do
  if ! command -v "$command_name" >/dev/null 2>&1; then
    echo "error: $command_name is required" >&2
    exit 1
  fi
done

prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  if [[ ! -x "$prefix/bin/$tool" ]]; then
    echo "error: the pinned Lean toolchain does not include $tool" >&2
    exit 1
  fi
done

# Palomar adds these kernels itself; they must not appear in the submitted JSON.
config=$(mktemp "${TMPDIR:-/tmp}/palomar-comparator.XXXXXX")
trap 'rm -f "$config"' EXIT
python3 - comparator.json "$config" "$prefix" <<'PY'
import json
from pathlib import Path
import sys

source, destination, prefix = sys.argv[1:]
config = json.loads(Path(source).read_text())
if not isinstance(config, dict):
    raise SystemExit("error: comparator.json must contain a JSON object")
if "external_kernels" in config:
    raise SystemExit("error: Palomar does not allow external_kernels in comparator.json")
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron"],
}
Path(destination).write_text(json.dumps(config, indent=2) + "\n")
PY

lake exe cache get
lake comparator --config "$config"
