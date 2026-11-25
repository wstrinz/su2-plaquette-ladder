#!/usr/bin/env bash
# Rebuild from the unmodified handoff, in a fresh disposable directory.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
build=$(mktemp -d "${TMPDIR:-/tmp}/su2-ladder-lean.XXXXXXXX")
printf 'Build directory: %s\n' "$build"
cp -R "$here/../handoff/lean" "$build/lean"
pin=77b55881495a059ed22123e4e85eaaa8c3faa422
if [[ -n ${SU2_DEPENDENCY_CACHE:-} ]]; then
    cache=$(cd "$SU2_DEPENDENCY_CACHE" && pwd)
    test "$(git -C "$cache/CertifiedGaps" rev-parse HEAD)" = "$pin"
    git -C "$cache/CertifiedGaps" diff --quiet HEAD
    test -d "$cache/lean/.lake/packages"
    ln -s "$cache/CertifiedGaps" "$build/CertifiedGaps"
    mkdir -p "$build/lean/.lake"
    ln -s "$cache/lean/.lake/packages" "$build/lean/.lake/packages"
else
    git clone --depth 1 https://github.com/LionSR/CertifiedGaps.git "$build/CertifiedGaps"
    git -C "$build/CertifiedGaps" fetch --depth 1 origin "$pin"
    git -C "$build/CertifiedGaps" checkout --detach "$pin"
fi
printf 'CertifiedGaps %s\n' "$(git -C "$build/CertifiedGaps" rev-parse HEAD)"
cd "$build/lean"
# The handoff manifest fixes the producer's absolute path. Relocate only that entry.
python3 - <<'PY'
import json
from pathlib import Path
manifest = Path("lake-manifest.json")
data = json.loads(manifest.read_text())
deps = [p for p in data["packages"] if p["name"] == "CertifiedGaps"]
assert len(deps) == 1 and deps[0]["type"] == "path"
deps[0]["dir"] = "../CertifiedGaps/code/lean"
manifest.write_text(json.dumps(data, indent=2))
PY
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2}
lake env lean --version
if [[ -z ${SU2_DEPENDENCY_CACHE:-} ]]; then
    lake exe cache get Mathlib.Tactic Mathlib.LinearAlgebra.UnitaryGroup Mathlib.Analysis.Complex.ExponentialBounds
fi
lake build GaugeGaps.FullSpectrum GaugeGaps.Lemma1Algebra GaugeGaps.LadderIntervals Mathlib.Analysis.Convex.Slope
lake env lean "$here/WindingContinuation.lean"
lake env lean "$here/ExtendedGap.lean"
lake env lean "$here/RefinedTension.lean"
