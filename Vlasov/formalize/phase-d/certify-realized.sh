#!/usr/bin/env bash
# certify-realized.sh — external REALIZED certification for the reuse score (PAPER Def. 3.4).
#
# Regenerates the standalone optimal-transport package from the CURRENT (live) project
# sources and builds it against Mathlib ALONE.  A GREEN build certifies that the
# "realized general layer" — Base/Geometry + OT/Wasserstein + OT/Coupling +
# Mathlib/ODE/PicardLindelof, 60 declarations — is genuinely self-contained / liftable:
# it "compiles in isolation", the strongest form of the REALIZED figure (not "the import
# graph looks clean" but "it actually builds standalone").
#
# No math source is committed in duplicate: this script copies the four files from the
# live tree on every run, so the standalone package can never drift from the originals.
# It reuses the main project's prebuilt Mathlib (symlinked), so a no-op re-run is fast and
# Mathlib is never rebuilt.  Exit code 0 iff the build is green.
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PKG="$(cd "$SCRIPT_DIR/../.." && pwd)"            # inner Lake package root (…/Vlasov/Vlasov)
STANDALONE="$SCRIPT_DIR/ot-standalone"

# the four "realized general" modules (module path under Vlasov/)
MODS=( "Base/Geometry" "OT/Wasserstein" "OT/Coupling" "Mathlib/ODE/PicardLindelof" )

echo "== regenerating standalone package from live sources =="
for m in "${MODS[@]}"; do
  src="$PKG/Vlasov/$m.lean"
  dst="$STANDALONE/Vlasov/$m.lean"
  [ -f "$src" ] || { echo "MISSING live source: $src"; exit 2; }
  mkdir -p "$(dirname "$dst")"
  cp -f "$src" "$dst"            # fresh copy => byte-identical to the live original
done

# scaffolding (config only — never the math); toolchain + manifest pinned to the main package
cp -f "$PKG/lean-toolchain"     "$STANDALONE/lean-toolchain"
cp -f "$PKG/lake-manifest.json" "$STANDALONE/lake-manifest.json"

cat > "$STANDALONE/lakefile.toml" <<'EOF'
name = "OTStandalone"
version = "0.1.0"
keywords = ["math"]
defaultTargets = ["OTStandalone"]

[leanOptions]
pp.unicode.fun = true # pretty-prints `fun a ↦ b`
relaxedAutoImplicit = false
weak.linter.mathlibStandardSet = true
maxSynthPendingDepth = 3

[[require]]
name = "mathlib"
path = "../../../.lake/packages/mathlib"

[[lean_lib]]
name = "OTStandalone"
globs = ["OTStandalone", "Vlasov.+"]
EOF

cat > "$STANDALONE/OTStandalone.lean" <<'EOF'
import Vlasov.Base.Geometry
import Vlasov.OT.Wasserstein
import Vlasov.OT.Coupling
import Vlasov.Mathlib.ODE.PicardLindelof
EOF

# reuse the main project's prebuilt Mathlib (+ its transitive deps) — never rebuild it
mkdir -p "$STANDALONE/.lake"
ln -sfn "$PKG/.lake/packages" "$STANDALONE/.lake/packages"

echo "== building OTStandalone against Mathlib alone =="
LOG="$STANDALONE/build.log"
( cd "$STANDALONE" && lake build OTStandalone ) > "$LOG" 2>&1
rc=$?

# P11 discipline: read the BUILD status first; a check off a failed build is stale.
echo "---- final build lines ----"
tail -n 3 "$LOG"
echo "---------------------------"
if [ "$rc" -eq 0 ] && grep -q "Build completed successfully" "$LOG"; then
  echo "REALIZED CERTIFICATION: GREEN  (standalone OT layer compiles against Mathlib alone)"
  exit 0
else
  echo "REALIZED CERTIFICATION: FAILED (rc=$rc) — first error:"
  grep -m1 -nE "error:" "$LOG" || true
  exit 1
fi
