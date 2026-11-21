#!/usr/bin/env bash
# Compile a single-file Lean proof against a prebuilt Lean 4.34.1 + Mathlib, then audit axioms.
#
# Required environment:
#   LEAN_HOME       path to the lean-4.34.1-linux directory (containing bin/lean)
#   MATHLIB         path to the prebuilt mathlib4 checkout (with .lake/build and .lake/packages)
#
# usage: compile_solution.sh <Solution.lean> [tag]
set -eu
LEAN_HOME="${LEAN_HOME:?set LEAN_HOME to the lean-4.34.1-linux directory}"
MATHLIB="${MATHLIB:?set MATHLIB to the prebuilt mathlib4 directory}"
SRC="$1"
TAG="${2:-candidate}"
RUN="${RUN_DIR:-.}/work/$TAG"
rm -rf "$RUN"; mkdir -p "$RUN/build"
cp "$SRC" "$RUN/Solution.lean"
LEAN="$LEAN_HOME/bin/lean"
LIBS="$LEAN_HOME/lib/lean:$MATHLIB/.lake/build/lib/lean"
for d in "$MATHLIB"/.lake/packages/*/.lake/build/lib/lean; do LIBS="$LIBS:$d"; done
export LEAN_PATH="$RUN/build:$LIBS"
cd "$RUN"
echo "== compiling $TAG =="
START=$(date +%s)
set +e
"$LEAN" -j2 --tstack=400000 --root=. -o build/Solution.olean Solution.lean > compile.log 2>&1
RC=$?
set -e
echo "compile rc=$RC elapsed=$(( $(date +%s) - START ))s log=$RUN/compile.log"
if [ "$RC" -ne 0 ]; then
  grep -m 12 -n "error" compile.log || tail -30 compile.log
  exit "$RC"
fi
cat > Audit.lean <<'EOF'
import Solution
#print axioms AlpogeRHCore1.zeroFreeRegion
EOF
echo "== axiom audit =="
"$LEAN" -j2 --tstack=400000 --root=. Audit.lean
echo "== done: $RUN =="
