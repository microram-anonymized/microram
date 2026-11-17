#!/usr/bin/env bash
# Library-wide axiom and registry audit.
#
#   scripts/audit_axioms.sh
#
# Builds RebuildBound and every module under RebuildBound/, imports them all
# and runs scripts/axiom_audit.lean in library mode:
#   - every constant of every RebuildBound module is walked from scratch
#     (types and values, not the .olean axiom lists, which compiled package
#     code could rewrite); the walk may reach only propext,
#     Classical.choice and Quot.sound, and no RebuildBound module declares an
#     axiom;
#   - every theorem in scripts/packages.txt is declared by its own package's
#     modules and has exactly its statement as its type, a constant declared
#     in a RebuildBound.Spec module;
#   - every imported RebuildBound module's source is visible to git (tracked,
#     or untracked but not ignored), so no ignored file is part of the
#     audited library.
# A registered package without any file yet is reported as pending.
#
# About a minute once the library is built. It does not replay the kernel:
# scripts/audit_spec.sh replays Spec, and `lake env leanchecker <modules>`
# replays any other modules (see README.md).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NAT_MAX_SIZE="${LEAN_NAT_MAX_SIZE:-1000000000}"

fail() { echo "audit_axioms: FAIL: $*" >&2; exit 1; }
# The walk below is timed with GNU time; check for it before the long build.
[ -x /usr/bin/time ] ||
  fail "GNU time is required at /usr/bin/time (Debian/Ubuntu package 'time', installed by scripts/install_deps.sh)"

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

find RebuildBound -type f -name '*.lean' -print0 | LC_ALL=C sort -z >"$TMP/sources" ||
  fail "cannot enumerate sources"
mapfile -d '' -t SOURCES <"$TMP/sources"
MODS=(RebuildBound)
for f in "${SOURCES[@]}"; do m="${f%.lean}"; MODS+=("${m//\//.}"); done

{
  echo library
  git ls-files --cached --others --exclude-standard -- RebuildBound.lean RebuildBound |
    grep '\.lean$' |
    sed 's/\.lean$//; s|/|.|g; s/^/base /'
} >"$TMP/input"
PENDING=()
while read -r id _ expects; do
  files=()
  [ -f "RebuildBound/Proofs/$id.lean" ] && files+=("RebuildBound/Proofs/$id.lean")
  if [ -d "RebuildBound/Proofs/$id" ]; then
    while IFS= read -r f; do files+=("$f"); done \
      < <(find "RebuildBound/Proofs/$id" -name '*.lean' | LC_ALL=C sort)
  fi
  if [ "${#files[@]}" -eq 0 ]; then PENDING+=("$id"); continue; fi
  for f in "${files[@]}"; do m="${f%.lean}"; echo "pkg $id ${m//\//.}"; done
  for e in $expects; do
    [[ "$e" == *=* ]] && echo "thm $id ${e%%=*} ${e#*=}"
  done
done < <(grep -v '^[[:space:]]*\(#\|$\)' scripts/packages.txt) >>"$TMP/input"
[ "${#PENDING[@]}" -eq 0 ] || echo "audit_axioms: pending (no files yet): ${PENDING[*]}"

echo "== audit_axioms: build ${#MODS[@]} modules"
lake build "${MODS[@]}" >"$TMP/build.log" 2>&1 || { tail -40 "$TMP/build.log"; fail "build failed"; }

{
  echo "import Lean"
  for m in "${MODS[@]}"; do echo "import $m"; done
  cat scripts/axiom_audit.lean
  echo "run_cmd AxiomAudit.main \"$TMP/input\""
} >"$TMP/Audit.lean"
echo "== audit_axioms: walk ($(grep -c '^pkg ' "$TMP/input") package modules, $(grep -c '^thm ' "$TMP/input") registered theorems)"
/usr/bin/time -f '%e %M' -o "$TMP/time" lake env lean "$TMP/Audit.lean" || fail "audit"
read -r WALL RSS <"$TMP/time"
echo "audit_axioms: PASS at $(git rev-parse --short HEAD) (${WALL}s walk wall, peak RSS $((RSS / 1024)) MB)"
