#!/usr/bin/env bash
# Build and kernel-replay the trusted base: every RebuildBound.Spec module.
#
#   scripts/audit_spec.sh
#
# A kernel replay of a proof module loads the Spec modules it imports without
# checking them, so Spec, the trusted base, is replayed separately here. One
# replay costs about 6 minutes and 180 GB peak RSS on a 64-thread host.
#
# Build the library and every Spec source explicitly, including modules not
# imported by the library root. leanchecker only discovers available .oleans:
# without this build it could silently omit a new source or replay an older
# version. Check source/output coverage before replay. Deleted modules' stale
# build products are removed first; leanchecker otherwise includes them too.
#
# The audited Spec is named by its scripts/spec_tree.sh hash, taken before the
# build and again after the replay; the audit fails if they differ. The PASS
# line prints the hash and says whether HEAD holds the same Spec; the hash is
# also recorded in .lake/audit-spec-pass.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NAT_MAX_SIZE="${LEAN_NAT_MAX_SIZE:-1000000000}"

fail() { echo "audit_spec: FAIL: $*" >&2; exit 1; }
# The replay below is timed with GNU time; check for it before the long build.
[ -x /usr/bin/time ] ||
  fail "GNU time is required at /usr/bin/time (Debian/Ubuntu package 'time', installed by scripts/install_deps.sh)"

LISTFILE="$(mktemp)"
TIMEFILE=""
trap 'rm -f "$LISTFILE" "$TIMEFILE"' EXIT

# Prefix matching includes RebuildBound.Spec itself if that module exists.
# Keep discovery in a checked pipeline: process substitution would hide a
# find/sort failure from set -e and could produce an incomplete module list.
find RebuildBound -type f \
  \( -path 'RebuildBound/Spec.lean' -o -path 'RebuildBound/Spec/*.lean' \) \
  -print0 | LC_ALL=C sort -z >"$LISTFILE" || fail "cannot enumerate Spec sources"
mapfile -d '' -t SOURCES <"$LISTFILE"
[ "${#SOURCES[@]}" -gt 0 ] || fail "no Spec sources found"
rm -f .lake/audit-spec-pass
SPEC_TREE="$(bash scripts/spec_tree.sh)" || fail "cannot hash the Spec sources"
MODS=()
for f in "${SOURCES[@]}"; do
  m="${f%.lean}"; MODS+=("${m//\//.}")
done

LIB=.lake/build/lib/lean
STALE=0
if [ -d "$LIB/RebuildBound" ]; then
  find "$LIB/RebuildBound" -type f \
    \( -path "$LIB/RebuildBound/Spec.olean" -o -path "$LIB/RebuildBound/Spec/*.olean" \) \
    -print0 | LC_ALL=C sort -z >"$LISTFILE" || fail "cannot enumerate Spec outputs"
  while IFS= read -r -d '' o; do
    m="${o#"$LIB"/}"; m="${m%.olean}"
    if [ ! -f "$m.lean" ]; then
      echo "audit_spec: removing stale build products of $m"
      rm -f "$LIB/$m".olean{,.hash,.server,.server.hash,.private,.private.hash} \
        "$LIB/$m".ilean{,.hash} "$LIB/$m".trace
      STALE=$((STALE + 1))
    fi
  done <"$LISTFILE"
fi

N="${#MODS[@]}"
echo "== audit_spec: build RebuildBound and $N Spec modules"
lake build RebuildBound "${MODS[@]}" || fail "build failed; kernel replay not run"
for f in "${SOURCES[@]}"; do
  [ -f "$LIB/${f%.lean}.olean" ] || fail "missing build output for $f"
done

echo "== audit_spec: leanchecker RebuildBound.Spec ($N source modules built and verified, $STALE stale removed)"
TIMEFILE="$(mktemp)"
if ! /usr/bin/time -f '%e %M' -o "$TIMEFILE" lake env leanchecker RebuildBound.Spec; then
  fail "kernel replay"
fi
read -r WALL RSS <"$TIMEFILE"
AFTER="$(bash scripts/spec_tree.sh)" || fail "cannot hash the Spec sources"
[ "$AFTER" = "$SPEC_TREE" ] ||
  fail "the Spec sources changed during the audit ($SPEC_TREE before, $AFTER after)"
HEAD_C="$(git rev-parse --short HEAD 2>/dev/null || echo none)"
if [ "$(bash scripts/spec_tree.sh HEAD 2>/dev/null || true)" = "$SPEC_TREE" ]; then
  WHERE="the Spec of HEAD $HEAD_C"
else
  WHERE="DIRTY: not the Spec of HEAD $HEAD_C"
fi
mkdir -p .lake
echo "$SPEC_TREE $HEAD_C $(date -u +%Y-%m-%dT%H:%M:%SZ)" >.lake/audit-spec-pass
echo "audit_spec: PASS spec-tree $SPEC_TREE ($WHERE; ${WALL}s replay wall, peak RSS $((RSS / 1024)) MB)"
