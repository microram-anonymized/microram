#!/usr/bin/env bash
# Regression tests for audit_spec.sh using the pinned Lean tools in an isolated
# temporary project. No Mathlib download or changes to this checkout are needed.
#
#   scripts/test_audit_spec.sh
set -euo pipefail

LEAN_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
FIXTURE="$(mktemp -d "${TMPDIR:-/tmp}/audit-spec-test.XXXXXXXX")"
trap 'rm -rf "$FIXTURE"' EXIT
export PATH="$HOME/.elan/bin:$PATH"

mkdir -p "$FIXTURE/scripts" "$FIXTURE/RebuildBound/Spec"
cp "$LEAN_DIR/scripts/audit_spec.sh" "$LEAN_DIR/scripts/spec_tree.sh" "$FIXTURE/scripts/"
cp "$LEAN_DIR/lean-toolchain" "$FIXTURE/lean-toolchain"
cd "$FIXTURE"

cat >lakefile.toml <<'TOML'
name = "RebuildBound"
version = "0.1.0"
defaultTargets = ["RebuildBound"]

[[lean_lib]]
name = "RebuildBound"
# Only imports of the root are built by the library target. This deliberately
# exercises audit_spec's explicit build of otherwise unimported Spec modules.
globs = ["RebuildBound"]
TOML
cat >RebuildBound.lean <<'LEAN'
import RebuildBound.Spec.Base
import RebuildBound.Proof
LEAN
cat >RebuildBound/Spec/Base.lean <<'LEAN'
theorem RebuildBound.Spec.base : 1 + 1 = 2 := rfl
LEAN
cat >RebuildBound/Proof.lean <<'LEAN'
theorem RebuildBound.proof : True := True.intro
LEAN
# audit_spec names the audited Spec by its tree hash and compares it with HEAD's.
git -c init.templateDir= init -q
gitc() {
  git -c core.hooksPath=/dev/null -c commit.gpgsign=false \
    -c user.name='Audit regression test' -c user.email='audit-test@example.invalid' "$@"
}
gitc commit -q --allow-empty -m 'Temporary audit regression fixture'

PASSED=0
LOG="$FIXTURE/audit.log"
fail() {
  echo "test_audit_spec: FAIL: $*" >&2
  if [ -f "$LOG" ]; then tail -60 "$LOG" >&2; fi
  exit 1
}
run_case() { # <label> <pass|fail> [expected failure message]
  local label="$1" want="$2" diagnostic="${3:-}" got
  if bash scripts/audit_spec.sh >"$LOG" 2>&1; then got=pass; else got=fail; fi
  [ "$got" = "$want" ] || fail "$label: expected $want, got $got"
  if [ "$want" = pass ]; then
    grep -q '^audit_spec: PASS' "$LOG" || fail "$label: success message missing"
  elif grep -q '^audit_spec: PASS' "$LOG"; then
    fail "$label: failed audit printed PASS"
  fi
  if [ -n "$diagnostic" ]; then
    grep -Fq "$diagnostic" "$LOG" || fail "$label: expected diagnostic missing: $diagnostic"
  fi
  PASSED=$((PASSED + 1))
  echo "ok    $label ($want)"
}

run_case 'clean project builds before replay' pass
test -f .lake/build/lib/lean/RebuildBound/Spec/Base.olean ||
  fail 'clean audit did not produce Base.olean'
# The Spec is not committed yet: the PASS line must say so, and name the
# audited tree, which is also recorded in .lake/audit-spec-pass.
TREE="$(bash scripts/spec_tree.sh)"
grep -q "^audit_spec: PASS spec-tree $TREE (DIRTY: not the Spec of HEAD" "$LOG" ||
  fail 'PASS line does not name the dirty audited tree'
[ "$(cut -d' ' -f1 .lake/audit-spec-pass)" = "$TREE" ] ||
  fail '.lake/audit-spec-pass does not record the audited tree'
gitc add RebuildBound.lean RebuildBound lakefile.toml lean-toolchain
gitc commit -q -m 'Commit the Spec'
run_case 'committed Spec is reported clean' pass
grep -q "^audit_spec: PASS spec-tree $TREE (the Spec of HEAD $(git rev-parse --short HEAD);" "$LOG" ||
  fail 'PASS line does not report the Spec of HEAD'

cat >RebuildBound/Spec/Detached.lean <<'LEAN'
theorem RebuildBound.Spec.detached : 2 + 2 = 4 := rfl
LEAN
run_case 'new valid unimported Spec module is built' pass
test -f .lake/build/lib/lean/RebuildBound/Spec/Detached.olean ||
  fail 'audit omitted the unimported Detached module'
cp .lake/build/lib/lean/RebuildBound/Spec/Detached.olean "$FIXTURE/Detached.olean"

cat >RebuildBound/Spec/Invalid.lean <<'LEAN'
theorem RebuildBound.Spec.invalid : False := True.intro
LEAN
run_case 'new invalid unimported Spec module is rejected' fail \
  'build failed; kernel replay not run'
rm RebuildBound/Spec/Invalid.lean

# Preserve the previously valid .olean while changing its source. An audit
# that only replays existing products would incorrectly accept this case.
cat >RebuildBound/Spec/Detached.lean <<'LEAN'
theorem RebuildBound.Spec.detached : False := True.intro
LEAN
test -f .lake/build/lib/lean/RebuildBound/Spec/Detached.olean ||
  fail 'stale-output case requires the previous Detached.olean'
run_case 'changed invalid source cannot reuse an old .olean' fail \
  'build failed; kernel replay not run'

rm RebuildBound/Spec/Detached.lean
# Reinstall the known-valid output in case the failed rebuild removed it.
# Include auxiliary products emitted by other Lean toolchain versions.
cp "$FIXTURE/Detached.olean" .lake/build/lib/lean/RebuildBound/Spec/Detached.olean
COMPANIONS=(olean.hash ilean ilean.hash trace olean.private olean.private.hash
  olean.server olean.server.hash)
for suffix in "${COMPANIONS[@]}"; do
  printf 'stale output\n' >".lake/build/lib/lean/RebuildBound/Spec/Detached.$suffix"
done
run_case 'deleted Spec module has its orphan outputs removed' pass
for suffix in olean "${COMPANIONS[@]}"; do
  test ! -e ".lake/build/lib/lean/RebuildBound/Spec/Detached.$suffix" ||
    fail "orphan Detached.$suffix was retained"
done

cat >RebuildBound/Proof.lean <<'LEAN'
theorem RebuildBound.proof : False := True.intro
LEAN
run_case 'full library build failure is rejected' fail 'build failed; kernel replay not run'
cat >RebuildBound/Proof.lean <<'LEAN'
theorem RebuildBound.proof : True := True.intro
LEAN

cat >RebuildBound/Spec.lean <<'LEAN'
theorem RebuildBound.Spec.root : True := True.intro
LEAN
run_case 'valid unimported root Spec module is built' pass
test -f .lake/build/lib/lean/RebuildBound/Spec.olean ||
  fail 'audit omitted the root Spec module'
cp .lake/build/lib/lean/RebuildBound/Spec.olean "$FIXTURE/Spec.olean"
cat >RebuildBound/Spec.lean <<'LEAN'
theorem RebuildBound.Spec.root : False := True.intro
LEAN
run_case 'invalid unimported root Spec module is rejected' fail \
  'build failed; kernel replay not run'
rm RebuildBound/Spec.lean
cp "$FIXTURE/Spec.olean" .lake/build/lib/lean/RebuildBound/Spec.olean
for suffix in "${COMPANIONS[@]}"; do
  printf 'stale output\n' >".lake/build/lib/lean/RebuildBound/Spec.$suffix"
done
run_case 'deleted root Spec module has its orphan outputs removed' pass
for suffix in olean "${COMPANIONS[@]}"; do
  test ! -e ".lake/build/lib/lean/RebuildBound/Spec.$suffix" ||
    fail "orphan Spec.$suffix was retained"
done

# Keep the library itself valid: an empty trusted source set must be rejected
# explicitly, rather than incidentally failing on an obsolete import.
rm RebuildBound/Spec/Base.lean
cat >RebuildBound.lean <<'LEAN'
import RebuildBound.Proof
LEAN
run_case 'empty Spec source set is rejected' fail 'no Spec sources found'

echo "test_audit_spec: $PASSED cases passed"
