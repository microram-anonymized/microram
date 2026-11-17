#!/usr/bin/env bash
# Verify spec-test discovery with the production Lake configuration and pinned
# toolchain in a small isolated project. No Mathlib download or repo edits.
set -euo pipefail

LEAN_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
FIXTURE="$(mktemp -d "${TMPDIR:-/tmp}/spec-target-test.XXXXXXXX")"
trap 'rm -rf "$FIXTURE"' EXIT
export PATH="$HOME/.elan/bin:$PATH"

cp "$LEAN_DIR/lean-toolchain" "$FIXTURE/lean-toolchain"
# Keep the actual targets, globs, test driver and default targets. These tiny
# fixtures need only Lean core, so omit dependency declarations.
python3 - "$LEAN_DIR/lakefile.toml" "$FIXTURE/lakefile.toml" <<'PY'
from pathlib import Path
import re
import sys

source = Path(sys.argv[1]).read_text()
source = re.sub(r"(?ms)^\[\[require\]\].*?(?=^\[\[|\Z)", "", source)
Path(sys.argv[2]).write_text(source)
PY
cd "$FIXTURE"
mkdir -p RebuildBound spec_tests/Nested
cat >RebuildBound.lean <<'LEAN'
theorem RebuildBound.valid : True := True.intro
LEAN
cat >spec_tests/Smoke.lean <<'LEAN'
import RebuildBound
#guard 2 + 2 == 4
LEAN

PASSED=0
check() { # <label> <pass|fail> <Lake arguments...>
  local label="$1" want="$2" got
  shift 2
  if lake "$@" >case.log 2>&1; then got=pass; else got=fail; fi
  if [ "$got" != "$want" ]; then
    cat case.log >&2
    echo "test_spec_target: FAIL: $label: expected $want, got $got" >&2
    exit 1
  fi
  if [ "$want" = fail ] && ! grep -q 'NewFailure.lean' case.log; then
    cat case.log >&2
    echo "test_spec_target: FAIL: $label did not fail on the new test" >&2
    exit 1
  fi
  PASSED=$((PASSED + 1))
  echo "ok    $label ($want)"
}

check 'default build includes valid tests' pass build
test -f .lake/build/lib/lean/spec_tests/Smoke.olean
check 'lake test has a working driver' pass test

# Neither a root import nor an explicit list needs updating for a new test,
# including a test inside a new subdirectory.
cat >spec_tests/Nested/NewFailure.lean <<'LEAN'
#guard 2 + 2 == 5
LEAN
check 'new nested regression fails lake test' fail test
check 'new nested regression fails default build' fail build

cat >spec_tests/Nested/NewFailure.lean <<'LEAN'
#guard 2 + 2 == 4
LEAN
check 'fixed regression passes lake test' pass test
test -f .lake/build/lib/lean/spec_tests/Nested/NewFailure.olean
check 'fixed regression passes default build' pass build

echo "test_spec_target: $PASSED cases passed"
