#!/usr/bin/env bash
# Git hash of the trusted Spec sources, to bind an audit to one exact Spec.
#
#   scripts/spec_tree.sh               the Spec in the working tree
#   scripts/spec_tree.sh <commit>      the Spec in <commit>
#   scripts/spec_tree.sh --check <ref> fail unless the working tree and HEAD
#                                      both hold the Spec of <ref>
#
# The hash is that of a git tree object holding exactly RebuildBound/Spec/
# and, if present, RebuildBound/Spec.lean: the sources scripts/audit_spec.sh
# builds and replays (`git ls-tree --full-tree <hash>` lists it). For the
# working tree every file there counts, tracked, untracked or ignored, so a
# stray file makes the hash differ from any commit's. The objects are
# written to the repository's object store through a temporary index; the
# checkout's index is not touched.
set -euo pipefail

LEAN_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$LEAN_DIR"
REL="$(git rev-parse --show-prefix)"
fail() { echo "spec_tree: FAIL: $*" >&2; exit 1; }

# <tree-ish> holding lean/ at its path: restrict RebuildBound/ to the Spec entries.
restrict() {
  local entries
  entries="$(git ls-tree --full-tree "$1:${REL}RebuildBound" -- Spec Spec.lean)" ||
    fail "no RebuildBound/ in $1"
  [ -n "$entries" ] || fail "no Spec sources in $1"
  printf '%s\n' "$entries" | git mktree
}

worktree_hash() {
  local paths=() dir tree
  [ -d RebuildBound/Spec ] && paths+=(RebuildBound/Spec)
  [ -e RebuildBound/Spec.lean ] && paths+=(RebuildBound/Spec.lean)
  [ "${#paths[@]}" -gt 0 ] || fail "no Spec sources in the working tree"
  # A fresh index file must not exist yet: git rejects an empty one.
  dir="$(mktemp -d)"
  GIT_INDEX_FILE="$dir/index" git add -f -- "${paths[@]}"
  tree="$(GIT_INDEX_FILE="$dir/index" git write-tree)"
  rm -rf "$dir"
  restrict "$tree"
}

commit_hash() {
  local c
  c="$(git rev-parse -q --verify "$1^{commit}")" || fail "$1 is not a commit"
  restrict "$c"
}

case "${1:-}" in
  "") worktree_hash ;;
  --check)
    [ $# -eq 2 ] || { sed -n '2,16p' "$0"; exit 2; }
    want="$(commit_hash "$2")"
    head="$(commit_hash HEAD)"
    work="$(worktree_hash)"
    [ "$head" = "$want" ] || fail "HEAD's Spec $head differs from $2's $want"
    [ "$work" = "$want" ] || fail "the working tree's Spec $work differs from $2's $want (uncommitted, untracked or ignored files in RebuildBound/Spec)"
    echo "spec_tree: HEAD and the working tree hold the Spec of $2: $want"
    ;;
  -*) sed -n '2,16p' "$0"; exit 2 ;;
  *) [ $# -eq 1 ] || { sed -n '2,16p' "$0"; exit 2; }; commit_hash "$1" ;;
esac
