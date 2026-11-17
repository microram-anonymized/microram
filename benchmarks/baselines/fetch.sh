#!/usr/bin/env bash
# Fetch the baseline sources at their pinned versions (README.md in this
# directory): download fresh copies, check every hash, apply the patches under
# patches/ and write fetch_record.json, which the worker builds embed.
#
#   benchmarks/baselines/fetch.sh [DESTINATION]    (default third_party/baselines)
#
# The destination is replaced only after every check passes. Needs git, curl,
# patch, sha256sum, md5sum and python3.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
DEST="${1:-$ROOT/third_party/baselines}"
PATCHES="$ROOT/benchmarks/baselines/patches"

H2O2RAM_URL="https://github.com/55199789/H2O2RAM"
H2O2RAM_COMMIT="906eb97252b1b7e1cdfbaa8d46162c33ce364956"
# sha256 over `sha256sum` lines of every file, sorted by path, before patching.
H2O2RAM_TREE_SHA256="626e16ce784ec11e98be9bb55a84d5399d1fd59b6345fe02705d4cea7591a1ed"
H2O2RAM_PATCHES=(P-H1-planner-stderr.patch P-H2-frozen-planner.patch P-H3-constant-time-cmov.patch
                 P-H4-level-layout.patch P-H5-fresh-dummy-lookups.patch P-H6-two-tier-extract.patch
                 P-H7-executable-path.patch)

SONIC_URL="https://zenodo.org/records/20646913/files/sonic-usenix26-artifacts-20260612.tar.gz?download=1"
SONIC_FILE="sonic-usenix26-artifacts-20260612.tar.gz"
SONIC_MD5="9d71747e2ca64349871ab903eac136de"
SONIC_SHA256="aa02c4fc6884d797bfdda5d8ccfbe465192727e9e493f9b0e2da5c634d177d67"
SONIC_TREE_SHA256="7315332dfba4ff5fbe3bf7af41cd13eedf473d94285836ffcc9a18fb13ccac36"
# P-S1: ZingORAM's per-tree PRNG is used by several threads at once; one generator per thread.
SONIC_PATCHES=(P-S1-per-thread-prng.patch)

fail() { echo "fetch.sh: $*" >&2; exit 1; }
tree_sha256() {
  (cd "$1" && find . -path ./.git -prune -o -type f -print0 | LC_ALL=C sort -z | xargs -0 sha256sum) |
    sha256sum | cut -d' ' -f1
}
file_sha256() { sha256sum "$1" | cut -d' ' -f1; }
check() { [ "$2" = "$3" ] || fail "$1: expected $2, got $3"; }

mkdir -p "$DEST"
WORK="$(mktemp -d "$DEST/.fetch-XXXXXX")"
trap 'rm -rf "$WORK"' EXIT

echo "fetching H2O2RAM $H2O2RAM_COMMIT" >&2
git init -q "$WORK/h2o2ram"
git -C "$WORK/h2o2ram" fetch -q --depth 1 "$H2O2RAM_URL" "$H2O2RAM_COMMIT"
git -C "$WORK/h2o2ram" -c advice.detachedHead=false checkout -q FETCH_HEAD
check "H2O2RAM commit" "$H2O2RAM_COMMIT" "$(git -C "$WORK/h2o2ram" rev-parse HEAD)"
rm -rf "$WORK/h2o2ram/.git"
check "H2O2RAM tree" "$H2O2RAM_TREE_SHA256" "$(tree_sha256 "$WORK/h2o2ram")"
PATCH_JSON=""
for name in "${H2O2RAM_PATCHES[@]}"; do
  # P-H2, P-H3 and P-H5 change nothing unless the build defines their flag;
  # P-H1, P-H4, P-H6 and P-H7 apply to both builds.
  patch -s -p1 --forward --no-backup-if-mismatch -d "$WORK/h2o2ram" < "$PATCHES/h2o2ram/$name" ||
    fail "patch $name does not apply"
  PATCH_JSON+="${PATCH_JSON:+,}{\"id\":\"$(cut -d- -f1-2 <<<"$name")\",\"file\":\"h2o2ram/$name\",\"sha256\":\"$(file_sha256 "$PATCHES/h2o2ram/$name")\"}"
done
H2O2RAM_PATCHED="$(tree_sha256 "$WORK/h2o2ram")"

echo "fetching SONIC $SONIC_FILE" >&2
curl -fsSL --retry 3 -o "$WORK/$SONIC_FILE" "$SONIC_URL"
check "SONIC md5" "$SONIC_MD5" "$(md5sum "$WORK/$SONIC_FILE" | cut -d' ' -f1)"
check "SONIC sha256" "$SONIC_SHA256" "$(file_sha256 "$WORK/$SONIC_FILE")"
mkdir "$WORK/sonic"
tar xzf "$WORK/$SONIC_FILE" -C "$WORK/sonic" --strip-components=1 --no-same-owner
rm "$WORK/$SONIC_FILE"
check "SONIC tree" "$SONIC_TREE_SHA256" "$(tree_sha256 "$WORK/sonic")"
for name in "${SONIC_PATCHES[@]}"; do
  patch -s -p1 --forward --no-backup-if-mismatch -d "$WORK/sonic" < "$PATCHES/sonic/$name" ||
    fail "patch $name does not apply"
  PATCH_JSON+="${PATCH_JSON:+,}{\"id\":\"$(cut -d- -f1-2 <<<"$name")\",\"file\":\"sonic/$name\",\"sha256\":\"$(file_sha256 "$PATCHES/sonic/$name")\"}"
done
SONIC_PATCHED="$(tree_sha256 "$WORK/sonic")"

version() { "$@" 2>/dev/null | head -n1 || echo unknown; }
package() { dpkg-query -W -f='${Version}' "$1" 2>/dev/null || echo unknown; }
H2O2RAM_PATCHED="$H2O2RAM_PATCHED" SONIC_PATCHED="$SONIC_PATCHED" PATCH_JSON="[$PATCH_JSON]" \
GCC="$(version g++ --version)" CLANG="$(version clang++ --version)" CMAKE="$(version cmake --version)" \
TBB="$(package libtbb-dev)" NLOPT="$(package libnlopt-dev)" OPENSSL="$(package libssl-dev)" \
python3 - "$WORK/fetch_record.json" <<EOF
import json, os, sys
record = {
    "fetch_record_schema_version": 1,
    "sources": {
        "h2o2ram": {"url": "$H2O2RAM_URL", "commit": "$H2O2RAM_COMMIT", "license": "MIT",
                    "tree_sha256": "$H2O2RAM_TREE_SHA256",
                    "patched_tree_sha256": os.environ["H2O2RAM_PATCHED"]},
        "sonic": {"url": "$SONIC_URL", "file": "$SONIC_FILE", "license": "CC-BY-4.0",
                  "md5": "$SONIC_MD5", "sha256": "$SONIC_SHA256", "tree_sha256": "$SONIC_TREE_SHA256",
                  "patched_tree_sha256": os.environ["SONIC_PATCHED"]},
    },
    "patches": json.loads(os.environ["PATCH_JSON"]),
    "toolchain": {"gcc": os.environ["GCC"], "clang": os.environ["CLANG"], "cmake": os.environ["CMAKE"],
                  "libtbb-dev": os.environ["TBB"], "libnlopt-dev": os.environ["NLOPT"],
                  "libssl-dev": os.environ["OPENSSL"]},
}
with open(sys.argv[1], "w") as stream:
    json.dump(record, stream, indent=2, sort_keys=True)
    stream.write("\n")
EOF

rm -rf "$DEST/h2o2ram" "$DEST/sonic"
mv "$WORK/h2o2ram" "$WORK/sonic" "$DEST/"
mv "$WORK/fetch_record.json" "$DEST/fetch_record.json"
echo "fetched into $DEST (record sha256 $(file_sha256 "$DEST/fetch_record.json"))" >&2
