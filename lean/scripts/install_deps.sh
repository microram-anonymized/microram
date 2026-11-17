#!/usr/bin/env bash
# Install everything needed to build the RebuildBound Lean project on Ubuntu
# (see README.md).
#
#   - system packages: curl, git, build tools, and python3 and GNU time,
#     which the audit scripts use (apt; uses sudo only if needed and only
#     when a package is missing)
#   - elan (Lean toolchain manager) in ~/.elan: the pinned release below,
#     checked against its SHA-256 before it runs; it fetches the Lean
#     version pinned in lean-toolchain (v4.34.1) on first use
#   - Mathlib's prebuilt cache (`lake exe cache get`), so Mathlib is not
#     compiled locally. Disk: about 8 GB in .lake/. RAM: a file importing
#     Mathlib's Poisson theory peaks at about 3.4 GB.
# Only the elan archive is checked here. The Lean release that elan fetches
# and Mathlib's cached .olean files are trusted as downloaded; leanchecker
# replays RebuildBound's modules but not Mathlib's.
#
# Usage: scripts/install_deps.sh [--no-build] [--no-apt]
#   --no-build  install the toolchain only; skip the Mathlib cache and build
#   --no-apt    skip system packages (e.g. no sudo and they are present)
set -euo pipefail

DO_BUILD=1
DO_APT=1
for arg in "$@"; do
  case "$arg" in
    --no-build) DO_BUILD=0 ;;
    --no-apt) DO_APT=0 ;;
    -h|--help) sed -n '2,20p' "$0"; exit 0 ;;
    *) echo "unknown option: $arg" >&2; exit 2 ;;
  esac
done

PROJECT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

if [ -r /etc/os-release ] && ! grep -qiE 'ubuntu|debian' /etc/os-release; then
  echo "warning: this script targets Ubuntu; continuing anyway" >&2
fi

# --- system packages ---------------------------------------------------------
if [ "$DO_APT" = 1 ]; then
  PKGS=(curl git ca-certificates build-essential python3 time)
  MISSING=()
  for p in "${PKGS[@]}"; do
    dpkg -s "$p" >/dev/null 2>&1 || MISSING+=("$p")
  done
  if [ "${#MISSING[@]}" -gt 0 ]; then
    SUDO=""
    if [ "$(id -u)" -ne 0 ]; then
      command -v sudo >/dev/null || { echo "need root or sudo to install: ${MISSING[*]}" >&2; exit 1; }
      SUDO=sudo
    fi
    echo "==> installing system packages: ${MISSING[*]}"
    $SUDO apt-get update
    $SUDO env DEBIAN_FRONTEND=noninteractive apt-get install -y "${MISSING[@]}"
  else
    echo "==> system packages already present"
  fi
fi

# --- elan --------------------------------------------------------------------
# A pinned elan release (tag v4.2.4, commit 227caca1), not the moving
# installer script: the script would download whatever release is latest.
# This does what that script does (unpack elan-init and run it), after
# checking the archive's SHA-256 (as published with the GitHub release).
ELAN_VERSION=v4.2.4
declare -A ELAN_SHA256=(
  [x86_64-unknown-linux-gnu]=42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63
  [aarch64-unknown-linux-gnu]=05febd124d84ebf994b2e7479922a5650b1e950c17ae3bd1ddd776b65bb72bf9
)
export PATH="$HOME/.elan/bin:$PATH"
if ! command -v elan >/dev/null; then
  ARCH="$(uname -m)-unknown-linux-gnu"
  WANT="${ELAN_SHA256[$ARCH]:-}"
  [ -n "$WANT" ] || { echo "no pinned elan $ELAN_VERSION archive for $ARCH" >&2; exit 1; }
  echo "==> installing elan $ELAN_VERSION ($ARCH)"
  ELAN_TMP="$(mktemp -d)"
  trap 'rm -rf "$ELAN_TMP"' EXIT
  curl -sSfL -o "$ELAN_TMP/elan.tar.gz" \
    "https://github.com/leanprover/elan/releases/download/$ELAN_VERSION/elan-$ARCH.tar.gz"
  echo "$WANT  $ELAN_TMP/elan.tar.gz" | sha256sum -c --quiet ||
    { echo "elan archive checksum mismatch" >&2; exit 1; }
  tar -xzf "$ELAN_TMP/elan.tar.gz" -C "$ELAN_TMP" elan-init
  "$ELAN_TMP/elan-init" -y --default-toolchain none
else
  echo "==> elan already installed: $(elan --version)"
fi

# --- pinned toolchain --------------------------------------------------------
cd "$PROJECT_DIR"
echo "==> installing toolchain pinned in lean-toolchain: $(cat lean-toolchain)"
elan toolchain install "$(cat lean-toolchain)"

if [ "$DO_BUILD" = 1 ]; then
  echo "==> fetching Mathlib and its prebuilt cache (large download)"
  lake exe cache get
  echo "==> building the project"
  lake build
fi

cat <<EOF

Done. elan is not added to your shell startup files. Either run
  export PATH="\$HOME/.elan/bin:\$PATH"
in each shell, or add that line to ~/.bashrc.
EOF
