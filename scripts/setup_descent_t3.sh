#!/usr/bin/env bash
# Install the official pinned compiler without sudo, then replay the descent proofs.
set -euo pipefail
cd "$(dirname "$0")/.."
case "$(uname -s):$(uname -m)" in
  Linux:x86_64) ;;
  *) echo 'This installer targets Linux x86_64; use elan for other platforms.' >&2; exit 2 ;;
esac
version=4.20.0
expected=f3b058430f87dd9569c7ebd269f0af1be7b010b754849b543ee6cf9ccc08d4f0
cache_root="${XDG_CACHE_HOME:-$HOME/.cache}/perfectpower-lean"
compiler="$cache_root/lean-$version-linux"
archive="$cache_root/lean-$version-linux.tar.zst"
mkdir -p "$cache_root"
if [[ ! -x "$compiler/bin/lean" ]]; then
  if [[ ! -f "$archive" ]]; then
    curl --fail --location --connect-timeout 15 --max-time 600 \
      "https://github.com/leanprover/lean4/releases/download/v$version/lean-$version-linux.tar.zst" \
      --output "$archive.partial"
    mv "$archive.partial" "$archive"
  fi
  printf '%s  %s\n' "$expected" "$archive" | sha256sum --check -
  tar --zstd --no-same-owner -xf "$archive" -C "$cache_root"
fi
export PATH="$compiler/bin:$PATH"
export TAR_OPTIONS="${TAR_OPTIONS:+$TAR_OPTIONS }--no-same-owner"
if ! lean --version > "$cache_root/lean-startup.log" 2>&1; then
  if ! grep -q 'failed to locate application' "$cache_root/lean-startup.log"; then
    cat "$cache_root/lean-startup.log" >&2
    exit 1
  fi
  cc -shared -fPIC -Wall -Wextra -Werror scripts/lean_proc_self_compat.c \
    -ldl -o "$cache_root/lean-proc-self-compat.so"
  export LD_PRELOAD="$cache_root/lean-proc-self-compat.so${LD_PRELOAD:+:$LD_PRELOAD}"
fi
lean --version
[[ "$(cat lean-toolchain)" == "leanprover/lean4:v$version" ]] || {
  echo 'Repository toolchain differs from this pinned installer.' >&2; exit 2;
}
lake exe cache get
bash scripts/check_descent_t3.sh
