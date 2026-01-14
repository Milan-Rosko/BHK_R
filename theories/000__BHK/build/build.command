#!/usr/bin/env bash
set -Eeuo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"

pause() { [[ -t 0 ]] && { printf "\nPress Enter to close..."; IFS= read -r _ || true; }; }
trap 'rc=$?; ((rc!=0)) && echo && echo "Build failed (exit status: $rc)."; pause; exit $rc' EXIT

echo "== Coq build (copy to ./build, build there, export proof.txt) =="

[[ -f _CoqProject ]] || { echo "Error: _CoqProject not found."; exit 2; }

# Make Finder launches less painful (optional).
if command -v opam >/dev/null 2>&1; then eval "$(opam env 2>/dev/null || true)"; fi
command -v coq_makefile >/dev/null 2>&1 || { echo "Error: coq_makefile not found in PATH."; exit 127; }

BUILD="build"
mkdir -p "$BUILD"

echo "Syncing project into $BUILD/ ..."
rsync -a --delete \
  --exclude "$BUILD/" \
  --exclude ".git/" \
  --exclude "*.vo" --exclude "*.vos" --exclude "*.vok" --exclude "*.glob" \
  --exclude ".Makefile.coq.d" --exclude ".Makefile.coq.d.tmp" \
  --exclude "Makefile.coq" --exclude "Makefile.coq.conf" \
  ./ "$BUILD/"

SAN="$BUILD/_CoqProject.for-coq_makefile"
awk '
  /^[[:space:]]*#/ { print; next }
  /^[[:space:]]*$/ { print; next }
  /^[[:space:]]*-Q[[:space:]]+/ { print; next }
  /^[[:space:]]*-R[[:space:]]+/ { print; next }
  /^[[:space:]]*-I[[:space:]]+/ { print; next }
  /^[[:space:]]*-arg[[:space:]]+/ { print; next }
  /^[[:space:]]*[A-Za-z_][A-Za-z0-9_]*[[:space:]]*=[[:space:]]*/ { print; next }
  /^[[:space:]]*[^[:space:]]+\.(v|ml|mli|mlg|mlpack|mllib)[[:space:]]*$/ { print; next }
  /^[[:space:]]*-/ {
    gsub(/^[[:space:]]+|[[:space:]]+$/,"",$0)
    n=split($0,a,/[[:space:]]+/)
    for(i=1;i<=n;i++) if(a[i]!="") print "-arg " a[i]
    next
  }
  { next }
' "$BUILD/_CoqProject" > "$SAN"

TARGET="${1:-all}"
JOBS="${JOBS:-1}"  # keep deterministic; set JOBS=8 if you want parallel

echo "Building inside $BUILD/ ..."
pushd "$BUILD" >/dev/null
rm -f Makefile.coq Makefile.coq.conf .Makefile.coq.d .Makefile.coq.d.tmp
coq_makefile -f "_CoqProject.for-coq_makefile" -o Makefile.coq
make -f Makefile.coq -j "$JOBS" "$TARGET"
popd >/dev/null

# -------- proof.txt (root) --------
hash_file() {
  local f="$1"
  if command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$f" | awk '{print $1}'
  elif command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$f" | awk '{print $1}'
  else
    echo "Error: neither shasum nor sha256sum is available." >&2
    exit 127
  fi
}

UTC_NOW="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

{
  echo "Success."
  echo "Date: $UTC_NOW"
  echo "Hashes (SHA-256):"
  # List all .v files in the project, excluding build/, stable-sorted.
  find . -path "./$BUILD" -prune -o -name "*.v" -print \
    | LC_ALL=C sort \
    | while IFS= read -r f; do
        h="$(hash_file "$f")"
        echo "$h  ${f#./}"
      done
} > "$ROOT/proof.txt"
# -------------------------------

echo
echo "Done. Wrote $ROOT/proof.txt"
pause
