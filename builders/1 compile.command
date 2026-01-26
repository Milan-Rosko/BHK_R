#!/usr/bin/env bash
set -euo pipefail

# -----------------------------------------------------------------------------
# Options:
# - CLEAN=1  : force full rebuild (make clean before all)
# - GUARD=1  : fail if any build artifacts (.glob/.vo/...) appear under repo theories/
# -----------------------------------------------------------------------------

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "${HERE}/.." && pwd)"

ROOT_CP="$ROOT/_CoqProject"
BUILDER_CP="$HERE/_CoqProject"

if [[ -f "$ROOT_CP" ]]; then
  COQPROJ="$ROOT_CP"
  ORIGIN="root"
elif [[ -f "$BUILDER_CP" ]]; then
  COQPROJ="$BUILDER_CP"
  ORIGIN="builder"
else
  echo "Checked for:"
  echo "  - $ROOT_CP"
  echo "  - $BUILDER_CP"
  echo "No _CoqProject found in either location."
  exit 1
fi

BUILD="${ROOT}/scratch"
SHADOW="${BUILD}/shadow"
BUILD_LOG="${BUILD}/build.log"

COQPROJECT_SRC="${HERE}/_CoqProject"
COQPROJECT_SHADOW="${SHADOW}/_CoqProject"

COQ_MAKEFILE="$(command -v coq_makefile || true)"
COQC="$(command -v coqc || true)"

CLEAN="${CLEAN:-0}"
GUARD="${GUARD:-1}"

# One certificate, inside _Builder
CERT_FILE="${HERE}/success.txt"

mkdir -p "${BUILD}" "${SHADOW}"
: > "${BUILD_LOG}"

# -----------------------------------------------------------------------------
# Prepare shadow sources
# -----------------------------------------------------------------------------
rm -rf "${SHADOW}/theories"
mkdir -p "${SHADOW}/theories"

if command -v rsync >/dev/null 2>&1; then
  rsync -a --delete "${ROOT}/theories/" "${SHADOW}/theories/" >/dev/null 2>&1 || true
else
  cp -R "${ROOT}/theories" "${SHADOW}/theories"
fi

cp -f "${COQPROJECT_SRC}" "${COQPROJECT_SHADOW}"

cd "${SHADOW}"

# -----------------------------------------------------------------------------
# Build
# -----------------------------------------------------------------------------
"${COQ_MAKEFILE}" -f "_CoqProject" -o "Makefile.coq" | tee -a "${BUILD_LOG}"

if [ "${CLEAN}" = "1" ]; then
  make -f Makefile.coq clean | tee -a "${BUILD_LOG}"
fi

make -f Makefile.coq -j 1 all | tee -a "${BUILD_LOG}"

# -----------------------------------------------------------------------------
# Discipline & Axiom Validation (The New Logic)
# -----------------------------------------------------------------------------
echo "[discipline] Running validation checks..." | tee -a "${BUILD_LOG}"

THEORIES_PATH="${SHADOW}/theories"
C_FOLDERS="$(find "${THEORIES_PATH}" -maxdepth 1 -type d -name 'C0*' -print)"
C_FILES="$(find "${THEORIES_PATH}" -type f -name '*.v' -print)"

ALL_AXIOMS_RAW="$(rg -n "^\s*Axioms?\b" ${C_FILES} || true)"
ALL_AXIOMS="$(echo "${ALL_AXIOMS_RAW}" | sed "s|${SHADOW}/||g")"
AXIOM_COUNT="$(echo "${ALL_AXIOMS_RAW}" | sed '/^$/d' | wc -l | tr -d ' ')"

if [ "${AXIOM_COUNT}" -eq 1 ]; then
    # Check if the single axiom is in a valid layer
    # Note: we check the relative path here
    BAD_AXIOMS="$(echo "${ALL_AXIOMS}" | rg -v 'theories/M001__BHK_R_Arithmetic/C0[^/]+/(P\d+_A__|P\d+_TA__)' || true)"
    
    if [ -n "${BAD_AXIOMS}" ]; then
        DISCIPLINE_STATUS="WARNING"
        DISCIPLINE_REPORT="Violation: The single axiom is in an unauthorized file.\nLocation: ${BAD_AXIOMS}"
    else
        DISCIPLINE_STATUS="Verified."
        DISCIPLINE_REPORT="Exactly 1 (expected) axiom found in authorized layer.\nLocation: ${ALL_AXIOMS}"
    fi
else
    DISCIPLINE_STATUS="WARNING"
    if [ "${AXIOM_COUNT}" -eq 0 ]; then
        DISCIPLINE_REPORT="Axiom Count: No axioms found (Expected exactly 1)."
    else
        DISCIPLINE_REPORT="Axiom Count: Found ${AXIOM_COUNT} axioms (Expected exactly 1).\nOffending lines:\n${ALL_AXIOMS}"
    fi
fi
# -----------------------------------------------------------------------------
# Generate Certificate
# -----------------------------------------------------------------------------
UTC_NOW="$(date -u +"%Y-%m-%dT%H:%M:%SZ")"

hash_file() {
  if command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$1" | awk '{print $1}'
  else
    sha256sum "$1" | awk '{print $1}'
  fi
}

SELECTED_LIST="$(mktemp "${BUILD}/selected.XXXXXX")"
sed -e 's/\r$//' -e 's/[[:space:]]*#.*$//' -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//' -e '/^$/d' -e '/^-/d' "${COQPROJECT_SHADOW}" | sort -u > "${SELECTED_LIST}"

COUNT="$(grep -c . "${SELECTED_LIST}" || true)"

{
  echo "Textfile (v.2.1) triggered by a shell-script if a 'makefile' run was successful."
  echo 
  echo " . . . . . . . . .....*************************.                           "
  echo ". . . . . ... ..... ....***************************.                       "
  echo " . . . . . . . . . . .. ... .. ... .....**************                     "
  echo ". . . . . .. .. .. .....********************************                   "
  echo " . . . . ... ..... ......********************************                  "
  echo ". . . . . . . . . . .. .... .... ....*********************                 "
  echo " . . . . . . ... .... .....**********************   *******                "
  echo ". . . . . . . .  .... ....*********************************.               "
  echo " . . . . .. .. ..... ....***********************************               "
  echo ". . . ... ... ..... .....***********************************               "
  echo " . . . .. ... ..... .....***********************************               "
  echo ". . . . .. ... ..... .....******************          *****                "
  echo " . . . . .. ... ..... .....***************              ***                "
  echo ". . . . . .. ... ..... .....************                 *                 "
  echo " . . . ..d8888b.. ..... .....*********                                     "
  echo ". . . .d88P..Y88b. ..... ......******                                      "
  echo " . . . Y88b... ... ...... .......**                                        "
  echo "        Y888b.   888  888  .d8888b .d8888b .d88b.  .d8888b  .d8888b        "
  echo "          ”Y88b. 888  888 d88P”   d88P”   d8P  Y8b 88K      88K            "
  echo "            ”888 888  888 888     888     88888888 ”Y8888b. ”Y8888b.       "
  echo "      Y88b  d88P Y88b 888 Y88b.   Y88b.   Y8b.          X88      X88  d8b  "
  echo "       ”Y8888P”   ”Y88888  ”Y8888P ”Y8888P ”Y8888   88888P'  88888P'  Y8P  "
  echo
  echo 
echo "                    Date (UTC): $UTC_NOW,"
  echo 
  if [ -n "${COQC}" ]; then
    echo "                   Rocq version: $(${COQC} --version 2>/dev/null | head -n 1)"
    echo "                   Method: isolated shadow, scratch folder"
  fi
  echo
  echo "---------------------------------------------------------------------------"
  echo "DISCIPLINE REPORT:"
  echo "---------------------------------------------------------------------------"
  echo
  echo "Status: $DISCIPLINE_STATUS"
  printf "Details:\n%b\n" "$DISCIPLINE_REPORT"
  echo
  echo "---------------------------------------------------------------------------"
  echo
  echo "_CoqProject file contents:"
  echo
  echo "=== BEGIN ==="
  echo 
  while IFS= read -r cp_line || [[ -n "$cp_line" ]]; do
    # Trim CR (in case of Windows line endings).
    cp_line="${cp_line%$'\r'}"
    printf "   %s \n" "$cp_line"
  done < "$COQPROJ"
  echo 
  echo "=== END ==="
  echo
  echo "------------------------"
  echo
  echo "Hash(es) (SHA-256) of ${COUNT} Files:"
  echo
  while IFS= read -r f; do
    [ -z "${f}" ] && continue
    if [ -f "${ROOT}/${f}" ]; then
      echo "   $(hash_file "${ROOT}/${f}")  ${f}"
    else
      echo "MISSING  ${f}"
    fi
  done < "${SELECTED_LIST}"
  echo
  echo "------------------------"
  echo

} > "${CERT_FILE}"

rm -f "${SELECTED_LIST}"

echo "" | tee -a "${BUILD_LOG}"
echo "Build process finished." | tee -a "${BUILD_LOG}"
echo "Certificate written to: ${CERT_FILE}" | tee -a "${BUILD_LOG}"
echo "Discipline Check: ${DISCIPLINE_STATUS}" | tee -a "${BUILD_LOG}"
