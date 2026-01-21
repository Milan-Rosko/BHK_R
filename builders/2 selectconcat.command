#!/usr/bin/env bash
# builders/composer.command

set -Eeuo pipefail

die() { echo "Error: $*" >&2; exit 2; }

TTY="/dev/tty"

# Prefer /dev/tty when available; otherwise we can still read from stdin if interactive.
have_tty() { [[ -r "$TTY" && -w "$TTY" ]]; }
is_interactive_stdin() { [[ -t 0 ]]; }

pause() {
  if have_tty; then
    printf "\nPress Enter to close..." >"$TTY"
    IFS= read -r _ <"$TTY" || true
  elif is_interactive_stdin; then
    printf "\nPress Enter to close..." >&2
    IFS= read -r _ || true
  fi
}

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
cd "$ROOT"

BUILD="$ROOT/scratch"
mkdir -p "$BUILD"

OUT="$ROOT/builders/_Composition"
LISTING="$BUILD/composer.list.txt"

prompt_num() {
  # prompt_num "Question" default min max
  local q="$1" def="$2" min="$3" max="$4" ans

  # Choose input/output streams
  local in_fd out_fd
  if have_tty; then
    in_fd="$TTY"; out_fd="$TTY"
  else
    in_fd="/dev/stdin"; out_fd="/dev/stderr"
  fi

  # If truly non-interactive (no tty and stdin not a terminal), fall back to default.
  if ! have_tty && ! is_interactive_stdin; then
    echo "$def"
    return 0
  fi

  while true; do
    printf "%s" "$q" >"$out_fd"
    IFS= read -r ans <"$in_fd" || true
    ans="${ans:-$def}"
    if [[ "$ans" =~ ^[0-9]+$ ]] && (( ans >= min && ans <= max )); then
      echo "$ans"
      return 0
    fi
    printf "Please enter a number in [%s-%s].\n" "$min" "$max" >"$out_fd"
  done
}

# Returns chapter id C### from absolute path, else empty.
chapter_of_abs() {
  local abs="$1"
  if [[ "$abs" =~ /theories/(C[0-9][0-9][0-9])__ ]]; then
    echo "${BASH_REMATCH[1]}"
  else
    echo ""
  fi
}

[[ -d "$ROOT/theories" ]] || die "Expected $ROOT/theories to exist."

CHAPTERS_FILE="$BUILD/chapters.$$"
CHAPTER_DIRS_FILE="$BUILD/chapter_dirs.$$"
CHAPTERS_UNIQ="$BUILD/chapters_uniq.$$"

: >"$CHAPTERS_FILE"
: >"$CHAPTER_DIRS_FILE"
: >"$CHAPTERS_UNIQ"

cleanup_tmp() { rm -f "$CHAPTERS_FILE" "$CHAPTER_DIRS_FILE" "$CHAPTERS_UNIQ" 2>/dev/null || true; }

on_exit() {
  local rc=$?
  cleanup_tmp
  if ((rc!=0)); then
    echo >&2
    echo "Composer failed (exit status: $rc)." >&2
    pause
  fi
  exit $rc
}
trap on_exit EXIT

# Find chapter directories and build sorted lists.
find "$ROOT/theories" -mindepth 1 -maxdepth 1 -type d -name 'C[0-9][0-9][0-9]__*' \
  | LC_ALL=C sort \
  | while IFS= read -r absdir; do
      base="$(basename "$absdir")"          # C003__Carryless_Pairing
      chap="${base%%__*}"                  # C003
      printf "%s\n" "$chap" >>"$CHAPTERS_FILE"
      printf "%s\t%s\n" "$chap" "$base" >>"$CHAPTER_DIRS_FILE"
    done

# Dedup chapters preserving order.
last=""
while IFS= read -r c; do
  [[ -z "$c" ]] && continue
  if [[ "$c" != "$last" ]]; then
    printf "%s\n" "$c" >>"$CHAPTERS_UNIQ"
    last="$c"
  fi
done <"$CHAPTERS_FILE"

N_CHAPTERS="$(wc -l <"$CHAPTERS_UNIQ" | tr -d ' ')"
[[ "$N_CHAPTERS" -gt 0 ]] || die "No chapter directories found matching theories/C###__*"

# Display chapter directories to the user before asking for options
echo "Found $N_CHAPTERS chapters:"
echo

i=0
while IFS=$'\t' read -r chap base; do
  [[ -z "$chap" || -z "$base" ]] && continue
  i=$((i+1))
  if have_tty; then
    printf "  %3d. %s  %s\n" "$i" "$chap" "$base" >"$TTY"
  else
    printf "  %3d. %s  %s\n" "$i" "$chap" "$base" >&2
  fi
done <"$CHAPTER_DIRS_FILE"

# New prompt to ask if user wants to exclude _R_ files
exclude_r=false
if have_tty; then
  printf "\nDo you want to exclude files with '_R_' in the name? (y/n): " >"$TTY"
else
  printf "\nDo you want to exclude files with '_R_' in the name? (y/n): " >&2
fi

if ! have_tty && ! is_interactive_stdin; then
  exclude_r="n"  # default to 'no' if no interaction
else
  IFS= read -r exclude_r <"$TTY"
  exclude_r="${exclude_r:-n}"  # default to 'n' if input is empty
fi

case "$exclude_r" in
  [Yy]* ) exclude_r=true ;;
  [Nn]* ) exclude_r=false ;;
  * )    exclude_r=false ;;
esac

# Dialogue for chapter range selection
if have_tty; then
  printf "\nSelect interval by number (FROM..TO).\n" >"$TTY"
else
  printf "\nSelect interval by number (FROM..TO).\n" >&2
fi

if ! have_tty && ! is_interactive_stdin; then
  FROM="1"
  TO="$N_CHAPTERS"
else
  FROM="$(prompt_num "FROM [1-$N_CHAPTERS] (default 1): " "1" 1 "$N_CHAPTERS")"
  TO="$(prompt_num "TO   [1-$N_CHAPTERS] (default $FROM): " "$FROM" 1 "$N_CHAPTERS")"
fi

if (( FROM > TO )); then
  die "FROM must be <= TO (got FROM=$FROM TO=$TO)"
fi

CHAP_FROM="$(sed -n "${FROM}p" "$CHAPTERS_UNIQ")"
CHAP_TO="$(sed -n "${TO}p" "$CHAPTERS_UNIQ")"
[[ -n "$CHAP_FROM" && -n "$CHAP_TO" ]] || die "Internal error resolving FROM/TO chapters."

echo
echo "Output:"
echo "  OUT:     $OUT"
echo "  LISTING: $LISTING"
echo "Interval:"
echo "  $CHAP_FROM .. $CHAP_TO"
echo

in_interval_chap() {
  local start="$1" end="$2" chap="$3"
  [[ -z "$chap" ]] && return 1
  local s="${start#C}" e="${end#C}" c="${chap#C}"
  [[ "$c" =~ ^[0-9][0-9][0-9]$ ]] || return 1
  ((10#$c >= 10#$s && 10#$c <= 10#$e))
}

: >"$LISTING"

# Find .v files and exclude _R_ if selected
find "$ROOT/theories" -type f -name '*.v' \
  | LC_ALL=C sort \
  | while IFS= read -r abs; do
      # Exclude files containing _R_ if user opted for exclusion
      if [[ "$exclude_r" == true && "$abs" =~ _R_ ]]; then
        continue
      fi
      chap="$(chapter_of_abs "$abs")"
      in_interval_chap "$CHAP_FROM" "$CHAP_TO" "$chap" || continue
      printf "%s\n" "${abs#"$ROOT/"}"
    done >>"$LISTING"

# Include README files, excluding _R_ files if selected
find "$ROOT/theories" -type f \( -name 'README' -o -name 'README.md' -o -name 'README.txt' -o -name 'readme' -o -name 'readme.md' -o -name 'readme.txt' \) \
  | LC_ALL=C sort \
  | while IFS= read -r abs; do
      # Exclude files containing _R_ if user opted for exclusion
      if [[ "$exclude_r" == true && "$abs" =~ _R_ ]]; then
        continue
      fi
      chap="$(chapter_of_abs "$abs")"
      in_interval_chap "$CHAP_FROM" "$CHAP_TO" "$chap" || continue
      printf "%s\n" "${abs#"$ROOT/"}"
    done >>"$LISTING"

V_COUNT="$( (grep -E '\.v$' "$LISTING" || true) | wc -l | tr -d ' ')"
R_COUNT="$( (grep -E '/README(\.md|\.txt)?$|/readme(\.md|\.txt)?$' "$LISTING" || true) | wc -l | tr -d ' ')"
TOTAL="$(wc -l <"$LISTING" | tr -d ' ')"

if [[ "$TOTAL" -eq 0 ]]; then
  echo "Warning: selected 0 files for interval $CHAP_FROM..$CHAP_TO." >&2
fi

UTC_NOW="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
: >"$OUT"
{
  echo "# _Composition generated by builders/composer.command"
  echo "# Generated (UTC): $UTC_NOW"
  echo "# Interval: ${CHAP_FROM}-${CHAP_TO} (indices ${FROM}-${TO} of ${N_CHAPTERS})"
  echo "# Format: one ROOT-relative path per line; blank lines and lines starting with '#' ignored."
  echo
  cat "$LISTING"
} >>"$OUT"

echo "Selected:"
echo "  .v files:     $V_COUNT"
echo "  README files: $R_COUNT"
echo "  total lines:  $TOTAL"
echo
echo "Done. Wrote $OUT"
exit 0
