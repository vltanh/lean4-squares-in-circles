#!/usr/bin/env bash
# Remove ONLY disposable untracked n=9 search directories from THIS checkout.
# Default: dry run. Usage: bash scripts/cleanup-n9-scratch.sh --apply
set -Eeuo pipefail
usage() { echo "Usage: $0 [--dry-run|--apply]" >&2; exit 2; }
mode="${1:---dry-run}"
[[ "$#" -le 1 ]] || usage
[[ "$mode" == "--dry-run" || "$mode" == "--apply" ]] || usage
root="$(git rev-parse --show-toplevel 2>/dev/null)" || {
  echo "ERROR: not inside a Git checkout; no cleanup performed" >&2; exit 1;
}
cd "$root"
[[ -f research/nine/CURRENT_MASK_DIRECTIVE.md ]] || {
  echo "ERROR: expected n=9 directive missing; no cleanup performed" >&2; exit 1;
}
declare -a targets=()
for p in research/nine/.runs research/nine/.scratch; do
  [[ -d "$p" || -L "$p" ]] && targets+=("$p")
done
if [[ -d research/nine/computer_assisted ]]; then
  while IFS= read -r -d '' p; do targets+=("$p"); done < <(
    find research/nine/computer_assisted -type d \
      \( -name .runs -o -name .scratch -o -name intermediate_runs \) \
      -prune -print0
  )
fi
if (( ${#targets[@]} == 0 )); then
  echo "No disposable scratch directories found in this checkout."
  exit 0
fi
for p in "${targets[@]}"; do
  if [[ -L "$p" ]]; then
    echo "SKIP symlink: $p"; continue
  fi
  resolved="$(realpath -e -- "$p")" || { echo "SKIP unresolved: $p"; continue; }
  case "$resolved" in
    "$root"/research/nine/.runs|"$root"/research/nine/.scratch|"$root"/research/nine/computer_assisted/*) ;;
    *) echo "SKIP outside guarded n=9 scratch tree: $p"; continue ;;
  esac
  if [[ -n "$(git ls-files -- "$p")" ]]; then
    echo "SKIP contains tracked proof inputs: $p"; continue
  fi
  echo "$mode $p ($(du -sh -- "$p" | cut -f1))"
  if [[ "$mode" == "--apply" ]]; then
    rm -rf -- "$p"
  fi
done
echo "Accepted certificates, source archives, hashed manifests and Git-tracked files were not touched."
