#!/usr/bin/env bash
# Source-level defence in depth. Authoritative checks run through Lean in CI.
set -euo pipefail

tracked="$(git ls-files -- 'CausalSet.lean' 'CausalSet/*.lean' 'CausalSet/**/*.lean')" || {
  echo "Trust policy: unable to enumerate project Lean sources." >&2
  exit 2
}

if [[ -z "$tracked" ]]; then
  echo "Trust policy: no project Lean sources found." >&2
  exit 2
fi

mapfile -t files <<< "$tracked"
pattern='(^|[[:space:](⟨])(sorry|admit)([[:space:]),;⟩]|$)|(^|[[:space:](`])(private[[:space:]]+)?(axiom|opaque|unsafe|extern)([[:space:]]|$)|@\[[^]]*extern[^]]*\]|implemented_by|native_decide|ofReduceBool|ofReduceNat|skipKernelTC'

status=0
grep -nE "$pattern" -- "${files[@]}" || status=$?
case "$status" in
  0)
    echo "Trust policy violation in project Lean source." >&2
    exit 1
    ;;
  1)
    echo "Trust policy check passed (${#files[@]} files)."
    ;;
  *)
    echo "Trust policy: grep failed with status $status." >&2
    exit 2
    ;;
esac
