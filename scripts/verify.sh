#!/usr/bin/env bash
# Local verification gate: match every trust layer of the hosted Lean checkpoint.
set -euo pipefail

AXIOM_AUDIT_REF="v0.1.2"
AXIOM_AUDIT_SHA="46024e005996495c65ef609368e11ab39c4222e3"
ALLOW="propext,Classical.choice,Quot.sound"
tool=".lake/axiom-audit"

bash scripts/check-trust.sh
lake build --wfail
lake exe mk_all --check --lib CausalSet
LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}" lake env leanchecker CausalSet
lake env lean Audit.lean

# A cached executable alone is insufficient evidence of the pinned audit revision.
valid=false
if [[ -x "$tool/.lake/build/bin/axiom-audit" && -f "$tool/lean-toolchain" ]] &&
   cmp -s lean-toolchain "$tool/lean-toolchain" &&
   [[ "$(git -C "$tool" rev-parse HEAD 2>/dev/null || true)" == "$AXIOM_AUDIT_SHA" ]] &&
   [[ -z "$(git -C "$tool" status --porcelain --untracked-files=no -- . ':(exclude)lean-toolchain' 2>/dev/null)" ]]; then
  valid=true
fi

if [[ "$valid" != true ]]; then
  rm -rf "$tool"
  git clone -q --depth 1 --branch "$AXIOM_AUDIT_REF" \
    https://github.com/leanprover-community/axiom-audit.git "$tool"
  if [[ "$(git -C "$tool" rev-parse HEAD)" != "$AXIOM_AUDIT_SHA" ]]; then
    echo "axiom-audit ref does not match pinned commit" >&2
    exit 1
  fi
  cp lean-toolchain "$tool/"
  (cd "$tool" && lake build)
fi

lake env "$tool/.lake/build/bin/axiom-audit" --allow "$ALLOW" --root CausalSet
echo "All verification layers passed."
