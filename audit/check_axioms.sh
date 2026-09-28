#!/bin/sh
# Fails unless every audited declaration uses only the three standard axioms.
set -eu
out=$(lake env lean audit/Axioms.lean)
printf '%s\n' "$out"
n=$(printf '%s\n' "$out" | grep -c "depends on axioms")
bad=$(printf '%s\n' "$out" | grep -v "depends on axioms: \[propext, Classical.choice, Quot.sound\]" || true)
if [ -n "$bad" ] || [ "$n" -lt 62 ]; then
  echo "axiom audit FAILED" >&2
  exit 1
fi
echo "axiom audit passed: $n declarations"
