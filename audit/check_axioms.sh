#!/bin/sh
# Fails unless every audited declaration uses only the three standard axioms.
set -eu
out=$(lake env lean audit/Axioms.lean)
printf '%s\n' "$out"
printf '%s\n' "$out" > audit/axioms_report.txt
n=$(printf '%s\n' "$out" | grep -c "depend")
bad=$(printf '%s\n' "$out" | grep -v "depends on axioms: \[propext, Classical.choice, Quot.sound\]" | grep -v "does not depend on any axioms" || true)
if [ -n "$bad" ] || [ "$n" -lt 68 ]; then
  echo "axiom audit FAILED" >&2
  exit 1
fi
echo "axiom audit passed: $n declarations"
