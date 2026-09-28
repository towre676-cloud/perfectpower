#!/bin/sh
# Fails unless every audited declaration depends only on a subset of the standard axioms
# {propext, Classical.choice, Quot.sound}: no sorryAx, no Lean.ofReduceBool, no custom axioms.
set -eu
out=$(lake env lean audit/Axioms.lean)
printf '%s\n' "$out"
printf '%s\n' "$out" > audit/axioms_report.txt
n=$(printf '%s\n' "$out" | grep -c "depend" || true)
bad=$(printf '%s\n' "$out" | grep "depend" | grep -v "does not depend on any axioms" \
      | sed -n 's/.*depends on axioms: \[\(.*\)\]$/\1/p' | tr ',' '\n' | sed 's/^ *//' \
      | grep -v -x -e propext -e Classical.choice -e Quot.sound || true)
unparsed=$(printf '%s\n' "$out" | grep -v "depend" | grep -v '^$' || true)
if [ -n "$bad" ] || [ -n "$unparsed" ] || [ "$n" -lt 80 ]; then
  echo "axiom audit FAILED: nonstandard axioms: [$bad] other output: [$unparsed] count: $n" >&2
  exit 1
fi
echo "axiom audit passed: $n declarations"
