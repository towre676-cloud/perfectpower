#!/bin/sh
# Fails unless every audited declaration depends only on a subset of the standard axioms
# {propext, Classical.choice, Quot.sound}: no sorryAx, no Lean.ofReduceBool, no custom axioms.
set -eu
# Lean wraps long messages at 100 columns; rejoin continuation lines (they start with a space).
out=$(lake env lean audit/Axioms.lean | awk 'NR > 1 && /^ / { sub(/^ +/, " "); printf "%s", $0; next } { if (NR > 1) printf "\n"; printf "%s", $0 } END { printf "\n" }')
printf '%s\n' "$out"
printf '%s\n' "$out" > audit/axioms_report.txt
n=$(printf '%s\n' "$out" | grep -c "depend" || true)
bad=$(printf '%s\n' "$out" | grep "depend" | grep -v "does not depend on any axioms" \
      | sed -n 's/.*depends on axioms: \[\(.*\)\]$/\1/p' | tr ',' '\n' | sed 's/^ *//' \
      | grep -v -x -e propext -e Classical.choice -e Quot.sound || true)
unparsed=$(printf '%s\n' "$out" | grep -v "depend" | grep -v '^$' || true)
if [ -n "$bad" ] || [ -n "$unparsed" ] || [ "$n" -lt 100 ]; then
  echo "axiom audit FAILED: nonstandard axioms: [$bad] other output: [$unparsed] count: $n" >&2
  exit 1
fi
echo "axiom audit passed: $n declarations"
