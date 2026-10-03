#!/bin/sh
# Run GNATprove on the unmodified AdaCore QA31-008 regression and on the selective-support variant.
# Needs gnatprove (FSF 13 build) and cvc5, z3 on PATH.  Usage: spark_pilot/run.sh [baseline|selective] [level]
set -eu
here=$(cd "$(dirname "$0")" && pwd)
arm=${1:-baseline}; level=${2:-2}
work=$(mktemp -d)
up="$here/../why3_isqrt/upstream/AdaCore__spark2014/testsuite/gnatprove/tests/QA31-008__von_neumann_sqrt"
cp "$up/p.ads" "$here/$arm/p.gpr" "$work/"
if [ "$arm" = baseline ]; then cp "$up/p.adb" "$work/"; else cp "$here/selective/p.adb" "$work/"; fi
cd "$work"
gnatprove -P p.gpr --prover=cvc5,z3 --report=all -j2 --level="$level" 2>&1 | grep -E "medium:|high:|error" || true
echo "proved: $(grep -c 'info:' obj/gnatprove/gnatprove.out 2>/dev/null || echo ?)  (work dir $work)"
