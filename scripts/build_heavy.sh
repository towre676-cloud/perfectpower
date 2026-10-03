#!/bin/sh
# Build the memory-heavy generated modules one at a time (a parallel `lake build` can exhaust
# memory on them: the class-list boxes and the rank-one slab checks reach 4-10 GB each), then
# everything else with the ordinary parallel build.
set -eu
for f in PerfectPower/Generated/RankOneSources/K*.lean PerfectPower/Generated/RankOneZeros/K*.lean PerfectPower/Generated/RankOneNorm/K*.lean PerfectPower/Generated/ClassLists/K*.lean; do
  m=$(echo "$f" | sed -e 's/\.lean$//' -e 's|/|.|g')
  lake build "$m" >/dev/null
done
lake build
