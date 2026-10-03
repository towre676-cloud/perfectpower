#!/bin/sh
# Build the memory-heavy generated modules one at a time (a parallel `lake build` can exhaust
# memory on them: the class-list boxes and the rank-one slab checks reach 4-10 GB each), then
# everything else with the ordinary parallel build.
set -eu
# Generated k=22 chunks must precede the source, avoiding parallel kernel reductions.
if [ -f PerfectPower/Generated/RankOneSources/K22.lean ] && [ -f PerfectPower/Generated/RankOneSources/K22Parts/IntegerDefs.lean ]; then
  lake build PerfectPower.Generated.RankOneSources.K22Parts.IntegerDefs >/dev/null
  for f in PerfectPower/Generated/RankOneSources/K22Parts/Chunk*.lean; do
    m=$(echo "$f" | sed -e 's/\.lean$//' -e 's|/|.|g')
    lake build "$m" >/dev/null
  done
fi
for f in PerfectPower/Generated/RankOneSources/K*.lean PerfectPower/Generated/RankOneZeros/K*.lean PerfectPower/Generated/RankOneNorm/K*.lean PerfectPower/Generated/ClassLists/K*.lean; do
  m=$(echo "$f" | sed -e 's/\.lean$//' -e 's|/|.|g')
  lake build "$m" >/dev/null
done
lake build
