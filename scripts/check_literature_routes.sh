#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
for module in QuadraticProjection MixedRunge CubicCovariants RankTwoSieve; do
  lake env lean "PerfectPower/$module.lean" -o ".lake/build/lib/lean/PerfectPower/$module.olean"
done
log=$(mktemp)
trap 'rm -f "$log"' EXIT
lake env lean -s 65536 audit/MixedRunge.lean | tee "$log"
lake env lean audit/LiteratureRoutes.lean | tee -a "$log"
python3 - "$log" <<'PY'
import re, sys
from pathlib import Path
text = Path(sys.argv[1]).read_text()
reports = re.findall(r'depends on axioms: \[([^\]]*)\]', text)
total = len(reports) + text.count('does not depend on any axioms')
assert total == 14, f'expected 14 reports, got {total}'
for report in reports:
    unexpected = {x.strip() for x in report.split(',') if x.strip()} - {'propext','Classical.choice','Quot.sound'}
    assert not unexpected, unexpected
PY
PYTHONPATH=python python3 -m unittest python.tests.test_mixed_runge python.tests.test_rank_two_signed_sieve
