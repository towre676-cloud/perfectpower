#!/usr/bin/env bash
set -euo pipefail
mkdir -p .lake/build/lib/lean/PerfectPower receipts/voronoi_witness
lake env lean -s65536 PerfectPower/VoronoiEnclosure.lean -o .lake/build/lib/lean/PerfectPower/VoronoiEnclosure.olean
lake env lean -s65536 audit/VoronoiEnclosure.lean > receipts/voronoi_witness/lean_axioms.log
python3 - <<'PY'
import re
from pathlib import Path
s=Path('receipts/voronoi_witness/lean_axioms.log').read_text()
rows=re.findall(r"'PerfectPower\.[^']+' (?:does not depend on any axioms|depends on axioms: \[([^]]*)\])",s)
assert len(rows)==17,s
assert all(set(x.strip() for x in row.split(',') if x.strip()) <= {'propext','Classical.choice','Quot.sound'} for row in rows),s
print('Seventeen Voronoi enclosure declarations: standard axioms only')
PY
PYTHONPATH=python python3 -m unittest discover -s python/tests -p test_voronoi_witness.py
