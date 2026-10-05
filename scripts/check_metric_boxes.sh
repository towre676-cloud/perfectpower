#!/usr/bin/env bash
set -euo pipefail
mkdir -p .lake/build/lib/lean/PerfectPower receipts/metric_boxes
for name in BernsteinBoxes RationalVoronoiPacket UniformHyperellipticMetric; do
  lake env lean -s65536 "PerfectPower/$name.lean" -o ".lake/build/lib/lean/PerfectPower/$name.olean"
done
lake env lean -s65536 audit/MetricBoxes.lean > receipts/metric_boxes/foundational_axioms.log
python3 - <<'PY'
import json,os,subprocess
from pathlib import Path
for row in json.loads(Path('receipts/metric_boxes/kernel_manifest.json').read_text()):
    source=Path(row['file']);log=Path('receipts/metric_boxes')/(source.stem+'_kernel.log')
    with log.open('w') as handle:
        subprocess.run(['lake','env','lean','-s65536',str(source)],stdout=handle,stderr=subprocess.STDOUT,check=True)
    print('Kernel checked',source,flush=True)
PY
python3 - <<'PY'
import re,json
from pathlib import Path
root=Path('receipts/metric_boxes')
s=(root/'foundational_axioms.log').read_text()
expected=28
for row in json.loads((root/'kernel_manifest.json').read_text()):
    s+=(root/(Path(row['file']).stem+'_kernel.log')).read_text();expected+=row['declarations']
rows=re.findall(r"'PerfectPower\.[^']+' (?:does not depend on any axioms|depends on axioms: \[([^]]*)\])",s)
assert len(rows)==expected,(len(rows),expected,s)
assert all(set(x.strip() for x in row.split(',') if x.strip()) <= {'propext','Classical.choice','Quot.sound'} for row in rows),s
print(str(expected)+' metric, arithmetic and native-packet declarations: standard axioms only')
PY
PYTHONPATH=python python3 -m unittest discover -s python/tests -p test_metric_boxes.py
