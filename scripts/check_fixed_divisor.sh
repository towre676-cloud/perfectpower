#!/usr/bin/env bash
set -euo pipefail
PYTHONPATH=python python3 python/develop_fixed_divisor.py
mkdir -p .lake/build/lib/lean/PerfectPower
for m in NativeNearSquare NativePolynomialSquare FastDivisors NativePolynomialRoots PowerFreeLocal FixedDivisor; do
  lake env lean "PerfectPower/$m.lean" -o ".lake/build/lib/lean/PerfectPower/$m.olean"
done > receipts/fixed_divisor/lean_build.log 2>&1
lake env lean audit/FixedDivisor.lean > receipts/fixed_divisor/lean_reusable.log 2>&1
lake env lean audit/FixedDivisorPackets.lean > receipts/fixed_divisor/lean_packets.log 2>&1
PYTHONPATH=python python3 -m unittest discover -s python/tests -p test_fixed_divisor.py -v > receipts/fixed_divisor/python_tests.log 2>&1
python3 - <<'PY'
from pathlib import Path
import re,json,hashlib
p=Path('receipts/fixed_divisor');summary=json.loads((p/'summary.json').read_text())
allowed={'propext','Classical.choice','Quot.sound'}
for f,n in [('lean_reusable.log',16),('lean_packets.log',summary['generated_declarations'])]:
 s=(p/f).read_text();rows=re.findall(r'depends on axioms:\s*\[([^]]*)\]',s)
 assert len(rows)==n,(f,len(rows),n)
 assert not any(x in s for x in ['error:','sorryAx','Lean.ofReduceBool'])
 assert all({v.strip() for v in row.split(',') if v.strip()}<=allowed for row in rows)
assert hashlib.sha256(Path('audit/FixedDivisorPackets.lean').read_bytes()).hexdigest()==summary['source_sha256']
assert 'Ran 24 tests' in (p/'python_tests.log').read_text()
summary.update(kernel_checked=True,reusable_theorems=16,focused_python_tests=24)
(p/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print('185 declarations audited: standard axioms only; 24 focused tests pass')
PY
