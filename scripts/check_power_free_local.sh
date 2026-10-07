#!/usr/bin/env bash
set -euo pipefail
PYTHONPATH=python python3 python/develop_power_free_local.py
lake build PerfectPower.PowerFreeLocal > receipts/power_free_local/lean_build.log 2>&1
lake env lean audit/PowerFreeLocal.lean > receipts/power_free_local/lean_reusable.log 2>&1
lake env lean audit/PowerFreeLocalPackets.lean > receipts/power_free_local/lean_packets.log 2>&1
PYTHONPATH=python python3 -m unittest discover -s python/tests -p test_power_free_local.py -v > receipts/power_free_local/python_tests.log 2>&1
python3 - <<'PY'
import json,re,hashlib
from pathlib import Path
out=Path('receipts/power_free_local');summary=json.loads((out/'summary.json').read_text())
allowed={'propext','Classical.choice','Quot.sound'}
for name,expected in [('lean_reusable.log',summary['reusable_theorems']),('lean_packets.log',summary['generated_declarations'])]:
 s=(out/name).read_text();lines=re.findall(r'depends on axioms:\s*\[([^]]*)\]',s)
 assert len(lines)==expected,(name,len(lines),expected)
 assert not any(x in s for x in ['error:','sorryAx','Lean.ofReduceBool'])
 assert all({v.strip() for v in line.split(',') if v.strip()}<=allowed for line in lines)
assert hashlib.sha256(Path('audit/PowerFreeLocalPackets.lean').read_bytes()).hexdigest()==summary['generated_source_sha256']
s=(out/'python_tests.log').read_text();assert 'Ran 11 tests' in s and '\nOK' in s
summary['kernel_checked']=True;summary['focused_python_tests']=11
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print('132 declarations: standard axioms only; 11 focused tests pass')
PY
