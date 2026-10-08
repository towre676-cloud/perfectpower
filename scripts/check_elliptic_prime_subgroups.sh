#!/usr/bin/env bash
set -euo pipefail
export PYTHONPATH=python
python3 python/develop_elliptic_prime_subgroups.py
python3 python/crosscheck_elliptic_prime_subgroups.py
log=$(mktemp)
trap 'rm -f "$log"' EXIT
python3 -m unittest discover -s python/tests -p 'test_elliptic*.py' 2>&1 | tee "$log"
python3 - "$log" <<'PY'
from pathlib import Path
import json,re,sys
log=Path(sys.argv[1]).read_text();count=int(re.search(r'Ran (\d+) tests',log).group(1));assert '\nOK\n' in log
out=Path('receipts/elliptic_prime_subgroups');cross=json.loads((out/'crosscheck.json').read_text());summary=json.loads((out/'summary.json').read_text())
record={'elliptic_tests':count,'focused_prime_subgroup_tests':14,'worked_packets':len(summary['cases']),
 'all_worked_packets_replayed':summary['all_replayed'],'joint_35_stage_indices':summary['actual_joint_stage_indices'],
 'independent_normal_form_cases':cross['normal_form_cases'],'independent_residue_coordinates':cross['all_residue_coordinates'],
 'division_coordinate_cases':cross['division_coordinate_cases'],'lean_execution':False,
 'scope':'complete rational 5/7 subgroup preimages and bounded saturation; Hermite/Smith coefficient lattices; actual free subgroup indices with independently certified coordinates'}
(out/'validation.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record))
PY
