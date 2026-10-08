#!/usr/bin/env bash
set -euo pipefail
PYTHONPATH=python python3 python/develop_residue_atlas_intersection_factored.py
PYTHONPATH=python python3 -m unittest discover -s python/tests -p test_residue_atlas_intersection_factored.py
PYTHONPATH=python python3 python/crosscheck_residue_atlas_intersection_factored.py
lake build PerfectPower.ResidueAtlasIntersectionFactored
proof_log=$(mktemp)
trap 'rm -f "$proof_log"' EXIT
lake env lean audit/ResidueAtlasIntersectionFactoredAudit.lean | tee "$proof_log"
for source in receipts/residue_atlas_intersection_factored/*.lean; do
  lake env lean -s 65536 "$source" | tee -a "$proof_log"
done
python3 - "$proof_log" <<'PY'
import json,re,sys
from pathlib import Path
text=Path(sys.argv[1]).read_text()
sets=re.findall(r'depends on axioms:\s*\[([^]]*)\]',text)
free=text.count('does not depend on any axioms')
generic=Path('audit/ResidueAtlasIntersectionFactoredAudit.lean').read_text().count('#print axioms')
native=sum(p.read_text().count('#print axioms') for p in Path('receipts/residue_atlas_intersection_factored').glob('*.lean'))
assert len(sets)+free==generic+native, 'missing proof records'
for values in sets:
    assert {v.strip() for v in values.split(',') if v.strip()} <= {'propext','Classical.choice','Quot.sound'}
assert 'sorryAx' not in text and 'Lean.ofReduceBool' not in text
receipt={'lean_version':'4.20.0','generic_declarations_audited':generic,'native_declarations_audited':native,
 'total_declarations_audited':generic+native,'native_worked_intersections':6,
 'axioms':'standard axioms only or axiom-free; no sorryAx or Lean.ofReduceBool',
 'focused_python_tests':11,'independent_census_cases':120,
 'scope':'typed nested and coprime predicate covers, exact counts and source-bound concrete Lean replays',
 'generic_python_interpreter_refinement':False,'global_height_bound':False}
Path('receipts/residue_atlas_intersection_factored/validation.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
PY
