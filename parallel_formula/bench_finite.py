"""Compare original and reduced proof fixtures; these are not industrial workloads."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import time
import z3
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'python'))
from perfectpower.finite_formula import emit_finite_query
rows=[]
for source in sorted(p for p in (ROOT/'parallel_formula/finite').glob('*.smt2') if not p.name.endswith('.reduced.smt2')):
    text=source.read_bytes().decode('utf-8');out=emit_finite_query(text)
    row={'source':str(source.relative_to(ROOT)),'sha256':out.source_sha256,'lifted_points':out.points}
    for label,script in [('original',text),('reduced',out.smt)]:
        solver=z3.Solver();solver.set(timeout=2000)
        solver.add(z3.parse_smt2_string(script));start=time.perf_counter();answer=solver.check()
        row[label]={'answer':str(answer),'seconds':time.perf_counter()-start,
                    'model':str(solver.model()) if answer==z3.sat else None}
    rows.append(row)
report={'solver':z3.get_version_string(),'timeout_ms':2000,'scope':'authored proof fixtures; no independent industrial speedup claim','cases':rows}
(ROOT/'parallel_formula/finite_results.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
