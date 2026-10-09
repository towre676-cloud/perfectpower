"""Bind actual Lean descent proofs to the source atlas and the census comparison."""
import argparse
import hashlib
import json
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parents[1]


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('log',type=Path);args=parser.parse_args()
    rows=json.loads((ROOT/'data/mordell_descent_sources.json').read_text())['rows'];log=args.log.read_text()
    if 'error:' in log or 'sorry' in log or 'ofReduceBool' in log:raise ValueError('descent atlas compilation failed')
    names=[]
    for name,axioms in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log):
        if set(a.strip() for a in axioms.split(',') if a.strip())-{'propext','Classical.choice','Quot.sound'}:raise ValueError('unsupported axiom')
        names.append(name)
    names+=re.findall(r"'([^']+)' does not depend on any axioms",log)
    expected=['PerfectPower.MordellDescentAtlas.no_points_'+('m'+str(-r['k']) if r['k']<0 else 'p'+str(r['k'])) for r in rows]
    if sorted(names)!=sorted(expected):raise ValueError('descent declaration audit mismatch')
    census={r['k']:r for r in map(json.loads,(ROOT/'data/mordell_census.jsonl').read_text().splitlines())}
    if any(census[r['k']]['x_coordinates'] for r in rows):raise ValueError('proved empty curve contradicts stored census')
    completion=json.loads((ROOT/'receipts/mordell_completion/summary.json').read_text())
    hard={r['k'] for r in completion['rows']};intersection=sorted(hard&{r['k'] for r in rows})
    sources=['PerfectPower/MordellDescentCore.lean','PerfectPower/MordellDescentMask.lean','PerfectPower/MordellDescentAtlas.lean','data/mordell_descent_sources.json']+[p.relative_to(ROOT).as_posix() for p in sorted((ROOT/'PerfectPower/MordellDescentAtlas').glob('Block*.lean'))]
    out=dict(schema='pp-mordell-descent-atlas/1',proof_status='kernel_checked',global_empty_source_curves=len(rows),
             audited_declarations=names,hard_completion_curves=len(hard),hard_completion_intersection=intersection,
             source_sha256={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sources},
             audit_sha256=hashlib.sha256(log.encode()).hexdigest(),execution_verified=False,
             scope='global integral emptiness for these source offsets; does not establish rational rank or saturation for the 457 hard census curves')
    (ROOT/'receipts/mordell_descent_atlas.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:out[k] for k in ['global_empty_source_curves','hard_completion_curves','hard_completion_intersection']}))


if __name__=='__main__':main()
