"""Reproduce a comparison specimen and bounded independent arithmetic checks."""
from hashlib import sha256
import json
from pathlib import Path

from perfectpower.population_algebra import PopulationComparison

root=Path(__file__).resolve().parents[1]
T=10**40
spec=dict(universe=dict(kind='curve',left=[0,0,2],right=[0,0,0,3],
          predicate={'expr':'y-'+str(6*T*T),'relation':'<='}),
          left={'expr':'x','relation':'>='},right={'expr':'y-600','relation':'<='})
comparison=PopulationComparison(spec)
expected=dict(universe=2*T+1,left=T+1,right=21,both=11,left_only=T-10,
              right_only=10,neither=T-10,union=T+11,symmetric_difference=T)
assert comparison.summary()['counts']==expected
examples=[]
for part in ('both','left_only','right_only','neither'):
    for rank in sorted({0,comparison.count(part)-1}):
        row=comparison.select(part,rank);x,y=row['record']['values']['x'],row['record']['values']['y']
        assert 2*x*x==3*y**3
        assert comparison.transport(part,rank,'universe')['object_id']==row['object_id']
        assert comparison.transport('universe',row['addresses']['universe'],part)['object_id']==row['object_id']
        examples.append(row)
paths=['python/perfectpower/population_algebra.py','python/perfectpower/populations.py',
       'PerfectPower/PopulationPartitions.lean','audit/PopulationPartitions.lean']
receipt=dict(schema='pp-population-algebra-receipt/1',base_commit='fa5186cf4a51d3a9660b610a61e46f06dea4fb8d',
             source_files={p:sha256((root/p).read_bytes()).hexdigest() for p in paths},
             summary=comparison.summary(),examples=examples,checks='Closed-form counts, equation evaluation and two-way original-object transport.',
             trust='Exact Python replay. Lean generic laws are audited separately; compiler execution and global curve solving are not newly verified.')
destination=root/'receipts/population_algebra';destination.mkdir(parents=True,exist_ok=True)
(destination/'huge-curve-spec.json').write_text(json.dumps(spec,indent=2)+'\n')
(destination/'comparison.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(dict(result='passed',population_count=str(expected['universe']),examples=len(examples))))
