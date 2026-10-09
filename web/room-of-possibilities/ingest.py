"""Export real PerfectPower populations and pin the source used by the exhibit."""
import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('--repo', type=Path, required=True)
args = parser.parse_args()
repo = args.repo.resolve()
sys.path.insert(0, str(repo / 'python'))
from perfectpower.populations import ExactPopulation
from perfectpower.population_algebra import PopulationComparison

T = 10**40
spec = {'kind': 'curve', 'left': [0, 0, 2], 'right': [0, 0, 0, 3],
        'predicate': {'expr': 'y-' + str(6*T*T), 'relation': '<='}}
pop = ExactPopulation(spec)
small = ExactPopulation({**spec, 'predicate': {'expr': 'y-384', 'relation': '<='}})
records = [pop.select(r) for r in (0, 1, 8, T-1, T, T+1, T+8, 2*T)]
for row in records:
    x, y = row['values']['x'], row['values']['y']
    assert 2*x*x == 3*y*y*y
    assert pop.rank(row) == row['rank'] == pop.locate(x=x, y=y)
assert pop.count() == 2*T + 1
assert small.count() == 17
paths = ['README.md', 'docs/POPULATION_MONOGRAPH.md',
         'python/perfectpower/populations.py', 'python/perfectpower/query_space.py',
         'python/perfectpower/coefficient_charts.py', 'python/perfectpower/population_algebra.py',
         'PerfectPower/PopulationPartitions.lean']
payload = {'title': 'PerfectPower / The room of possibilities',
    'source_repository': 'https://github.com/towre676-cloud/perfectpower',
    'source_commit': subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip(),
    'source_revision_scope': 'source_commit records the checkout base; source_files pin the executed bytes, including any uncommitted changes',
    'source_worktree_dirty': bool(subprocess.check_output(['git','-C',str(repo),'status','--porcelain'],text=True).strip()),
    'source_files': {p: hashlib.sha256((repo/p).read_bytes()).hexdigest() for p in paths},
    'specification': spec, 'cardinality': pop.count(), 'population_id': pop.population_id,
    'rank_examples': records, 'small_population': small.page(0, 17),
    'scope': 'Exact Python population export from repository; not a new Lean proof. Machine workshop is a fictional bounded integer model.'}
comparisons=[]
for ceiling, cutoff, name in ((T,10,'Enormous family'),(8,3,'Seventeen pictured points')):
    comparison_spec={'universe':{**spec,'predicate':{'expr':'y-'+str(6*ceiling**2),'relation':'<='}},
                     'left':{'expr':'x','relation':'>='},
                     'right':{'expr':'y-'+str(6*cutoff**2),'relation':'<='}}
    comparison=PopulationComparison(comparison_spec)
    counts=comparison.summary()['counts']
    assert counts['universe']==2*ceiling+1
    assert counts['both']==cutoff+1 and counts['left_only']==ceiling-cutoff
    assert counts['right_only']==cutoff and counts['neither']==ceiling-cutoff
    examples=[]
    for part in ('both','left_only','right_only','neither'):
        for rank in sorted({0,comparison.count(part)-1}):
            if rank<0:continue
            row=comparison.select(part,rank)
            values=row['record']['values'];x,y=values['x'],values['y']
            assert 2*x*x==3*y**3
            recovered=comparison.transport(part,rank,'universe')
            assert recovered['object_id']==row['object_id']
            assert comparison.transport('universe',row['addresses']['universe'],part)['object_id']==row['object_id']
            examples.append(row)
    protocol=json.dumps({'op':'register','kind':'population_comparison',
        'name':'room-comparison-'+str(ceiling),'specification':comparison_spec},separators=(',',':'))
    comparisons.append(dict(name=name,ceiling=ceiling,cutoff=cutoff,summary=comparison.summary(),
        examples=examples,registration_request=protocol,object_name='room-comparison-'+str(ceiling)))
payload['comparisons']=comparisons
payload['comparison_scope']='Exported exact backend results. Four-way partition, original point identity and rank transport replayed in Python. Browser displays decimal strings.'
def stringify_big(v):
    if isinstance(v, bool): return v
    if isinstance(v, int): return str(v)
    if isinstance(v, list): return [stringify_big(x) for x in v]
    if isinstance(v, dict): return {k: stringify_big(x) for k, x in v.items()}
    return v
out = Path(__file__).resolve().parent
(out/'ingested-population.json').write_text(json.dumps(stringify_big(payload), indent=2)+'\n')
print(json.dumps({'count': str(pop.count()), 'small_count': small.count(), 'examples': len(records), 'commit': payload['source_commit']}))
