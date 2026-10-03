"""Generate k=22 slab checks as separate modules; generation is not proof.
Run scripts/check_k22_split.py afterward to check each module sequentially.
"""
import sys,json,re
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
import argparse
parser=argparse.ArgumentParser(description='Generate separate kernel-checkable slab modules for k=22.')
parser.add_argument('--chunk',type=int,default=200)
parser.add_argument('--integer',action='store_true',help='clear fixed denominators before kernel evaluation')
parser.add_argument('--slices',type=int,default=2000,help='integer-mode slices per module')
args=parser.parse_args()
if args.slices < 1: parser.error('slices must be positive')
if args.chunk < 1: parser.error('chunk must be positive')
import os
os.chdir(Path(__file__).resolve().parents[1])
import rank_one_sources as s
r=s.find(22,(-1,-6,-3,-4),9,-14,2,(388537,-357959,99671))
root=Path('PerfectPower/Generated/RankOneSources/K22Parts');root.mkdir(parents=True,exist_ok=True)
for old in root.glob('Chunk*.lean'): old.unlink()
per=max(1,r['slab_elements']//(2*r['_c']['C']+1))
b=s.lean_block(r,0,chunk=args.slices*per if args.integer else args.chunk)
start=b.index('set_option maxRecDepth');end=b.index('theorem slab_0')
base=b[:start]
ns='namespace PerfectPower.Generated.RankOneSources.K22\nopen PerfectPower.UnitBox PerfectPower.UnitPremises PerfectPower.RankOne\n'
(root/'Defs.lean').write_text('import PerfectPower.RankOne\nset_option Elab.async false\n'+ns+base+'\nend PerfectPower.Generated.RankOneSources.K22\n')
if args.integer:
 from math import lcm
 c=r['_c']
 xs=[c['lo'],c['hi'],c['J'],c['_t2lo'],c['_T']**2]
 denominator=lcm(*(x.denominator for x in xs))
 values=[int(x*denominator) for x in xs]
 (root/'IntegerDefs.lean').write_text('import PerfectPower.Generated.RankOneSources.K22Parts.Defs\nimport PerfectPower.RankOneIntegerSlab\n'+ns+'open PerfectPower.RankOneIntegerSlab\ndef scaled : Scaled := ⟨'+','.join(map(str,[denominator]+values))+'⟩\ntheorem scaled_matches : Matches c0 scaled := by unfold Matches; decide +kernel\nend PerfectPower.Generated.RankOneSources.K22\n')
chunks=re.findall(r'set_option maxRecDepth.*?(?=set_option maxRecDepth|\Z)',b[start:end],re.S)
imports=[]
for i,t in enumerate(chunks):
 if args.integer:
  t=t.replace('by decide +kernel', 'by\n  rw [show slabSliceB 9 (-14) η0 c0 = PerfectPower.RankOneIntegerSlab.slice 9 (-14) η0 c0 scaled from\n    funext (fun l => PerfectPower.RankOneIntegerSlab.slice_eq scaled_matches 9 (-14) η0 l)]\n  decide +kernel')
 name=f'PerfectPower.Generated.RankOneSources.K22Parts.Chunk{i}'
 dependency='IntegerDefs' if args.integer else 'Defs'
 (root/f'Chunk{i}.lean').write_text(f'import PerfectPower.Generated.RankOneSources.K22Parts.{dependency}\nset_option Elab.async false\n'+ns+t+'\nend PerfectPower.Generated.RankOneSources.K22\n')
 imports.append(name)
Path('PerfectPower/Generated/RankOneSources/K22.lean').write_text('\n'.join('import '+x for x in imports)+'\nset_option Elab.async false\n'+ns+b[end:]+'\nend PerfectPower.Generated.RankOneSources.K22\n')
Path('receipts/k22_split.json').write_text(json.dumps({k:v for k,v in r.items() if k!='_c'}|{'chunk_modules':len(chunks),'integer_endpoints':args.integer,'status':'generated; compilation pending'},indent=2)+'\n')
print('GENERATED',len(chunks),r['slab_elements'],flush=True)
