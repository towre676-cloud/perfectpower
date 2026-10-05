"""Deterministic arithmetic showcase, not a new experimental flavor fit."""
import json
from pathlib import Path
from perfectpower.weyl_scaffold import search, orbit_size, symmetry_defect

ROOT=Path(__file__).resolve().parents[1]
alphabet=['-1/3','-1/5','-1/12','0','1/12','1/5','1/3']
truth=['1/12','-1/3','0','0','1/5']
# Rational fixture with five independently probed axes: tests software recovery.
rows=[[int(i==j) for j in range(5)] for i in range(5)]
recovery=search(alphabet,rows,truth)
# Real scaffold shape: only two running columns; three constants.
# These are designed rational log samples, NOT actual RG evolution.
scale_rows=[[-5,-2,1,2,7],[-4,-3,1,2,7],[-3,-1,1,2,7]]
from fractions import Fraction as F
target=[sum(F(a)*b for a,b in zip(truth,row)) for row in scale_rows]
ambiguous=search(alphabet,scale_rows,target)
result={'kind':'synthetic exact arithmetic demonstration; no physical evidence claim',
 'recovery':recovery,'fixed_constant_scaffold':ambiguous,
 'orbit_examples':{'distinct_full_support':orbit_size([1,2,3,4,5]),
                   'equal_full_support':orbit_size([1]*5),
                   'original_sparse_shape':orbit_size(truth)},
 'same_orbit_different_predictions':search([0,1],[[1,2]],[1]),
 'every_tied_optimum':search([-1,0,1],[[1,1]],[0]),
 'spherical_bowl_with_target':symmetry_defect([[1,0],[0,1]],[1,0]),
 'five_axis_scale_rank_bound':3,'centered_scale_rank_bound':2}
path=ROOT/'receipts/b5_revision/showcase.json'
path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps(result,indent=2))
