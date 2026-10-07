"""Regenerate exact late-bias fold packets, without a numerical thermal scan."""
import json
from pathlib import Path
from perfectpower.dimensionful_walls import WallModel
from perfectpower.wall_fluctuations import HiggsWall
from perfectpower.wall_bifurcations import late_bias_fold_census

ROOT=Path(__file__).resolve().parents[1]

def main():
    cases={
        'published_late_bias_benchmark':(WallModel(30000,.1,.025000033333333335,300000,3000,2.584366229533845e-13,3000),HiggsWall()),
        'physical_interior_fold':(WallModel(1,3,1,10,0,3,1),HiggsWall(portal=0,v_GeV=10)),
        'unstable_boundary_endpoint_fold':(WallModel(1,1,1,10,0,4,.5),HiggsWall(portal=1,lam=1,v_GeV=2))}
    result={name:late_bias_fold_census(m,h) for name,(m,h) in cases.items()}
    result['conclusion']='The supplied benchmark has no stationary cubic fold anywhere in its active late-bias window. Its pressure-driven network annihilation is a separate dynamical assumption; spinodal loss is not its false-vacuum removal mechanism.'
    result['execution_verified']=False
    result['verification_scope']='Exact Python rational arithmetic and Sturm root/sign calculations; no Lean execution or cosmological dynamics inferred.'
    path=ROOT/'receipts/flavor_cosmology/wall_bifurcations.json'
    path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(path)

if __name__=='__main__':main()
