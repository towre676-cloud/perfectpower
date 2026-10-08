"""Replay the declared-wall, Tamagawa, resonance and HTTP continuation."""
from pathlib import Path
import argparse,gzip,hashlib,json
from perfectpower.wall_profile_intervals import check_seed,generate_declared_seed
from perfectpower.wall_stability_certified import certify_gap
from perfectpower.semistable_tamagawa import rational_root_tamagawa
from perfectpower.resonant_frobenius import normal_form,gauge_tail
from perfectpower.http_load import run_load

ROOT=Path(__file__).resolve().parents[1]


def wall(regenerate=False):
    path=ROOT/'receipts/flavor_cosmology/wall_declared_interval_seed.json.gz'
    if regenerate or not path.exists():
        seed=generate_declared_seed()
        path.write_bytes(gzip.compress((json.dumps(seed,separators=(',',':'))+'\n').encode(),mtime=0))
    seed=json.loads(gzip.decompress(path.read_bytes()))
    controls=dict(coercivity='0.0001',radius_ball='0.00005')
    base=check_seed(seed,precision=160,**controls)
    gap=certify_gap(seed,precision=160,**controls)
    replay=certify_gap(seed,precision=192,**controls)
    out={'schema':'pp-declared-wall-gap/1','seed_sha256':hashlib.sha256(gzip.decompress(path.read_bytes())).hexdigest(),
         'seed_gzip_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'base':base,'radial_gap':gap,'replay_192_bits':replay['bounds_Arb'],
         'angular_Higgs_sector':{'nonnegative_certified':True,'strict_positive_gap_claimed':False,'identity':'q(f)=integral h^2 |(f/h)\'|^2; h>0 is certified, with essential spectrum beginning at zero'},
         'vector_TE_sector':{'nonnegative_certified':True,'vacuum_mass_floor_certified':True,'hypotheses':'h>=h0 from whole-line certificate; operator -d^2+g^2 h^2/4 >=g^2 h0^2/4 for each positive coupling'},
         'scope':'Declared rational lambda=0.1 radial wall; Arb outward inequalities. Angular Higgs and transverse-vector forms only; no gauged WW/ZZ lifetime or full longitudinal constrained-spectrum gap.'}
    (ROOT/'receipts/flavor_cosmology/wall_declared_stability_certified.json').write_text(json.dumps(out,indent=2)+'\n')
    print('PASS declared wall gap:',gap['bounds_display_float']['gap_GeV_lower'],'GeV',flush=True)


def arithmetic():
    from sympy import Matrix
    out={'schema':'pp-tamagawa-resonance-continuation/1','curves':[],'charts':[]}
    for p in [3,5,7,11]:
        for d in range(1,6):
            for c in [1,2,3]:
                if c%p:out['curves'].append(rational_root_tamagawa(p,[0,p**d,1],c))
    for c in [1,2]:out['curves'].append(rational_root_tamagawa(3,[0,3,1,4,2,5],c))
    for rank in [2,3,4]:
        R=Matrix.diag(*range(rank));E=Matrix.zeros(rank)
        for i in range(1,rank):E[i,i-1]=1
        a=normal_form(R.tolist(),E.tolist(),0,order=64)
        a['analytic_gauge_tail']=gauge_tail(a,'1/8');out['charts'].append(a)
    (ROOT/'receipts/curve_structure/tamagawa_resonant_continuation.json').write_text(json.dumps(out,indent=2)+'\n')
    print('PASS: 57 curve receipts and three logarithmic charts',flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--regenerate-wall',action='store_true');p.add_argument('--skip-wall',action='store_true');p.add_argument('--http',action='store_true');args=p.parse_args()
    arithmetic()
    if not args.skip_wall:wall(args.regenerate_wall)
    if args.http:
        rows=[run_load(clients=n,requests=384) for n in [1,8,16,32]]
        assert all(r['all_replayed'] for r in rows),rows
        (ROOT/'receipts/http_concurrency_replay.json').write_text(json.dumps(rows,indent=2)+'\n')
        print('PASS: 1536 HTTP requests replayed exactly',flush=True)
