"""Independent signed source censuses, affine identities and Leibniz determinants."""
import json
from fractions import Fraction
from itertools import permutations
from pathlib import Path
import random
from perfectpower.integer_valued_power_charts import power_charts,chart_scan,branch_power_charts,branch_power_scan
from perfectpower.branching_residue_patch import branching_patch,patch_scan
from perfectpower.unordered_weighted_determinant import weighted_determinant
from perfectpower.bounded_residue_patch import evaluate


def ev(cs,x):return sum(Fraction(c)*x**i for i,c in enumerate(cs))


def leibniz(A):
    n=len(A);out=0
    for sigma in permutations(range(n)):
        inversions=sum(sigma[i]>sigma[j] for i in range(n) for j in range(i+1,n))
        value=(-1)**inversions
        for i,j in enumerate(sigma):value*=A[i][j]
        out+=value
    return out


def main():
    rng=random.Random(20261008);boxes=source_checks=branch_checks=det_checks=0
    for _ in range(36):
        L=rng.choice([1,2,3,4,6]);cs=[str(Fraction(rng.randrange(-4,5),L)) for _ in range(rng.randrange(1,5))]
        d=rng.choice([2,3,4]);k=rng.randrange(-2,3);b=[[-8,9],[-7,8]]
        packet=power_charts(cs,d,b,offset=k,factors=[[2,2],[3,1]],explicit_limit=1)
        expected=[[x,y] for x in range(-8,10) for y in range(-7,9)
                  if ev(cs,x).denominator==1 and ev(cs,x)+k==y**d]
        assert chart_scan(packet)['points']==expected
        branched=branch_power_charts(packet,2,2)
        assert branch_power_scan(branched)['points']==expected
        assert branched['candidate_count']<=chart_scan(packet)['candidate_count']
        boxes+=1;source_checks+=18*16
    for p in [2,3,5,7]:
        for terms in [[[1,1,1]],[[1,0,2],[-1,3,0]],[[1,2,0],[1,0,2],[-2,0,0]],
                      [[1,1,0],[-1,0,2]],[[p,0,0]]]:
            patch=branching_patch(terms,[[-9,10],[-8,11]],p,2)
            expected=[[x,y] for x in range(-9,11) for y in range(-8,12) if evaluate(terms,x,y)==0]
            assert patch_scan(patch)['points']==expected
            branch_checks+=400
    for n in range(1,5):
        for h in range(1,7):
            for _ in range(4):
                C=[[rng.randrange(-5,6) for _ in range(h)] for _ in range(n)]
                V=[[rng.randrange(-5,6) for _ in range(n)] for _ in range(h)]
                packet=weighted_determinant(C,V,[rng.randrange(5) for _ in range(h)],rng.choice([-3,2,5]))
                assert packet['unordered_sum']==leibniz(packet['matrix'])
                det_checks+=1
    result={'rational_power_boxes':boxes,'rational_source_points_checked':source_checks,
            'branch_source_points_checked':branch_checks,'independent_leibniz_determinants':det_checks,
            'all_equal':True}
    out=Path(__file__).resolve().parents[1]/'receipts'/'arithmetic_chart_pipeline'
    out.mkdir(parents=True,exist_ok=True)
    (out/'crosscheck.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
