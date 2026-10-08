"""Independent exact finite-coordinate checks; SymPy is a development oracle."""
import json
from itertools import combinations,product
from math import gcd,prod,isqrt
from pathlib import Path
from sympy import Matrix,ZZ
from sympy.matrices.normalforms import smith_normal_form
from perfectpower.elliptic_torsion_index import _lattice
from perfectpower.pell7_complete import solutions,orbit,address


def run():
    cases=relations_checked=0
    for r,orders in ((0,[2]),(0,[5]),(0,[7]),(0,[2,2]),(1,[2]),(1,[5]),(1,[7])):
        d=r+len(orders)
        for k in range(1,9):
            rows=([[k,1],[k+1,0],[2*k+1,1]] if r else
                  [[(k+j*(i+1))%n for i,n in enumerate(orders)] for j in range(3)])
            if r==0 and len(orders)==2 and k%2==0:rows[0]=[1,0];rows[1]=[0,1]
            L=_lattice(rows,r,orders);A=Matrix(L['smith']['matrix'])
            minors=[abs(int(A[:,list(cols)].det())) for cols in combinations(range(A.cols),d)]
            g=0
            for x in minors:g=gcd(g,x)
            assert g==L['ambient_lattice_index']
            R=Matrix(L['relation_basis']).T
            D=smith_normal_form(R,domain=ZZ)
            factors=[abs(int(D[i,i])) for i in range(min(D.shape)) if abs(D[i,i])>1]
            assert factors==L['group_invariant_factors']
            for cs in product(range(-2,3),repeat=len(rows)):
                values=[sum(c*row[i] for c,row in zip(cs,rows)) for i in range(d)]
                actual=all(x==0 for x in values[:r]) and all(values[r+j]%n==0 for j,n in enumerate(orders))
                try:
                    coord,params=R.gauss_jordan_solve(Matrix(cs))
                    represented=not params.rows and all(x.q==1 for x in coord)
                except ValueError:represented=False
                assert represented==actual
                relations_checked+=1
            cases+=1
    expected=[]
    for x in range(100001):
        if (x*x+7)%2:continue
        y=isqrt((x*x+7)//2)
        if x*x+7==2*y*y:expected.extend((sx*x,sy*y) for sx,sy in product((-1,1),repeat=2))
    assert solutions(100000)==sorted(expected)
    addresses=0
    for i,n in product(range(2),(0,1,2,10,100,1000)):
        x,y=orbit(i,n)
        for sx,sy in product((-1,1),repeat=2):
            a=address(sx*x,sy*y);assert (a['seed_index'],a['n'])==(i,n);addresses+=1
    return dict(coordinate_models=cases,relation_memberships=relations_checked,
                pell_census_bound=100000,pell_signed_solutions=len(expected),
                pell_large_signed_addresses=addresses,all_exact=True,execution_verified=False)

if __name__=='__main__':
    out=run();p=Path(__file__).resolve().parents[1]/'receipts/torsion_index_pell7/crosscheck.json'
    p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
