"""Independent exact lattice census and division-coordinate crosschecks."""
import json,random
from itertools import product
from pathlib import Path
import sympy as S
from sympy.matrices.normalforms import smith_normal_form
from sympy.polys.domains import ZZ
from perfectpower.elliptic_subgroups import row_basis
from perfectpower.elliptic_lattice_presentation import lattice_data
from perfectpower.elliptic_prime_division import odd_division_polynomials,local_root_obstruction
from perfectpower.elliptic_prime_division_verifier import silverman_division
from perfectpower.elliptic_arithmetic import EllipticCurve
from perfectpower import polyalg as P


def main():
    rng=random.Random(20261008);cases=coordinates=0
    for p in (5,7):
        for r in range(5):
            for _ in range(8):
                R=row_basis([[rng.randrange(p) for j in range(r)] for i in range(rng.randrange(r+1))],p,r)
                a=lattice_data({'prime':p,'source_points':[None]*r,'relation_basis':R})
                H=S.Matrix(a['row_hermite']) if r else S.zeros(0,0)
                U=S.Matrix(a['smith_left']) if r else S.zeros(0,0)
                V=S.Matrix(a['smith_right']) if r else S.zeros(0,0)
                assert H.det()==a['coefficient_lattice_index'] and U.det() in (-1,1) and V.det() in (-1,1)
                assert U*H*V==S.diag(*a['smith_diagonal'])
                snf=smith_normal_form(H,domain=ZZ)
                assert [abs(snf[i,i]) for i in range(r)]==a['smith_diagonal']
                span={tuple(sum(c*row[j] for c,row in zip(cs,R))%p for j in range(r)) for cs in product(range(p),repeat=len(R))}
                inv=H.inv()
                for v in product(range(p),repeat=r):
                    row=S.Matrix(1,r,list(v));coefficients=row*inv
                    assert all(x.q==1 for x in coefficients)==(v in span)
                    coordinates+=1
                cases+=1
    polynomial_cases=0
    examples=[(EllipticCurve([0,0,1,-1,0]),[[0,0]]),
              (EllipticCurve([-4,1]),[[0,1],[2,1]]),
              (EllipticCurve([0,-2]),[[3,5]]),
              (EllipticCurve([0,-1,1,0,0]),[[0,0]]),
              (EllipticCurve([1,-1,1,-3,3]),[[1,0]])]
    for E,points in examples:
        for prime in (5,7):
            psi,phi=odd_division_polynomials(E,prime);sp,sphi=silverman_division(E,prime)
            assert psi==sp
            for z in points:
                A=E.checked(z)
                for n in (-2,-1,1,2):
                    h=E.mul(A,n);target=E.mul(h,prime)
                    if h is None or target is None:continue
                    denom=P.evaluate(psi,h[0])**2
                    assert denom and P.evaluate(phi,h[0])/denom-E.cubic[2]/3==target[0]
                    f=P.add(sphi,P.scale(P.power(sp,2),-target[0]))
                    assert local_root_obstruction(E,f) is None
                    polynomial_cases+=1
    receipt={'seed':20261008,'normal_form_cases':cases,'all_residue_coordinates':coordinates,
             'division_coordinate_cases':polynomial_cases,'sympy_smith_and_inverse_lattice_agree':True,
             'original_vs_short_model_polynomials_agree':True,'no_local_obstruction_on_known_divisible_points':True,
             'scope':'exact finite lattice census and rational point multiplication identities; no full Mordell-Weil basis assertion'}
    out=Path(__file__).resolve().parents[1]/'receipts'/'elliptic_prime_subgroups';out.mkdir(exist_ok=True)
    (out/'crosscheck.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))

if __name__=='__main__':main()
