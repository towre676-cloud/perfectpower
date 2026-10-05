"""Exact residual-overlap spectrum in the real cyclotomic field Q(2cos(6deg))."""
from pathlib import Path
from fractions import Fraction
import json
import sympy as sp
from flint import fmpq_poly, fmpq_mat
from develop_valentiner_frames import generators, group_closure, residual_frames, order, mul, IDENTITY

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'receipts/m22_interactions'
Z=fmpq_poly([0,1])
MOD=fmpq_poly([1,0,1,0,0,0,-1,0,-1,0,-1,0,0,0,1,0,1])
POW=[Z**i % MOD for i in range(60)]
S=(1+2*(POW[12]+POW[48])) % MOD
OMEGA=POW[20]


def field(g):
    den,entries=g
    return [((a+b*S+(c+d*S)*OMEGA)/den) % MOD for a,b,c,d in entries]


def projector(g,n,k,elements,lookup):
    p=IDENTITY; acc=[fmpq_poly([]) for _ in range(9)]
    for a in range(n):
        phase=POW[(-k*a*(60//n))%60]
        f=field(p)
        acc=[(v+phase*w) % MOD for v,w in zip(acc,f)]
        p=mul(p,g)
    return [x/n for x in acc]


def trace(p):
    return p[0]+p[4]+p[8]


def overlaps(p,q):
    result=fmpq_poly([])
    for i in range(3):
        for j in range(3):
            result+=p[3*i+j]*q[3*j+i]
    return result % MOD


def exact_frames(frames,elements,lookup):
    allframes=[]
    keys=set()
    for frame in frames:
        source=frame['source']
        if source['type']=='cyclic':
            g=elements[source['element']];n=order(g)
            if n in (12,15):
                g=mul(mul(g,g),g);n//=3
            assert n in (3,4,5)
            ps=[projector(g,n,k,elements,lookup) for k in range(n)]
            assert all(trace(p) in (0,1) for p in ps)
            ps=[p for p in ps if trace(p)==1]
        else:
            i,j,k=source['elements'];gi,gj,gk=map(field,(elements[i],elements[j],elements[k]))
            identity=field(IDENTITY)
            ps=[[ (a+si*b+sj*c+si*sj*d)/4 for a,b,c,d in zip(identity,gi,gj,gk)] for si in (-1,1) for sj in (-1,1)]
            assert all(trace(p) in (0,1) for p in ps)
            ps=[p for p in ps if trace(p)==1]
        assert len(ps)==3
        key=tuple(sorted(tuple(str(x) for x in p) for p in ps))
        assert key not in keys
        keys.add(key)
        assert all(overlaps(p,q)==int(i==j) for i,p in enumerate(ps) for j,q in enumerate(ps))
        allframes.append(ps)
    covered=0
    for g in elements:
        n=order(g)
        if n not in (3,4,5):
            continue
        ps=[projector(g,n,k,elements,lookup) for k in range(n)]
        if any(trace(p) not in (0,1) for p in ps):
            # Scalar central elements have a rank-three eigenspace.
            assert n==3 and any(trace(p)==3 for p in ps)
            continue
        ps=[p for p in ps if trace(p)==1]
        assert len(ps)==3
        key=tuple(sorted(tuple(str(x) for x in p) for p in ps))
        assert key in keys
        covered+=1
    assert covered==474
    print('all 474 noncentral order 3/4/5 elements covered exactly',flush=True)
    return allframes


def interval_product(a,b):
    values=[x*y for x in a for y in b]
    return min(values),max(values)


def interval_horner(coefficients, interval):
    v=(Fraction(0),Fraction(0))
    for c in reversed(coefficients):
        a,b=interval_product(v,interval)
        v=a+c,b+c
    return v


def certify(values):
    # The eight real powers span the conjugation-fixed subfield.
    realbasis=[fmpq_poly([1])]+[POW[i]+POW[(-i)%60] for i in range(1,8)]
    columns=fmpq_mat([[b[i] for b in realbasis] for i in range(16)])
    leftinverse=(columns.transpose()*columns).inv()*columns.transpose()
    t=sp.Symbol('t')
    polys=[sp.Poly(1,t),sp.Poly(t,t)]
    for i in range(2,8):
        polys.append(sp.Poly(t*polys[-1].as_expr()-polys[-2].as_expr(),t))
    # For i=2 recurrence uses q0=2, unlike the first basis vector 1.
    polys=[sp.Poly(1,t),sp.Poly(t,t),sp.Poly(t*t-2,t)]
    for i in range(3,8):
        polys.append(sp.Poly(t*polys[-1].as_expr()-polys[-2].as_expr(),t))
    # Discover rather than assume the real generator's exact minimal polynomial.
    tf=POW[1]+POW[59]
    powers=[fmpq_poly([1])]
    for _ in range(8):
        powers.append(powers[-1]*tf % MOD)
    mat=sp.Matrix([[sp.Rational(str(p[i])) for p in powers] for i in range(16)])
    kernel=mat.nullspace()
    assert len(kernel)==1
    minpoly=sp.Poly(sum(kernel[0][i]*t**i for i in range(9)),t).monic()
    intervals=minpoly.intervals(eps=sp.Rational(1,10**40))
    bounds=intervals[-1][0]
    tinterval=tuple(Fraction(int(x.p),int(x.q)) for x in bounds)
    records=[]
    for v in values:
        # Conjugation is evaluated as z -> z^-1.
        conjugate=sum((v[i]*POW[(-i)%60] for i in range(16)),fmpq_poly([])) % MOD
        assert conjugate==v
        coefficients=leftinverse*fmpq_mat([[v[i]] for i in range(16)])
        assert columns*coefficients==fmpq_mat([[v[i]] for i in range(16)])
        poly=sp.Poly(sum(sp.Rational(str(coefficients[i,0]))*polys[i].as_expr() for i in range(8)),t)
        coeff=[Fraction(int(poly.nth(i).p),int(poly.nth(i).q)) for i in range(8)]
        low,high=interval_horner(coeff,tinterval)
        records.append({'polynomial':str(poly.as_expr()),'coefficients_ascending':[str(c) for c in coeff],
            'interval':[str(low),str(high)],'approximate':float((low+high)/2)})
    records.sort(key=lambda r:r['approximate'])
    for a,b in zip(records,records[1:]):
        assert Fraction(a['interval'][1])<Fraction(b['interval'][0])
    assert records[0]['approximate']==0 and records[-1]['approximate']==1
    return {'real_generator':'t = 2 cos(pi/30), the largest real root', 'minimal_polynomial':str(minpoly.as_expr()),
        'generator_isolating_interval':[str(x) for x in tinterval], 'squared_overlap_values':records,
        'minimum_positive_squared_overlap':records[1], 'maximum_subunit_squared_overlap':records[-2],
        'all_values_exactly_real':True,'all_intervals_strictly_ordered':True}


def main():
    elements,lookup,words=group_closure(generators())
    frames,_,_,_,_=residual_frames(elements,lookup,words)
    exact=exact_frames(frames,elements,lookup)
    values={}
    comparisons=0
    for i,a in enumerate(exact):
        for j in range(i,len(exact)):
            for m,p in enumerate(a):
                for n,q in enumerate(exact[j]):
                    v=overlaps(p,q)
                    key=tuple(str(v[k]) for k in range(16))
                    values.setdefault(key,(v,[i,j,m,n]));comparisons+=1
        if i%30==0:
            print('exact frames processed',i,'distinct overlap values',len(values),flush=True)
    result=certify([v for v,_ in values.values()])
    involutions=[g for g in elements if order(g)==2]
    identity=field(IDENTITY)
    lines=[[(a+b)/2 for a,b in zip(identity,field(g))] for g in involutions]
    expected=[fmpq_poly([0]),(3-S)/8,fmpq_poly([1])/4,fmpq_poly([1])/2,(3+S)/8,fmpq_poly([1])]
    fixed={}
    for p in lines:
        assert trace(p)==1
        for q in lines:
            v=overlaps(p,q)
            assert v in expected
            fixed.setdefault(str(v),v)
    assert len(fixed)==6
    result.update({'complete_frame_count':len(exact),'unordered_frame_pairs_with_repetition':len(exact)*(len(exact)+1)//2,
        'exact_entry_comparisons':comparisons,'field_modulus':str(MOD),'group_closure_exact':True,
        'distinct_squared_overlap_count':len(values),
        'involution_line_pairs_checked_exactly':len(lines)**2,
        'involution_line_squared_overlap_spectrum':['0','(3-sqrt(5))/8','1/4','1/2','(3+sqrt(5))/8','1'],
        'scope':'All minimal Abelian residual frames and all two-involution fixed-line overlaps in the stated triplet; no breaking deformations.'})
    (OUT/'valentiner_exact_gap.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print('certified minimum',result['minimum_positive_squared_overlap']['polynomial'],result['minimum_positive_squared_overlap']['approximate'],flush=True)
    print('certified maximum',result['maximum_subunit_squared_overlap']['polynomial'],result['maximum_subunit_squared_overlap']['approximate'],flush=True)


if __name__=='__main__':
    main()
