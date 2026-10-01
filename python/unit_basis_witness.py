"""Exact fundamental-domain witness that the proposed units generate the unit group of Z[x]
(stdlib only; adapted from the direct-H handoff, Apache-2.0).

For `Z[x]`, `x^3 = P x + Q` with three real roots, and units `ε1, ε2` (norm ±1, inverses checked
in Lean), let `v_r` be the log-embedding of `ε_r`.  Any unit `u` can be moved by `ε1^{-e1} ε2^{-e2}`
into the centered parallelogram `{r1 v1 + r2 v2 : -1/2 <= r_i < 1/2}`; there every conjugate is at
most `U_i = sqrt(max(|ε1_i|, 1/|ε1_i|) max(|ε2_i|, 1/|ε2_i|))`, and Lagrange interpolation bounds
the coordinates by an explicit box.  This script:
- isolates the roots by rational bisection and encloses every logarithm with a rational atanh series
  and an explicit remainder (no floating point);
- computes the box, lists every triple of norm ±1 in it (`candidates`), and shows that each one other
  than ±1 has a log coordinate outside the parallelogram.
Hence `O^x = ±ε1^Z ε2^Z` for the order `Z[x]`.  The finite part (every box triple of norm ±1 is a
listed candidate) is re-checked by the Lean kernel (`Generated/Field756.lean`, `Generated/D72Unit.lean`);
the real-log fundamental-domain argument itself is in this script, not in Lean.

Run: python3 python/unit_basis_witness.py      Writes receipts/unit_basis_witness.json.
"""
from fractions import Fraction as F
from math import isqrt
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]

def add(x,y):return x[0]+y[0],x[1]+y[1]
def neg(x):return -x[1],-x[0]
def sub(x,y):return add(x,neg(y))
def mul(x,y):
    a=[s*t for s in x for t in y];return min(a),max(a)
def div(x,y):
    assert not y[0]<=0<=y[1]
    return mul(x,(min(1/y[0],1/y[1]),max(1/y[0],1/y[1])))
def ab(x):
    return (F(0) if x[0]<=0<=x[1] else min(abs(x[0]),abs(x[1])),max(abs(x[0]),abs(x[1])))
def const(x):return F(x),F(x)
def ceil(x):return -((-x.numerator)//x.denominator)
def bounds(x,bits=40):
    S=1<<bits
    return [str(F((x[0]*S).numerator//(x[0]*S).denominator,S)),str(F(ceil(x[1]*S),S))]

def isolate(P,Q,lo,hi):
    f=lambda x:x**3-P*x-Q
    lo,hi=F(lo),F(hi);assert f(lo)*f(hi)<0
    for _ in range(80):
        m=(lo+hi)/2
        assert f(m)!=0
        if f(lo)*f(m)<0:hi=m
        else:lo=m
    assert f(lo)*f(hi)<0
    d=sub(mul(const(3),mul((lo,hi),(lo,hi))),const(P))
    assert not d[0]<=0<=d[1]
    return lo,hi

def log_series(x,J=40):
    assert x>0
    z=(x-1)/(x+1); assert 0<=z<F(1)
    zz=z*z;term=z;total=F(0)
    for k in range(J):
        total+=term/(2*k+1);term*=zz
    rem=2*term/((2*J+1)*(1-zz))
    return 2*total,2*total+rem

LOG2=log_series(F(2))

def log_endpoint(x):
    assert x>0
    k=x.numerator.bit_length()-x.denominator.bit_length()
    u=x/F(2)**k
    while u<1:u*=2;k-=1
    while u>=2:u/=2;k+=1
    assert 1<=u<2
    return add(mul(const(k),LOG2),log_series(u))

def log_interval(x):
    assert x[0]>0
    return log_endpoint(x[0])[0],log_endpoint(x[1])[1]

def conj(g,roots):
    a,b,c=g
    return [add(add(const(a),mul(const(b),d)),mul(const(c),mul(d,d))) for d in roots]

def norm(P,Q,g):
    a,b,c=g;m=((a,Q*c,Q*b),(b,a+P*c,P*b+Q*c),(c,b,a+P*c))
    return m[0][0]*(m[1][1]*m[2][2]-m[1][2]*m[2][1])-m[0][1]*(m[1][0]*m[2][2]-m[1][2]*m[2][0])+m[0][2]*(m[1][0]*m[2][1]-m[1][1]*m[2][0])

def sqrt_upper(x,bits=80):
    assert x>=0
    S=1<<bits;k=isqrt((x.numerator*S*S)//x.denominator)
    out=F(k+1,S);assert out*out>=x
    return out

def witness(P,Q,e1,e2,brackets):
    roots=[isolate(P,Q,*z) for z in brackets]
    assert roots[0][1]<roots[1][0]<roots[1][1]<roots[2][0]
    assert abs(norm(P,Q,e1))==abs(norm(P,Q,e2))==1
    E1,E2=conj(e1,roots),conj(e2,roots)
    L1=[log_interval(ab(x)) for x in E1];L2=[log_interval(ab(x)) for x in E2]
    det=sub(mul(L1[0],L2[1]),mul(L2[0],L1[1]));assert not det[0]<=0<=det[1]
    U=[]
    for x,y in zip(E1,E2):
        xx,yy=ab(x),ab(y);assert xx[0]>0 and yy[0]>0
        U.append(sqrt_upper(max(xx[1],1/xx[0])*max(yy[1],1/yy[0])))
    coord=[F(0),F(0),F(0)]
    for i,d in enumerate(roots):
        j,k=[v for v in range(3) if v!=i];v,w=roots[j],roots[k]
        den=mul(sub(d,v),sub(d,w))
        coefficients=[div(mul(v,w),den),div(neg(add(v,w)),den),div(const(1),den)]
        for r,s in enumerate(coefficients):coord[r]+=ab(s)[1]*U[i]
    box=list(map(ceil,coord));units=[]
    for a in range(-box[0],box[0]+1):
        for b in range(-box[1],box[1]+1):
            for c in range(-box[2],box[2]+1):
                g=(a,b,c);N=norm(P,Q,g)
                if abs(N)!=1:continue
                logs=[log_interval(ab(z)) for z in conj(g,roots)]
                s1=div(sub(mul(logs[0],L2[1]),mul(logs[1],L2[0])),det)
                s2=div(sub(mul(L1[0],logs[1]),mul(L1[1],logs[0])),det)
                outside=any(s[1]<-F(1,2) or s[0]>F(1,2) for s in (s1,s2))
                torsion=g in ((1,0,0),(-1,0,0))
                assert outside or torsion,(g,s1,s2)
                units.append({'coordinates':g,'norm':N,'unit_log_coordinates':[bounds(s1),bounds(s2)],
                              'excluded_from_centered_domain':outside,'torsion':torsion})
    return {'P':P,'Q':Q,'units':[e1,e2],'root_intervals':[[str(a),str(b)] for a,b in roots],
            'coordinate_box':box,'integer_triples':(2*box[0]+1)*(2*box[1]+1)*(2*box[2]+1),
            'norm_one_candidates':len(units),'candidates':units,
            'result':'only +1 and -1 can lie in the centered fundamental parallelogram; finite arithmetic checked exactly'}

def main():
    data={'status':'Exact rational finite-domain witness. The generic real-log fundamental-domain argument and field/order identification are mathematical dependencies, not implemented Lean proofs.',
          'log_enclosures':'40 rational atanh terms after reduction to [1,2); explicit geometric remainder',
          'fields':[witness(6,2,(-5,0,1),(11,1,-2),[(-3,-2),(-1,0),(2,3)]),
                    witness(9,6,(-1,-3,1),(-1,0,2),[(-3,-2),(-1,0),(3,4)])]}
    p=ROOT/'receipts'/'unit_basis_witness.json'
    p.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps([{k:r[k] for k in ('P','Q','coordinate_box','integer_triples','norm_one_candidates','result')} for r in data['fields']],indent=2))

if __name__=='__main__':main()
