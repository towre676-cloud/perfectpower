"""Exact Q(sqrt(5)) nonet tensors in a rational kinetic metric.

Numerics propose projectors; exact generator/CP covariance, orthogonality,
completeness and ranks certify them. Every loop-table identity is then checked
coefficient by coefficient. Reconstruction tolerance is never proof evidence.
"""
from fractions import Fraction as F
from itertools import combinations_with_replacement
from functools import lru_cache
from math import lcm
from collections import defaultdict
import numpy as np

METRIC=(2,6,2,6,2,6,2,6)
PAIRS=list(combinations_with_replacement(range(8),2))
ZERO=(F(0),F(0));ONE=(F(1),F(0))
def add(a,b):return (a[0]+b[0],a[1]+b[1])
def mul(a,b):return (a[0]*b[0]+5*a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def scale(a,n):return (a[0]*n,a[1]*n)
def padd(*polys):
 out={}
 for p in polys:
  for m,c in p.items():out[m]=add(out.get(m,ZERO),c)
 return {m:c for m,c in out.items() if c!=ZERO}
def pscale(p,c):return {m:mul(v,c) for m,v in p.items() if mul(v,c)!=ZERO}
def pmul(p,q):
 out={}
 for m,a in p.items():
  for n,b in q.items():
   k=tuple(sorted(m+n));out[k]=add(out.get(k,ZERO),mul(a,b))
 return {m:c for m,c in out.items() if c!=ZERO}
def var(i):return {(i,):ONE}
def power(p,n):
 out={():ONE}
 for _ in range(n):out=pmul(out,p)
 return out

@lru_cache(None)
def hermitian_matrices():
 from develop_valentiner_frames import matrix
 B=[]
 for i in range(3):
  for j in range(i+1,3):
   r=[[0]*3 for _ in range(3)];r[i][j]=r[j][i]=1;B.append(matrix(r))
   r=[[0]*3 for _ in range(3)];r[i][j]=(-1,0,-2,0);r[j][i]=(1,0,2,0);B.append(matrix(r))
 B.extend([matrix([[1,0,0],[0,-1,0],[0,0,0]]),matrix([[1,0,0],[0,1,0],[0,0,-2]])])
 return tuple(B)

def trace_exact(g,real_part=False):
 d,a=g;t=tuple(sum(F(a[3*i+i][j],d) for i in range(3)) for j in range(4))
 if real_part:return (t[0]-t[2]/2,t[1]-t[3]/2)
 assert t[2:]==(0,0),t
 return t[:2]

def adjoint_exact(g,cp=False):
 from develop_valentiner_frames import mul as mm,dagger,conjugate
 B=hermitian_matrices();out=[]
 h2=(F(3,128),F(1,128)) if cp else ONE
 for i,b in enumerate(B):
  row=[]
  for q in B:
   if cp:q=(q[0],tuple(conjugate(e) for e in q[1]))
   row.append(scale(mul(trace_exact(mm(mm(mm(b,g),q),dagger(g))),h2),F(1,METRIC[i])))
  out.append(row)
 return out

def symmetric_action(L):
 return [[mul(L[i][k],L[j][k]) if k==ell else add(mul(L[i][k],L[j][ell]),mul(L[i][ell],L[j][k]))
          for k,ell in PAIRS] for i,j in PAIRS]

def integer_matrix(A):
 D=lcm(*(x.denominator for row in A for p in row for x in p))
 return tuple(np.array([[int(p[j]*D) for p in row] for row in A],dtype=object) for j in range(2)),D

def matmul(A,B):
 return (A[0]@B[0]+5*A[1]@B[1],A[0]@B[1]+A[1]@B[0])
def transpose(A):return (A[0].T,A[1].T)
def equal(A,B):return all(np.array_equal(a,b) for a,b in zip(A,B))
def scaled(A,n):return tuple(a*n for a in A)


def reconstruct_projectors(numeric_projectors):
 D=80;w2=np.array([METRIC[i]**2 if i==j else 2*METRIC[i]*METRIC[j] for i,j in PAIRS]);w=np.sqrt(w2)
 bs=np.arange(-1600,1601);proposed=[];err=0
 for p in numeric_projectors:
  q=w[:,None]*p*w[None,:];a=np.empty((36,36),object);b=np.empty_like(a)
  for i in range(36):
   for j in range(i,36):
    if abs(q[i,j])<1e-10:aa=bb=0
    else:
     target=D*q[i,j];rr=target-bs*np.sqrt(5);idx=np.argmin(abs(rr-np.round(rr)));bb=int(bs[idx]);aa=int(round(rr[idx]));error=abs(aa+bb*np.sqrt(5)-target)
     if error>1e-8:raise ValueError('Projector proposal not reconstructed in denominator 80')
     err=max(err,float(error/D))
    a[i,j]=a[j,i]=aa;b[i,j]=b[j,i]=bb
  proposed.append((a,b))
 return proposed,D,w2,err


def certify_projectors(numeric_projectors):
 from develop_valentiner_frames import generators,matrix
 Q,D,w2,error=reconstruct_projectors(numeric_projectors);weights=np.diag([72//int(x) for x in w2]).astype(object)
 assert all(72%int(x)==0 for x in w2)
 for i,p in enumerate(Q):
  assert equal(matmul((p[0]@weights,p[1]@weights),p),scaled(p,72*D))
  assert sum(p[0][j,j]*(72//int(w2[j])) for j in range(36))==[1,8,8,9,10][i]*72*D
  assert sum(p[1][j,j]*(72//int(w2[j])) for j in range(36))==0
  for q in Q[:i]:assert equal(matmul((p[0]@weights,p[1]@weights),q),(np.zeros((36,36),object),)*2)
 assert equal(tuple(sum((p[j] for p in Q),np.zeros((36,36),object)) for j in range(2)),(D*np.diag(w2).astype(object),np.zeros((36,36),object)))
 actions=[adjoint_exact(g) for g in generators()]
 K=matrix([[(6,-2,0,0),(0,0,-4,0),(2,-2,2,-2)],[(0,0,-4,0),(0,0,6,-2),(0,0,2,-2)],[(2,-2,2,-2),(0,0,2,-2),(4,0,-2,2)]])
 actions.append(adjoint_exact(K,cp=True))
 for L in actions:
  B,BD=integer_matrix(symmetric_action(L))
  for p in Q:assert equal(matmul(matmul(transpose(B),p),B),scaled(p,BD**2))
 return Q,D,{'coefficient_field':'Q(sqrt(5))','projector_denominator':D,'ranks':[1,8,8,9,10],
  'exact_idempotence_orthogonality_completeness':True,'exact_generators_checked':4,'exact_generalized_CP_checked':True,
  'rational_kinetic_metric':list(METRIC),'proposal_float_error_not_proof':error,
  'proof':'Integer-pair matrix identities with arbitrary-precision integers; numeric proposals become certified exact invariant projectors.'}


def projected_poly(Q,D,up=True,down=False):
 off=2 if up else 12;other=12 if down else off;out={}
 for i,(a,b) in enumerate(PAIRS):
  for j,(c,d) in enumerate(PAIRS):
   k=tuple(sorted((off+a,off+b,other+c,other+d)));v=(F(int(Q[0][i,j]),D),F(int(Q[1][i,j]),D))
   out[k]=add(out.get(k,ZERO),v)
 return {m:c for m,c in out.items() if c!=ZERO}


def sector_polys(offset,Q,D):
 from develop_valentiner_frames import mul as mm
 B=hermitian_matrices();eta=var(offset);s=var(offset+1);a=[var(offset+2+i) for i in range(8)]
 N=padd(*(pscale(power(x,2),(F(g),F(0))) for x,g in zip(a,METRIC)))
 A2=[]
 for i in range(8):
  p={}
  for j,k in PAIRS:
   coeff=scale(trace_exact(mm(mm(B[i],B[j]),B[k]),real_part=True),F(1 if j==k else 2,METRIC[i]))
   if coeff!=ZERO:p= padd(p,pscale(pmul(a[j],a[k]),coeff))
  A2.append(p)
 T3=padd(*(pscale(pmul(x,y),(F(g),F(0))) for x,y,g in zip(a,A2,METRIC)))
 q=[power(eta,2),power(s,2),pmul(eta,s),N];cov=[[pmul(eta,x) for x in a],[pmul(s,x) for x in a],A2]
 self=[power(eta,4),pmul(power(eta,3),s),pmul(power(eta,2),power(s,2)),pmul(eta,power(s,3)),power(s,4),
       pmul(power(eta,2),N),pmul(pmul(eta,s),N),pmul(power(s,2),N),pmul(eta,T3),pmul(s,T3),power(N,2),
       projected_poly(Q[2],D,up=offset==0)]
 return q,cov,self


def exact_quartics(Q,D):
 uq,uc,us=sector_polys(0,Q,D);dq,dc,ds=sector_polys(10,Q,D)
 out=us+ds+[pmul(a,b) for a in uq for b in dq]
 out.extend(padd(*(pscale(pmul(a,b),(F(g),F(0))) for a,b,g in zip(x,y,METRIC))) for x in uc for y in dc)
 out.extend(projected_poly(p,D,up=True,down=True) for p in Q[2:])
 assert len(out)==52
 return out


def integer_polynomials(polys):
 D=lcm(*(v.denominator for p in polys for c in p.values() for v in c))
 return [{m:tuple(int(v*D) for v in c) for m,c in p.items()} for p in polys],D

def hessian_polys(p):
 out={}
 for m,(a,b) in p.items():
  for i in set(m):
   n=list(m);ci=n.count(i);n.remove(i)
   for j in set(n):
    r=n.copy();cj=r.count(j);r.remove(j);k=(i,j)
    out.setdefault(k,{})[tuple(r)]=add(out.get(k,{}).get(tuple(r),(0,0)),(a*ci*cj,b*ci*cj))
 return out


def exact_product(H,K):
 metric=[1,1,*METRIC,1,1,*METRIC,1,1,1,1];out={}
 for ij in H.keys()&K.keys():
  weight=(6//metric[ij[0]])*(6//metric[ij[1]])
  for a,x in H[ij].items():
   for b,y in K[ij].items():
    k=tuple(sorted(a+b));c=(weight*(x[0]*y[0]+5*x[1]*y[1]),weight*(x[0]*y[1]+x[1]*y[0]))
    old=out.get(k,(0,0));out[k]=(old[0]+c[0],old[1]+c[1])
 return {m:c for m,c in out.items() if c!=(0,0)}


def verify_loop_table(polys,table,progress=None):
 ints,D=integer_polynomials(polys);H=[hessian_polys(p) for p in ints];lookup=defaultdict(list)
 for k,i,j,c in table:lookup[i,j].append((k,F(c)))
 count=0;compared=0
 for i in range(len(polys)):
  for j in range(i,len(polys)):
   lhs=exact_product(H[i],H[j]);rhs={}
   for k,c in lookup[i,j]:
    for m,v in ints[k].items():rhs[m]=add(rhs.get(m,ZERO),scale(v,c*72*D))
   for m in lhs.keys()|rhs.keys():assert lhs.get(m,(0,0))==rhs.get(m,ZERO),(i,j,m,lhs.get(m),rhs.get(m))
   count+=1;compared+=len(lhs.keys()|rhs.keys())
  if progress:progress(i,count)
 return {'operator_count':len(polys),'symmetric_products_verified':count,'nonzero_monomial_comparisons':compared,
  'polynomial_common_denominator':D,'scalar_loop_normalization':'16*pi^2 beta(V4)=Tr[(G^-1 Hess V4)^2]/2',
  'exact_zero_residual_for_every_product':True,'arithmetic':'Python arbitrary-precision integers and rational fractions in Q(sqrt(5))'}


def independence_witness(polys):
 import sympy as s
 prime=1000000009;r=int(s.sqrt_mod(5,prime));rng=np.random.default_rng(2503);basis={};rows=[]
 for sample in range(120):
  x=rng.integers(-5,6,max(k for p in polys for m in p for k in m)+1).tolist();v=[]
  for p in polys:
   a=0
   for m,(b,c) in p.items():
    z=1
    for k in m:z=z*x[k]%prime
    coef=(int(b.numerator)*pow(int(b.denominator),-1,prime)+r*int(c.numerator)*pow(int(c.denominator),-1,prime))%prime;a=(a+coef*z)%prime
   v.append(a)
  for k,row in sorted(basis.items()):
   fac=v[k];v=[(a-fac*b)%prime for a,b in zip(v,row)]
  pivot=next((i for i,a in enumerate(v) if a),None)
  if pivot is not None:
   inv=pow(v[pivot],-1,prime);basis[pivot]=[a*inv%prime for a in v];rows.append(x)
  if len(basis)==len(polys):return {'prime':prime,'sqrt5_embedding_mod_prime':r,'exact_rank':len(polys),'independent_evaluation_points':rows}
 raise AssertionError('Exact operator independence witness failed')


def extended_quartics(Q,D):
    polys=exact_quartics(Q,D);uq,_,_=sector_polys(0,Q,D);dq,_,_=sector_polys(10,Q,D)
    hh=pscale(padd(*(power(var(i),2) for i in range(20,24))),(F(1,2),F(0)))
    return polys+[power(hh,2)]+[pmul(hh,q) for q in uq+dq]


def cp_matrix():
 from develop_valentiner_frames import matrix
 return matrix([[(6,-2,0,0),(0,0,-4,0),(2,-2,2,-2)],[(0,0,-4,0),(0,0,6,-2),(0,0,2,-2)],[(2,-2,2,-2),(0,0,2,-2),(4,0,-2,2)]])


def certify_odd_projector(numeric_odd,Q,D):
 odd,OD,w2,error=reconstruct_projectors([numeric_odd]);odd=odd[0];assert OD==D
 weights=np.diag([72//int(x) for x in w2]).astype(object)
 assert equal(matmul((odd[0]@weights,odd[1]@weights),odd),scaled(Q[4],72*D))
 from develop_valentiner_frames import generators
 for L,sign in [(adjoint_exact(g),1) for g in generators()]+[(adjoint_exact(cp_matrix(),cp=True),-1)]:
  B,BD=integer_matrix(symmetric_action(L));assert equal(matmul(matmul(transpose(B),odd),B),scaled(odd,sign*BD**2))
 selfpoly=projected_poly(odd,D);assert not selfpoly
 return odd,{'exact_group_invariant':True,'exact_CP_parity':-1,'squared_operator':'P_5_plus_P_5prime','self_polynomial_identically_zero':True,'proposal_error_not_proof':error}


def pure_adjoint_mass_gap_certificate():
 import sympy as s
 a,M,x,y,z=s.symbols('a M x y z',positive=True)
 f=lambda t:(a*a-t*t)*(M*M-t*t)/(t*t)
 d12=s.factor(f(x)-(y/x)**2*f(y));d23=s.factor((y/z)**2*f(y)-f(z))
 assert s.simplify(d12-(y*y-x*x)*(a*a+M*M-x*x-y*y)/(x*x))==0
 assert s.simplify(d23-(z*z-y*y)*(a*a+M*M-y*y-z*z)/(z*z))==0
 return {'assumptions':'Canonical triangular D=[[a I,0],[C,M I]], C traceless Hermitian; 0<m1<m2<m3<min(a,M), a,M>0',
   'source_squared_inverse':'f(m)=(a^2-m^2)(M^2-m^2)/m^2',
   'first_positive_difference':str(d12),'second_positive_difference':str(d23),
   'trace_condition':'Largest |source eigenvalue| equals sum of the other two',
   'necessary_mass_bound':'m2/m1 < 1+m2/m3 < 2',
   'scope':'Exact finite-mass exclusion of strong light-family hierarchy for a pure traceless source with universal bare Higgs and heavy mass; singlet shifts, nonuniversal masses or kinetic terms change the assumptions.'}
