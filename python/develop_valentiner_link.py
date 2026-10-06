"""Product-family sequestering, sextic link alignment, and physical CP pairs.
No nominated CKM angle or golden coefficient enters this calculation.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
from math import factorial
import json
import numpy as np
import sympy as s
from develop_valentiner_frames import generators,group_closure,numeric,mul,IDENTITY,product,conjugate
from develop_valentiner_invariants import Z,O,add,scale,exact_integer
from perfectpower.flavor_mediator import canonical_mediator,mixing_record
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'receipts/m22_interactions'

def invariant_census(elements):
    # Molien averages over class signatures, using power-sum Newton identities
    # for the nine-dimensional bifundamental, independently of Schur decompositions.
    signatures=Counter()
    for g in elements:
        power=IDENTITY;values=[]
        for k in range(6):
            power=mul(power,g)
            values.append(tuple(sum(F(power[1][3*i+i][j],power[0]) for i in range(3)) for j in range(4)))
        signatures[tuple(values)]+=1
    chars=[]
    for a,na in signatures.items():
        for b,nb in signatures.items():
            powers=[product(x,conjugate(y)) for x,y in zip(a,b)];h=[O]
            for n in range(1,7):
                v=Z
                for k in range(1,n+1):v=add(v,product(powers[k-1],h[n-k]))
                h.append(scale(v,F(1,n)))
            chars.append((na*nb,h))
    dims={}
    for p in range(7):
        for q in range(7-p):
            v=Z
            for n,h in chars:v=add(v,scale(product(h[p],conjugate(h[q])),F(n,1080**2)))
            dims[f'{p},{q}']=exact_integer(v)
    assert dims['3,0']==1 and dims['6,0']==2 and dims['2,2']==2
    return dims

def coefficient_functions():
    r=json.loads((OUT/'valentiner_invariants.json').read_text())
    exact_norm=sum(s.sympify(t['coefficient'])*s.conjugate(s.sympify(t['coefficient']))*s.Rational(int(np.prod([factorial(k) for k in t['powers']])),factorial(6)) for t in r['sextic']['terms'])
    assert s.simplify(exact_norm)==16
    terms=[(tuple(t['powers']),complex(s.sympify(t['coefficient']).evalf())) for t in r['sextic']['terms']]
    def value(v):return sum(c*np.prod(v**np.array(p)) for p,c in terms)
    norm=sum(abs(c)**2/(factorial(6)/np.prod([factorial(t) for t in p])) for p,c in terms)
    # Build the symmetric six-index tensor. Its Hilbert norm equals the weighted
    # polynomial coefficient norm, not the unweighted monomial coefficient norm.
    tensor=np.zeros((3,)*6,complex)
    for idx in np.ndindex(tensor.shape):
        p=tuple(idx.count(j) for j in range(3));mult=factorial(6)/np.prod([factorial(t) for t in p])
        tensor[idx]=next((c/mult for powers,c in terms if powers==p),0)
    assert abs(np.vdot(tensor,tensor)-norm)<1e-12
    def link(L):
        transformed=tensor
        for axis in range(6):
            transformed=np.tensordot(transformed,L,axes=([axis],[0]))
            transformed=np.moveaxis(transformed,-1,axis)
        return np.vdot(tensor,transformed)
    return value,link,float(norm)

def match_link(L,C,mu=.8,md=1.3,h=.57,g=.71,g_reverse=.23):
    M=np.block([[mu*np.eye(3),g*L],[g_reverse*L.conj().T,md*np.eye(3)]])
    A=np.linalg.solve(M,np.vstack([np.zeros((3,3)),C]))
    metric=np.eye(3)+A.conj().T@A
    vals,u=np.linalg.eigh(metric);ki=(u/np.sqrt(vals))@u.conj().T
    light=np.vstack([np.eye(3),-A])@ki
    heavy=np.hstack([np.vstack([np.zeros((3,3)),C]),M])
    assert np.linalg.matrix_rank(heavy)==6
    assert np.max(abs(heavy@light))<1e-12
    assert np.max(abs(light.conj().T@light-np.eye(3)))<1e-12
    Y=-h*A[:3]@ki
    return Y

def main():
    elements,_,words=group_closure(generators());ms=[numeric(g) for g in elements]
    dims=invariant_census(elements);print('exact bifundamental census',dims,flush=True)
    r=json.loads((OUT/'valentiner_cp.json').read_text())
    X=np.array([[complex(s.sympify(t).evalf()) for t in row] for row in r['unitary_CP_matrix']])
    # Orthogonal real fixed space of the anti-linear involution supplies a CP basis.
    action=np.block([[X.real,X.imag],[X.imag,-X.real]])
    _,z=np.linalg.eigh(action);fixed=z[:,-3:];W=fixed[:3]+1j*fixed[3:]
    assert np.max(abs(W.conj().T@W-np.eye(3)))<1e-12
    assert np.max(abs(X@W.conj()-W))<1e-12
    value,link,norm=coefficient_functions()
    gamma=value(X[:,0]);rng=np.random.default_rng(6021080)
    for _ in range(8):
        v=rng.normal(size=3)+1j*rng.normal(size=3);v/=np.linalg.norm(v)
        assert abs(value(X@v.conj())-gamma*np.conjugate(value(v)))<1e-12
    assert abs(abs(gamma)-1)<1e-12
    assert max(abs(link(g)-norm) for g in ms)<2e-11
    random_residual=[]
    for _ in range(12):
        a=rng.normal(size=(3,3))+1j*rng.normal(size=(3,3));q,rq=np.linalg.qr(a);q=q@np.diag(np.diag(rq)/abs(np.diag(rq)))
        q/=np.linalg.det(q)**(1/3)
        random_residual.append(float(norm-link(q).real))
        assert abs(link(X@q.conj()@X.conj().T)-link(q).conjugate())<2e-11
        assert norm-link(q).real>-1e-11
    cu=W@np.diag([.07,.31,.9]);cd=W@np.diag([.08,.27,.85])
    yu=canonical_mediator(.9*np.eye(3),cu,h=.6)['Y']
    # Choose largest physical |J| in the group, without a target phase or magnitude.
    records=[mixing_record(yu,match_link(g,cd)) for g in ms]
    idx=max(range(1080),key=lambda i:abs(records[i]['J']))
    L=ms[idx];cpL=X@L.conj()@X.conj().T
    partner=mixing_record(yu,match_link(cpL,cd));selected=records[idx]
    assert abs(selected['J'])>1e-3 and abs(selected['J']+partner['J'])<1e-12
    assert abs(selected['depth']-partner['depth'])<1e-12
    # Independent weak-basis CP invariant, with nondegenerate matched spectra.
    yd=match_link(L,cd);Hu=yu@yu.conj().T;Hd=yd@yd.conj().T
    cpdet=float(np.linalg.det(Hu@Hd-Hd@Hu).imag)
    assert abs(cpdet)>1e-14
    # The link term alone does not fix source frames. Allowed real column changes
    # produce physical responses when source columns are not orthogonal.
    raw=np.array([[1.,.3,.1],[.2,1.,.4],[.1,.15,1.]])
    free=[]
    for coefficient in [.8,1.,1.2]:
        C=W@raw@np.diag([.08,.27*coefficient,.85])
        free.append({'second_column_coupling':coefficient,'observables':mixing_record(yu,match_link(L,C))})
    result={'bifundamental_bidegree_dimensions':dims,'family_group':'3.A6_u x 3.A6_d','quartic_direct_overlap_allowed':False,
        'first_allowed_dressed_cross_overlap_degree':6,'dressed_cross_overlap':'|phi_ui^dagger Lambda phi_dj|^2',
        'sextic_link_holomorphic_dimension':2,'sextic_link_basis':['det(Lambda)^2','I6(Lambda)=<F6,F6 composed with Lambda>'],
        'link_tensor_norm_squared':norm,'maximum_group_link_residual':float(max(abs(link(g)-norm) for g in ms)),
        'random_unitary_alignment_energies':random_residual,'triplet_sextic_CP_factor':[float(gamma.real),float(gamma.imag)],
        'CP_basis':[[[float(t.real),float(t.imag)] for t in row] for row in W],
        'selected_link_element':idx,'selected_link_word':words[idx],'physical_CP_pair':[selected,partner],
        'weak_basis_commutator_determinant_imaginary':cpdet,'free_real_coupling_cases':free,
        'reverse_link_coupling_included':.23,'renormalizable_scalar_counts':{'quadratic_with_Higgs':8,'cubic_CP_even':1,'quartic_with_Higgs':49,'total_CP_even':58},'right_light_modes':3,'heavy_modes':6,'scope':'Specified product symmetry and link model, tree matching at H=0. Physical CP pair is conditional on CP-real source frames; those frames and the selected group vacuum are not dynamically selected. No golden target input.'}
    (OUT/'valentiner_link.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':main()
