"""Gaussian mediation, exact rank restrictions and its fermion boundary.

The positive square completes specified source coefficients, without deriving
those inputs from symmetry. Finite 8-prime,9,5+5-prime mediators have no
triplet-bilinear Yukawa invariant; ordinary adjoints and singlets do.
"""
import numpy as np
from .nonet_potential import sector_features


def factorize_cross(matrix,mass=10.,tolerance=1e-10):
    C=np.asarray(matrix,float)
    if C.ndim!=2 or not np.all(np.isfinite(C)) or mass<=0:raise ValueError('Finite matrix and positive mass required')
    U,s,Vh=np.linalg.svd(C,full_matrices=False);keep=s>tolerance*max(1,s[0])
    up=mass*U[:,keep]*np.sqrt(s[keep]);down=-mass*Vh[keep].T*np.sqrt(s[keep])
    return up,down,{'rank':int(sum(keep)),'singular_values':s.tolist(),'matching_error':float(np.max(abs(C+up@down.T/mass**2)))}


def mediation_plan(coefficients,projectors,mass=10.,finite_only=False,sector_ratios=(1.,1.,1.)):
    c=np.asarray(coefficients,float);groups=[]
    if c.shape!=(60,) or mass<=0:raise ValueError('Sixty source coefficients and positive mediator mass required')
    if not finite_only:
        for name,kind,block,dim in [('singlet','quadratic',c[32:48].reshape(4,4),1),('ordinary_adjoint','adjoint',c[48:57].reshape(3,3),8)]:
            up,down,cert=factorize_cross(block,mass)
            groups.append({'name':name,'kind':kind,'up':up,'down':down,'dimension':dim,'certificate':cert})
    for name,k in [('finite_adjoint',2),('finite_nine',3),('CP_pair_five',4)]:
        vals,E=np.linalg.eigh(projectors[k]);E=E[:,vals>.5];coupling=c[55+k]
        ratio=float(sector_ratios[k-2])
        if ratio<=0:raise ValueError('Positive sector ratio required')
        u=mass*np.sqrt(abs(coupling))*ratio;d=-np.sign(coupling)*mass*np.sqrt(abs(coupling))/ratio
        groups.append({'name':name,'kind':'finite','projector_index':k,'embedding':E,'up':float(u),'down':float(d),'dimension':E.shape[1],
                       'certificate':{'rank':1,'matching_error':float(abs(coupling+u*d/mass**2))}})
    return {'groups':groups,'mass':float(mass),'finite_only':bool(finite_only),
            'real_mediator_coordinates':sum(g['dimension']*(g['up'].shape[1] if isinstance(g['up'],np.ndarray) else 1) for g in groups)}


def currents(x,plan,projectors):
    up=sector_features(np.asarray(x)[:10],projectors);down=sector_features(np.asarray(x)[10:],projectors);out=[];gradient=[]
    for g in plan['groups']:
        if g['kind']=='quadratic':
            J=up[0]@g['up']+down[0]@g['down'];D=np.column_stack([g['up'].T@up[1],g['down'].T@down[1]])
        elif g['kind']=='adjoint':
            J=(g['up'].T@up[2]+g['down'].T@down[2]).reshape(-1)
            D=np.concatenate([np.einsum('mr,mij->rij',g['up'],up[3]),np.einsum('mr,mij->rij',g['down'],down[3])],axis=2).reshape(-1,20)
        else:
            E=g['embedding'];J=E.T@(g['up']*up[4]+g['down']*down[4]);D=np.zeros((len(J),20))
            D[:,2:10]=g['up']*E.T@up[5];D[:,12:]=g['down']*E.T@down[5]
        out.extend(J);gradient.extend(D)
    return np.array(out),np.array(gradient)


def completed_hessian(source_hessian,current_jacobian,mass):
    H=np.asarray(source_hessian);D=np.asarray(current_jacobian)
    if D.shape[1]!=len(H) or mass<=0:raise ValueError('Compatible Hessian, Jacobian and positive mass required')
    return np.block([[H+D.T@D/mass**2,D.T],[D,mass**2*np.eye(len(D))]])


def exact_mediator_certificates():
    import sympy as s
    u=s.symbols('u0:4');d=s.symbols('d0:4');C=s.Matrix(4,4,lambda i,j:-u[i]*d[j])
    assert all(C.extract([i,j],[k,l]).det()==0 for i in range(4) for j in range(i+1,4) for k in range(4) for l in range(k+1,4))
    a,b,c,d=s.symbols('a b c d');F=s.Matrix([-s.Rational(1,2)*(a*a-c*c),-s.Rational(1,2)*(b*b-d*d),-a*b,-c*d])
    determinant=s.factor(F.jacobian([a,b,c,d]).det());assert s.expand(determinant-(b*b*c*c-a*a*d*d))==0
    return {'single_mediator_cross_matrix_rank_at_most':1,'rank_one_mixed_dimension':{'singlet_4_by_4':7,'adjoint_3_by_3':5,'finite_channels':3,'total':15},
      'single_per_channel_mixed_codimension':13,'single_per_channel_real_coordinates':36,'single_per_channel_cubic_coefficients':20,
      'universal_minimum_real_coordinates':55,'universal_minimum_multiplets':10,'universal_source_current_coefficients':56,'Gaussian_mass_coefficients':19,
      'finite_only_real_coordinates':27,'finite_only_total_neutral_coordinates_with_sources_Higgs':48,
      'finite_orientation_parameter_Jacobian_determinant':str(determinant),
      'finite_orientation_scope':'Two finite-eight/pair self coefficients and their two cross coefficients are generically independently adjustable; radial contacts compensate radial self terms.',
      'fermion_bilinear_representation':'3bar tensor 3 = 1 + ordinary 8','new_fermion_couplings_for_finite_8prime_9_5pair':0,
      'allowed_heavy_mass_Yukawas_for_each_singlet_or_ordinary8_copy_per_sector':1,
      'scope':'Gaussian tree matching on the declared triplets. Extra mediator self interactions and source contacts are allowed, not claimed forbidden.'}


def exact_heavy_vertex_counterexample():
    import sympy as s
    L=[s.Rational(2),s.Rational(3)];A=s.Matrix([[0,1],[1,0]]);B=s.Matrix([[0,s.I],[-s.I,0]])
    G=s.Matrix(2,2,lambda i,j:L[i]*(L[j]*A[i,j]+B[i,j])/s.sqrt((1+L[i]**2)*(1+L[j]**2)))
    product=s.simplify(G[0,1]*G[1,0]);assert s.im(product)==-s.Rational(3,25)
    return {'Hermitian_source_vertex':str(A),'Hermitian_heavy_mass_vertex':str(B),'heavy_singular_values':['2','3'],'source_eigenvalues':['3/2','8/3'],
      'heavy_state_vertex_pair':str(product),'imaginary_part':'-3/25',
      'scope':'Counterexample to termwise vertex reality, not a standalone complete CP-breaking vacuum or all-diagram theta calculation.'}


def exact_finite_mediator_operator_census():
    """Full degree<=4 scalar census for 20 odd sources plus an even real 27.

    CP is averaged exactly over the antiunitary coset, using its action on
    Hermitian matrices. No numerical projector trace rounds these counts.
    """
    from fractions import Fraction as F
    from develop_valentiner_frames import group_closure,generators,mul,matrix,normalize,product,conjugate,IDENTITY
    from develop_valentiner_invariants import Z,O,add,sub,scale,exact_integer
    group,lookup,_=group_closure(generators());K=matrix([
        [(6,-2,0,0),(0,0,-4,0),(2,-2,2,-2)],
        [(0,0,-4,0),(0,0,6,-2),(0,0,2,-2)],
        [(2,-2,2,-2),(0,0,2,-2),(4,0,-2,2)]])
    def star(g):return (g[0],tuple(conjugate(v) for v in g[1]))
    def cp_scale(g):return normalize(g[0]*128,[product(v,(3,1,0,0)) for v in g[1]])
    assert cp_scale(mul(K,star(K)))==IDENTITY
    def trace(g):return tuple(sum(F(g[1][3*i+i][j],g[0]) for i in range(3)) for j in range(4))
    def symmetric(chars,n):
        h=[O]
        for degree in range(1,n+1):
            total=Z
            for k in range(1,degree+1):total=add(total,product(chars[k-1],h[degree-k]))
            h.append(scale(total,F(1,degree)))
        return h[n]
    totals=[[Z]*5,[Z]*5]
    for g in group:
        powers=[];p=g
        for k in range(1,9):powers.append(trace(p));p=mul(p,g)
        ordinary=[sub(product(t,conjugate(t)),O) for t in powers]
        U=mul(g,K);T=cp_scale(mul(U,star(U)));assert T in lookup
        tp=[];p=T
        for k in range(1,9):tp.append(trace(p));p=mul(p,T)
        twisted=[sub(tp[k-1],O) if k%2 else sub(product(tp[k//2-1],conjugate(tp[k//2-1])),O) for k in range(1,9)]
        for parity,chars in enumerate([ordinary,twisted]):
            W=[sub(sub(scale(add(product(chars[k-1],chars[k-1]),chars[2*k-1]),F(1,2)),O),chars[k-1]) for k in range(1,5)]
            V=[add(t,scale(O,2)) for t in chars[:4]];V2=symmetric(V,2);W2=symmetric(W,2)
            values=[W2,symmetric(W,3),symmetric(W,4),product(V2,W[0]),product(V2,W2)]
            totals[parity]=[add(t,scale(v,F(1,len(group)))) for t,v in zip(totals[parity],values)]
    before=[exact_integer(t) for t in totals[0]]
    even=[exact_integer(scale(add(a,b),F(1,2))) for a,b in zip(*totals)]
    odd=[n-e for n,e in zip(before,even)]
    return {'representation':'W=Sym2(8)-1-8=8prime+9+5+5prime, real dimension 27',
      'group_order':len(group),'CP_coset_group_elements_checked':len(group),
      'labels':['W_quadratic','W_cubic','W_quartic','single_sector_source2_W','single_sector_source2_W2'],
      'before_CP':before,'CP_even':even,'CP_odd':odd,
      'complete_scalar_coefficients_without_Higgs':60+even[0]+even[1]+even[2]+2*even[3]+2*even[4],
      'complete_scalar_coefficients_with_Higgs':70+2*even[0]+even[1]+even[2]+2*even[3]+2*even[4],
      'CP_matrix_common_factor_squared':'(3+sqrt(5))/128',
      'CP_trace_formula':'For K=Ad(g) CP on 8, T=(g X)(g X)*: trace(K^odd)=trace(T^odd)-1, trace(K^even)=|trace(T^(even/2))|^2-1.',
      'scope':'All nonderivative scalar monomials through degree four for the declared 20 odd source coordinates, even real W27, Higgs, sector Z2 and generalized CP. Tadpoles and Higgs-linear-W cubics vanish because W has no singlet.'}


def exact_SU3_27_certificate():
    import sympy as s
    from itertools import combinations_with_replacement
    B=[]
    for i in range(3):
        for j in range(i+1,3):
            a=s.zeros(3);a[i,j]=a[j,i]=1/s.sqrt(2);B.append(a)
            a=s.zeros(3);a[i,j]=-s.I/s.sqrt(2);a[j,i]=s.I/s.sqrt(2);B.append(a)
    B.extend([s.diag(1,-1,0)/s.sqrt(2),s.diag(1,1,-2)/s.sqrt(6)])
    pairs=list(combinations_with_replacement(range(8),2))
    D=s.Matrix([[s.simplify(s.re(s.trace(Q*B[i]*B[j]))*(1 if i==j else s.sqrt(2))) for i,j in pairs] for Q in B])
    assert s.simplify(D*D.T-s.Rational(5,6)*s.eye(8))==s.zeros(8)
    p,q,nu,nd=s.symbols('p q nu nd');invariant=s.expand(p*p-nu*nd/8-s.Rational(6,5)*(q-nu*nd/3))
    assert invariant==p*p-s.Rational(6,5)*q+s.Rational(11,40)*nu*nd
    self=s.simplify(nu**2-nu**2/8-s.Rational(6,5)*nu**2/6);assert self==s.Rational(27,40)*nu**2
    return {'SU3_adjoint_covariant_Gram':'5/6 times identity_8','projector_27_rank':27,
      'mixed_invariant':'Tr(A B)^2 - 6/5 Tr(A^2 B^2) + 11/40 Tr(A^2) Tr(B^2)',
      'self_invariant':'27/40 [Tr(A^2)]^2','enforced_finite_channel_relation':'lambda_8prime=lambda_9=lambda_CP_pair5',
      'scope':'Exact SU(3) projector identity and unsplit 27-plet tree coefficient relation. Finite-group mass splitting and other SU(3)-breaking interactions remove the equality.'}
