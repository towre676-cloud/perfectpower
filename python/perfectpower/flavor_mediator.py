"""Tree-level shared-mediator matching and explicitly scoped alignment tests.

No derived golden CKM interaction is claimed. The scalar alignment EFT is a
separate ordinary CP-invariant model, not a SUSY completion of the prior circuit.
"""
from fractions import Fraction as Q
from itertools import combinations, combinations_with_replacement, permutations
from math import gcd, pi, sqrt
import numpy as np


def abelian_circuit_audit(max_order=120):
    """Additional ordinary phase characters, with neutral fixed coefficients."""
    from .flavor_completion import supersymmetric_circuit, holomorphic_coefficient_extension
    terms=supersymmetric_circuit()['superpotential_terms']
    terms+=holomorphic_coefficient_extension()['additional_superpotential_terms']
    powers=[int(t['fields'][1][1:]) for t in terms
            if t['fields'][0]=='Dstar' and len(t['fields'])==2]
    divisor=gcd(*powers)
    checks=[]
    for n in range(1,max_order+1):
        roots=[]
        for q in range(n):
            charges={f'Z{k}':k*q%n for k in range(1,17)}
            charges.update({f'D{k}':-k*q%n for k in range(2,17)})
            charges.update({'Dstar':0,'Dgold':0,'T':0})
            if all(sum(charges[f] for f in t['fields'])%n==0 for t in terms):roots.append(q)
        assert len(roots)==gcd(n,divisor)
        checks.append({'order':n,'allowed_Z1_charges':roots,'T_charge':0})
    return {'constant_term_driver_charges_zero':['Dstar','Dgold'],
            'Z_n_charge':'n*q(Z1)','constraint_gcd':divisor,
            'general_character_relation':'2*q(Z1)=0; q(T)=0',
            'cyclic_checks':checks,'neutral_T_cannot_distinguish_O_from_O_times_T':True,
            'scope':'Ordinary diagonal Abelian phase actions preserving every initialized monomial with neutral fixed M and coefficients. Charged coupling spurions, field mixing and non-Abelian actions are outside this result.'}


def mediator_operator_audit(neutral_count=17,adjoint=False):
    """All mass and two-Weyl-one-scalar invariants in the declared SM quark sector.

    Q is a family anti-triplet; X_f anti-triplet, X_f^c triplet.
    Scalars F_{fi} are triplets with independent U(1)^6 charges.
    Complex singlets and an optional complex adjoint include their conjugates.
    Gauge representations here are only color 3/bar3 and weak 1/2.
    """
    if type(neutral_count) is not int or not 0<=neutral_count<=17:
        raise ValueError('neutral_count must be 0..17')
    zero=(0,)*6
    def field(name,color,weak,y,flavor,charge=zero):
        return {'name':name,'color_triality':color,'weak_dimension':weak,
                'hypercharge_sixths':y,'flavor':flavor,'phase_charges':list(charge)}
    fermions=[field('Q',1,2,1,-1)]
    scalars=[field('H',0,2,3,0),field('H_conjugate',0,2,-3,0)]
    for sector,index,y in (('u',0,4),('d',3,-2)):
        fermions.extend([field('X_'+sector,1,1,y,-1),field('Xc_'+sector,-1,1,-y,1)])
        for i in range(3):
            charge=tuple(int(j==index+i) for j in range(6))
            fermions.append(field(sector+str(i+1)+'c',-1,1,-y,0,tuple(-x for x in charge)))
            scalars.extend([field('F_'+sector+str(i+1),0,1,0,1,charge),
                            field('F_'+sector+str(i+1)+'_conjugate',0,1,0,-1,tuple(-x for x in charge))])
    names=[f'Z{k}' for k in range(1,min(16,neutral_count)+1)]+(['T'] if neutral_count==17 else [])
    for name in names:
        scalars.extend([field(name,0,1,0,0),field(name+'_conjugate',0,1,0,0)])
    if adjoint:scalars.extend([field('Sigma',0,1,0,8),field('Sigma_conjugate',0,1,0,8)])
    allowed=[]
    def invariant(fields):
        if sum(f['color_triality'] for f in fields)!=0:return False
        if sum(f['weak_dimension']==2 for f in fields) not in (0,2):return False
        if sum(f['hypercharge_sixths'] for f in fields)!=0:return False
        if any(sum(f['phase_charges'][j] for f in fields) for j in range(6)):return False
        reps=sorted(f['flavor'] for f in fields if f['flavor'])
        return reps in ([],[-1,1],[-1,1,8])
    for a,b in combinations_with_replacement(fermions,2):
        if invariant([a,b]):allowed.append({'fields':[a['name'],b['name']],
                                          'coefficient_dimension':1,'flavor_contraction_multiplicity':1})
        for s in scalars:
            if invariant([a,b,s]):allowed.append({'fields':[a['name'],b['name'],s['name']],
                                                'coefficient_dimension':0,'flavor_contraction_multiplicity':1})
    return {'fermions':fermions,'scalars':scalars,'operators':allowed,'count':len(allowed),
            'symmetry':'SM gauge x global SU(3)_F x U(1)^6 x CP',
            'independent_real_coefficients':True,'heavy_color_triplet_Dirac_species':6,
            'matching_interactions':'M_f X_f.X_f^c + h_f Q.H_f.X_f^c + sum_i lambda_fi X_f.F_fi.f_i^c + h.c.',
            'neutral_terms':'Every declared neutral scalar and its conjugate can enter a flavor-universal mediator mass with an independent real CP-even coefficient.',
            'adjoint_terms':'Both Sigma and its conjugate have independent up/down mediator couplings.' if adjoint else None,
            'scope':'Complete stated two-fermion mass/Yukawa sector only. Ordinary non-SUSY Weyl notation, one SM Higgs plus its conjugate. No lepton, baryon-violating or gauged flavor completion; the 34-field singlet driving sector is not included as a unified theory.'}


def alignment_basis():
    """CP-even SU(3) x U(1)^6 scalar invariants through degree six.

    Generated by Gram contractions; balanced epsilon pairs are Gram determinants.
    Gram-rank syzygies first occur at degree eight for six SU(3) triplets.
    """
    labels=['U1','U2','U3','D1','D2','D3']
    rows=[]
    for i in range(6):rows.append({'degree':2,'kind':'norm','indices':[i]})
    for ij in combinations_with_replacement(range(6),2):
        rows.append({'degree':4,'kind':'norm_product','indices':list(ij)})
    for ij in combinations(range(6),2):
        rows.append({'degree':4,'kind':'overlap_absolute_square','indices':list(ij)})
    for ijk in combinations_with_replacement(range(6),3):
        rows.append({'degree':6,'kind':'norm_product','indices':list(ijk)})
    for i in range(6):
        for jk in combinations(range(6),2):
            rows.append({'degree':6,'kind':'norm_times_overlap_square','indices':[i,*jk]})
    for ijk in combinations(range(6),3):
        rows.append({'degree':6,'kind':'real_Gram_triangle','indices':list(ijk)})
    return {'labels':labels,'operators':rows,'counts':{str(d):sum(x['degree']==d for x in rows) for d in (2,4,6)},
            'renormalizable_triplet_operator_count':42,
            'with_one_SM_Higgs':{'H_quadratic':1,'H_quartic':1,'H_norm_times_flavon_norm':6,'total':50},
            'orthogonal_frame_reduction':'Fixed norms and separately orthogonal U/D frames leave only constants plus sum_ij K_ij |V_ij|^2 through degree six. Every Gram triangle vanishes.',
            'first_available_nonlinear_orientation_degree':8,
            'scope':'Six complex fundamental triplets, independent U(1)^6 phases and CP. Fixed positive norms and exact orthogonality are assumptions of the orientation theorem, not generic consequences of arbitrary finite quartic coefficients. Neutral singlet norm couplings do not add orientation tensors at degree four.'}


def inverse_sqrt(metric):
    a=np.asarray(metric,dtype=complex)
    if a.shape!=(3,3) or not np.all(np.isfinite(a)) or np.max(abs(a-a.conj().T))>1e-10:
        raise ValueError('finite Hermitian 3x3 metric required')
    values,u=np.linalg.eigh(a)
    if min(values)<=0:raise ValueError('positive metric required')
    return (u*(1/np.sqrt(values)))@u.conj().T


def canonical_mediator(mass,columns,h=1.):
    """Exact tree matching at H=0, all orders in flavon/heavy mass mixing.

    heavy row block [L,M]; normalized light RH null frame [R,-M^-1 L R].
    Higher-dimensional Higgs operators and loop thresholds are not matched.
    """
    m,l=map(lambda x:np.asarray(x,dtype=complex),(mass,columns))
    if m.shape!=(3,3) or l.shape!=(3,3) or not np.all(np.isfinite(m)) or not np.all(np.isfinite(l)) or not np.isfinite(h):
        raise ValueError('finite 3x3 matrices and coupling required')
    if min(np.linalg.svd(m,compute_uv=False))<1e-12:raise ValueError('invertible mediator mass required')
    a=np.linalg.solve(m,l);metric=np.eye(3)+a.conj().T@a;r=inverse_sqrt(metric)
    null=np.vstack((r,-a@r))
    return {'Y':-h*a@r,'uncanonical_Y':-h*a,'right_metric':metric,'light_right_frame':null,
            'heavy_row':np.hstack((l,m))}


def full_fermion_mass(mass,columns,higgs_vev,h=1.):
    return np.block([[np.zeros((3,3),complex),h*higgs_vev*np.eye(3)],
                     [np.asarray(columns,complex),np.asarray(mass,complex)]])


def mixing_record(yu,yd):
    from .flavor_completion import ckm_from_yukawas,physical_chart
    v,spectra=ckm_from_yukawas(yu,yd)
    u,b,w=map(float,(abs(v[0,1]),abs(v[1,2]),abs(v[0,2])))
    j=float(np.imag(v[0,0]*v[1,1]*v[0,1].conjugate()*v[1,0].conjugate()))
    chart=physical_chart(v) if min(u,b,w)>1e-12 else None
    return {'Vus':u,'Vcb':b,'Vub':w,'J':j,
            'depth':w*(1-w*w)/(u*b) if u*b>1e-14 else None,
            'delta_degrees':chart['delta_degrees'] if chart else None,
            'spectra':[[float(x) for x in s] for s in spectra],
            'unitarity_residual':float(np.max(abs(v@v.conj().T-np.eye(3))))}


def assignment_certificate(cost):
    """Exact rational dual witness for the 3x3 minimum-cost assignment.

    Write beta_j=C[p^-1(j),j]-alpha_p^-1(j). Difference constraints
    alpha_i-alpha_k <= C[i,p(k)]-C[k,p(k)] are solved by relaxation.
    """
    c=[[Q(x) for x in row] for row in cost]
    if len(c)!=3 or any(len(row)!=3 for row in c):raise ValueError('3x3 cost required')
    energies=[(sum(c[i][p[i]] for i in range(3)),p) for p in permutations(range(3))]
    optimum,p=min(energies);alpha=[Q(0)]*3
    for _ in range(3):
        for i in range(3):
            for k in range(3):alpha[i]=min(alpha[i],alpha[k]+c[i][p[k]]-c[k][p[k]])
    beta=[Q(0)]*3
    for i in range(3):beta[p[i]]=c[i][p[i]]-alpha[i]
    reduced=[[c[i][j]-alpha[i]-beta[j] for j in range(3)] for i in range(3)]
    assert all(x>=0 for row in reduced for x in row)
    assert sum(alpha)+sum(beta)==optimum
    return {'cost':[[str(x) for x in row] for row in c],
            'optimum':str(optimum),'winning_permutations':[list(q) for e,q in energies if e==optimum],
            'row_dual':list(map(str,alpha)),'column_dual':list(map(str,beta)),
            'reduced_cost':[[str(x) for x in row] for row in reduced],
            'proof':'For every doubly stochastic B, E=sum alpha+sum beta+sum reduced_ij B_ij >= optimum. A winning permutation is unitary and attains the bound.',
            'scope':'Exact global orientation result only on fixed-norm orthogonal frames. Degenerate costs can leave mixed and CP-violating flat directions; those are not uniquely selected predictions.'}


def degree_eight_example():
    """A capability example, not the desired small-angle golden solution."""
    omega=np.exp(2j*pi/3)
    v=np.array([[omega**(i*j) for j in range(3)] for i in range(3)])/sqrt(3)
    b=abs(v)**2
    return {'interaction':'sum_ij |U_i^dagger D_j|^4 / Lambda^4, equal fixed norms',
            'scalar_degree':8,'minimum_sum_B_squared':'1',
            'proof':'Each normalized row obeys sum_j B_ij^2 >= 1/3. Equality requires B_ij=1/3; the Fourier matrix is unitary and attains it.',
            'B':b.tolist(),'J':float(np.imag(v[0,0]*v[1,1]*v[0,1].conjugate()*v[1,0].conjugate())),
            'J_absolute_exact':'1/(6*sqrt(3))','CKM_magnitudes':'all 1/sqrt(3)',
            'golden_hierarchical_solution':False,
            'scope':'Shows a CP-even higher-degree orientation potential can select nonzero |J| with conjugate CP partners. Other degree-eight invariants have independent coefficients under the declared symmetry; no UV generation of this coefficient pattern is supplied.'}


def golden_squared_relation():
    """Exact magnitude-only necessary equation in p=|Vus|^2,q=|Vcb|^2,r=|Vub|^2."""
    coefficients={(0,0,2):1,(0,0,3):-4,(0,0,4):6,(0,0,5):-4,(0,0,6):1,
                  (1,1,1):-7,(1,1,2):14,(1,1,3):-7,(2,2,0):1}
    return {'variables':['p','q','r'],'coefficients':[{'powers':list(k),'coefficient':v} for k,v in sorted(coefficients.items())],
            'equation':'[r(1-r)^2]^2 - 7*p*q*r(1-r)^2 + (p*q)^2 = 0',
            'branches':'p,q,r>0; r<1; C=sqrt(r)*(1-r)/sqrt(p*q)<1 selects phi^-2 rather than phi^2.',
            'CP_phase_not_fixed':True,'formal_max_scalar_degree_of_raw_overlap_expression':24,
            'scope':'Observable target, not an independently derived scalar interaction. Squaring this expression into an energy term would encode the desired relation by construction.'}


def adjoint_background(a,b,phase=11*pi/30,coefficient=(3-sqrt(5))/2):
    """Favorable initialized texture; the symmetry does not enforce its entries."""
    return np.array([[0,a,coefficient*a*b*np.exp(-1j*phase)],
                     [a,0,b],[coefficient*a*b*np.exp(1j*phase),b,0]],complex)


def matched_adjoint(gu,gd,vus,vcb,lu=(1e-5,.003,.9),ld=(2e-5,4e-4,.02),phase=11*pi/30):
    from scipy.optimize import root
    def evaluate(logs,canonical=True):
        a,b=np.exp(logs);s=adjoint_background(a,b,phase)
        us=canonical_mediator(np.eye(3)+gu*s,np.diag(lu))
        ds=canonical_mediator(np.eye(3)+gd*s,np.diag(ld))
        key='Y' if canonical else 'uncanonical_Y'
        return mixing_record(us[key],ds[key]),a,b,s,us,ds
    def residual(logs):
        row,*_=evaluate(logs)
        return [row['Vus']-vus,row['Vcb']-vcb]
    if abs(gd-gu)<1e-12:raise ValueError('distinct couplings required for this continuation seed')
    seed=np.log([vus/abs(gd-gu),vcb/abs(gd-gu)])
    sol=root(residual,seed,tol=1e-10)
    if not np.all(np.isfinite(sol.x)) or max(abs(x) for x in residual(sol.x))>1e-9:
        raise ArithmeticError('anchor matching did not converge')
    row,a,b,s,us,ds=evaluate(sol.x)
    mass_min=min(np.linalg.svd(np.eye(3)+g*s,compute_uv=False).min() for g in (gu,gd))
    if mass_min<.2 or max(a,b)>1:raise ArithmeticError('outside declared controlled mass/adjoint domain')
    uncanonical,*_=evaluate(sol.x,False)
    def serialized(x):return [[[float(z.real),float(z.imag)] for z in r] for r in x]
    return {'up_adjoint_coupling':gu,'down_adjoint_coupling':gd,'a':float(a),'b':float(b),
            'phase_input_degrees':phase*180/pi,'golden_input':(3-sqrt(5))/2,
            'observables':row,'uncanonical_observables_same_background':uncanonical,
            'anchor_residual':list(map(float,residual(sol.x))),
            'minimum_mediator_mass_singular_value':float(mass_min),'Sigma':serialized(s),
            'right_metric_eigenvalues':[list(map(float,np.linalg.eigvalsh(x['right_metric']))) for x in (us,ds)],
            'scope':'Exact unbroken-EW tree matching for a chosen Hermitian adjoint background. Only a,b fit Vus,Vcb. Adjoint orientation, golden entry and phase are initialized; all up/down adjoint couplings are independent. No adjoint scalar potential, loop threshold or protected vacuum origin is claimed.'}
