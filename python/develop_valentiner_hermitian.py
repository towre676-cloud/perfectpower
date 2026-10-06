"""One canonical action for finite hierarchical spectra and one-loop phase zero."""
from pathlib import Path
import json
import numpy as np
import sympy as sy
import mpmath as mp
from perfectpower.flavor_hermitian import *
from perfectpower.flavor_canonical import current_pair
from perfectpower.flavor_quantum import scalar_threshold
from develop_valentiner_canonical import fields
from develop_valentiner_quantum import standard_CKM
from valentiner_electroweak import branch,COORDINATE_SCALES
from valentiner_adjoint_quartics import quartic_projectors,BASIS
from valentiner_canonical_operators import certificate as character_certificate

ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'receipts/m22_interactions'


def symbolic_certificate():
    r1,r2,r3=sy.symbols('r1 r2 r3',real=True);pairs=[(r1,r2),(r1,r3),(r2,r3)]
    V=sy.Matrix([[1,r,r*r] for r in [r1,r2,r3]])
    F=sy.Matrix([[1,a+b,a*a+b*b] for a,b in pairs]);G=sy.Matrix([[1,a+b,a*b] for a,b in pairs])
    Delta=(r2-r1)*(r3-r1)*(r3-r2)
    assert sy.expand(-V.det()*F.det()*G.det()-Delta**3)==0
    x,y,z,a,b,c,d,e,f=sy.symbols('x y z a b c d e f',real=True)
    T=sy.Matrix([[x,a+sy.I*b,c+sy.I*d],[a-sy.I*b,y,e+sy.I*f],[c-sy.I*d,e-sy.I*f,z]])
    tau=sy.im(T[0,1]*T[1,2]*T[2,0]);second=T*T
    pairdet=[sy.expand(sy.im(second[i,j]*sy.conjugate(T[i,j]))) for i,j in [(0,1),(0,2),(1,2)]]
    assert all(sy.expand(v-sign*tau)==0 for v,sign in zip(pairdet,[-1,1,-1]))
    Rd=sy.diag(r1,r2,r3);chi=sy.im(sy.trace(Rd**2*T**2*Rd*T))
    assert sy.expand(chi-Delta*tau)==0
    return {'ordinary_real_coordinate_determinant':'Delta(R)^3 tau^3',
            'Hilbert_Schmidt_coordinate_determinant':'8 Delta(R)^3 tau^3',
            'basis_independent_form':'8 [Im Tr(R2 T2 R T)]^3 in Hilbert-Schmidt coordinates',
            'off_diagonal_pair_determinants':['-tau','+tau','-tau'],
            'word_field_degrees':FIELD_DEGREES,'words':WORD_NAMES,
            'proof':'Exact symbolic Vandermonde factors and generic Hermitian off-diagonal identities; no fitted eigenprojector coefficients.'}


def adjusted_frame(masses,ys,ms,vev):
    q=[doublet_weights(v,y,m,vev) for v,y,m in zip(masses,ys,ms)];qu,qd=q
    reference=standard_CKM();target=[abs(reference[0,1]),abs(reference[1,2]),abs(reference[0,2]),
       float(np.imag(reference[0,1]*reference[1,2]*reference[0,2].conjugate()*reference[1,1].conjugate()))]
    s13=target[2]/(qu[0]*qd[2]);c13=np.sqrt(1-s13*s13)
    s12=target[0]/(qu[0]*qd[1]*c13);s23=target[1]/(qu[1]*qd[2]*c13)
    c12,c23=np.sqrt(1-np.array([s12,s23])**2)
    sine=target[3]/(qu[0]**2*qu[1]**2*qd[1]**2*qd[2]**2*s12*s23*s13*c12*c23*c13**2)
    if not 0<sine<1:raise ValueError('Finite-current target outside the chosen branch')
    delta=np.arcsin(sine);V=standard_CKM(s12,s13,s23,delta)
    return V,q,target,[float(s12),float(s13),float(s23),float(delta)]


def coupling_certificate():
    c=character_certificate();assert c['exact_character_multiplicities']['triplet_adjoint_triplet']==1
    terms=[]
    for sector,charge in [('up',(1,0)),('down',(0,1))]:
        for right,rcharge in [('bare',(0,0)),('heavy',charge)]:
            if rcharge==charge:terms.append({'sector':sector,'right':right,'field':'identity'})
            for sf,scharge in [('up',(1,0)),('down',(0,1))]:
                for name in ['eta','nonet_singlet','nonet_adjoint']:
                    if tuple((a+b)%2 for a,b in zip(charge,rcharge))==scharge:
                        terms.append({'sector':sector,'right':right,'field':name+'_'+sf})
        terms.append({'sector':sector,'right':'bare','field':'Higgs'})
    assert len(terms)==10
    return {'group_order':c['group_order'],'enumerated_fermion_contractions':terms,'symmetry':'3.A6_u and Z2_up x Z2_down and generalized CP, with the retained scalar source groups',
      'ordinary_quarks':'neutral 3_u','up_vectorlike_triplet':'3_u, odd only under Z2_up',
      'down_vectorlike_triplet':'3_u, odd only under Z2_down',
      'new_scalar_content':'one real Hermitian nonet and one real singlet per sector, odd under its corresponding Z2',
      'renormalizable_contractions_per_sector':['y Q-Higgs-q_R','m Psi_L-Psi_R','g eta Psi_L-q_R','c_s Tr(H)/3 Psi_L-q_R','c_a H_traceless Psi_L-q_R'],
      'independent_real_coefficients_per_sector':5,
      'forbidden_at_renormalizable_order':['Q-Higgs-Psi_R','constant Psi_L-q_R','wrong-sector eta or H insertion','H or eta insertion in Psi_L-Psi_R'],
      'scope':'Complete renormalizable fermion census on this declared field content; derivative and higher scalar insertion operators are separate.'}


def affine_spectrum_search(L,A,ys,ms,vev,light,rscale,tscale):
    """Restrict C_f to I,R,T and determine it from masses alone.

    The exact rational sextic and isolating intervals certify every real
    source-ratio branch for the decimal-input fixture. No CKM target enters.
    """
    from perfectpower.flavor_completion import physical_chart
    def rational_matrix(M):
        return sy.Matrix([[sy.Rational(str(v.real))+sy.I*sy.Rational(str(v.imag)) for v in row] for row in M])
    L,A=rational_matrix(L),rational_matrix(A);R=A*A.conjugate().T/sy.Rational(str(rscale));T=L*L.conjugate().T/sy.Rational(str(tscale))
    R-=sy.trace(R)/3*sy.eye(3);T-=sy.trace(T)/3*sy.eye(3)
    invariants=[sy.trace(R*R),sy.trace(R*T),sy.trace(T*T),R.det(),sy.trace(R*R*T),sy.trace(R*T*T),T.det()]
    assert all(sy.expand(sy.im(v))==0 for v in invariants)
    r2,rt,t2,dR,pRRT,pRTT,dT=[sy.expand(sy.re(v)) for v in invariants]
    t=sy.symbols('t');g=r2+2*rt*t+t2*t*t;f=dR+pRRT*t+pRTT*t*t+dT*t**3
    sectors=[];frames=[]
    for sector,y,m,masses in zip(['up','down'],ys,ms,light):
        magnitudes=[sy.Rational(str(v)) for v in source_for_light_masses(masses,y,m,vev)]
        branches=[];vectors=[];sign_search=[]
        with mp.workdps(80):
            conv=lambda v:mp.mpf(str(sy.N(v,85)))
            RR=mp.matrix([[complex(0) for _ in range(3)] for _ in range(3)]);TT=RR.copy()
            for i in range(3):
                for j in range(3):
                    RR[i,j]=mp.mpc(str(sy.N(sy.re(R[i,j]),85)),str(sy.N(sy.im(R[i,j]),85)))
                    TT[i,j]=mp.mpc(str(sy.N(sy.re(T[i,j]),85)),str(sy.N(sy.im(T[i,j]),85)))
            for signs in [(1,1,1),(1,1,-1),(1,-1,1),(1,-1,-1)]:
                h=[sign*v for sign,v in zip(signs,magnitudes)]
                mean=sum(h)/3;center=[v-mean for v in h];q=sum(v*v for v in center);d=sy.prod(center)
                P=sy.Poly(sy.expand(q**3*f*f-d*d*g**3),t,domain=sy.QQ)
                intervals=P.intervals(eps=sy.Rational(1,10**35))
                for (lo,hi),multiplicity in intervals:
                    value=conv((lo+hi)/2);gv=conv(g.subs(t,(lo+hi)/2));fv=conv(f.subs(t,(lo+hi)/2))
                    a=mp.sign(conv(d)/fv)*mp.sqrt(conv(q)/gv);b=value*a
                    C=conv(mean)*mp.eye(3)+a*RR+b*TT;ev,U=mp.eighe(C)
                    order=[min(range(3),key=lambda j:abs(ev[j]-conv(v))) for v in h];assert len(set(order))==3
                    err=max(abs(ev[j]/conv(v)-1) for j,v in zip(order,h))
                    frame=mp.matrix([[U[i,j] for j in order] for i in range(3)])
                    branches.append({'signs':list(signs),'ratio':float(value),'a0':float(conv(mean)-a*conv(sy.trace(A*A.conjugate().T/sy.Rational(str(rscale)))/3)-b*conv(sy.trace(L*L.conjugate().T/sy.Rational(str(tscale)))/3)),
                                     'a1':float(a),'a2':float(b),'root_interval':[str(lo),str(hi)],'root_multiplicity':int(multiplicity),
                                     'source_eigenvalue_relative_residual_80_digits':float(err)})
                    vectors.append(array(frame))
                at_infinity=sy.simplify(q**3*dT*dT-d*d*t2**3)==0
                assert not at_infinity,'Exceptional pure-T branch requires explicit handling'
                sign_search.append({'signs':list(signs),'sextic_degree':int(P.degree()),'rational_sextic_coefficients':[str(c) for c in P.all_coeffs()],
                                    'exact_real_root_count':int(P.count_roots(-sy.oo,sy.oo)),'pure_T_branch':False})
        sectors.append({'sector':sector,'sign_search':sign_search,'branches':branches,
                        'total_branches':len(branches),'overall_sign_equivalence':'C and -C give the same masses and current magnitudes; the heaviest-mixing eigenvalue is fixed positive.'})
        frames.append(vectors)
    pairs=[]
    for i,U in enumerate(frames[0]):
        for j,D in enumerate(frames[1]):
            V=U.conj().T@D;qu,qd=[doublet_weights(v,y,m,vev) for v,y,m in zip(light,ys,ms)];current=qu[:,None]*V*qd[None,:]
            pairs.append({'up_branch':i,'down_branch':j,'decoupling_observables':physical_chart(V),'abs_CKM':abs(V).tolist(),
                          'abs_finite_light_current':abs(current).tolist(),
                          'finite_CP_quartet':float(np.imag(current[0,1]*current[1,2]*current[0,2].conjugate()*current[1,1].conjugate()))})
    return {'restricted_source_space':['I','R','T'],'sectors':sectors,'branch_pairs':pairs,
            'uses_CKM_targets':False,'scope':'All real branches on a specified affine source-center slice, with fixed source vacuum, Higgs coefficients, messenger masses and illustrative mass inputs. The slice is not enforced against the other allowed scalar-center or kinetic operators.'}


def source_jacobian(w,coefficients,rscale,tscale):
    # Matrix polynomials are differentiated in canonical physical coordinates.
    J=np.zeros((18,71));h=1e-5
    def source(z):
        L,A,_,_=fields(z);R=A@A.conj().T/rscale;T=L@L.conj().T/tscale
        return [evaluate_polynomial(R,T,c) for c in coefficients]
    with mp.workdps(90):
        for i in range(70):
            e=np.eye(70)[i]*h
            plus=source(w+e);minus=source(w-e)
            for sector in range(2):
                difference=(plus[sector]-minus[sector])/(2*h*COORDINATE_SCALES[i])
                J[9*sector:9*sector+9,i]=np.array([float(v) for v in hermitian_coordinates(matrix(difference))])
    return J


def protected_fixed_mass_response(R,T,Cmat,ys,ms,vev):
    """Vary allowed scalar-center coefficients; retain canonical fermions.

    Every branch keeps the six exact finite masses and the analytic one-loop
    phase theorem. Only the explicitly declared center coefficients change.
    """
    from scipy.linalg import expm
    from itertools import combinations
    rows=[];response=[];step=1e-4
    actual=lambda c:current_pair(*[block_spectrum(C,y,m,vev) for C,y,m in zip(c,ys,ms)])
    def chart(current):
        V=current['V'];return np.array([abs(V[0,1]),abs(V[1,2]),abs(V[0,2]),current['CP_quartet']])
    ref=actual(Cmat);refm=[block_spectrum(C,y,m,vev)['masses'][:3] for C,y,m in zip(Cmat,ys,ms)]
    for i,j in combinations(range(3),2):
        for imaginary in [False,True]:
            generator=np.zeros((3,3),complex)
            generator[i,j]=1j if imaginary else 1;generator[j,i]=1j if imaginary else -1
            pair=[]
            for sign in [-1,1]:
                W=expm(sign*step*generator);C=W@Cmat[1]@W.conj().T;C=(C+C.conj().T)/2
                H=nonet_target(C);cal=polynomial_calibration(R,T,H);fit=nonet_mix(cal['matrix'])
                cur=actual([Cmat[0],fit]);values=chart(cur);pair.append(values)
                residual=max(np.max(abs(block_spectrum(c,y,m,vev)['masses'][:3]/old-1)) for c,y,m,old in zip([Cmat[0],fit],ys,ms,refm))
                rows.append({'plane':[i,j],'imaginary_generator':imaginary,'angle':sign*step,'observables':values.tolist(),
                             'finite_six_mass_relative_residual':float(residual),
                             'source_polynomial_target_error_90_digits':cal['target_error'],
                             'source_polynomial_coefficients':cal['coefficients'],
                             'tree_and_one_loop_phase_theorem_preserved':True})
            response.append((pair[1]-pair[0])/(2*step))
    J=np.array(response).T/chart(ref)[:,None];J/=np.linalg.norm(J,axis=0)
    sv=np.linalg.svd(J,compute_uv=False)
    return {'branches':rows,'fractional_column_normalized_response_singular_values':sv.tolist(),
            'scope':'Full finite-spectrum masses fixed, canonical fermion metrics and all five real fermion coefficients unchanged. Allowed degree-at-most-eight scalar-center coefficients move four physical weak directions while preserving exact tree and one-loop mass-phase cancellation.'}


def main():
    seed=np.array(json.loads((OUT/'valentiner_adjoint_uv.json').read_text())['vacuum']['field_coordinates'])
    projectors,_=quartic_projectors();vev=.03;w,H0,stationarity=branch(seed,projectors,vev)
    L,A,_,_=fields(w);rscale=float(np.trace(A@A.conj().T).real);tscale=float(np.trace(L@L.conj().T).real)
    R=A@A.conj().T/rscale;T=L@L.conj().T/tscale
    ys=[1.2,.57];ms=[1.,1.];Y=[np.array([1e-5,.003,.9]),np.array([2e-5,.0004,.02])]
    light=[vev*v for v in Y];V,q,target,angles=adjusted_frame(light,ys,ms,vev)
    rows=[];spectra=[];Cmat=[];coefficients=[]
    for sector,masses,y,m,U in zip(['up','down'],light,ys,ms,[np.eye(3),V]):
        cvalues=source_for_light_masses(masses,y,m,vev);C=U@np.diag(cvalues)@U.conj().T;C=(C+C.conj().T)/2
        H=nonet_target(C);cal=polynomial_calibration(R,T,H);fitted=nonet_mix(cal['matrix'])
        spectra.append(block_spectrum(fitted,y,m,vev));Cmat.append(fitted);coefficients.append(cal['coefficients'])
        rows.append({'sector':sector,'bare_y':y,'messenger_mass':m,'target_light_masses':masses.tolist(),
                     'Hermitian_mixing_eigenvalues':cvalues.tolist(),'nonet_eigenvalues':np.linalg.eigvalsh(H).tolist(),
                     'source_polynomial_coefficients':cal['coefficients'],'source_polynomial_target_error_90_digits':cal['target_error'],
                     'maximum_absolute_source_coefficient':cal['maximum_absolute_coefficient'],
                     'actual_light_mass_relative_residual':float(np.max(abs(spectra[-1]['masses'][:3]/masses-1))),
                     'all_six_masses':spectra[-1]['masses'].tolist(),
                     'positive_tree_determinant':float((vev*y*m)**3)})
    current=current_pair(*spectra);observed=[abs(current['V'][0,1]),abs(current['V'][1,2]),abs(current['V'][0,2]),current['CP_quartet']]
    residual=float(max(abs(np.array(observed)/np.array(target)-1)))
    # Explicit universal local stability certificate for the added nonets.
    J=source_jacobian(w,coefficients,rscale,tscale);values=[]
    for c in coefficients:values.append(evaluate_polynomial(R,T,c))
    J=np.column_stack([J,np.r_[np.array([float(v) for v in hermitian_coordinates(matrix(values[0]))]),np.zeros(9)],
                         np.r_[np.zeros(9),np.array([float(v) for v in hermitian_coordinates(matrix(values[1]))])]])
    A0=np.zeros((73,73));A0[:71,:71]=H0;A0[71:,71:]=8*np.eye(2)
    norm=float(np.linalg.norm(J,2));lower=float(min(np.linalg.eigvalsh(A0)[0],1.)/(1+norm)**2)
    # Random scalar mass mixing tests the theorem independently of a selected
    # scalar spectrum. The proof works for every real scalar mixing matrix.
    nonet=np.concatenate([np.eye(3)[None,:,:]/np.sqrt(3),BASIS]);rng=np.random.default_rng(91056);loopchecks=[]
    for sector,y,m in zip(['up','down'],ys,ms):
        Z=rng.normal(size=(3,3))+1j*rng.normal(size=(3,3));C=(Z+Z.conj().T)/2
        spec=block_spectrum(C,y,m,.3);g=neutral_vertices(nonet,y);mix=rng.normal(size=(91,11));G=np.einsum('ab,bij->aij',mix,g)
        scalar_hessian=np.diag(np.linspace(.4,4.,91));result=scalar_threshold(spec['mass_matrix'],G,scalar_hessian)
        reality=paired_vertex_reality(spec,G)
        loopchecks.append({'sector':sector,'scalar_modes':91,'one_loop_phase_numerical_error':result['delta_theta'],
                           'individual_vertex_pair_reality_relative_error':reality,
                           'UV_phase_coefficient_numerical_error':result['UV_phase_coefficient']})
    partner=current_pair(*[block_spectrum(C.conj(),y,m,vev) for C,y,m in zip(Cmat,ys,ms)])
    fittedCP=float(current['CP_quartet']);cp_residual=abs(partner['CP_quartet']+fittedCP)
    result={'schema':'pp-valentiner-hermitian/1','input_vacuum_receipt':'valentiner_adjoint_uv.json',
       'polynomial_basis_exact_certificate':symbolic_certificate(),'renormalizable_fermion_certificate':coupling_certificate(),
       'base_joint_vacuum':stationarity,'base_field_coordinates':w.tolist(),'polynomial_normalizations':{'R_scale':rscale,'T_scale':tscale},
       'scalar_lock':{'new_real_nonet_components':18,'new_real_odd_singlets':2,'physical_neutral_scalar_total':91,
                     'potential':'V_base + sum_f [Tr(H_f-eta_f F_f)^2/2 + (eta_f^2-1)^2]',
                     'maximum_elementary_scalar_degree':18,'matched_odd_singlet_values':[1.,1.],
                     'source_jacobian_spectral_norm':norm,'positive_full_Hessian_eigenvalue_lower_bound':lower,
                     'proof':'delta x^T A0 delta x + ||delta H-J delta x||^2; A0 positive. Congruence lower bound min(lambda_min(A0),1)/(1+||J||)^2.',
                     'scope':'Exact local positivity and unchanged base stationary point of the specified squared-lock scalar EFT, not global selection or a renormalizable scalar UV completion.'},
       'finite_spectrum_fit':{'vev':vev,'sectors':rows,'four_physical_current_targets':target,
                              'four_physical_current_outputs':list(map(float,observed)),'maximum_relative_target_residual':residual,
                              'abs_full_light_current':abs(current['V']).tolist(),'CP_quartet':fittedCP,
                              'row_deficit_eigenvalues':np.linalg.eigvalsh(current['row_deficit']).tolist(),
                              'column_deficit_eigenvalues':np.linalg.eigvalsh(current['column_deficit']).tolist(),
                              'calibrated_source_frame_angles':angles,
                              'CP_partner_quartet':partner['CP_quartet'],'CP_partner_residual':cp_residual,
                              'scope':'Six illustrative hierarchical masses and four PDG-2026-derived physical-current targets matched at finite vev. Source polynomial coefficients are fitted inputs, not a prediction of the golden relation.'},
       'one_loop_theorem':{'scalar_phase_exact':'zero for every real neutral scalar mixing and positive scalar spectrum',
                          'proof':'In the eigenbasis of Hermitian C, D is three real 2x2 blocks. Each scalar vertex is a real block coefficient times a Hermitian flavor matrix, plus a flavor-diagonal real Higgs vertex. Every paired G_ik G_ki is real, so each diagonal chirality-changing self-energy has zero phase separately.',
                          'numerical_tests':loopchecks,'scope':'Canonical bare metrics and the complete five-coefficient renormalizable fermion action; higher fermion operators and two-loop corrections are not covered.'},
       'prediction_boundary':{'source_center_coefficients_are_independent':True,'low_degree_kinetic_basis_also_allowed':True,
                              'golden_relation_derived':False,'frame_statement':'At fixed source centers, all allowed five-coefficient renormalizable fermion variations preserve their source eigenframes. Higher kinetic terms can change them.'},
       'protected_fixed_mass_response':protected_fixed_mass_response(R,T,Cmat,ys,ms,vev),
       'mass_only_affine_candidate_search':affine_spectrum_search(L,A,ys,ms,vev,light,rscale,tscale),
       'references':{'rank_saturation_prior':'https://arxiv.org/abs/2312.13349',
                     'one_loop_NB_prior':'https://doi.org/10.1007/JHEP09(2025)162',
                     'CKM_reference':'https://pdg.lbl.gov/2026/reviews/rpp2026-rev-ckm-matrix.pdf'}}
    assert residual<1e-8 and lower>0 and cp_residual<1e-12
    assert all(abs(c['one_loop_phase_numerical_error'])<1e-10 for c in loopchecks)
    (OUT/'valentiner_hermitian.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'current_fit_relative_error':residual,'light_mass_relative_errors':[r['actual_light_mass_relative_residual'] for r in rows],
                      'J':fittedCP,'Hessian_positive_lower_bound':lower,'loop_checks':loopchecks},indent=2))


if __name__=='__main__':main()
