"""Reproduce a stable joint flavor vacuum with universal source couplings."""
from pathlib import Path
from itertools import combinations
from fractions import Fraction as Q
import json
import numpy as np
import mpmath as mp
from valentiner_adjoint_uv import *
from valentiner_rank_lifting import hessian as source_hessian
from valentiner_adjoint_quartics import symmetric_square,adjoint
from valentiner_source_cp import cp_matrix,source_pair_cp_certificate
from develop_valentiner_frames import generators,group_closure,numeric,product as fp,conjugate,mul
from develop_valentiner_invariants import O,Z,add,sub,scale,exact_integer
from perfectpower.flavor_kinetic import KineticCovariants,fixed_spectrum_bare_metric,matrix,hermitian_function
from valentiner_label_operators import trace_candidates
from valentiner_joint_certificate import ModularComplex,modular_pivots

ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'receipts/m22_interactions'


def adjoint_character_certificate():
    group=group_closure(generators())[0];sums=[Z,Z,Z]
    for g in group:
        trace=lambda h:tuple(sum(Q(h[1][3*i+i][j],h[0]) for i in range(3)) for j in range(4))
        c=sub(fp(trace(g),conjugate(trace(g))),O);g2=mul(g,g);c2=sub(fp(trace(g2),conjugate(trace(g2))),O);g3=mul(g2,g);c3=sub(fp(trace(g3),conjugate(trace(g3))),O)
        h2=scale(add(fp(c,c),c2),Q(1,2));h3=scale(add(add(fp(fp(c,c),c),scale(fp(c,c2),3)),scale(c3,2)),Q(1,6))
        sums[0]=add(sums[0],fp(h2,conjugate(h2)));sums[1]=add(sums[1],h3);sums[2]=add(sums[2],fp(fp(c,c),c))
    dims=[exact_integer(scale(v,Q(1,1080))) for v in sums];assert dims==[6,1,2]
    return {'End_Sym2_adjoint_singlets':dims[0],'Sym3_adjoint_singlets':dims[1],'full_adjoint_cube_singlets':dims[2]}


def scalar_basis_certificate():
    rng=np.random.default_rng(661080);rows=[]
    for _ in range(60):
        x=np.array([ModularComplex(v) for v in rng.integers(-3,4,54)],object)
        degrees,names,values=trace_candidates(x,exact=True);rows.append(values)
    results=[]
    for d in [2,4,6]:
        idx=[i for i,v in enumerate(degrees) if v==d];rank,witness=modular_pivots(np.array(rows,dtype=np.int64)[:,idx]);assert rank==len(idx)
        results.append({'degree':d,'rank':rank,'evaluation_minor_rows':witness,'operators':[names[i] for i in idx]})
    return {'balanced_source_trace_basis':results,'prime':1000003,'CP_even_source_scalar_counts_through_six':{'2':3,'3':1,'4':12,'5':3,'6':47},
            'complete_renormalizable_scalar_counts_with_adjoint':{'quadratic':4,'cubic':1,'quartic':25,'total':30},
            'quartic_partition':{'source_and_link':12,'two_mediator_and_source_bilinear':7,'pure_mediator_CP_even':5,'linear_mediator_dressed_source':1},
            'scope':'Zero matter/Higgs slice. Source/link higher operators include the sextic breaking EFT. No claim of a complete all-degree EFT or full SM scalar action.'}


def independent_CP_invariant(yu,yd):
    with mp.workdps(80):
        U,D=matrix(yu),matrix(yd);Hu,Hd=U*U.H,D*D.H
        vu,_=mp.eighe(Hu);vd,_=mp.eighe(Hd)
        vand=lambda values:mp.fprod(values[j]-values[i] for i,j in combinations(range(3),2))
        det=mp.im(mp.det(Hu*Hd-Hd*Hu));J=det/(2*vand(vu)*vand(vd))
        return {'commutator_determinant_imaginary':mp.nstr(det,65),'J_from_weak_basis_invariant':mp.nstr(J,65)}


def cp_transform(w):
    x,t=uv_unpack(w);L,A,B=unpack(x);X=numeric(cp_matrix())
    C=np.einsum('aij,jk,bkl,il->ab',BASIS,X,BASIS.conj(),X.conj()).real
    return uv_pack(pack(X@L.conj()@X.conj().T,X@A.conj()@X.conj().T,X@B.conj()@X.conj().T),C@t.conj())


def svd_record(yu,yd):
    a,sa,_=np.linalg.svd(yu);b,sb,_=np.linalg.svd(yd);V=a[:,::-1].conj().T@b[:,::-1];r=physical_chart(V)
    r['spectra']=[sa[::-1].tolist(),sb[::-1].tolist()];return r


def fixed_mass_kinetic_test(w):
    yu,yd,V,obs,down=quarks(w);x,t=uv_unpack(w);L,A,B=unpack(x)
    null=down['null_map'];Y0=down['unnormalized_Y']
    frame=KineticCovariants((RHO*L)@(RHO*B),RHO*A)
    U,_,_=np.linalg.svd(yu);U=U[:,::-1];rows=[];responses=[]
    with mp.workdps(90):
        u=matrix(U);u=u*hermitian_function(u.H*u,lambda v:1/mp.sqrt(v));d=matrix(yd);Hd=d*d.H
        for i,j in combinations(range(3),2):
            for kind in ['real','imaginary']:
                g=mp.zeros(3)
                if kind=='real':g[i,j]=1;g[j,i]=-1
                else:g[i,j]=g[j,i]=mp.j
                pair=[]
                for sign in [-1,1]:
                    rot=u*mp.expm(mp.mpf(str(sign*1e-7))*g)*u.H;target=rot*Hd*rot.H
                    match=fixed_spectrum_bare_metric(Y0,null,target);completion=frame.positive_completion(match['bare_metric']);record=svd_record(yu,match['matched_Y']);pair.append(record)
                    rows.append({'plane':[i,j],'kind':kind,'rotation':sign*1e-7,'minimum_bare_metric_eigenvalue':match['minimum_bare_metric_eigenvalue'],
                                 'metric_operator_distance_from_identity':match['metric_operator_distance_from_identity'],'positive_completion_error':completion['error'],'target_H_error':match['target_H_error'],'observables':record})
                responses.append([(pair[1][k]-pair[0][k])/2e-7 for k in ['Vus','Vcb','Vub','J']])
    J=np.array(responses).T;scaled=J/np.array([abs(obs[k]) for k in ['Vus','Vcb','Vub','J']])[:,None];s=np.linalg.svd(scaled/np.linalg.norm(scaled,axis=0),compute_uv=False)
    residual=max(np.max(abs(np.log(np.array(r['observables']['spectra'])/np.array(obs['spectra'])))) for r in rows)
    assert s[-1]>.001 and residual<1e-7
    return {'metrics':rows,'four_response_singular_values':s.tolist(),'six_mass_max_log_residual':float(residual),'source_vacuum_and_superpotential_unchanged':True,
            'scope':'Allowed higher kinetic operators remain an independent UV input; this is a fixed-mass protection test, not a fit of CKM targets.'}


def main():
    projectors,pr=quartic_projectors();seed=json.loads((OUT/'valentiner_rank_cp_positive.json').read_text());x=np.array(seed['fields'])
    w=uv_pack(x,z_components(x));z,stationarity=solve(w,projectors);yu,yd,V,obs,down=quarks(z)
    partner=cp_transform(z);_,_,_,cpobs,_=quarks(partner)
    assert abs(obs['J'])>1e-6 and abs(obs['J']+cpobs['J'])<1e-12
    assert min(np.ravel(obs['spectra']))>1e-8 and stationarity['minimum_canonical_scalar_mass_squared']>0
    invariant=independent_CP_invariant(yu,yd);assert abs(float(invariant['J_from_weak_basis_invariant'])/obs['J']-1)<1e-7
    rng=np.random.default_rng(671970);direction=rng.normal(size=70);step=3e-6
    step=3e-5
    fd=(-potential(z+2*step*direction,projectors)[0]+8*potential(z+step*direction,projectors)[0]-8*potential(z-step*direction,projectors)[0]+potential(z-2*step*direction,projectors)[0])/(12*step)
    _,gradient=potential(z,projectors)
    cp_energy_error=abs(potential(partner,projectors)[0]-potential(z,projectors)[0])
    cp_stationarity=max(abs(potential(partner,projectors)[1]))
    deformation_cases=[]
    saved=float(DEFAULT_CROSS[2])
    try:
        for change in [-.01,.01]:
            DEFAULT_CROSS[2]=saved*(1+change)
            q,qr=solve(z,projectors);record=quarks(q)[3]
            assert abs(record['J'])>1e-6 and qr['minimum_canonical_scalar_mass_squared']>0
            deformation_cases.append({'operator':'Tr(LL-dagger AA-dagger)','coefficient_fractional_change':change,'stationarity':qr,'observables':record})
    finally:
        DEFAULT_CROSS[2]=saved
    result={'schema':'pp-valentiner-adjoint-uv/1','field_content':{'family_group':'3.A6_u x 3.A6_d x 3.A6_H x C6_A x C6_B x CP','complex_flavor_fields':35,'real_scalar_coordinates':70,
              'sources':['A=(3_u,3bar_H)','B=(3_d,3bar_H)'],'link':'L=(3_u,3bar_d)','mediator':'S=(1_u,1_d,8_H), charge (-1,+1)',
              'quark_column_couplings_per_sector':1},'scalar_operator_certificate':scalar_basis_certificate(),'adjoint_character_certificate':adjoint_character_certificate(),
            'mediator_quartic_projectors':pr,'parameters':{'epsilon':EPSILON,'source_penalties':list(PENALTIES),'radius_unit':RHO,'mediator_mass':MEDIATOR_MASS,'renormalizable_dressed_vertex_k':float(np.sqrt(EPSILON)*MEDIATOR_MASS*RHO**2),
              'mediator_quartic_coefficients':QUARTIC_COEFFICIENTS.tolist(),'mediator_source_quartic_coefficients':MASS_COEFFICIENTS.tolist(),'cross_source_coefficients':DEFAULT_CROSS[2:].tolist()},
            'radial_stabilizer':{'coefficient':RADIAL_STABILIZER,'flavor_field_degree':12,'invariant':'(N_L+N_A+N_B)^6','coercivity_proof':'The five positive mediator quartics sum to a positive lower bound times ||s||^4. Young inequality bounds the dressed quartic below by minus a constant times the squared total source norm after absorbing half this mediator quartic. Negative holomorphic source terms grow at most as the cubed total norm. The positive degree-twelve radial term dominates these terms, making the polynomial potential coercive. This proves existence of global minima, not that the retained CP-breaking minimum is global.'},
            'vacuum':{'field_coordinates':z.tolist(),'stationarity':stationarity,'observables':obs,'abs_CKM':abs(V).tolist(),'weak_basis_CP':invariant},
            'CP_partner':{'observables':cpobs,'energy_residual':cp_energy_error,'stationarity_max':float(cp_stationarity)},
            'derivative_directional_absolute_error':float(abs(fd-gradient@direction)),'fixed_mass_kinetic_test':fixed_mass_kinetic_test(z),
            'fully_reminimized_one_percent_UV_deformations':deformation_cases,
            'branch_search':'Numerical seed from a bounded 15-trial search over five prescribed ray-pair/penalty choices and three coupling strengths. The first retained full-rank physical-CP witness seeds full 70-field minimization. No golden coefficient, phase, mixing anchor or observed quark mass is used as a target.',
            'conclusion':'A specified CP-even joint source/link/adjoint potential with every allowed renormalizable scalar channel nonzero has a locally stable full-rank three-family vacuum and physical weak CP. Canonical heavy matching uses universal source couplings. CKM magnitudes do not fit observation and the golden relation is not enforced. Global energy selection, complete high-degree UV matching and radiative behavior remain open.'}
    result['quark_matching_scope']='Ordinary Dirac messengers in u,d,H family spaces, with both allowed orientations of the link and heavy-source vertices. The H-messenger phase charge permits the unique S-dagger bare-quark vertex in the up sector and S in the down sector. All ten mass/Yukawa coefficients per charge sector are nonzero real benchmark inputs. Canonical bare matter metrics remain an independent assumption; no all-degree or radiative UV completion is asserted.'
    result['quark_shared_adjoint_contractions']={'up_readout':'L B S-dagger','down_readout':'A S','triplet_adjoint_triplet_singlet_multiplicity':1,'heavy_modes_per_sector':9,'light_right_modes_per_sector':3,'independent_real_coefficients_per_sector':10,'coefficient_relations':'Representation fixes component contractions. Overall scalar and fermion coupling constants remain independent.'}
    result['source_seed_CP_geometry']={'group_column_indices':[19,36],'canonical_ray_pair':[5,36],'fixed_by_declared_CP_coset':False}
    (OUT/'valentiner_adjoint_uv.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print('stationarity',stationarity,'observables',obs,'kinetic',result['fixed_mass_kinetic_test']['four_response_singular_values'],flush=True)


if __name__=='__main__':main()
