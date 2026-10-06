"""Shared mediator matching, fermion-safe UV completion and scalar-loop closure."""
from pathlib import Path
from fractions import Fraction
import json
import numpy as np
from scipy.linalg import qr
from scipy.optimize import root
from copy import deepcopy
from perfectpower.nonet_potential import *
from perfectpower.nonet_mediators import *
from perfectpower.quartic_renormalization import *
from perfectpower.flavor_hermitian import paired_vertex_reality
from perfectpower.flavor_quantum import scalar_threshold
from develop_valentiner_nonet_joint import hessian,frame_and_spectrum,source_jacobian,source_eigenvalues
from valentiner_adjoint_quartics import quartic_projectors,adjoint,symmetric_square,BASIS
from develop_valentiner_frames import generators,group_closure,numeric
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'receipts/m22_interactions'


def scalar_vertices(count,sector):
    G=np.zeros((count,6,6),complex);j=10*sector
    G[j,3:,:3]=.1*np.eye(3);G[j+1,3:,:3]=.7*np.eye(3)
    G[j+2:j+10,3:,:3]=.8*BASIS;G[20,:3,:3]=[1.2,.57][sector]*np.eye(3)/np.sqrt(2)
    return G


def build():
    previous=json.loads((OUT/'valentiner_nonet_joint.json').read_text());z=np.array(previous['canonical_coordinates']);c=np.array(previous['coefficients'])
    portals=np.array(previous['Higgs_portals']);mu2=previous['Higgs_mu2'];P,pcert=quartic_projectors();P=np.array(P)
    fun=lambda z:joint_higgs(z,c,P,portals,mu2);H=hessian(fun,z);obs,sectors,V=frame_and_spectrum(z)
    rng=np.random.default_rng(512);points=rng.normal(size=(128,20));design=np.array([operators(x,P)[0][8:] for x in points])
    completions={};plans={}
    for mode,finite_only in [('universal',False),('fermion_safe_finite',True)]:
        plan=mediation_plan(c,P,finite_only=finite_only,sector_ratios=(1.1,.8,1.3) if finite_only else (1.,1.,1.));plans[mode]=plan
        J,D=currents(z[:20],plan,P);DD=np.column_stack([D,np.zeros(len(D))]);HV=completed_hessian(H,DD,plan['mass'])
        ev,O=np.linalg.eigh(HV);comp=[]
        for x in points:
            jj,_=currents(x,plan,P);comp.append(jj@jj/(2*plan['mass']**2))
        added=np.linalg.lstsq(design,comp,rcond=None)[0];contact=c[8:]+added
        cross=contact[-3:] if finite_only else contact[24:]
        closure_error=float(np.max(abs(cross)));assert closure_error<1e-10
        loops=[]
        for f,s in enumerate(sectors):
            G=scalar_vertices(len(HV),f);rot=np.einsum('ik,ijl->kjl',O,G);loops.append(paired_vertex_reality(s,rot))
        groups=[]
        for g in plan['groups']:
            rec={k:(v.tolist() if isinstance(v,np.ndarray) else v) for k,v in g.items() if k!='embedding'}
            groups.append(rec)
        completions[mode]={'neutral_scalar_count':len(HV),'real_mediator_count':len(J),'mass':plan['mass'],
          'groups':groups,'mediator_vacuum':(-J/plan['mass']**2).tolist(),'source_contact_coefficients':contact.tolist(),
          'matching_contact_cross_residual':closure_error,'full_Hessian_minimum':float(ev[0]),
          'one_loop_paired_vertex_reality_with_new_fermion_vertices_zero':max(loops),
          'source_observables_identical':obs,
          'scope':'Positive Gaussian-square completion of declared source coefficients; additional symmetry-allowed scalar interactions have zero chosen coefficients. Not a symmetry-enforced prediction.'}
        schur=HV[:21,:21]-HV[:21,21:]@np.linalg.solve(HV[21:,21:],HV[21:,:21])
        completions[mode]['full_Hessian_schur_error']=float(np.max(abs(schur-H)))
        assert ev[0]>0 and max(loops)<1e-12
        if not finite_only:
            # An allowed ordinary-adjoint heavy-mass Yukawa is equivariant
            # with one real coefficient for its whole eight-dimensional copy.
            offset=21+plan['groups'][0]['certificate']['rank'];eta,s0,A0=nonet_fields(z[:20])[0]
            M=np.eye(3)+.05*np.einsum('a,aij->ij',-J[offset-21:offset-21+8]/plan['mass']**2,BASIS)
            C=.1*eta*np.eye(3)+.7*s0*np.eye(3)+.8*A0
            DDferm=np.block([[.03*1.2*np.eye(3),np.zeros((3,3))],[C,M]])
            G=scalar_vertices(len(HV),0);G[offset:offset+8,3:,3:]=.05*BASIS
            threshold=scalar_threshold(DDferm,G,HV)
            completions[mode]['allowed_adjoint_heavy_Yukawa_test']={'real_coefficient':.05,'tree_determinant':str(np.linalg.det(DDferm)),
              'one_loop_mass_phase':threshold['delta_theta'],'UV_phase_coefficient':threshold['UV_phase_coefficient'],
              'relative_correction_norm':threshold['relative_correction_norm'],
              'scope':'Actual completed scalar Hessian and equivariant ordinary-adjoint heavy-mass vertex. Neutral-scalar mass threshold only, not a complete gauge matching calculation.'}
    # The complete scalar quartic one-loop multiplication is reusable.
    vv=lambda x:tuple(v[8:] for v in operators(x,P))
    algebra,certificate=compile_loop_algebra(vv,20,52)
    sparse=[];max_rational_error=0
    for k,i,j in np.argwhere(abs(algebra)>1e-8):
        if j<i:continue
        q=Fraction(float(algebra[k,i,j])).limit_denominator(10000);err=abs(float(q)-algebra[k,i,j]);max_rational_error=max(max_rational_error,err)
        sparse.append([int(k),int(i),int(j),str(q)])
    tables={'operator_names':OPERATOR_NAMES[8:],'nonzero_symmetric_products':sparse,
            'maximum_rational_reconstruction_error':max_rational_error,
            'scope':'Rational coefficient candidates reconstructed from numerical polynomial contractions, with off-grid identity checks; not exact symbolic finite-group tensors.'}
    (OUT/'nonet_scalar_loop_algebra.json').write_text(json.dumps(tables,indent=2,sort_keys=True)+'\n')
    closures={}
    for name,seeds in [('radial',[18,30]),('one_finite_channel',[18,30,57]),('three_finite_channels',[18,30,57,58,59])]:
        B,cc=generated_subalgebra(algebra,np.eye(52)[np.array(seeds)-8]);cc['seeds']=[OPERATOR_NAMES[i] for i in seeds]
        cc['support']=[OPERATOR_NAMES[i+8] for i in range(52) if np.linalg.norm(B[i])>1e-5];closures[name]=cc
    su3_seed=np.zeros(52);su3_seed[49:52]=1
    _,su3_closure=generated_subalgebra(algebra,np.vstack([np.eye(52)[10],np.eye(52)[22],su3_seed]))
    closures['SU3_unified_27']=su3_closure
    # The previous mass-preserving response applies to mediated as well as
    # direct coefficients, because the Gaussian source Schur complement is H.
    shifted=c.copy();shifted[:8]+=.03**2*portals;HQ=np.einsum('m,mij->ij',shifted,polynomial_hessians(lambda x:operators(x,P)[1],z[:20],step=.25));grad=operators(z[:20],P)[1]
    E=source_jacobian(z[:20]);DQ=-np.linalg.solve(HQ,grad[:8].T);DG=-np.linalg.solve(HQ,grad[32:].T)
    T=E@DQ;chosen=qr(T,pivoting=True)[2][:6];FIX=DG-DQ[:,chosen]@np.linalg.solve(T[:,chosen],E@DG)
    def physical_response(directions):
        eps=1e-6
        return np.column_stack([(np.array(frame_and_spectrum(np.r_[z[:20]+eps*dx,z[20]])[0]['squared_magnitudes'])-
                                 np.array(frame_and_spectrum(np.r_[z[:20]-eps*dx,z[20]])[0]['squared_magnitudes']))/(2*eps) for dx in directions.T])
    R=physical_response(FIX)
    # Rank-one trees can still retain all four physical directions. Tangent
    # spaces are evaluated as candidate coupling restrictions at this vacuum,
    # rather than claiming this non-rank-one benchmark satisfies their minors.
    safe_response=R[:,-3:]
    tangent=np.zeros((28,20));gu=np.arange(1,5)*.1;gd=np.array([.4,-.3,.2,-.1]);au=np.array([.1,.3,-.2]);ad=np.array([.2,-.1,.4])
    for i in range(4):
        for j in range(4):tangent[4*i+j,i]=-gd[j];tangent[4*i+j,4+j]=-gu[i]
    for i in range(3):
        for j in range(3):tangent[16+3*i+j,8+i]=-ad[j];tangent[16+3*i+j,11+j]=-au[i]
    for i in range(3):tangent[25+i,14+2*i]=-1;tangent[25+i,15+2*i]=-.5
    # Use only actual direct/mediated finite directions for the physical rank;
    # the off-locus rank-one tangent is an algebraic parameter diagnostic.
    finite_singular=np.linalg.svd(safe_response,compute_uv=False)
    # Vary actual UV current coefficients, holding UV source contacts fixed.
    safe=plans['fermion_safe_finite'];current_derivatives=[]
    for x in points:
        up=sector_features(x[:10],P);down=sector_features(x[10:],P);row=[]
        for g in safe['groups']:
            u=g['embedding'].T@up[4];d=g['embedding'].T@down[4];j=g['up']*u+g['down']*d
            row.extend([-j@u/safe['mass']**2,-j@d/safe['mass']**2])
        current_derivatives.append(row)
    L=np.linalg.lstsq(design,current_derivatives,rcond=None)[0]
    DGuv=-np.linalg.solve(HQ,grad[8:].T@L);DGuv-=DQ[:,chosen]@np.linalg.solve(T[:,chosen],E@DGuv)
    Ruv=physical_response(DGuv);uv_singular=np.linalg.svd(Ruv,compute_uv=False);uv_checks=[]
    base_contact=np.array(completions['fermion_safe_finite']['source_contact_coefficients'])
    for column in qr(Ruv,pivoting=True)[2][:4]:
        epsilon=2e-6;sides=[]
        for sign in [-1,1]:
            trial=deepcopy(safe);group=trial['groups'][column//2];key='up' if column%2==0 else 'down';group[key]+=sign*epsilon
            comp=[]
            for x in points:
                jj,_=currents(x,trial,P);comp.append(jj@jj/(2*trial['mass']**2))
            cc=c.copy();cc[8:]=base_contact-np.linalg.lstsq(design,comp,rcond=None)[0]
            target=source_eigenvalues(z[:20])
            def equations(w):
                coefficients=cc.copy();coefficients[chosen]+=w[20:];coefficients[:8]+=.03**2*portals
                return np.r_[potential(w[:20],coefficients,P)[1],source_eigenvalues(w[:20])-target]
            w0=np.r_[z[:20]+sign*epsilon*DGuv[:,column],np.zeros(6)]
            sol=root(equations,w0,tol=1e-10);err=float(np.max(abs(equations(sol.x))));assert err<1e-9
            zz=np.r_[sol.x[:20],z[20]];rr,ss,_=frame_and_spectrum(zz)
            coeff=cc.copy();coeff[chosen]+=sol.x[20:];new_mu=2*.13*.03**2+operators(zz[:20],P)[0][:8]@portals
            HS=hessian(lambda t:joint_higgs(t,coeff,P,portals,new_mu),zz)
            _,ddd=currents(zz[:20],trial,P);HU=completed_hessian(HS,np.column_stack([ddd,np.zeros(len(ddd))]),trial['mass'])
            sides.append({'sign':sign,'equation_residual':err,'depth':rr['depth'],'J':rr['J'],'squared_magnitudes':rr['squared_magnitudes'],
                          'complete_mass_change':float(max(np.max(abs(s['masses']-base['masses'])) for s,base in zip(ss,sectors))),
                          '48_scalar_Hessian_minimum':float(np.linalg.eigvalsh(HU)[0])})
        fd=(np.array(sides[1]['squared_magnitudes'])-np.array(sides[0]['squared_magnitudes']))/(2*epsilon)
        uv_checks.append({'coupling':int(column),'group':safe['groups'][column//2]['name'],'sector':key,'sides':sides,
                          'finite_response':fd.tolist(),'implicit_response':Ruv[:,column].tolist(),
                          'relative_response_error':float(np.linalg.norm(fd-Ruv[:,column])/max(np.linalg.norm(Ruv[:,column]),1e-30))})
    Fuv=np.array([v['finite_response'] for v in uv_checks]).T;Iuv=np.array([v['implicit_response'] for v in uv_checks]).T
    uv_rank={'finite_singular_values':np.linalg.svd(Fuv,compute_uv=False).tolist(),
             'finite_implicit_error_spectral_norm':float(np.linalg.norm(Fuv-Iuv,2))}
    assert uv_rank['finite_implicit_error_spectral_norm']<uv_rank['finite_singular_values'][-1]
    beta=loop_product(algebra,c[8:],c[8:]);DX=-np.linalg.solve(HQ,grad[8:].T@beta)
    DX-=DQ[:,chosen]@np.linalg.solve(T[:,chosen],E@DX)
    eps=1e-7;plus=frame_and_spectrum(np.r_[z[:20]+eps*DX,z[20]])[0];minus=frame_and_spectrum(np.r_[z[:20]-eps*DX,z[20]])[0]
    loop_drift={'quartic_beta_coefficients_16pi2':beta.tolist(),'fixed_mass_depth_response_16pi2':float((plus['depth']-minus['depth'])/(2*eps)),
               'fixed_mass_J_response_16pi2':float((plus['J']-minus['J'])/(2*eps)),
               'scope':'Sensitivity to the scalar-only quartic counterterm with compensating quadratic parameters, not a complete physical CKM renormalization group evolution.'}
    result={'matching_certificates':exact_mediator_certificates(),'complete_finite_mediator_scalar_census':exact_finite_mediator_operator_census(),
      'soft_mediator_counterterm_certificate':exact_soft_mediator_counterterm_certificate(),'heavy_vertex_exact_counterexample':exact_heavy_vertex_counterexample(),
      'completions':completions,'projector_certificate':pcert,'scalar_loop_compilation':certificate,
      'rational_table_maximum_error':max_rational_error,'scalar_loop_subalgebras':closures,
      'exact_rank_one_running_certificate':exact_two_scalar_rank_certificate(),
      'finite_mediated_fixed_mass_response_singular_values':finite_singular.tolist(),
      'finite_mediated_fixed_mass_observable_response':safe_response.tolist(),
      'single_mediator_mixed_parameter_Jacobian_rank':int(np.linalg.matrix_rank(tangent)),
      'six_UV_current_coupling_fixed_mass_response_singular_values':uv_singular.tolist(),
      'six_UV_current_coupling_finite_checks':uv_checks,'six_UV_current_coupling_finite_rank_check':uv_rank,
      'SU3_27_projector_rank':round(np.trace(P[2]+P[3]+P[4])),'exact_SU3_27_certificate':exact_SU3_27_certificate(),
      'scalar_loop_fixed_mass_drift':loop_drift,
      'source_receipt':'valentiner_nonet_joint.json','scope':'Constructive matching and light-scalar counterterms. No derived golden CKM interaction; thresholds and complete UV operator census are distinct.',
      'sources':[{'title':'One-loop algebras and fixed flow trajectories in adjoint multi-scalar gauge theory','url':'https://arxiv.org/abs/2303.13884'},
                 {'title':'RG-stable parameter relations of a scalar field theory in absence of a symmetry','url':'https://arxiv.org/abs/2502.11011'}]}
    assert closures['one_finite_channel']['dimension']==9 and closures['radial']['dimension']==2 and su3_closure['dimension']==5
    assert max_rational_error<1e-8 and finite_singular[-1]>1e-6 and uv_singular[-1]>1e-6
    return result


def main():
    r=build();(OUT/'valentiner_mediator_closure.json').write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'completions':{k:{a:v[a] for a in ['neutral_scalar_count','full_Hessian_minimum','matching_contact_cross_residual']} for k,v in r['completions'].items()},
          'loop_subalgebras':r['scalar_loop_subalgebras'],'finite_response':r['finite_mediated_fixed_mass_response_singular_values'],'UV_response':r['six_UV_current_coupling_fixed_mass_response_singular_values'],
          'allowed_adjoint_Yukawa':r['completions']['universal']['allowed_adjoint_heavy_Yukawa_test']},indent=2))

if __name__=='__main__':main()
