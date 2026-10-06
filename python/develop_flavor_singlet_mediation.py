"""Exact insertion maps and a complete singlet/finite-mediator CP benchmark."""
from pathlib import Path
from fractions import Fraction as F
import json
import numpy as np
from perfectpower.flavor_insertion_running import *
from perfectpower.exact_nonet_algebra import certify_projectors,extended_quartics,verify_loop_table
from perfectpower.nonet_potential import operators,joint_higgs,nonet_fields
from perfectpower.nonet_mediators import mediation_plan,currents,completed_hessian
from perfectpower.nonet_spectral_matching import finite_scalar_poles
from perfectpower.flavor_hermitian import block_spectrum,paired_vertex_reality
from perfectpower.flavor_quantum import scalar_threshold
from develop_valentiner_nonet_joint import hessian
from develop_valentiner_mediator_closure import scalar_vertices
from valentiner_adjoint_quartics import quartic_projectors
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'receipts/m22_interactions'


def exact_singlet_matching_certificate():
    import sympy as s
    sigma,J,Fermion,h,M=s.symbols('sigma J F h M',real=True,nonzero=True)
    V=M*M*sigma*sigma/2+sigma*(J+h*Fermion)+J*J/(2*M*M)
    solution=-(J+h*Fermion)/(M*M);matched=s.factor(V.subs(sigma,solution))
    assert s.expand(matched+h*J*Fermion/(M*M)+h*h*Fermion**2/(2*M*M))==0
    return {'exact_Gaussian_stationary_field':str(solution),'matched_potential_with_source_contact':str(matched),
            'full_nonlocal_Lagrangian':'(J_source+sum h_f F_f)(M^2+Box)^-1(J_source+sum h_f F_f)/2 - J_source^2/(2 M^2)',
            'mass_matrix':'M_f=(m_f-h_f J_source/M^2) I','four_fermion_Lagrangian':'(sum h_f F_f)^2/(2 M^2)',
            'two_derivative_Lagrangian':'[partial(J_source+sum h_f F_f)]^2/(2 M^4)',
            'scope':'Exact Gaussian tree matching; derivative expansion holds below the mediator threshold. All correlated four-fermion and derivative operators are retained in the stated functional, not a one-loop finite EFT matching calculation.'}


def singlet_UV_benchmark(P):
    old=json.loads((OUT/'valentiner_nonet_joint.json').read_text());z=np.array(old['canonical_coordinates']);c=np.array(old['coefficients']);portals=np.array(old['Higgs_portals'])
    fun=lambda v:joint_higgs(v,c,P,portals,old['Higgs_mu2']);H=hessian(fun,z)
    plan=mediation_plan(c,P,finite_only=True,sector_ratios=(1.1,.8,1.3));J,D=currents(z[:20],plan,P);DD=np.column_stack([D,np.zeros(len(D))]);mass=plan['mass']
    coefficients=np.array([.10,-.12,.07,.08,.05,.09,-.06,.11,.04]);v,g=operators(z[:20],P);q=np.r_[v[:8],z[20]**2/2];dq=np.zeros((9,21));dq[:8,:20]=g[:8];dq[8,20]=z[20]
    JS=float(coefficients@q);DS=coefficients@dq;allJ=np.r_[J,JS];allD=np.vstack([DD,DS]);vac=-allJ/mass**2
    HV=completed_hessian(H,allD,mass);eigenvalues,O=np.linalg.eigh(HV);rows=[];sectors=[]
    hf=[.06,-.04];bare=[1.,.9];n=len(HV)
    for f,(eta,s,A) in enumerate(nonet_fields(z[:20])):
        m=bare[f]+hf[f]*vac[-1];y=[1.2,.57][f];C=.1*eta*np.eye(3)+.7*s*np.eye(3)+.8*A;spectrum=block_spectrum(C,y,m,z[20]/np.sqrt(2));sectors.append(spectrum)
        G=scalar_vertices(n,f);G[-1,3:,3:]=hf[f]*np.eye(3);rot=np.einsum('ab,aij->bij',O,G);threshold=scalar_threshold(spectrum['mass_matrix'],G,HV)
        rows.append({'sector':['up','down'][f],'bare_heavy_mass':bare[f],'singlet_heavy_Yukawa':hf[f],'matched_heavy_mass':m,
                    'full_fermion_masses':spectrum['masses'].tolist(),'tree_determinant_phase':float(np.angle(np.linalg.det(spectrum['mass_matrix']))),
                    'maximum_mixed_vertex_pair_imaginary_part':paired_vertex_reality(spectrum,rot),'first_order_neutral_scalar_phase':threshold['delta_theta'],
                    'UV_phase_coefficient':threshold['UV_phase_coefficient'],'relative_correction_norm':threshold['relative_correction_norm']})
    V=sectors[0]['doublet_frame'].conj().T@sectors[1]['doublet_frame'];Jweak=float(np.imag(V[0,0]*V[1,1]*V[0,1].conjugate()*V[1,0].conjugate()))
    schur=HV[:21,:21]-HV[:21,21:]@np.linalg.solve(HV[21:,21:],HV[21:,:21]);poles=finite_scalar_poles(H,allD,np.full(len(allD),mass**2))
    source_contact_delta=JS*JS/(2*mass**2)
    return {'source_coordinates':z.tolist(),'source_coefficients':c.tolist(),'Higgs_portals':portals.tolist(),'Higgs_mu2':old['Higgs_mu2'],
            'singlet_source_current_coefficients':coefficients.tolist(),'singlet_source_current_value':JS,'singlet_current_Jacobian':DS.tolist(),
            'mediator_mass':mass,'finite_mediator_count':len(J),'singlet_mediator_count':1,'full_physical_neutral_scalar_count':n,
            'all_real_scalars_before_removing_Higgs_Goldstones':n+3,'UV_scalar_vacuum':vac.tolist(),
            'source_gradient_norm':float(np.max(abs(fun(z)[1]))),'minimum_full_scalar_Hessian_eigenvalue':float(eigenvalues[0]),
            'Gaussian_source_Schur_residual':float(np.max(abs(schur-H))),'singlet_contact_at_source_vacuum':source_contact_delta,
            'physical_weak_CP_quartet':Jweak,'light_charged_current_squared':(abs(V)**2).tolist(),'sector_thresholds':rows,
            'scalar_pole_matching':poles,
            'renormalizable_fermion_census':{'old_real_coefficients_per_sector':5,'new_allowed_singlet_heavy_Yukawas_per_sector':1,'new_finite27_fermion_Yukawas':0,
                  'total_two_sector_real_fermion_coefficients':12,'representation_reason':'3bar tensor 3 = 1 + ordinary 8. The even family singlet permits only an identity heavy-mass vertex; finite 8prime,9,5+5prime permit no renormalizable triplet bilinear. Shaping signs forbid their heavy-to-ordinary vertices and the Higgs-heavy endpoint.'},
            'scope':'Constructed renormalizable Gaussian completion of the retained joint local CP-breaking source vacuum. All permitted singlet heavy Yukawas are nonzero. Other permitted scalar self coefficients may vary without changing the vertex theorem if a stable positive-mass vacuum exists. No new global CP-vacuum winner, golden relation, complete finite EFT threshold or all-loop phase prediction.'}


def exact_beta(coefficients,quartics,packet):
    out=[F(0)]*packet['heavy_mass_insertion_count_per_sector']
    for i,j,k,a,b in packet['nonzero_tensor_entries']:
        assert F(b)==0;out[i]+=F(a)*coefficients[j]*quartics[k]
    return out


def scalar_closed_module_certificate(packet,benchmark):
    n=packet['heavy_mass_insertion_count_per_sector'];s=packet['singlet_module_dimension']
    assert all((i<s)==(j<s) for i,j,k,a,b in packet['nonzero_tensor_entries'])
    quartics=[F.from_float(v) for v in benchmark['source_coefficients'][8:]]+[F(13,100)]+[F.from_float(v) for v in benchmark['Higgs_portals']]
    g=[F.from_float(v) for v in benchmark['singlet_source_current_coefficients']];mass=F.from_float(benchmark['mediator_mass']);rows=[]
    for h in [F(3,50),-F(1,25)]:
        coefficients=[-h*v/(mass*mass) for v in g]+[F(0)]*(n-s);beta=exact_beta(coefficients,quartics,packet)
        assert all(v==0 for v in beta[s:])
        rows.append({'tree_matched_mass_coefficients':list(map(str,coefficients)),'scalar_beta_times_16pi_squared':list(map(str,beta)),'all_six_adjoint_beta_coefficients_exactly_zero':True})
    b0=list(map(F,rows[0]['tree_matched_mass_coefficients']));b1=list(map(F,rows[1]['tree_matched_mass_coefficients']));v0=list(map(F,rows[0]['scalar_beta_times_16pi_squared']));v1=list(map(F,rows[1]['scalar_beta_times_16pi_squared']));minor_count=0
    for i in range(s):
        for j in range(i+1,s):
            assert b0[i]*b1[j]-b0[j]*b1[i]==0
            assert v0[i]*b1[j]+b0[i]*v1[j]-v0[j]*b1[i]-b0[j]*v1[i]==0
            minor_count+=1
    assert all(2*v0[i]+3*v1[i]==0 for i in range(s))
    return {'rank_one_mass_coefficient_matrix':{'rows':2,'columns':s,'exact_matching_minors_checked':minor_count,'exact_minor_derivatives_checked':minor_count,'independent_rank_one_relations':s-1,'matched_row_ratio':'-3/2','scalar_running_preserves_rank_one':True,'proof':'Both sector rows evolve by the same linear insertion map. A factorization B=h g.T therefore evolves with the common g vector, preserving every two-by-two minor.','scope':'Mass-insertion rows, scalar running only; quartic exchange matrices and full gauge/Yukawa EFT flow have separate running.'},'exact_invariant_singlet_module_dimension':s,'adjoint_module_dimension':n-s,'exact_singlet_to_adjoint_tensor_entries':0,
            'holds_for_every_source_Higgs_quartic':True,'sector_matching_and_beta':rows,
            'scope':'Scalar-loop closure for arbitrary running values of the 61 quartics. Full fermion/gauge/derivative EFT running and finite threshold matching require the correlated operators in the UV matching functional.'}


def build():
    P=np.array(quartic_projectors()[0]);Q,D,cert=certify_projectors(P);table=json.loads((OUT/'nonet_scalar_loop_algebra.json').read_text())['nonzero_symmetric_products'];full=json.loads((OUT/'nonet_higgs_exact_loop_algebra.json').read_text())['symmetric_products']
    maps=compile_scalar_insertion_maps(Q,D);higgs=compile_scalar_insertion_maps(Q,D,include_higgs=True);uv=singlet_UV_benchmark(P)
    return {'exact_projectors':cert,'quartic_tensor_proof':verify_loop_table(extended_quartics(Q,D),full),
            'source_insertion_map':maps,'source_Higgs_insertion_map':higgs,'one_scale_protection_kernel':protection_kernel_certificate(),
            'all_rotated_linear_obstruction':rotated_linear_obstruction(table),'exact_singlet_matching':exact_singlet_matching_certificate(),
            'singlet_finite_UV':uv,'closed_singlet_module':scalar_closed_module_certificate(higgs,uv)}

if __name__=='__main__':
    destination=OUT/'flavor_singlet_mediation.json';destination.write_text(json.dumps(build(),indent=2,sort_keys=True)+'\n');print(destination)
