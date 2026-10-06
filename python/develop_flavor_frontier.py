"""Exact flavor tensor proof, complete soft-current running and physical tests."""
from pathlib import Path
from fractions import Fraction
import json
import numpy as np
from scipy.optimize import minimize,root
from scipy.integrate import solve_ivp
from perfectpower.exact_nonet_algebra import *
from perfectpower.flavor_mechanism_search import *
from perfectpower.nonet_running import *
from perfectpower.nonet_physical_tests import *
from perfectpower.nonet_potential import potential,nonet_fields,numerical_hessian,joint_higgs
from perfectpower.nonet_mediators import mediation_plan,currents
from perfectpower.flavor_quantum import fermion_CW_gradient
from perfectpower.quartic_renormalization import compile_loop_algebra
from develop_valentiner_nonet_joint import frame_and_spectrum,hessian
from develop_valentiner_mediator_closure import scalar_vertices
from valentiner_adjoint_quartics import quartic_projectors,CP_odd_projector,EMBED

ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'receipts/m22_interactions'


def rational_table(A):
    out=[];error=0
    for k,i,j in np.argwhere(abs(A)>1e-8):
        if j<i:continue
        q=Fraction(float(A[k,i,j])).limit_denominator(10000);error=max(error,abs(float(q)-A[k,i,j]));out.append([int(k),int(i),int(j),str(q)])
    return out,error


def exact_self_decompositions(Q,D,polys):
    import sympy as s
    base=[polys[10],polys[11]];monomials=list(base[1]);rows=None
    for m in monomials:
        for n in monomials:
            M=s.Matrix([[s.Rational(base[k].get(t,ZERO)[0])+s.sqrt(5)*s.Rational(base[k].get(t,ZERO)[1]) for k in range(2)] for t in [m,n]])
            if M.det()!=0:rows=(m,n,M);break
        if rows is not None:break
    m,n,M=rows;out=[]
    for q in Q[2:]:
        p=projected_poly(q,D);rhs=s.Matrix([s.Rational(p.get(t,ZERO)[0])+s.sqrt(5)*s.Rational(p.get(t,ZERO)[1]) for t in [m,n]])
        coef=[s.simplify(x) for x in M.inv()*rhs];assert all(x.is_Rational for x in coef)
        rec=padd(*(pscale(b,(F(str(c)),F(0))) for b,c in zip(base,coef)));assert rec==p
        out.append(list(map(str,coef)))
    return out


def matched_quartics(uv,gu,gd,mass2,self_decomposition):
    c=uv.copy()
    for R,(a,b) in enumerate(self_decomposition):
        for off,g in [(0,gu[R]),(12,gd[R])]:
            c[10+off]-=g*g/(2*mass2[R])*float(F(a));c[11+off]-=g*g/(2*mass2[R])*float(F(b))
        c[49+R]-=gu[R]*gd[R]/mass2[R]
    return c


def soft_running(kernel,c,q,p,m,gauge,gu,gd,M2,eigenvalues,decompositions):
    initial=np.r_[c,q,p.ravel(),m,gauge,gu,gd,M2]
    def derivative(t,v):
        quart=v[:61];quad=v[61:70];par=v[70:78].reshape(2,4);mass=v[78:80];gg=v[80:83]
        u,d,ms=v[83:86],v[86:89],v[89:92];b=kernel.beta(quart,quad,par,mass,gg)
        med=mediation_beta(quart[[10,22]],quart[[11,23]],quart[49:52],u,d,ms,eigenvalues,par[:,3])
        b['quadratics'][3]+=np.dot([8,9,10],u*u)/2;b['quadratics'][7]+=np.dot([8,9,10],d*d)/2
        return np.r_[b['quartics'],b['quadratics'],b['Yukawas'].ravel(),b['heavy_masses'],b['gauge'],med['beta_gu'],med['beta_gd'],med['beta_mass2']]/(16*np.pi*np.pi)
    def Higgs_zero(t,v):return v[52]
    Higgs_zero.terminal=True;Higgs_zero.direction=-1
    sol=solve_ivp(derivative,(0,.85),initial,rtol=2e-9,atol=2e-11,dense_output=True,events=Higgs_zero)
    if not sol.success:raise RuntimeError(sol.message)
    rows=[]
    for t in sorted(set([0.,.01,.1,min(.5,sol.t[-1]),float(sol.t[-1])])):
        v=sol.sol(t);eff=matched_quartics(v[:61],v[83:86],v[86:89],v[89:92],decompositions)
        rows.append({'log_scale_ratio':t,'parameters':v.tolist(),'tree_matched_finite_channels':eff[49:52].tolist(),
          'Higgs_quartic':float(v[52]),'singlet_Yukawa_ratios':(v[70:78].reshape(2,4)[:,1]/v[70:78].reshape(2,4)[:,2]).tolist()})
    return {'nonconstant_parameters':92,'minimal_action_parameters':83,'vacuum_energy_runs_separately':True,
      'beta_initial':(derivative(0,initial)*16*np.pi*np.pi).tolist(),'trajectory':rows,
      'first_Higgs_quartic_zero_log_scale':float(sol.t_events[0][0]) if len(sol.t_events[0]) else None,
      'gauge_input':[float(x) for x in gauge],'scope':'One-loop MS-bar running above heavy thresholds in the renormalizable Gaussian soft-current class, with zero lepton Yukawas. Tree matching of running parameters is recorded, not a physical CKM RG prediction or full finite threshold matching.'}


def scalar_matching(c,plan,P):
    rng=np.random.default_rng(508);points=rng.normal(size=(100,20));design=[];values=[]
    zcoeff=np.zeros(2)
    for g in plan['groups']:
        dim=g['dimension'];zcoeff+=dim*np.array([g['up']**2,g['down']**2])/(4*plan['mass']**2)
    for x in points:
        v,grad=operators(x,P);H=polynomial_hessians(lambda y:operators(y,P)[1][8:].T@c[:52],x)
        _,D=currents(x,plan,P);threshold=-np.trace(D@H@D.T)/(2*plan['mass']**2)
        displacement=np.zeros(20);displacement[2:10]=zcoeff[0]*x[2:10];displacement[12:]=zcoeff[1]*x[12:]
        values.append(threshold-(grad[8:].T@c[:52])@displacement/2);design.append(v[8:])
    coef=np.linalg.lstsq(design,values,rcond=None)[0];error=float(np.max(abs(np.array(design)@coef-values)))
    off_grid=[]
    for x in rng.normal(size=(5,20)):
        v,grad=operators(x,P);H=polynomial_hessians(lambda y:operators(y,P)[1][8:].T@c[:52],x)
        _,D=currents(x,plan,P);displacement=np.zeros(20)
        displacement[2:10]=zcoeff[0]*x[2:10];displacement[12:]=zcoeff[1]*x[12:]
        direct=-np.trace(D@H@D.T)/(2*plan['mass']**2)-(grad[8:].T@c[:52])@displacement/2
        off_grid.append(float(abs(v[8:]@coef-direct)/max(1,abs(direct))))
    assert max(off_grid)<1e-10
    return {'canonical_quartic_threshold_16pi2':coef.tolist(),'adjoint_wavefunction_threshold_16pi2':zcoeff.tolist(),
      'polynomial_fit_absolute_error':error,'independent_point_relative_errors':off_grid,
      'scope':'Leading massless-source, large-mediator one-loop matching at mu=M, including scalar canonical normalization. All coefficients must be divided by 16*pi^2. Finite light masses and heavy-quark matching are outside this approximation.'}


def callan_symanzik_check(kernel,c,q,p,m,gauge,P):
    rng=np.random.default_rng(8);b=kernel.beta(c,q,p,m,gauge);gamma=scalar_gamma(p,gauge);tests=[]
    HQ=quadratic_basis(np.zeros(24))[2];H2=np.einsum('i,iab->ab',q,HQ);constant=np.trace(H2@H2)/2-18*np.sum(m**4)
    for _ in range(5):
        z=rng.normal(size=24);v,grad=quartic_value_gradient(z,P);v2,g2,_=quadratic_basis(z)
        H=H2+polynomial_hessians(lambda x:quartic_value_gradient(x,P)[1].T@c,z)
        hh=z[20:]@z[20:]/2;ferm=0
        for f,(y,eta,s,a) in enumerate(p):
            x=z[10*f:10*f+10];C=(eta*x[0]+s*x[1])*np.eye(3)+a*np.einsum('a,aij->ij',x[2:],BASIS)
            K=C@C+y*y*hh*np.eye(3);ferm+=np.trace(K@K).real+2*m[f]**2*np.trace(C@C).real+3*m[f]**4
        gaugepart=(9*gauge[1]**4/8+3*gauge[1]**2*gauge[2]**2/4+3*gauge[2]**4/8)*hh**2
        residual=v@b['quartics']+v2@b['quadratics']+constant-(grad.T@c+g2.T@q)@(gamma@z)-np.trace(H@H)/2+6*ferm-gaugepart
        tests.append(float(abs(residual)/max(1,abs(np.trace(H@H)/2),6*ferm)))
    assert max(tests)<1e-9
    return {'off_grid_relative_residuals':tests,'vacuum_energy_beta_16pi2':float(constant),
      'scope':'One-loop Callan-Symanzik identity for the full minimal scalar potential, with gauge/Yukawa contributions and off-diagonal scalar anomalous dimensions.'}


def quantum_feedback(z,c,q,p,m,gauge,P):
    def scalarH(zz):
        return np.einsum('i,iab->ab',q,quadratic_basis(zz)[2])+polynomial_hessians(lambda x:quartic_value_gradient(x,P)[1].T@c,zz)
    zz=np.r_[z[:20],0.,0.,z[20],0.];H=scalarH(zz);w,U=np.linalg.eigh(H);weights=np.zeros_like(w);mask=abs(w)>1e-12;weights[mask]=w[mask]*(np.log(abs(w[mask]))-1)
    indices=list(range(20))+[22];sg=[]
    for j in indices:
        e=np.eye(24)[j]*.005;dH=(scalarH(zz+e)-scalarH(zz-e))/.01
        sg.append(float(np.dot(weights,np.diag(U.T@dH@U))/(32*np.pi*np.pi)))
    fg=np.zeros(21);phases=[]
    sectors=frame_and_spectrum(z)[1];HP=H[np.ix_(indices,indices)]
    for f,sector in enumerate(sectors):
        vertices=scalar_vertices(21,f);fg+=fermion_CW_gradient(sector['mass_matrix'],vertices)
        phases.append(higher_order_phase_diagnostic(sector['mass_matrix'],vertices,HP))
    h=z[20];hh=h*h/2;mw=gauge[1]**2*hh/2;mz=(gauge[1]**2+gauge[2]**2)*hh/2;gg=np.zeros(21)
    gg[-1]=(6*mw*(np.log(mw)-1/3)*gauge[1]**2*h/2+3*mz*(np.log(mz)-1/3)*(gauge[1]**2+gauge[2]**2)*h/2)/(32*np.pi*np.pi)
    grad=np.array(sg)+fg+gg;shift=-np.linalg.solve(HP,grad)
    return {'scalar_CW_gradient':sg,'fermion_CW_gradient':fg.tolist(),'gauge_CW_gradient':gg.tolist(),
      'linearized_vacuum_shift':shift.tolist(),'shift_over_background_norm':float(np.linalg.norm(shift)/np.linalg.norm(z)),
      'one_loop_determinant_expansion':phases,'scope':'Landau-gauge one-loop gradient at the retained tree vacuum, MS-bar inputs fixed at mu=1. Linear displacement is a validity diagnostic, not a re-minimized quantum vacuum or a complete two-loop phase.'}


def global_branches(z,c,P,portals,mu2):
    shifted=c.copy();shifted[:8]+=.03**2*portals;rng=np.random.default_rng(809);rows=[]
    for k in range(24):
        x=z[:20]+rng.normal(size=20)*.5 if k<8 else rng.normal(size=20)*.7
        sol=minimize(lambda x:potential(x,shifted,P),x,jac=True,method='BFGS',options={'gtol':2e-9,'maxiter':800})
        rows.append({'start':k,'fixed_Higgs_energy':float(sol.fun),'coordinates':sol.x.tolist(),'gradient':float(np.linalg.norm(sol.jac))})
    previous=json.loads((OUT/'valentiner_nonet_joint.json').read_text());CP=np.array(previous['CP_adjoint_matrix']);T=np.eye(20);T[2:10,2:10]=CP;T[12:20,12:20]=CP
    w,E=np.linalg.eigh((T+T.T)/2);fixed=E[:,w>.5];cp=[];fun=lambda zz:joint_higgs(zz,c,P,portals,mu2)
    for k in range(6):
        sol=minimize(lambda y:(potential(fixed@y,shifted,P)[0],fixed.T@potential(fixed@y,shifted,P)[1]),rng.normal(size=fixed.shape[1])*.7,jac=True,method='BFGS',options={'gtol':2e-9,'maxiter':800})
        trial=np.r_[fixed@sol.x,z[20]];ref=root(lambda zz:fun(zz)[1],trial,tol=1e-11);zz=ref.x;H=hessian(fun,zz);obs=frame_and_spectrum(zz)[0]
        cp.append({'energy':float(fun(zz)[0]),'full_gradient':float(np.linalg.norm(fun(zz)[1])),'full_Hessian_minimum':float(np.linalg.eigvalsh(H)[0]),
                   'CP_fixed_residual':float(np.linalg.norm(T@zz[:20]-zz[:20])),'J':obs['J'],'coordinates':zz.tolist()})
    stable=[v for v in cp if v['full_Hessian_minimum']>1e-6 and v['full_gradient']<1e-8];best=min(stable,key=lambda v:v['energy']);baseline=fun(z)[0]
    assert best['energy']<baseline-1e-3 and best['CP_fixed_residual']<1e-8
    return {'baseline_CP_breaking_energy':float(baseline),'all_field_starts':rows,'CP_fixed_dimension':fixed.shape[1],
      'CP_fixed_full_Higgs_branches':cp,'stable_CP_conserving_competitor':best,'energy_gap_below_retained_branch':float(baseline-best['energy']),
      'retained_branch_is_not_global':True,'scope':'Numerical stationary points and strict resolved energy comparison establish a lower CP-conserving competitor. The global winner over every branch is not classified.'}


def build():
    prev=json.loads((OUT/'valentiner_nonet_joint.json').read_text());old=json.loads((OUT/'valentiner_mediator_closure.json').read_text())
    z=np.array(prev['canonical_coordinates']);P,pc=quartic_projectors();P=np.array(P);Q,D,proof=certify_projectors(P);polys=exact_quartics(Q,D)
    table=json.loads((OUT/'nonet_scalar_loop_algebra.json').read_text())['nonzero_symmetric_products']
    exact={'projectors':proof,'loop_products':verify_loop_table(polys,table),'independence':independence_witness(polys),
      'projector_integer_pairs':[[a.tolist(),b.tolist()] for a,b in Q]}
    (OUT/'nonet_exact_tensor_proof.json').write_text(json.dumps(exact,indent=2,sort_keys=True)+'\n')
    A,acert=compile_loop_algebra(lambda x:quartic_value_gradient(x,P),24,61,samples=100);fulltable,error=rational_table(A)
    fullproof=verify_loop_table(extended_quartics(Q,D),fulltable)
    full={'operator_names':OPERATOR_NAMES[8:]+['Higgs_norm_squared']+[n+'_Higgs_portal' for n in OPERATOR_NAMES[:8]],
          'symmetric_products':fulltable,'exact_tensor_proof':fullproof,'proposal_maximum_error_not_proof':error}
    (OUT/'nonet_higgs_exact_loop_algebra.json').write_text(json.dumps(full,indent=2,sort_keys=True)+'\n')
    # Use the certified rational table as the evolution tensor.
    A.fill(0)
    for k,i,j,value in fulltable:A[k,i,j]=A[k,j,i]=float(F(value))
    kernel=RunningKernel(P,A);c=np.r_[prev['coefficients'][8:],prev['Higgs_lambda'],prev['Higgs_portals']];q=np.r_[prev['coefficients'][:8],-prev['Higgs_mu2']]
    p=np.array([[1.2,.1,.7,.8],[.57,.1,.7,.8]]);m=np.ones(2);gauge=np.array([1.,.65,.36])
    _,gamma,ycert=yukawa_beta(p,gauge);yerror=float(np.max(abs(yukawa_beta(p,gauge)[0]-analytic_yukawa_beta(p,gauge))))
    bp,bcert=coupled_quartic_beta(c,P,p,gauge,samples=100);fast=kernel.beta(c,q,p,m,gauge);berror=float(np.max(abs(bp-fast['quartics'])));assert berror<1e-8
    current=current_eigenvalues(Q,D,polys);selfdec=exact_self_decompositions(Q,D,polys);plan=mediation_plan(np.array(prev['coefficients']),P,finite_only=True,sector_ratios=(1.1,.8,1.3))
    gu=np.array([v['up'] for v in plan['groups']]);gd=np.array([v['down'] for v in plan['groups']]);M2=np.full(3,plan['mass']**2)
    contact=np.r_[old['completions']['fermion_safe_finite']['source_contact_coefficients'],prev['Higgs_lambda'],prev['Higgs_portals']]
    assert np.max(abs(matched_quartics(contact,gu,gd,M2,selfdec)-c))<1e-10
    running=soft_running(kernel,contact,q,p,m,gauge,gu,gd,M2,current['finite8_self_current_eigenvalues'],selfdec)
    odd,oddproof=certify_odd_projector(CP_odd_projector(),Q,D);oddpoly=projected_poly(odd,D,up=True,down=True)
    t=np.r_[z[:2],z[2:10]/np.sqrt(METRIC),z[10:12],z[12:20]/np.sqrt(METRIC)];oddvalue=0
    for mon,(a,b) in oddpoly.items():oddvalue+=float(a+b*np.sqrt(5))*np.prod(t[list(mon)])
    quality={'CP_odd_quartic_proof':oddproof,'vacuum_value':float(oddvalue),
      'allowed_operator':'i c O4(Au,Ad) bar(Q_L) H d_R/Lambda^4 + h.c.; dimension eight',
      'CP_consistency':'O4(CP fields)=-O4(fields), hence (i O4)(CP fields)=(i O4(fields))*',
      'tree_phase_formula':'3 atan(c O4/(y_d Lambda^4))',
      'example_phases':{str(L):float(3*np.arctan(oddvalue/(.57*L**4))) for L in [1,10,100,1000]},
      'cutoff_for_1e_minus10_with_unit_coefficient':float((abs(oddvalue)/(.57*np.tan(1e-10/3)))**.25),
      'scope':'One explicit allowed higher Yukawa operator on this minimal field content. Cutoffs in declared model units; no complete higher-operator census or derived cutoff.'}
    closures={}
    for name,indices in [('one_finite',[10,22,49]),('ordinary_cross',[10,22,48]),('radial',[10,22])]:closures[name]=exact_subalgebra(table,np.eye(52,dtype=int)[indices].tolist())
    unified=np.zeros(52,int);unified[49:52]=1;closures['SU3_unified']=exact_subalgebra(table,[np.eye(52,dtype=int)[10].tolist(),np.eye(52,dtype=int)[22].tolist(),unified.tolist()])
    thermal_values=[thermal_quadratic(e,c,P,p,gauge) for e in np.eye(24)];thermal_H=np.zeros((24,24))
    for i in range(24):
        thermal_H[i,i]=2*thermal_values[i]
        for j in range(i):thermal_H[i,j]=thermal_H[j,i]=thermal_quadratic(np.eye(24)[i]+np.eye(24)[j],c,P,p,gauge)-thermal_values[i]-thermal_values[j]
    result={'exact_restricted_subalgebras':closures,'coordinate_subalgebra_census':coordinate_subalgebra_census(table),
      'pure_adjoint_complete_action':{'scalar_coefficients':15,'quartics':12,'nonconstant_running_parameters_with_gauge':24,'with_soft_mediators':33,
        'mass_hierarchy_certificate':pure_adjoint_mass_gap_certificate()},
      'finite_current_running':current,'finite_self_decompositions':selfdec,'complete_soft_running':running,
      'complete_minimal_running_check':{'analytic_tensor_Yukawa_error':yerror,'fast_direct_quartic_error':berror,'direct_beta_certificate':bcert,
        'initial_beta':{k:v.tolist() for k,v in fast.items()},'Callan_Symanzik':callan_symanzik_check(kernel,c,q,p,m,gauge,P)},
      'heavy_scalar_matching_certificate':heavy_scalar_matching_certificate(),'canonical_scalar_matching':scalar_matching(c,plan,P),
      'gauge_threshold':{'delta_inverse_gauge_squared':gauge_threshold_delta_inverse(gauge,np.array([v['masses'][3:] for v in prev['fermion_spectra']]),1.).tolist(),
          'above_heavy_beta_coefficients':[-3,-19/6,27/2],'below_heavy_SM_coefficients':[-7,-19/6,41/6],
          'independent_gauge_boundary_remains':True,'scope':'One-loop gauge matching of the six electroweak-singlet vectorlike quarks. Gauge normalization remains an input.'},
      'dimension_eight_quality_operator':quality,'higher_kinetic_response':kinetic_response(z),
      'quantum_vacuum_feedback':quantum_feedback(z,c,q,p,m,gauge,P),
      'vacuum_comparison':global_branches(z,np.array(prev['coefficients']),P,np.array(prev['Higgs_portals']),prev['Higgs_mu2']),
      'leading_high_temperature_mass_eigenvalues':np.linalg.eigvalsh(thermal_H).tolist(),
      'thermal_scope':'Leading high-temperature expansion of the minimal action; positive thermal masses indicate asymptotic restoration. Not a resummed transition or cosmological sign-selection calculation.',
      'conclusion':'Exact loop algebra, complete specified one-loop running and new finite-mass/quality/vacuum tests constrain the next mechanism. Golden CKM and Sommerfeld coupling remain unpredicted.',
      'sources':['https://arxiv.org/pdf/1809.06797','https://arxiv.org/html/2407.16202v2']}
    return result


def main():
    result=build();(OUT/'flavor_frontier.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'proof':'Exact 52- and 61-quartic tables','closed_coordinate_subspaces':len(result['coordinate_subalgebra_census']['closed_supports']),
      'running_parameters':result['complete_soft_running']['nonconstant_parameters'],'Higgs_zero':result['complete_soft_running']['first_Higgs_quartic_zero_log_scale'],
      'dimension8_phase':result['dimension_eight_quality_operator']['example_phases'],'CP_competitor_gap':result['vacuum_comparison']['energy_gap_below_retained_branch'],
      'CW_shift_fraction':result['quantum_vacuum_feedback']['shift_over_background_norm']},indent=2))

if __name__=='__main__':main()
