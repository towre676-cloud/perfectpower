"""Rebuild the completion experiment, with retained failed numerical cases.

PYTHONPATH=python OPENBLAS_NUM_THREADS=1 python python/develop_flavor_completion.py
"""
from pathlib import Path
from math import pi, sqrt
from itertools import product
import json
import hashlib
import gzip
import numpy as np
from perfectpower.flavor_completion import (
    exact_lock_family, scalar_counterterm, cyclic_operator_basis,
    supersymmetric_circuit, circuit_spectrum, holomorphic_coefficient_extension,
    allowed_circuit_deformation, soft_circuit_branches, angular_derivatives,
    scalar_loop_minimum, joint_loop_minimum, yukawa_operator_basis,
    matched_texture, sm_running_example, circuit_quantum_minimum)
from perfectpower.flavor_prediction import ckm_from_depth
from perfectpower.flavor_completion import physical_chart

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'receipts/flavor_completion'


def save(name,data):
    encoded=(json.dumps(data,sort_keys=True,indent=2,allow_nan=False)+'\n').encode()
    if name in ('quark_operators.json','extended_quark_operators.json'):
        # Deterministic compression keeps the exhaustive operator tables small.
        (OUT/(name+'.gz')).write_bytes(gzip.compress(encoded,mtime=0))
        (OUT/name).unlink(missing_ok=True)
    else:
        (OUT/name).write_bytes(encoded)


def main():
    OUT.mkdir(exist_ok=True)
    training=json.loads((ROOT/'receipts/flavor_prediction/training.json').read_text())
    # Only Vus and Vcb are used. Neither CP measurements nor Vub are fit targets.
    u,v=training['Vus']['mean'],training['Vcb']['mean']
    save('lock_family.json',{'cases':[exact_lock_family(x) for x in ('0','1/1000','1/10','1')]})
    counterterms=[]
    for lock,kappa in product(('0','1/1000','1/10','1'),(None,'1/1000','1/100','1/10')):
        counterterms.append(scalar_counterterm(lock,kappa))
    save('scalar_counterterms.json',{'cases':counterterms,'all_declared_cases_break_stationary_family':all(not x['stationary_family_closed_under_this_divergence'] for x in counterterms)})
    save('single_field_operators.json',{'cyclic_groups':[cyclic_operator_basis(rotation_order=n) for n in range(1,61)]})
    save('supersymmetric_circuit.json',supersymmetric_circuit())
    save('circuit_spectra.json',{'base':circuit_spectrum(),'golden_extension':circuit_spectrum(True)})
    save('holomorphic_coefficient.json',holomorphic_coefficient_extension())
    save('allowed_initial_deformations.json',{'cases':[allowed_circuit_deformation(x) for x in (1e-4,1e-3,1e-2)]})
    soft=[soft_circuit_branches(e) for e in (1e-8,1e-6,1e-4,1e-3)]
    save('soft_selection.json',{'cases':soft})
    quantum=[]; quantum_failures=[]
    for epsilon,coupling in product((1e-6,1e-4,1e-3),(.1,.3,1.)):
        try:
            quantum.append(circuit_quantum_minimum(epsilon,coupling))
        except (ValueError,ArithmeticError) as e:
            quantum_failures.append({'epsilon':epsilon,'coupling':coupling,'reason':str(e),'accepted_as_prediction':False})
    save('full_circuit_quantum.json',{'cases':quantum,'failed_or_uncontrolled_cases':quantum_failures,
        'attempted_count':9,'accepted_count':len(quantum)})
    single=[]
    for r,m,l in product((.01,.03,.05,.1,.2),(.5,1.,2.),(0.,.001,.1,1.)):
        row=scalar_loop_minimum(r,m,l)
        row['physical_CKM_chart']=0<=row['coefficient']<=2
        row['CKM_if_tree_angle_coefficient_portal_retained']=physical_chart(ckm_from_depth(row['coefficient'],row['phase_degrees']*pi/180,u,v)) if row['physical_CKM_chart'] else None
        single.append(row)
    save('single_scalar_loops.json',{'cases':single,'count':len(single)})
    joint=[]; failures=[]
    for l,k,g,r in product((0.,.01,.1),(.001,.01,.1),(.5,1.,2.),(.01,.03,.1)):
        parameters={'lock':l,'kappa':k,'g_over_f':g,'Lambda_over_f':r}
        try:
            row=joint_loop_minimum(r,k,g,l)
            row['CKM_if_standard_depth_portal_retained']=physical_chart(ckm_from_depth(row['coefficient'],row['phase_degrees']*pi/180,u,v))
            joint.append(row)
        except (ValueError,ArithmeticError) as e:
            failures.append({'parameters':parameters,'reason':str(e),'accepted_as_prediction':False})
    save('joint_scalar_loops.json',{'attempted_count':len(joint)+len(failures),'accepted_count':len(joint),
        'cases':joint,'failed_or_uncontrolled_cases':failures,'all_accepted_local_hessians_positive':all(x['positive_local_hessian'] for x in joint)})
    save('quark_operators.json',yukawa_operator_basis())
    save('extended_quark_operators.json',yukawa_operator_basis(neutral_fields=17))
    golden=(3-sqrt(5))/2
    textures=[matched_texture(c,u,v) for c in (0.,.1,.2,golden,.6,1.)]
    save('quark_texture_counterexamples.json',{'cases':textures,'target_chart':physical_chart(ckm_from_depth(golden,11*pi/30,u,v))})
    save('sm_running.json',sm_running_example(u,v))
    # Illustrative consequences of actual complex T relaxation; the CKM mapping
    # remains a hypothesis, not a derived operator texture.
    forecasts=[]
    for study in soft:
        row=next(r for r in study['branches'] if r['root_power']==11)
        theta=row['phase_degrees']*pi/180
        for label,c,phase in (
            ('angle_readout',row['coefficient_from_angle'],theta),
            ('real_auxiliary_readout',row['coefficient_from_auxiliary_operator'],theta),
            ('holomorphic_T_times_unit_inverse_phase',row['holomorphic_T_magnitude'],theta-row['holomorphic_T_phase_degrees']*pi/180)):
            forecasts.append({'epsilon':study['epsilon'],'readout':label,'coefficient':c,'phase_degrees':phase*180/pi,
                'observables':physical_chart(ckm_from_depth(c,phase,u,v)),
                'scope':'conditional CKM chart readout, not a derived quark interaction. The third readout assumes a unit inverse phase, not a computed deformed holomorphic inverse field.'})
    save('conditional_readout_forecasts.json',{'cases':forecasts})
    d=angular_derivatives(11*pi/30)
    save('summary.json',{'anchors':{'Vus':u,'Vcb':v},'angular_curvature':d[2],'angular_third_derivative':d[3],
        'phase_tolerance_degrees_for_one_percent_C':.01*golden/(24*np.sin(12*11*pi/30))*180/pi,
        'base_chiral_fields':32,'extended_chiral_fields':34,'SUSY_vacua':16,
        'allowed_pure_scalar_W_terms':2448,'chosen_base_W_terms':37,'extended_allowed_W_terms':2907,
        'base_quark_operators':6460,'extended_quark_operators':7560,
        'one_field_CP_operators_degree12':48,'dangerous_one_field_operators':42,
        'exact_scalar_counterterm_cases':len(counterterms),'single_scalar_loop_cases':len(single),
        'joint_scalar_loop_cases_attempted':len(joint)+len(failures),'joint_scalar_loop_cases_accepted':len(joint),
        'joint_failed_cases':len(failures),'soft_continued_minima':sum(len(x['branches']) for x in soft),
        'full_circuit_quantum_cases_accepted':len(quantum),'full_circuit_quantum_failed_cases':len(quantum_failures),
        'all_soft_studies_prefer_root_powers_11_49':all(x['lowest_continued_branch_root_powers']==[11,49] for x in soft),
        'golden_initialized_texture_depth':textures[3]['observables']['depth'],
        'golden_initialized_texture_Vub':textures[3]['observables']['Vub'],
        'status':'constructed perturbatively protected SUSY vacuum equations; selected scalar deformation gives calculable local shifts. Symmetry enforcement of initial couplings and a derived golden CKM portal remain unresolved.',
        'new_Lean_theorems':0,'new_experimental_data':False,
        'loop_model_separation':'scalar-only and two-scalar EFT loops are distinct from the softly deformed 34-chiral-field circuit. All scalar and fermionic singlet modes enter the full-circuit DRbar calculation; quark and gauge thresholds do not.',
        'no_global_soft_circuit_or_cosmological_claim':True})
    save('sources.json',{'primary_sources':[
        {'title':'Radiative Corrections as the Origin of Spontaneous Symmetry Breaking','authors':'Coleman and Weinberg','year':1973,'url':'https://doi.org/10.1103/PhysRevD.7.1888','use':'effective-potential framework; scalar MSbar finite expression is specified in this implementation'},
        {'title':'Naturalness Versus Supersymmetric Non-renormalization Theorems','author':'Seiberg','year':1993,'url':'https://arxiv.org/abs/hep-ph/9309335','read':'pages 1, 5-7; Wilsonian/1PI distinction and Wess-Zumino discussion','use':'perturbative Wilsonian superpotential protection, with stated supersymmetry assumptions'},
        {'title':'Three-loop SM beta-functions for matrix Yukawa couplings','authors':'Bednyakov, Pikelner and Velizhanin','year':2014,'url':'https://arxiv.org/abs/1406.7171','read':'Eqs. 23-26, pages 5-6','use':'one-loop matrix Yukawa convention; d/dln(mu) implementation accounts for source ln(mu^2) convention'},
        {'title':'Geometrical CP violation from non-renormalisable scalar potentials','authors':'Varzielas, Emmanuel-Costa and Leser','year':2012,'url':'https://arxiv.org/abs/1204.3633','use':'comparison with actual symmetry-constrained operator analysis; does not derive this 66-degree model'}],
        'access':'primary paper text retrieved and relevant passages read; no local PDF byte acquisition claimed'})
    manifest={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(OUT.iterdir()) if p.name.endswith(('.json','.json.gz')) and p.name not in ('manifest.json','validation.json')}
    save('manifest.json',manifest)
    print(json.dumps({'receipts':len(manifest),'joint_accepted':len(joint),'joint_failed':len(failures),'soft_minima':64,'quark_operator_counts':[6460,7560]}))


if __name__=='__main__':
    main()
