"""Finite scalar pole matching and the higher-phase sequestering test."""
from pathlib import Path
import json
import numpy as np
from perfectpower.nonet_spectral_matching import *
from perfectpower.flavor_resummed_phase import *
from perfectpower.nonet_mediators import mediation_plan,currents
from perfectpower.nonet_potential import joint_higgs
from develop_valentiner_nonet_joint import hessian
from valentiner_adjoint_quartics import quartic_projectors

ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'receipts/m22_interactions'

def build():
    old=json.loads((OUT/'valentiner_nonet_joint.json').read_text());z=np.array(old['canonical_coordinates']);c=np.array(old['coefficients']);P=np.array(quartic_projectors()[0])
    H=hessian(lambda z:joint_higgs(z,c,P,np.array(old['Higgs_portals']),old['Higgs_mu2']),z)
    results={}
    for finite in [True,False]:
        plan=mediation_plan(c,P,finite_only=finite,sector_ratios=(1.1,.8,1.3));J,D=currents(z[:20],plan,P);D=np.column_stack([D,np.zeros(len(D))]);m2=np.full(len(D),plan['mass']**2)
        result=finite_scalar_poles(H,D,m2);metric=tree_metric(D,m2)
        result.update({'mediator_coordinates':len(D),'source_coordinates':len(H),'derivative_metric':metric.tolist(),
          'cross_sector_kinetic_block_norm':float(np.linalg.norm(metric[:10,10:20],2)),
          'source_energy_stationarity_unchanged':True})
        assert result['light_pole_maximum_absolute_error']<1e-10 and result['full_light_subspace_projector_error']<1e-5
        results['finite27' if finite else 'universal55']=result
    examples={}
    for structured in [False,True]:
        result=spectral_phase_example(structured)
        for key in ['D','vertices','scalar_Hessian']:
            a=result[key];result[key]={'real':a.real.tolist(),'imag':a.imag.tolist()}
        examples['Higgs_portal_row' if structured else 'three_scalar']=result
    high=high_precision_B0_top_block();assert abs(float(high['quadratic_determinant_phase'])-examples['three_scalar']['quadratic_determinant_phase'])<1e-20
    return {'exact_gaussian_certificate':exact_gaussian_spectral_certificate(),'finite_scalar_matching':results,
      'exact_Gaussian_wall_bridge':exact_gaussian_wall_certificate(),
      'exact_resolvent_phase_certificate':exact_resolvent_phase_certificate(),'physical_B0_phase_examples':examples,
      'high_precision_B0':high,'Higgs_sequestering':Higgs_sequestering_certificate(),
      'conclusion':'Finite Gaussian scalar exchange correlates derivative terms and exact pole residues. First-order mass-phase reality does not imply reality of the resummed one-loop determinant; exact Higgs sequestering would protect that restricted determinant but is not closed under the specified nonzero Yukawa running.',
      'remaining_scope':'No golden CKM or gauge-coupling prediction, complete invariant-vacuum realization of the spectral counterexamples, genuine two-loop diagram calculation, or global-vacuum classification.'}

def main():
    result=build();(OUT/'flavor_spectral_matching.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'pole_errors':{k:v['light_pole_maximum_absolute_error'] for k,v in result['finite_scalar_matching'].items()},
      'finite27_local_pole_error':result['finite_scalar_matching']['finite27']['maximum_two_derivative_relative_pole_error'],
      'B0_phases':{k:v['resummed_phase'] for k,v in result['physical_B0_phase_examples'].items()}},indent=2))

if __name__=='__main__':main()
