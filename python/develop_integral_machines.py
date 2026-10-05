"""Develop integral state realizations from retained rational machine receipts."""
import argparse
import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path
from perfectpower.deep_recovery_cli import exact_json
from perfectpower.integral_machine import (integral_machine,integralize_machine,
    verify_integral_machine,integral_power_output,integral_word_output,observation_fibre,modular_power_output)
from perfectpower.recurrence import Recurrence

ROOT=Path(__file__).resolve().parents[1]


def build(output):
    out=Path(output);out.mkdir(parents=True,exist_ok=True);hashes={}
    def read(path):
        raw=(ROOT/path).read_bytes();hashes[path]=hashlib.sha256(raw).hexdigest();return json.loads(raw)
    def write(name,data):
        (out/name).write_text(json.dumps(data,indent=2,sort_keys=True,default=exact_json)+'\n')
    stored=read('receipts/lost_work_development/recurrence_machines.json')
    models={r['id']:Recurrence(tuple(map(Q,r['coefficients'])),tuple(map(Q,r['initial'])))
        for r in read('receipts/sequence_recovery/results.json')['oeis_scan']['candidates']}
    results=[];checks=mod_checks=before=after=0;indices=[];image_torsion=0;fractional_transitions=fractional_readouts=0
    for row in stored['machines']:
        r=integralize_machine(row['machine']);assert verify_integral_machine(r)
        fractional_transitions+=sum(Q(x).denominator!=1 for a in row['machine']['operators_minimal'] for rr in a for x in rr)
        fractional_readouts+=sum(Q(x).denominator!=1 for rr in row['machine']['readouts_minimal'] for x in rr)
        before+=r['state_dimension'];after+=r['minimal_dimension'];indices.append(r['selected_word_lattice_index'])
        image_torsion+=any(x>1 for x in r['observation_image_factors'])
        for n in (0,1,2,10,50,100):
            assert integral_power_output(r,n)==tuple(models[i].nth(n) for i in row['ids']);checks+=len(row['ids'])
        for modulus in (2,3,4,6,8,9,12,19):
            for n in (0,1,10,100):
                assert modular_power_output(r,n,modulus)==tuple(int(models[i].nth(n))%modulus for i in row['ids']);mod_checks+=len(row['ids'])
        # Every coordinate of the complete integral state realization is an int.
        assert all(type(x) is int for key in ('operators_minimal','readouts_minimal')
            for a in (r[key] if key=='operators_minimal' else [r[key]]) for row_ in a for x in row_)
        results.append({'ids':row['ids'],'certificate':r,'definition_status':'supplied reconstructed recurrence models; not original OEIS definition proofs'})
    write('recurrence_machines.json',{'rows':results,'unshared_coordinates':before,'integral_minimal_coordinates':after})
    scaled=integral_machine([[[1,1],[0,1]]],[0,2],[[4,0]])
    bad=observation_fibre(scaled,[2,0]);good=observation_fibre(scaled,[4,12])
    assert bad['status']=='DIVISIBILITY_OBSTRUCTION' and bad['modulus']==4
    assert good['status']=='INTEGER_AFFINE_FIBRE'
    hidden=integral_machine([[[2,0],[0,3]]],[1,1],[[1,0]])
    fibre=observation_fibre(hidden,[5]);assert len(fibre['original_kernel_basis'])==1
    directional=integral_machine([[[1,1],[0,1]],[[1,0],[1,1]]],[1,0],[[1,0]])
    assert integral_word_output(directional,[0,1])==(1,) and integral_word_output(directional,[0,1],order='written')==(2,)
    write('examples.json',{'scaled_observation':scaled,'rejected_observation':[2,0],'obstruction':bad,
        'accepted_observation':[4,12],'complete_state_fibre':good,'invisible_direction':hidden,
        'invisible_state_fibre':fibre,'noncommuting':directional,
        'scope':'integer states in saturated reachable spaces; fibres are not seed-orbit membership'})
    summary={'schema':'pp-integral-machines-development/1','models':len(models),'groups':len(results),
        'unshared_state_coordinates':before,'minimal_integral_coordinates':after,'independent_values_checked':checks,
        'independent_modular_values_checked':mod_checks,'fractional_transition_entries_removed':fractional_transitions,
        'fractional_readout_entries_removed':fractional_readouts,
        'groups_with_nonprimitive_selected_word_bases':sum(i>1 for i in indices),
        'largest_selected_word_lattice_index':max(indices),'groups_with_observation_image_torsion':image_torsion,
        'selected_word_indices':indices,'source_sha256':hashes,'execution_verified':False,'new_lean_compilations':0,
        'scope':'minimal integral realization preserves all words of fixed supplied seeds; no exact integral orbit module, OEIS identification or primitive-cost optimality'}
    write('summary.json',summary);print(json.dumps(summary,indent=2),flush=True);return summary


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,default=ROOT/'receipts/integral_machines')
    args=p.parse_args();build(args.output)
