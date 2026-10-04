"""Stdlib-only replay of four old constructions on current PerfectPower data."""
import argparse
import hashlib
import json
import re
from pathlib import Path
from perfectpower import exact_linear as E
from perfectpower.deep_recovery_cli import exact_json
from perfectpower.weighted_hodge import weighted_hodge,regularized_constraint,constraint_projector
from perfectpower.power_sums import power_sum_witness,search_power_sums
from perfectpower.polynomial_symmetry import parse_sparse,power_coordinate,deweight,evaluate_sparse,pullback_points
from perfectpower.finite_weil import commutant,heisenberg_replay,crt_replay,degeneracy_replay

ROOT=Path(__file__).resolve().parents[1]


def audit_quartic_inputs(corpus, source, ledger):
    """Bind Python inputs to literal Lean packets and the stored proof ledger.

    This checks source integrity and the inherited ledger, not Lean execution.
    """
    rows=corpus['rows'];digest=hashlib.sha256(source.encode()).hexdigest()
    if ledger['source_sha256']!=digest or ledger['status']!='COMPLETE_KERNEL_CHECK' or ledger['checked_case_indices']!=list(range(len(rows))) or ledger['compiled_complete_lists']!=len(rows) or ledger['compiled_packet_equalities']!=len(rows):
        raise ValueError('complete matching outer kernel ledger required')
    lines=source.splitlines()
    for i,row in enumerate(rows):
        name=f'curve_{i:04d}'
        command=re.fullmatch(r'native_(linear_perturbation|square_leading_quartic) '+name+r' for ([-0-9, ]+)',lines[5+2*i])
        if not command or [int(x) for x in command[2].split(',')]!=row['parameters']:
            raise ValueError('outer parameter packet mismatch')
        theorem={'linear_perturbation':'PerfectPower.LinearPerturbation.complete','square_leading_quartic':'PerfectPower.SquareLeadingQuartic.complete'}[command[1]]
        if row['theorem']!=theorem:raise ValueError('outer family theorem mismatch')
        if command[1]=='linear_perturbation':
            l,a,b,c,d=row['parameters'];coefficients=[b*b+d,2*a*b+c,a*a+2*l*b,2*l*a,l*l]
        else:
            l,u,v,w,z=row['parameters'];coefficients=[z,w,v,u,l*l]
        if coefficients!=row['coefficients']:raise ValueError('outer polynomial does not match its proved parameters')
        packet=re.fullmatch(r'theorem '+name+r'_packet : '+name+r' = (∅|\{.*\}) := by decide \+kernel',lines[6+2*i])
        if not packet:raise ValueError('outer literal packet missing')
        literal=packet[1]
        if literal!='∅' and not re.fullmatch(r'\{\(-?\d+,-?\d+\)(,\(-?\d+,-?\d+\))*\}',literal):
            raise ValueError('outer literal packet malformed')
        points=sorted((int(x),int(y)) for x,y in re.findall(r'\((-?\d+),(-?\d+)\)',literal))
        if points!=sorted(tuple(p) for p in row['points']):raise ValueError('outer literal points mismatch')
    return {'matching_outer_packets':len(rows),'stored_kernel_ledger_status':ledger['status'],
            'source_sha256':digest,'lean_recompiled_here':False}


def build(output):
    output=Path(output);output.mkdir(parents=True,exist_ok=True);sources={}
    def read(relative):
        raw=(ROOT/relative).read_bytes();sources[relative]=hashlib.sha256(raw).hexdigest()
        return raw.decode()
    def write(name,data):
        (output/name).write_text(json.dumps(data,indent=2,default=exact_json,sort_keys=True)+'\n')
    cells=json.loads(read('receipts/branched_geometry/cell_models.json'));hodge=[]
    def mass(n,offset):return [[i+offset if i==j else 0 for j in range(n)] for i in range(n)]
    for row in cells:
        v,e,f=row['vertices'],row['edges'],row['faces']
        packet=weighted_hodge(row['boundary1'],row['boundary2'],mass(v,2),mass(e,3),mass(f,5))
        assert packet['dimensions'][2]==2*row['genus']
        vector=tuple(range(1,e+1));components=[E.apply(packet[k],vector) for k in ('gradient_projector','boundary_projector','harmonic_projector')]
        assert tuple(map(sum,zip(*components)))==vector
        packet.update({'genus':row['genus'],'mass_diagonal_offsets':[2,3,5],'replayed_vector':vector,'vector_components':components})
        hodge.append(packet)
    d=[[1,0]];mx=E.identity(2);my=E.identity(1)
    regularized=regularized_constraint(d,mx,my,1);exact=constraint_projector(d,mx)
    assert E.multiply(regularized,regularized)!=regularized and E.multiply(d,regularized)!=((0,0),)
    write('weighted_hodge.json',{'models':hodge,'regularization_counterexample':{'D':d,'epsilon':1,'regularized':regularized,'exact_projector':exact}})
    quartic=power_sum_witness([95800,217519,414560],422481,4)
    quintic=power_sum_witness([27,84,110,133],144,5)
    bounded=search_power_sums(5,4,144,primitive_only=True)
    assert (27,84,110,133,144) in bounded['solutions'] and quartic['gcd']==quintic['gcd']==1
    small_quartic=search_power_sums(4,3,200)
    write('power_sums.json',{'historical_witnesses':[quartic,quintic],'bounded_quintic_search':bounded,'bounded_quartic_search':small_quartic,
        'historical_scan_payload_recovered':False,'historical_gcd_127_claim_correct':False})
    source=parse_sparse(read('recovery_sources/deep_gems/PSG_Q_U_L_Z.txt'),('U','L','Z'))
    saved=parse_sparse(read('recovery_sources/deep_gems/PSG_Qtilde_W_L_Z.txt'),('L','W','Z'))
    # Reorder the independently saved expression into W,L,Z coordinates.
    saved={(e[1],e[0],e[2]):c for e,c in saved.items()}
    transformed=deweight(source,0,1,2,12);assert transformed==saved and len(source)==100
    pulled=power_coordinate(power_coordinate(source,0,2),2,2)
    descended=power_coordinate(power_coordinate(pulled,0,2,quotient=True),2,2,quotient=True)
    assert descended==source
    # Reversal must check ALL coefficients. A square outer ratio is insufficient.
    coeff=[sum(c*1**l*2**z for (u,l,z),c in transformed.items() if u==j) for j in range(7)]
    assert coeff[0]/coeff[6]==9 and coeff!=list(reversed(coeff))
    defects=[coeff[j]-9*coeff[6-j] for j in range(7)]
    assert any(defects)
    write('polynomial_quotient.json',{'source_terms':100,'degrees_U_L_Z':[max(e[i] for e in source) for i in range(3)],
        'deweighted_saved_expression_matches':True,'power_coordinate_roundtrip_exact':True,'coordinate_identity':'Q(L^2 W,L,Z)=L^12 Qtilde(W,L,Z)',
        'inverse_chart':'L != 0; U and Z must be integer squares to lift a square quotient point',
        'specialization_L1_Z2':{'coefficients_low_to_high':coeff,'outer_ratio':9,'reversal_defects_with_outer_ratio':defects},
        'original_P_to_resultant_reconstructed':False})
    corpus=json.loads(read('receipts/divisor_sum/complete_quartics.json'))
    lean_source=read('receipts/divisor_sum/CompleteQuartics.lean')
    ledger=json.loads(read('receipts/divisor_sum/lean_catalogue_validation.json'))
    audit=audit_quartic_inputs(corpus,lean_source,ledger);lifted=[];counts={2:0,3:0}
    for index,row in enumerate(corpus['rows']):
        assert row['complete'] is True
        for q in (2,3):
            packet=pullback_points(row['coefficients'],row['points'],q)
            counts[q]+=len(packet['points'])
            lifted.append({'source_row':index,'degree':4*q,'power':q,'outer_coefficients':row['coefficients'],
                           'outer_theorem':row['theorem'],'points':packet['points'],
                           'complete_relative_to_existing_outer_receipt':True,'new_lean_theorem':False})
    write('quartic_pullbacks.json',{'source_rows':len(corpus['rows']),'derived_curves':len(lifted),'point_counts':counts,'outer_source_audit':audit,
        'scope':'exact integer lifting of existing complete quartic receipts; outer theorem is inherited, no new Lean compilation', 'rows':lifted})
    weil=[commutant(n) for n in (2,3,4,5,7,8,9)]
    write('finite_weil.json',{'commutants':weil,'heisenberg':[heisenberg_replay(n) for n in (2,3,4,5,7,8,9)],
        'CRT':[crt_replay(a,b) for a,b in ((2,3),(3,4),(3,5),(4,5),(5,7))],
        'degeneracy':[degeneracy_replay(l,m) for l,m in ((2,4),(3,6),(3,9),(4,8),(5,10),(4,12))]})
    summary={'source_sha256':sources,'recovered_families':4,'surface_genera':[row['genus'] for row in hodge],
        'harmonic_dimensions':[row['dimensions'][2] for row in hodge],'derived_curves':len(lifted),'lifted_point_counts':counts,
        'primitive_quintic_solutions_in_box':len(bounded['solutions']),'outer_source_audit':audit,
        'commutant_dimensions':{p['level']:p['dimension'] for p in weil},'exact_replay':True,'new_lean_theorems':0}
    write('summary.json',summary);return summary


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,default=ROOT/'receipts/deep_gems')
    print(json.dumps(build(parser.parse_args().output),indent=2,sort_keys=True))
