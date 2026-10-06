"""Matrix-level flavor envelopes and exact inverse-Hessian response compilation."""
from pathlib import Path
from fractions import Fraction as Q
import argparse
import hashlib
import json
import sys
from perfectpower import polyalg as P
from perfectpower.flavor_matrix_response import (
    constants,operator_norm_envelope,verify_norm_envelope,
    rectangular_norm_envelope,verify_rectangular_envelope,
    protected_response,verify_protected_response,positive_definite,
    relaxed_response,verify_response)

ROOT=Path(__file__).resolve().parents[1]
SOURCE=ROOT/'receipts/m22_interactions/flavor_spectral_matching.json'
OUTPUT=ROOT/'receipts/flavor_cosmology/matrix_response.json'


def retained_metric(data):
    K=data['derivative_metric'];n=len(K)
    # Exact rational symmetrization of published binary floats, explicitly
    # distinguished from an exact algebraic-number finite-group realization.
    return [[(Q(K[i][j])+Q(K[j][i]))/2-(i==j) for j in range(n)] for i in range(n)]


def propagator_fixture():
    # Consume the two-source, three-unequal-mediator exact Gaussian fixture.
    H=[[Q(3),Q(1,3)],[Q(1,3),Q(2)]]
    D=[[1,2],[2,-1],[1,1]];mass2=[11,13,17]
    K=[[Q(i==j)+sum(Q(row[i]*row[j],m*m) for row,m in zip(D,mass2)) for j in range(2)] for i in range(2)]
    F=[[[H[i][j],K[i][j]] for j in range(2)] for i in range(2)]
    protection=protected_response(F,[[1],[0]],[[0],[1]],'3/50')
    assert verify_protected_response(protection)
    # Euclidean scalar two-point cross response, not a quark CP derivative.
    return {'H':[[str(x) for x in row] for row in H], 'D':D,'mediator_mass_squared':mass2,
            'tree_metric':[[str(x) for x in row] for row in K],
            'parameter':'nonnegative Euclidean squared momentum',
            'certified_response':protection,
            'static_relaxed_response':'3/53',
            'static_propagator_cross_entry':'-3/53',
            'scope':'Exact local two-derivative Euclidean scalar response for the published rational Gaussian fixture. No quark matching or replacement of its finite nonlocal propagator.'}


def build(raw):
    old=json.loads(raw);records={}
    for name,b,cross in [('finite27','567/500000','391/1000000'),('universal55','321/250000','83/200000')]:
        E=retained_metric(old['finite_scalar_matching'][name]);matrix=constants(E)
        cert=operator_norm_envelope(matrix,b)
        B=[[[E[i][j]] for j in range(10,20)] for i in range(10)]
        cross_cert=rectangular_norm_envelope(B,cross)
        assert verify_norm_envelope(cert) and verify_rectangular_envelope(cross_cert)
        records[name]={'source_coordinates':len(E),'metric_error_certificate':cert,
                       'cross_sector_certificate':cross_cert,
                       'mass10_metric_norm_upper':b,'mass10_cross_sector_norm_upper':cross,
                       'all_mass_metric_norm_upper':'(10/M)^2*'+b,
                       'all_mass_cross_sector_norm_upper':'(10/M)^2*'+cross,
                       'rounded_metric_positive_mass_squared_condition':str(100*Q(b))}
    fixture=propagator_fixture()
    # A pole outside the declared range must remain in the compiled denominator.
    H=[[[1],[0,1]],[[0,1],[1]]]
    finite=protected_response(H,[[1],[0]],[[1],[0]],'27/20',interval=('0','1/2'))
    assert verify_protected_response(finite)
    cancellation=relaxed_response(H,[[1],[0,1]],[[1],[0]],direct=[1])
    assert cancellation['numerator']==['0'] and cancellation['denominator']==['1','0','-1'] and verify_response(cancellation)
    return {'schema':'pp-flavor-matrix-response-release/1',
            'input_sha256':hashlib.sha256(raw).hexdigest(),
            'baseline_commit':'fc89cf403b33a6a029c81a0ed865ceaaf2f6c9c6',
            'metric_envelopes':records,'Gaussian_propagator_fixture':fixture,
            'finite_interval_fixture':finite,'singularity_preserving_cancellation':cancellation,
            'matrix_metric_realization':'Exact symmetrized binary-rational realization of the published derivative metrics; not exact algebraic finite-group tensors. Differences from the input arrays are only the explicitly averaged off-diagonal pairs.',
            'mass_transport':'At fixed EFT couplings the Gaussian current Jacobian scales with M, so the tree metric correction scales as 1/M^2. Transport of the retained rational matrix is exact; the physical matching origin is inherited from the published Gaussian completion.',
            'normalization_theorem':'For epsilon=(10/M)^2*b<1, all eigenvalues of the retained K_M lie in (1-epsilon,1+epsilon). Thus the rounded metric is positive and every canonically generalized eigenvalue of any supplied positive H lies between lambda_i(H)/(1+epsilon) and lambda_i(H)/(1-epsilon). This is a conditional normalization envelope, not a certified quark kinetic metric or an evaluation of H.',
            'scope':'Tree scalar matrix envelopes and supplied reduced-Hessian response budgets only. No actual strong-CP response, golden mixing prediction, new vacuum, complete two-loop matching or exact finite pole computation.',
            'formal_verification':False}


def verify_report(report,raw):
    try:
        if report['schema']!='pp-flavor-matrix-response-release/1' or report['formal_verification'] is not False or report['input_sha256']!=hashlib.sha256(raw).hexdigest():return False
        old=json.loads(raw)
        if set(report['metric_envelopes'])!={'finite27','universal55'}:return False
        for name,row in report['metric_envelopes'].items():
            E=retained_metric(old['finite_scalar_matching'][name]);n=len(E);cert=row['metric_error_certificate'];cross=row['cross_sector_certificate']
            if row['source_coordinates']!=n or not verify_norm_envelope(cert) or not verify_rectangular_envelope(cross):return False
            if [[list(map(Q,p)) for p in r] for r in cert['matrix']]!=[[[x] for x in r] for r in E]:return False
            if [[list(map(Q,p)) for p in r] for r in cross['block']]!=[[[E[i][j]] for j in range(10,20)] for i in range(10)]:return False
            if Q(row['mass10_metric_norm_upper'])!=Q(cert['bound']) or Q(row['mass10_cross_sector_norm_upper'])!=Q(cross['bound']) or Q(row['rounded_metric_positive_mass_squared_condition'])!=100*Q(cert['bound']):return False
        f=report['Gaussian_propagator_fixture']
        # Link to the explicitly declared exact Gaussian fixture without running
        # positivity discovery: rebuild only polynomial matrix arithmetic.
        if f['H']!=[['3','1/3'],['1/3','2']] or f['D']!=[[1,2],[2,-1],[1,1]] or f['mediator_mass_squared']!=[11,13,17]:return False
        D=f['D'];m=f['mediator_mass_squared'];K=[[Q(i==j)+sum(Q(r[i]*r[j],s*s) for r,s in zip(D,m)) for j in range(2)] for i in range(2)]
        if [list(map(Q,r)) for r in f['tree_metric']]!=K:return False
        if f['static_relaxed_response']!='3/53' or f['static_propagator_cross_entry']!='-3/53':return False
        wanted=[[[Q(f['H'][i][j]),K[i][j]] for j in range(2)] for i in range(2)]
        if [[list(map(Q,p)) for p in r] for r in f['certified_response']['response']['matrix']]!=wanted or not verify_protected_response(f['certified_response']):return False
        response=f['certified_response']['response']
        if response['observable_gradient']!=[['1'],['0']] or response['operator_gradient']!=[['0'],['1']] or response['direct']!=['0'] or f['certified_response']['budget']!='3/50':return False
        return verify_protected_response(report['finite_interval_fixture']) and verify_response(report['singularity_preserving_cancellation'])
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError):return False


if __name__=='__main__':
    sys.set_int_max_str_digits(0)
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--verify',action='store_true');args=parser.parse_args()
    raw=SOURCE.read_bytes()
    if args.verify:
        ok=verify_report(json.loads(OUTPUT.read_text()),raw);print(json.dumps({'matrix_response_replay':ok}));raise SystemExit(0 if ok else 1)
    report=build(raw);assert verify_report(report,raw)
    OUTPUT.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'matrix_metric_bounds':{k:r['mass10_metric_norm_upper'] for k,r in report['metric_envelopes'].items()},'cross_sector_bounds':{k:r['mass10_cross_sector_norm_upper'] for k,r in report['metric_envelopes'].items()},'Gaussian_cross_response_budget':'3/50'}))
