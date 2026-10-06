"""Deterministic elliptic witness, complete division-fibre and service corpus."""
import argparse
import hashlib
import json
import tempfile
from pathlib import Path
from perfectpower.elliptic_arithmetic import EllipticCurve,encode_point
from perfectpower.elliptic_certificates import certify_independence
from perfectpower.elliptic_certificate_verifier import verify_halves,verify_independence
from perfectpower.elliptic_quotients import EllipticQuotientFamily
from perfectpower.catalogue import Catalogue,encoded
from perfectpower.query_service import dispatch


def develop(output):
    output=Path(output);output.mkdir(parents=True,exist_ok=True);packets={}
    E=EllipticCurve([0,-2]);P=E.checked([3,5]);two=E.mul(P,2)
    packets['single_half']=E.rational_halves(two)
    packets['empty_half']=E.rational_halves(P)
    packets['infinity']=EllipticCurve([-1,0]).rational_halves(None)
    F=EllipticCurve([-25,0]);p=F.checked(['25/4','75/8'])
    packets['four_halves']=F.rational_halves(F.mul(p,2))
    E=EllipticCurve([-4,1]);points=[[0,1],[2,1]]
    packets['independent_pair']=certify_independence(E,points,prime_bound=100)
    packets['halved_pair']=certify_independence(E,[encode_point(E.mul(p,2)) for p in points],prime_bound=100)
    packets['dependent_pair']=certify_independence(E,[[0,1],[0,-1]],prime_bound=100,halving_limit=4)
    F=EllipticCurve([-2,0])
    packets['torsion_halving']=certify_independence(F,[encode_point(F.mul([2,2],2))],prime_bound=100,halving_limit=4)
    F=EllipticCurve([1,'-1/4',1,'-1/2','-9/4'])
    packets['model_transport']=F.model_transport([3,3],{'ainvs':[0,-2]})
    packets['two_isogeny']=EllipticCurve([-2,0]).two_isogeny([0,0],[2,2])
    quotient=EllipticQuotientFamily({'coefficients':[1,0,-4,0,0,0,1]})
    packets['quotient_lifts']=dict(source='y^2=x^6-4*x^2+1',quotient=E.specification,
        independent_quotient_points=points,
        fibres=[quotient.rational_lifts(0,*p) for p in points],
        explanation='Both quotient witnesses are independent; only the first lifts rationally. Independence does not remove the square condition on u=x^2.')
    for name,packet in packets.items():
        if packet.get('schema')=='pp-rational-halves/1' and not verify_halves(packet):raise AssertionError(name)
        if packet.get('schema')=='pp-elliptic-independence/2' and not verify_independence(packet):raise AssertionError(name)
        (output/(name+'.json')).write_text(json.dumps(json.loads(encoded(packet)),indent=2,sort_keys=True)+'\n')
    requests=[dict(op='register',kind='elliptic_curve',specification=E.specification,name='E'),
        dict(op='call',object='E',method='summary'),
        dict(op='call',object='E',method='point_multiply',args=dict(p=[0,1],scalar=2)),
        dict(op='call',object='E',method='rational_halves',args=dict(p=encode_point(E.mul([0,1],2)))),
        dict(op='call',object='E',method='independence',args=dict(points=points,prime_bound=100)),
        dict(op='verify_elliptic_halves',args=dict(cert=packets['single_half'])),
        dict(op='verify_elliptic_independence',args=dict(cert=packets['halved_pair']))]
    responses=[]
    with tempfile.TemporaryDirectory() as directory:
        database=Path(directory)/'objects.sqlite'
        # Close and reopen after registration, checking the persisted definition.
        for request in requests:
            with Catalogue(database) as catalogue:
                response=dispatch(catalogue,request)
            responses.append(dict(schema='pp-query-response/1',request_id=None,ok=True,result=response))
    (output/'service_requests.jsonl').write_text(''.join(encoded(r)+'\n' for r in requests))
    (output/'service_responses.jsonl').write_text(''.join(encoded(r)+'\n' for r in responses))
    names=sorted(p.name for p in output.iterdir() if p.name!='summary.json' and p.suffix in ('.json','.jsonl'))
    summary=dict(schema='pp-elliptic-witness-corpus/1',scientific_packets=len(packets),service_requests=len(requests),
        complete_rational_halving_fibres=4,independent_witness_pair_rank=2,recorded_pair_halvings=len(packets['halved_pair']['halving_steps']),
        execution_verified=False,complete_mordell_weil_basis=False,
        files={name:hashlib.sha256((output/name).read_bytes()).hexdigest() for name in names})
    (output/'summary.json').write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n')
    return summary


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',default='receipts/elliptic_witnesses')
    print(json.dumps(develop(parser.parse_args().output),sort_keys=True))
