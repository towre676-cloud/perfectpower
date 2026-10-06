"""Reproduce bounded saturation, real nodal endpoints and cold service replay."""
import argparse
import hashlib
import json
import tempfile
from pathlib import Path
from perfectpower.elliptic_arithmetic import EllipticCurve,encode_point
from perfectpower.elliptic_saturation_verifier import verify_saturation
from perfectpower.legendre_endpoint import endpoint_packet,verify_endpoint
from perfectpower.catalogue import Catalogue,encoded
from perfectpower.query_service import dispatch


def develop(output):
    out=Path(output);out.mkdir(parents=True,exist_ok=True)
    E=EllipticCurve([0,-2]);P=E.checked([3,5])
    saturation=dict(sixfold_witness=E.bounded_saturation([E.mul(P,6)]),
        duplicate_presentation=E.bounded_saturation([None,P,P,E.neg(P)]),
        unresolved_membership=E.bounded_saturation([P],coefficient_bound=0,max_steps=2),
        rational_torsion=EllipticCurve([0,1]).bounded_saturation([]))
    F=EllipticCurve([-4,1]);A=F.checked([0,1]);B=F.checked([2,1])
    saturation['hidden_two_relation']=F.bounded_saturation([F.add(A,B),F.add(A,F.neg(B))],max_steps=1)
    F=EllipticCurve([-36,0]);A=F.checked([12,36])
    saturation['width_stop']=F.bounded_saturation([F.mul(A,n) for n in [1,2,3,4]],coefficient_bound=0,max_steps=1)
    endpoints={f'endpoint_{i}':endpoint_packet(z,terms=48,bits=192,log_terms=128)
               for i,z in enumerate([0,'1/4','1/64','1/1048576','1/1099511627776'])}
    for name,c in saturation.items():
        assert verify_saturation(c),name
        (out/(name+'.json')).write_text(json.dumps(c,indent=2,sort_keys=True)+'\n')
    for name,c in endpoints.items():
        assert verify_endpoint(c),name
        (out/(name+'.json')).write_text(json.dumps(c,indent=2,sort_keys=True)+'\n')
    requests=[dict(op='register',kind='elliptic_curve',specification=E.specification,name='E'),
        dict(op='call',object='E',method='bounded_saturation',args=dict(points=[encode_point(E.mul(P,6))])),
        dict(op='verify_elliptic_saturation',args=dict(cert=saturation['sixfold_witness'])),
        dict(op='legendre_endpoint',args=dict(complement=0)),
        dict(op='verify_legendre_endpoint',args=dict(cert=endpoints['endpoint_2']))]
    responses=[]
    with tempfile.TemporaryDirectory() as tmp:
        for request in requests:
            with Catalogue(Path(tmp)/'objects.sqlite') as cat:answer=dispatch(cat,request)
            responses.append(dict(schema='pp-query-response/1',ok=True,request_id=None,result=answer))
    assert responses[1]['result']==saturation['sixfold_witness']
    assert responses[2]['result']['valid'] and responses[4]['result']['valid']
    (out/'service_requests.jsonl').write_text(''.join(encoded(r)+'\n' for r in requests))
    (out/'service_responses.jsonl').write_text(''.join(encoded(r)+'\n' for r in responses))
    files=sorted(p for p in out.iterdir() if p.suffix in ('.json','.jsonl') and p.name!='summary.json')
    result=dict(schema='pp-elliptic-bridges-corpus/1',saturation_packets=len(saturation),
        endpoint_packets=len(endpoints),cold_service_responses=len(responses),
        complete_mordell_weil_group=False,matveev_premises_removed=False,
        files={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in files})
    (out/'summary.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    return result


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',default='receipts/elliptic_bridges')
    print(json.dumps(develop(p.parse_args().output),sort_keys=True))
