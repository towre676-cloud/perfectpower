"""Reproduce complete rational division examples and cold-service transcripts."""
import argparse
import hashlib
import json
import tempfile
from pathlib import Path
from perfectpower.elliptic_arithmetic import EllipticCurve,encode_point
from perfectpower.elliptic_division_verifier import verify_thirds,verify_division
from perfectpower.catalogue import Catalogue,encoded
from perfectpower.query_service import dispatch


def develop(output):
    output=Path(output);output.mkdir(parents=True,exist_ok=True);packets={}
    E=EllipticCurve([0,1])
    packets['three_torsion']=E.rational_thirds(None)
    for n in (6,12,18,36):packets['six_torsion_'+str(n)]=E.rational_division(None,n)
    E=EllipticCurve([-3,-12,-12,0,0])
    for n in (3,9,18,27,36):packets['nine_torsion_'+str(n)]=E.rational_division(None,n)
    E=EllipticCurve([0,-2]);p=E.checked([3,5])
    for n in (3,6,12,18,36):packets['mordell_recover_'+str(n)]=E.rational_division(E.mul(p,n),n)
    packets['empty_thirds']=E.rational_thirds(p)
    packets['empty_eighteenths']=E.rational_division(p,18)
    E=EllipticCurve([1,'-1/4',1,'-1/2','-9/4']);p=E.checked([3,3])
    packets['generalized_thirtysixths']=E.rational_division(E.mul(p,36),36)
    E=EllipticCurve([0,9]);p=E.checked([3,6])
    packets['nontrivial_three_point_coset']=E.rational_thirds(E.mul(p,3))
    for name,packet in packets.items():
        check=verify_thirds if packet['schema']=='pp-rational-thirds/1' else verify_division
        if not check(packet):raise AssertionError(name)
        (output/(name+'.json')).write_text(json.dumps(json.loads(encoded(packet)),indent=2,sort_keys=True)+'\n')
    E=EllipticCurve([0,1])
    requests=[dict(op='register',kind='elliptic_curve',specification=E.specification,name='E'),
              dict(op='call',object='E',method='rational_thirds',args=dict(p=None)),
              dict(op='call',object='E',method='rational_division',args=dict(p=None,scalar=36)),
              dict(op='verify_elliptic_thirds',args=dict(cert=packets['three_torsion'])),
              dict(op='verify_elliptic_division',args=dict(cert=packets['nine_torsion_9'])),
              dict(op='verify_elliptic_division',args=dict(cert=packets['empty_eighteenths']))]
    responses=[]
    with tempfile.TemporaryDirectory() as directory:
        database=Path(directory)/'objects.sqlite'
        for request in requests:
            with Catalogue(database) as cat:answer=dispatch(cat,request)
            responses.append(dict(schema='pp-query-response/1',request_id=None,ok=True,result=answer))
    (output/'service_requests.jsonl').write_text(''.join(encoded(r)+'\n' for r in requests))
    (output/'service_responses.jsonl').write_text(''.join(encoded(r)+'\n' for r in responses))
    files=sorted(p for p in output.iterdir() if p.suffix in ('.json','.jsonl') and p.name!='summary.json')
    summary=dict(schema='pp-elliptic-division-corpus/1',scientific_packets=len(packets),
        cold_service_responses=len(responses),supported_scalars=[1,2,3,4,6,8,9,12,16,18,24,27,32,36],
        largest_rational_kernel_demonstrated=9,execution_verified=False,
        complete_mordell_weil_basis=False,global_integral_point_bound=False,
        files={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in files})
    (output/'summary.json').write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n')
    return summary


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',default='receipts/elliptic_composed_division')
    print(json.dumps(develop(parser.parse_args().output),sort_keys=True))
