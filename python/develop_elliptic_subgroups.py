"""Exact hidden division relations and complete rational subgroup preimages."""
import argparse
import hashlib
import json
import tempfile
from pathlib import Path
from perfectpower.elliptic_arithmetic import EllipticCurve,encode_point
from perfectpower.elliptic_subgroup_verifier import verify_subgroup_preimage
from perfectpower.elliptic_certificates import certify_independence
from perfectpower.catalogue import Catalogue,encoded
from perfectpower.query_service import dispatch


def develop(output):
    output=Path(output);output.mkdir(parents=True,exist_ok=True)
    E=EllipticCurve([-4,1]);P=E.checked([0,1]);Q=E.checked([2,1])
    two=[E.add(P,Q),E.add(P,E.neg(Q))]
    three=[E.add(E.mul(P,2),Q),E.add(P,E.mul(Q,2))]
    packets=dict(hidden_two_relation=E.subgroup_preimage(two,2),
                 hidden_three_relation=E.subgroup_preimage(three,3),
                 basis_two_closed=E.subgroup_preimage([P,Q],2),
                 basis_three_closed=E.subgroup_preimage([P,Q],3),
                 duplicate_generators=E.subgroup_preimage([P,P],2),
                 four_zero_generators=E.subgroup_preimage([None]*4,3))
    F=EllipticCurve([-3,-12,-12,0,0]);T=F.mul([0,0],3)
    packets['order_three_to_nine']=F.subgroup_preimage([T],3)
    F=EllipticCurve([1,'-1/4',1,'-1/2','-9/4']);h=F.checked([3,3])
    packets['generalized_three_replacement']=F.subgroup_preimage([F.mul(h,3)],3)
    F=EllipticCurve([0,-2]);h=F.checked([3,5])
    packets['rank_one_two_stage']=F.subgroup_preimage([F.mul(h,6)],2)
    packets['rank_one_three_stage']=F.subgroup_preimage(packets['rank_one_two_stage']['generators'],3)
    for name,packet in packets.items():
        if not verify_subgroup_preimage(packet):raise AssertionError(name)
        (output/(name+'.json')).write_text(json.dumps(json.loads(encoded(packet)),indent=2,sort_keys=True)+'\n')
    expected=sorted([encode_point(P),encode_point(Q)])
    for name in ('basis_two_closed','basis_three_closed'):
        assert packets[name]['relation_basis']==[]
        assert packets[name]['kernel_fibre']['points']==[None]
        assert packets[name]['generators']==expected
    independence=certify_independence(E,[encode_point(P),encode_point(Q)],prime_bound=100)
    assert independence['rank_lower_bound']==2
    (output/'witness_independence.json').write_text(json.dumps(independence,indent=2,sort_keys=True)+'\n')
    requests=[dict(op='register',kind='elliptic_curve',specification=E.specification,name='E'),
              dict(op='call',object='E',method='subgroup_preimage',args=dict(points=[encode_point(h) for h in two],prime=2)),
              dict(op='call',object='E',method='subgroup_preimage',args=dict(points=[encode_point(h) for h in three],prime=3)),
              dict(op='verify_elliptic_subgroup_preimage',args=dict(cert=packets['hidden_three_relation']))]
    responses=[]
    with tempfile.TemporaryDirectory() as tmp:
        db=Path(tmp)/'objects.sqlite'
        for request in requests:
            with Catalogue(db) as cat:answer=dispatch(cat,request)
            responses.append(dict(schema='pp-query-response/1',ok=True,request_id=None,result=answer))
    (output/'service_requests.jsonl').write_text(''.join(encoded(r)+'\n' for r in requests))
    (output/'service_responses.jsonl').write_text(''.join(encoded(r)+'\n' for r in responses))
    files=sorted(p for p in output.iterdir() if p.suffix in ('.json','.jsonl') and p.name!='summary.json')
    summary=dict(schema='pp-elliptic-subgroup-corpus/1',preimage_packets=len(packets),
                 cold_service_responses=len(responses),hidden_two_relation=[1,1],hidden_three_relation=[1,1],
                 witness_rank_lower_bound=independence['rank_lower_bound'],
                 witness_subgroup_closed_under_primes=[2,3],execution_verified=False,
                 complete_mordell_weil_group=False,
                 files={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in files})
    (output/'summary.json').write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n')
    return summary


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',default='receipts/elliptic_subgroups')
    print(json.dumps(develop(p.parse_args().output),sort_keys=True))
