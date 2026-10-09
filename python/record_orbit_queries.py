"""Retain reconstruction and acceptance of original-coordinate orbit reductions."""
import hashlib
import json
from pathlib import Path
from perfectpower.automatic_population import automatic_population_certificate,check_automatic_population
from perfectpower.checked_pell_orbits import pell_orbits_certificate,check_pell_orbits

ROOT=Path(__file__).resolve().parents[1]


def main():
    queries=[dict(condition=['mod','x',1,3],ranks=[0,999],objective=['pow','y',2])]
    cases=[('two_orbits_rank1000',pell_orbits_certificate(2,7,100,queries,global_ranks=[dict(orbit=0,rank=1000),dict(orbit=1,rank=1000)]),check_pell_orbits),
        ('negative_norm_zero_root',pell_orbits_certificate(3,-3,100,[{}]),check_pell_orbits),
        ('zero_norm',pell_orbits_certificate(2,0,100,[{}]),check_pell_orbits),
        ('empty_norm',pell_orbits_certificate(2,3,100,[{}]),check_pell_orbits)]
    for label,cs,cap,domain in [('square',[15,0,1],None,'integer'),('scaled_square',[1,1,1],None,'integer'),
        ('quadratic_large',[1,1,2],10**12,'integer'),('quadratic_positive',[-2,-3,2],100,'positive'),
        ('cubic',[-2,0,0,1],None,'integer'),('minus13',[-13,0,0,1],None,'integer'),
        ('descent',[-9985,0,0,1],None,'integer')]:
        cases.append((label,automatic_population_certificate(cs,queries,cutoff=cap,domain=domain),check_automatic_population))
    records=[];destination=ROOT/'receipts/orbit_reduction_queries.json'
    retained={r['name']:r for r in json.loads(destination.read_text())['records']} if destination.exists() else {}
    for label,packet,check in cases:
        previous=retained.get(label)
        if previous and previous['source_sha256']==packet['source_sha256'] and all(
                hashlib.sha256((ROOT/'PerfectPower'/f'{name}.lean').read_bytes()).hexdigest()==h
                for name,h in previous['library_sha256'].items()):
            records.append(previous)
            print(label+': retained kernel check matches current sources',flush=True)
            continue
        result=check(packet,timeout=240)
        if not result['accepted']:raise RuntimeError(label+': '+json.dumps(result))
        records.append(dict(name=label,specification=packet['specification'],source_count=packet['source_count'],
            source_points=packet['source_points'],results=packet['results'],
            specification_sha256=packet['specification_sha256'],source_sha256=packet['source_sha256'],
            library_sha256=result['library_sha256'],log_sha256=hashlib.sha256(result['log'].encode()).hexdigest(),
            proof_status='kernel_checked',execution_verified=False,scope=packet['scope']))
        destination.write_text(json.dumps(dict(schema='pp-orbit-reduction-replay/1',complete=False,records=records),indent=2)+'\n')
        print(label+': kernel checked',flush=True)
    destination.write_text(json.dumps(dict(schema='pp-orbit-reduction-replay/1',complete=True,records=records),indent=2)+'\n')


if __name__=='__main__':main()
