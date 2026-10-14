"""Exact all-chamber scan and a reused compilation benchmark."""
import sys,time,json,csv,math
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'python'))
from perfectpower.arithmetic_modes import SlopeAtlas,signed_ballot
from perfectpower.arithmetic_transport import height_ballot
OUT=ROOT/'receipts/arithmetic_modes'
def main():
    started=time.perf_counter();rows=[];violations=[]
    for d in range(1,65):
        a=SlopeAtlas(d)
        for wall,(count,signed) in zip(a.walls,a.results):
            rows.append({'d':d,'wall':str(wall),'count':str(count),'signed':str(signed)})
            if d%2 and signed>=0:violations.append({'d':d,'wall':str(wall),'signed':signed})
        if d%8==0:print('complete slope atlas',d,'chambers',len(a.walls),flush=True)
    with (OUT/'slope_chambers.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0],lineterminator='\n');w.writeheader();w.writerows(rows)
    t=time.perf_counter();a=SlopeAtlas(64);compile_seconds=time.perf_counter()-t
    primes=[n for n in range(2,500) if all(n%k for k in range(2,math.isqrt(n)+1))]
    bank=[(p,q) for i,p in enumerate(primes) for q in primes[i+1:]][:2000]
    t=time.perf_counter();compiled=[a.query(p,q) for p,q in bank];lookup=time.perf_counter()-t
    t=time.perf_counter();direct=[(height_ballot(p,q,64)['count'],signed_ballot(p,q,64)) for p,q in bank];baseline=time.perf_counter()-t
    assert all(int(c['count'])==d[0] and int(c['signed'])==d[1] for c,d in zip(compiled,direct))
    receipt={'schema':'pp-slope-chambers/1','horizons':64,'chambers':len(rows),'odd_sign_counterexamples':violations,
        'conjecture':'For every λ≥1, odd d has strictly negative signed ballot coefficient; checked through d=63, not proved generally.',
        'compile_exponent':64,'compile_seconds':compile_seconds,'queries':len(bank),'lookup_seconds':lookup,
        'direct_seconds':baseline,'warm_lookup_speedup':baseline/lookup,'including_setup_seconds':compile_seconds+lookup,
        'break_even_queries':math.ceil(compile_seconds/(baseline/len(bank)-lookup/len(bank))),
        'seconds':time.perf_counter()-started,'scope':'Comparison with the retained direct exact recurrences on this query bank; not arbitrary-workload superiority.'}
    (OUT/'slope_benchmark.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
