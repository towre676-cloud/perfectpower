"""Retain bounded population proofs and two marked Legendre generator receipts."""
import argparse
import hashlib
import json
from pathlib import Path
import time
from perfectpower.native_population_certificate import population_certificate
from perfectpower.period_matrix_balls import marked_legendre_monodromy

ROOT=Path(__file__).resolve().parents[1]
ZERO=['1/2',['1/2','1/4'],['-1/4','1/4'],['-1/4','-1/4'],['1/2','-1/4'],'1/2']
ONE=['1/2',['1/2','-1/4'],['5/4','-1/4'],['5/4','1/4'],['1/2','1/4'],'1/2']


def develop(output, periods=False):
    output=Path(output);output.mkdir(parents=True,exist_ok=True)
    def save(name, packet):
        (output/name).write_text(json.dumps(packet,sort_keys=True,indent=2)+'\n')
    predicate={'op':'or','args':[{'poly':[0,1],'relation':'<','modulus':4,'value':2},
                                {'poly':[-9,0,1],'relation':'='}]}
    packet=population_certificate(-12,12,predicate,[0,0,1],ranks=[0,3,9])
    save('population.json',packet)
    if periods:
        for name,path,expected in [('around-one',ONE,[[1,0],[-2,1]]),('inverse-zero',list(reversed(ZERO)),[[1,-2],[0,1]])]:
            started=time.perf_counter()
            result=marked_legendre_monodromy(path,order=24)
            if result['monodromy'] != expected:raise ArithmeticError('Marked generator regression: '+name)
            save(name+'.json',dict(path=path,order=24,seed_terms=48,rounding_bits=128,
                step_limit=256,result=result))
            print(name,result['monodromy'],time.perf_counter()-started,flush=True)
        zero=json.loads((ROOT/'receipts/nonflavor_frontier/legendre-monodromy.json').read_text())['result']['monodromy']
        one=json.loads((output/'around-one.json').read_text())['result']['monodromy']
        reverse=json.loads((output/'inverse-zero.json').read_text())['result']['monodromy']
        def mul(a,b):return [[sum(a[i][k]*b[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
        identity=[[1,0],[0,1]]
        if mul(zero,reverse)!=identity:raise ArithmeticError('Inverse orientation identity failed')
        if mul(zero,one)==mul(one,zero):raise ArithmeticError('Generators unexpectedly commute')
        save('generator-algebra.json',dict(zero=zero,one=one,inverse_zero=reverse,
            zero_then_one_matrix_product=mul(zero,one),one_then_zero_matrix_product=mul(one,zero),
            inverse_identity_checked=True,noncommuting=True,
            scope='exact algebra of individually certified matrices; no new concatenated-path analytic receipt'))
    source_paths=['PerfectPower/CauchyBinet.lean','PerfectPower/FiniteDomainCertificate.lean',
                  'python/perfectpower/native_population_certificate.py',
                  'python/perfectpower/period_matrix_balls.py','python/perfectpower/query_service.py']
    save('source-bindings.json',{p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in source_paths})


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,default=ROOT/'receipts/connected_closures')
    parser.add_argument('--periods',action='store_true');args=parser.parse_args();develop(args.output,args.periods)
