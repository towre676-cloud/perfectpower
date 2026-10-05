"""Stored-corpus expansion and independent polynomial-capacity measurements.

Uses existing complete quartic/Mordell lists as references. Pullback fibres
are independently enumerated by the integer rational-root theorem. Discrete
quartic minima are exhaustively checked inside a Cauchy bound for differences.
Timings describe this internal workload, not an industrial speedup claim.
"""
import argparse
import hashlib
import json
from math import isqrt
from pathlib import Path
from time import perf_counter
from perfectpower import polyalg as P
from perfectpower.compiler import mordell_complete
from perfectpower.decomposition import compose
from perfectpower.arithmetic_engine import ArithmeticEngine
from perfectpower.polynomial_composition import PolynomialCompiler,verify_compiled,discover_decompositions
from perfectpower.polynomial_domains import integer_domain,optimize_polynomial,verify_domain,verify_optimization
from perfectpower.polynomial_relations import solve_relation,verify_relation
from perfectpower.residue_cover import evaluate


ROOT=Path(__file__).resolve().parents[1]


def digest(value):return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def rational_integer_roots(f):
    f=list(f)
    while len(f)>1 and f[-1]==0:f.pop()
    roots=set()
    while len(f)>1 and f[0]==0:
        roots.add(0);f=f[1:]
    if len(f)==1:return sorted(roots)
    c=abs(f[0]);divisors=set()
    for d in range(1,isqrt(c)+1):
        if c%d==0:divisors.update((d,-d,c//d,-c//d))
    roots.update(n for n in divisors if sum(c*n**i for i,c in enumerate(f))==0)
    return sorted(roots)


def pullback_reference(inner,source):
    out=set()
    for u,v in source:
        shifted=list(inner);shifted[0]-=u
        out.update((x,v) for x in rational_integer_roots(shifted))
    return sorted(out)


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--limit',type=int)
    parser.add_argument('--output',type=Path,default=ROOT/'receipts'/'polynomial_capacity')
    args=parser.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    source_path=ROOT/'receipts'/'divisor_sum'/'complete_quartics.json'
    quartics=json.loads(source_path.read_text())['rows']
    if args.limit is not None:quartics=quartics[:args.limit]
    compiler=PolynomialCompiler();baseline=ArithmeticEngine();rows=[];examples=[]
    aggregate={'queries':0,'complete':0,'baseline_complete':0,'new_complete':0,
               'point_occurrences':0,'baseline_seconds':0.,'expanded_seconds':0.}
    def run(name,outer,inner,source):
        f=tuple(map(int,compose(outer,inner)));expected=pullback_reference(inner,source)
        start=perf_counter();old=baseline.solve(f,2,decomposition=False);old_time=perf_counter()-start
        start=perf_counter();new=compiler.solve(f,2);new_time=perf_counter()-start
        if new['status']!='COMPLETE' or new['points']!=expected or not verify_compiled(new):
            raise AssertionError((name,new['status'],new['points'],expected))
        if old['status']=='COMPLETE' and old['points']!=expected:raise AssertionError('baseline point conflict')
        aggregate['queries']+=1;aggregate['complete']+=1;aggregate['point_occurrences']+=len(expected)
        aggregate['baseline_complete']+=old['status']=='COMPLETE'
        aggregate['new_complete']+=old['status']!='COMPLETE'
        aggregate['baseline_seconds']+=old_time;aggregate['expanded_seconds']+=new_time
        rows.append({'name':name,'degree':len(f)-1,'coefficients_sha256':digest(f),
                     'points_sha256':digest(expected),'points':len(expected),
                     'baseline_status':old['status'],'status':new['status'],
                     'baseline_seconds':old_time,'expanded_seconds':new_time})
        if old['status']!='COMPLETE' and len(examples)<8:examples.append({'name':name,'result':new})
    for i,row in enumerate(quartics):
        for label,inner in (('cubic',[0,-4,1,1]),('nonmonic_quartic',[0,1,0,1,2])):
            run(f'quartic_{i}_{label}',row['coefficients'],inner,row['points'])
        if (i+1)%250==0:print(f'quartic sources {i+1}/{len(quartics)}',flush=True)
    for k in range(-100,101):
        if not k:continue
        known=mordell_complete(k)
        if known is None:continue
        table,theorems=known;source=sorted((u,v) for u,roots in table.items() for r in roots for v in {r,-r})
        shift=(next(iter(table))-4) if table else 7
        for label,inner in (('cubic',[shift,-4,1,1]),('quintic',[shift,-4,0,1,1,1])):
            run(f'mordell_{k}_{label}',[k,0,0,1],inner,source)
    optimization=[];domain_checks=0
    for i,row in enumerate(quartics):
        f=row['coefficients'];opt=optimize_polynomial(True,f)
        if opt['status']!='OPTIMAL' or not verify_optimization(opt):raise AssertionError('quartic optimizer')
        difference=P.subtract(P.compose_linear(P.poly(f),1,1),P.poly(f));bound=P.cauchy_bound(difference)+2
        values=[(x,sum(c*x**j for j,c in enumerate(f))) for x in range(-bound,bound+1)]
        best=min(v for x,v in values);points=[x for x,v in values if v==best]
        actual=[x for lo,hi in opt['optimizers'] for x in range(lo,hi+1)]
        if opt['value']!=best or actual!=points:raise AssertionError('independent minimum mismatch')
        predicate={'op':'or','args':[{'poly':f,'relation':'<='},{'poly':[i%11-5,1],'relation':'='}]}
        domain=integer_domain(predicate)
        if not verify_domain(domain):raise AssertionError('domain certificate')
        for x in range(-50,51):
            inside=any((lo is None or lo<=x) and (hi is None or x<=hi) for lo,hi in domain['intervals'])
            if inside!=(evaluate(f,x)<=0 or x+i%11-5==0):raise AssertionError('independent sign mismatch')
            domain_checks+=1
        optimization.append({'source':i,'minimum':best,'optimizers':opt['optimizers'],
                             'root_nodes':opt['root_nodes'],'oracle_radius':bound,
                             'domain_sha256':digest(domain['intervals'])})
    h=10**60;objective=tuple(map(int,P.power(P.poly([h*(h+1),-2*h-1,1]),2)))
    huge=optimize_polynomial(True,objective)
    if huge['value']!=0 or huge['optimizers']!=[[h,h+1]] or not verify_optimization(huge):raise AssertionError('huge ties')
    degree64=integer_domain({'poly':[-1]+[0]*63+[1],'relation':'='})
    if degree64['intervals']!=[[-1,-1],[1,1]]:raise AssertionError('degree64')
    relation=solve_relation([-2,0,0,1],[25,0,-10,0,1])
    if relation['points']!=[(3,0)] or not verify_relation(relation):raise AssertionError('two-sided equation')
    summary={'schema':'pp-polynomial-capacity-corpus/1',
             'scope':'stored mathematical corpus and constructed nonlinear pullbacks; no independent industrial performance claim',
             'source_sha256':hashlib.sha256(source_path.read_bytes()).hexdigest(),
             'quartic_sources':len(quartics),'arithmetic':aggregate,
             'optimization_cases':len(optimization),'independent_domain_values':domain_checks,
             'disagreements':0,'huge_tie_root_nodes':huge['root_nodes'],
             'execution_verified':False}
    files={'summary.json':summary,'arithmetic_rows.json':rows,'optimization_rows.json':optimization,
           'examples.json':examples,'huge_optimum.json':huge,'degree64_domain.json':degree64,
           'two_sided_relation.json':relation}
    for filename,data in files.items():(args.output/filename).write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(summary,indent=2))


if __name__=='__main__':main()
