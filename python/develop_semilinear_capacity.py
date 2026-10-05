"""Reproducible stored quartic, Bober recurrence and finite-image experiments.

Independent references use bounded exhaustive evaluation, literal affine
factors and previously proved outer point lists. No industrial speed claim.
"""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from math import isqrt
from pathlib import Path
import os
import subprocess
from time import perf_counter
from perfectpower import polyalg as P
from perfectpower.compiler import mordell_complete
from perfectpower.arithmetic_engine import ArithmeticEngine,verify_result
from perfectpower.polynomial_images import sign_domain_solve,verify_sign_solve
from perfectpower.semilinear_domains import (semilinear_domain,optimize_semilinear,verify_domain,
    verify_optimization,count_domain,select)
from perfectpower.curve_queries import query_curve,verify_curve_query
from perfectpower.gamma_arithmetic import hypergeometric


ROOT=Path(__file__).resolve().parents[1]


def digest(value):return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def value(f,n):return sum(c*n**i for i,c in enumerate(f))
def write(path,data):path.write_text(json.dumps(data,indent=2)+'\n')
def power(a,b,p,k):
    f=list(map(int,P.power(P.poly([b,a]),p)));f[0]+=k;return f
def conjunction(*args):return {'op':'and','args':list(args)}


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--limit',type=int)
    parser.add_argument('--baseline-python',type=Path);parser.add_argument('--output',type=Path,default=ROOT/'receipts/semilinear_capacity')
    args=parser.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    quartic_file=ROOT/'receipts/divisor_sum/complete_quartics.json';bober_file=ROOT/'data/gamma_bober52.json'
    quartics=json.loads(quartic_file.read_text())['rows'];bober=json.loads(bober_file.read_text())['rows']
    if args.limit is not None:quartics=quartics[:args.limit]
    started=perf_counter();optimization=[];negative=[]
    for i,row in enumerate(quartics):
        f=row['coefficients'];residues={i%7,(i+3)%7}
        predicate=conjunction({'op':'or','args':[{'poly':[0,1],'modulus':7,'relation':'=','value':r} for r in sorted(residues)]},
                              {'poly':f,'modulus':5,'relation':'!=','value':0})
        result=optimize_semilinear(predicate,f)
        if not verify_optimization(result):raise AssertionError('optimizer replay')
        bound=P.cauchy_bound(P.derivative(P.poly(f)))+35
        values=[(n,value(f,n)) for n in range(-bound,bound+1) if n%7 in residues and value(f,n)%5!=0]
        best=min(v for n,v in values);points=[n for n,v in values if v==best]
        if result['value']!=best or result['points']!=points:raise AssertionError('independent lattice optimum disagreement')
        optimization.append({'source':i,'value':best,'points':points,'reference_bound':bound,'root_nodes':result['root_nodes'],'answer_sha256':digest([best,points])})
        opposite=[-c for c in f];solved=sign_domain_solve(opposite)
        if not verify_sign_solve(solved):raise AssertionError('finite sign replay')
        bound=P.cauchy_bound(P.poly(f));expected=[]
        for x in range(-bound,bound+1):
            y2=-value(f,x)
            if y2<0:continue
            y=isqrt(y2)
            if y*y==y2:expected.extend((x,v) for v in sorted({y,-y}))
        if solved['points']!=expected:raise AssertionError('negative quartic reference disagreement')
        negative.append({'source':i,'points':len(expected),'answer_sha256':digest(expected),'candidates':solved['statistics']['candidates_checked']})
        if (i+1)%500==0:print(f'quartic objectives and opposite signs {i+1}/{len(quartics)}',flush=True)
    recurrence=[];h=10**100
    for i,row in enumerate(bober):
        rec=hypergeometric(row['numerator'],row['denominator'])
        for prime in (5,7,11,13,17,19,23,29,31,37,41,43,47):
            predicate=conjunction({'poly':[0,1],'relation':'>='},
                {'poly':rec['P'],'modulus':prime,'relation':'!=','value':0},
                {'poly':rec['Q'],'modulus':prime,'relation':'!=','value':0})
            domain=semilinear_domain(predicate)
            allowed=[]
            for r in range(prime):
                top=bottom=1
                for c in row['numerator']:
                    for j in range(1,c+1):top=top*(c*r+j)%prime
                for c in row['denominator']:
                    for j in range(1,c+1):bottom=bottom*(c*r+j)%prime
                if top and bottom:allowed.append(r)
            q,remainder=divmod(h+1,prime);expected=q*len(allowed)+sum(r<remainder for r in allowed)
            picked=prime*(h//len(allowed))+allowed[h%len(allowed)] if allowed else None
            if not verify_domain(domain) or count_domain(domain,0,h)!=expected or select(domain,h)!=picked or domain['nonnegative_density']!=str(Q(len(allowed),prime)):
                raise AssertionError('Bober recurrence literal-factor reference disagreement')
            recurrence.append({'source':row['table_line'],'prime':prime,'allowed':allowed,'count_0_to_10e100':expected,'selected_rank_10e100':picked,'density':domain['nonnegative_density']})
    print('all 52 independently sourced recurrence families complete',flush=True)
    engine=ArithmeticEngine();images=[];image_inputs=[]
    for k in range(-100,101):
        if not k:continue
        known=mordell_complete(k)
        if known is None:continue
        table,theorems=known
        for a,b in ((1,0),(3,k%7-3)):
            root=[b*b-k,2*a*b,a*a];f=list(map(int,P.power(P.poly(root),2)))
            result=engine.solve(f,3)
            expected=sorted({((v-b)//a,u*u) for u,ys in table.items() for y in ys for v in {y,-y} if (v-b)%a==0})
            if result['status']!='COMPLETE' or result['points']!=expected or not verify_result(result):raise AssertionError(('finite image reference',k,a,result['status']))
            image_inputs.append(f);images.append({'k':k,'a':a,'b':b,'points':expected,'proof_kind':result['proof']['kind']})
    baseline=None
    if args.baseline_python is not None:
        code="import json,sys;from perfectpower.arithmetic_engine import ArithmeticEngine; e=ArithmeticEngine();print(json.dumps([e.solve(f,3)['status'] for f in json.load(sys.stdin)]))"
        env=dict(os.environ,PYTHONPATH=str(args.baseline_python.resolve()))
        statuses=json.loads(subprocess.check_output(['python','-c',code],input=json.dumps(image_inputs).encode(),env=env,cwd=args.baseline_python.resolve().parent))
        baseline={'complete':statuses.count('COMPLETE'),'new_complete':len(statuses)-statuses.count('COMPLETE'),'scope':'same finite-image inputs under supplied baseline Python checkout'}
        for row,status in zip(images,statuses):row['baseline_status']=status
    print(f'complete finite-image curves {len(images)}',flush=True)
    boxed=[]
    for i,row in enumerate(quartics[:128]):
        f=row['coefficients'];a=abs(f[0])%7+1;b=f[1]-3;c=(i%7)+1;d=f[2]-2;p=2+i%5;q=2+(i//5)%5;k=f[0]
        left,right=power(a,b,p,k),power(c,d,q,k)
        predicate=conjunction(*[{'expr':expr,'relation':op} for expr,op in (('x+30','>='),('x-30','<='),('y+30','>='),('y-30','<='))],
                              {'expr':'x','modulus':5,'relation':'!=','value':i%5})
        result=query_curve(left,right,predicate,objective='x*x+x*y+y*y-3*x+2*y',point_limit=5000)
        expected=[(x,y) for x in range(-30,31) for y in range(-30,31) if (a*x+b)**p==(c*y+d)**q and x%5!=i%5]
        if result['points']!=expected or result['solution_count']!=len(expected) or not verify_curve_query(result):raise AssertionError('boxed curve reference disagreement')
        if expected:
            values=[(x*x+x*y+y*y-3*x+2*y,(x,y)) for x,y in expected];v=min(v for v,p in values);ties=[p for value,p in values if value==v]
            if result['optimization']['value']!=str(v) or result['optimization']['optimizer_points']!=ties:raise AssertionError('boxed bivariate objective disagreement')
        elif result['optimization']['status']!='EMPTY':raise AssertionError('empty box objective')
        boxed.append({'source':i,'powers':[p,q],'solution_count':len(expected),'optimization':result['optimization']})
    huge_predicate=conjunction(*[{'expr':expr,'relation':op} for expr,op in (('x','>='),('y','>='),(f'x-{10**90}','<='),(f'y-{10**90}','<='))])
    huge_count=query_curve([0,0,1],[0,0,0,1],huge_predicate)
    huge_opt=query_curve([0,0,1],[0,0,0,1],objective=f'(y-{10**60})**2')
    if huge_count['solution_count']!=10**30+1 or not verify_curve_query(huge_count) or not verify_curve_query(huge_opt):raise AssertionError('huge curve check')
    summary={'schema':'pp-semilinear-capacity-corpus/1','quartic_sources':len(quartics),'lattice_optima':len(optimization),
             'negative_quartics':len(negative),'bober_families':len(bober),'recurrence_modular_domains':len(recurrence),
             'finite_image_curves':len(images),'finite_image_baseline':baseline,'constructed_boxed_queries':len(boxed),
             'huge_curve_count':huge_count['solution_count'],'huge_optimizer_points':huge_opt['optimization']['optimizer_points'],
             'disagreements':0,'elapsed_seconds':perf_counter()-started,'execution_verified':False,
             'quartic_source_sha256':hashlib.sha256(quartic_file.read_bytes()).hexdigest(),
             'bober_source_sha256':hashlib.sha256(bober_file.read_bytes()).hexdigest(),
             'scope':'stored mathematical data and constructed queries; no industrial benchmark or world-record claim'}
    for name,data in (('summary',summary),('lattice_optima',optimization),('negative_quartics',negative),('bober_domains',recurrence),('finite_images',images),('boxed_queries',boxed),('huge_curve_count',huge_count),('huge_curve_optimum',huge_opt)):
        write(args.output/(name+'.json'),data)
    print(json.dumps(summary,indent=2),flush=True)


if __name__=='__main__':main()
