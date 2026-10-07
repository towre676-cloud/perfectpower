"""Independent Python reference cases for the browser's polynomial calendar.

All JSON integers in the portable fixture are strings. Original-day predicates
are also brute checked in small windows, independently of both Sturm solvers.
"""
from pathlib import Path
import json,random
from perfectpower.dresden import Progression,polynomial_calendar,polynomial_calendar_select
from perfectpower.core import evaluate

ROOT=Path(__file__).resolve().parents[1]
rng=random.Random(20261007)
def atom(p,r):return {'poly':p,'relation':r}
def factors(roots):
    p=[1]
    for r in roots:
        q=[0]*(len(p)+1)
        for i,c in enumerate(p):q[i]-=r*c;q[i+1]+=c
        p=q
    return p
def holds(node,x):
    if type(node) is bool:return node
    if 'poly'in node:
        v=evaluate(node['poly'],x)
        return {'=':v==0,'!=':v!=0,'<':v<0,'<=':v<=0,'>':v>0,'>=':v>=0}[node['relation']]
    values=[holds(n,x)for n in node['args']]
    return all(values)if node['op']=='and'else any(values)if node['op']=='or'else not values[0]
def portable(v):
    if type(v)is int:return str(v)
    if isinstance(v,list):return [portable(x)for x in v]
    if isinstance(v,dict):return {k:portable(x)for k,x in v.items()}
    return v
cases=[]
def record(predicate,residue,period,lo,hi,rank):
    p=Progression(residue,period);result=polynomial_calendar(p,predicate,lo,hi)
    selected=polynomial_calendar_select(result,rank)if rank<result['count']else None
    if hi-lo<=400:
        brute=[d for d in range(lo,hi+1)if(d-p.residue)%p.modulus==0 and holds(predicate,d)]
        assert len(brute)==result['count']
        assert selected==(brute[rank]if rank<len(brute)else None)
    cases.append({'predicate':portable(predicate),'residue':str(p.residue),'period':str(p.modulus),'lo':str(lo),'hi':str(hi),'rank':str(rank),'count':str(result['count']),'selected':str(selected)if selected is not None else None,'intervals':portable(result['bounded_parameter_intervals'])})
for i in range(144):
    roots=[rng.randint(-35,35)for _ in range(rng.randint(1,8))]
    p=factors(roots)if i%2 else [rng.randint(-30,30)for _ in range(rng.randint(1,9))]
    condition=atom(p,rng.choice(['=','!=','<','<=','>','>=']))
    if i%3==0:condition={'op':rng.choice(['and','or']),'args':[condition,atom([rng.randint(-50,50),rng.randint(-5,5)],'>=')]}
    if i%7==0:condition={'op':'not','args':[condition]}
    period=rng.randint(1,13)
    record(condition,rng.randrange(period),period,-100,100,rng.choice([0,1,7,10**30]))
for predicate in [True,False,{'op':'and','args':[]},{'op':'or','args':[]},atom([0],'='),atom([0],'!='),atom([7],'>'),atom([-7],'>')]:
    for r in [0,1,3]:record(predicate,r,4,-10,30,0)
for roots in [[0,0,1,1,2,2],[-3,-3,2,2,2],[-7,-5,-1,0,3,6,7,10],[10**24,10**24+10**20],[10**24]*4]:
    for relation in ['=','!=','<','<=','>','>=']:
        record(atom(factors(roots),relation),0,18980,0,10**60,10**20 if relation=='!='else 0)
for period in [10**40+7,18980,37960]:
    for condition in [atom([-10**100,0,1],'<='),{'op':'or','args':[atom(factors([period,period*10]),'<='),atom(factors([period*20,period*25]),'<=')]}]:
        record(condition,period-1,period,0,10**100,3)
for relation in ['=','!=','<','<=','>','>=']:
    record(atom([-2,0,1],relation),0,1,-10,10,0)
    record(atom([1,-4,4],relation),0,1,-10,10,0)
for lo,hi in [(0,0),(1,1),(2,2),(1,2)]:record(True,0,3,lo,hi,0)
out=ROOT/'receipts/dresden/polynomial-browser-fixtures.json'
out.write_text(json.dumps({'schema':'dresden-polynomial-browser-fixtures/1','cases':cases},indent=2)+'\n')
print(f'PASS: {len(cases)} independent polynomial/calendar cases; small windows also exhaustively checked.')
