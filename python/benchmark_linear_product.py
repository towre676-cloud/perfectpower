"""Reproducible complete-request comparison against existing trial divisors.

Synthetic frozen calibration/evaluation sets, not an industrial benchmark.
Both methods receive the same work limit. Wall times include all arithmetic;
no claim about general SMT performance follows from this experiment.
"""
import json
import random
import statistics
import time
from pathlib import Path
from perfectpower.linear_product import solve
from perfectpower.divisor_square import signed_divisors,Budget,WorkLimit


def baseline(left,right,work_limit):
    b,a=left;d,c=right;q=a*c;s=__import__('math').isqrt(q);t=a*d+b*c;k=(a*d-b*c)**2
    if not k or q<=0 or s*s!=q:raise ValueError('unsupported family')
    budget=Budget(work_limit);points=set()
    for u in signed_divisors(k,budget):
        budget.spend();v=k//u
        if (u+v-2*t)%(4*q) or (v-u)%(4*s):continue
        n,y=(u+v-2*t)//(4*q),(v-u)//(4*s)
        if y*y!=(a*n+b)*(c*n+d):raise AssertionError('baseline reconstruction')
        points.add((n,y))
    return {'points':[list(p) for p in sorted(points)],'work_used':budget.used}


def corpus():
    cases=[]
    for h in [1,2,3,6,12,30,60,210,300,1000,2310,30030]:
        cases.append({'id':f'calibration-{h}','split':'calibration','left':[0,1],'right':[h,1]})
    r=random.Random(20261011)
    for i in range(64):
        a,c=r.choice([1,4,9]),r.choice([1,4,9]);b=r.randint(-50,50);d=r.randint(100,20000)
        if i%3==0:a,c=-a,-c
        cases.append({'id':f'evaluation-{i:02d}','split':'evaluation','left':[b,a],'right':[d,c]})
    cases.extend([{'id':'evaluation-large-prime','split':'evaluation','left':[0,1],'right':[1000003,1]},
                  {'id':'evaluation-highly-composite','split':'evaluation','left':[0,1],'right':[510510,1]},
                  {'id':'evaluation-shift-80-digits','split':'evaluation','left':[-10**80,1],'right':[6-10**80,1]}])
    return cases


def timed(function,*args):
    samples=[];reference=None
    for _ in range(5):
        t=time.perf_counter()
        try:
            result=function(*args)
            samples.append(time.perf_counter()-t)
            if reference is not None and reference!=result:raise AssertionError('nondeterministic result')
            reference=result
        except WorkLimit as exc:
            samples.append(time.perf_counter()-t)
            return {'status':'WORK_LIMIT','seconds':statistics.median(samples),'seconds_samples':samples,'reason':str(exc)}
    return {'status':'COMPLETE','seconds':statistics.median(samples),'seconds_samples':samples,
            'cardinality':len(reference['points']),'work_used':reference['work_used'],'points':reference['points']}


def main():
    out=Path('receipts/linear_product');out.mkdir(parents=True,exist_ok=True)
    cases=corpus();(out/'benchmark-inputs.json').write_text(json.dumps(cases,indent=2)+'\n')
    rows=[];limit=200000
    for index,case in enumerate(cases):
        args=(case['left'],case['right'],limit)
        chart=lambda l,r,w:solve(l,r,work_limit=w)
        if index%2:
            old=timed(baseline,*args);new=timed(chart,*args)
        else:
            new=timed(chart,*args);old=timed(baseline,*args)
        if new['status']==old['status']=='COMPLETE' and new['points']!=old['points']:
            raise AssertionError(f"solution-set disagreement in {case['id']}")
        rows.append({**case,'chart':new,'trial_divisors':old})
    summaries={}
    for split in ('calibration','evaluation'):
        part=[r for r in rows if r['split']==split]
        comparable=[r for r in part if r['chart']['status']==r['trial_divisors']['status']=='COMPLETE']
        new_time=sum(r['chart']['seconds'] for r in comparable);old_time=sum(r['trial_divisors']['seconds'] for r in comparable)
        summaries[split]={'cases':len(part),'chart_complete':sum(r['chart']['status']=='COMPLETE' for r in part),
                          'baseline_complete':sum(r['trial_divisors']['status']=='COMPLETE' for r in part),
                          'comparable_cases':len(comparable),'solution_set_conflicts':0,
                          'chart_seconds_comparable':new_time,'baseline_seconds_comparable':old_time,
                          'aggregate_speed_ratio_comparable':old_time/new_time,
                          'chart_slower_cases':sum(r['chart']['seconds']>r['trial_divisors']['seconds'] for r in comparable),
                          'median_case_speed_ratio':statistics.median(r['trial_divisors']['seconds']/r['chart']['seconds'] for r in comparable)}
    report={'schema':'pp-linear-product-benchmark/1','corpus':'deterministic synthetic cases; evaluation generated independently of calibration',
            'work_limit_per_request':limit,'timing':'median of five full Python requests; alternate method order by case; work failures retained on first failing repetition; no kernel proof time included',
            'baseline':'existing divisor_square.signed_divisors on the same transformed constant, followed by congruence reconstruction',
            'scope':'finite split quadratic square equations only; no industrial or general solver speedup claim',
            'summary':summaries,'rows':rows}
    (out/'benchmark.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(summaries,indent=2))


if __name__=='__main__':main()
