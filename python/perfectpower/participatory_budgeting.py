"""Exact analytical allocations from complete Pabulib election snapshots."""
import csv
import hashlib
import io
from collections import Counter,OrderedDict
from copy import deepcopy
from fractions import Fraction as Q
from math import lcm
from random import Random
from .planning import CompletionPlanner,integer

class BudgetElection:
    def __init__(self,text,source=None):
        if type(text) is not str or len(text.encode('utf8'))>16000000:raise ValueError('bounded UTF-8 PB text required')
        sections={};current=None
        for line in text.splitlines():
            if line in ('META','PROJECTS','VOTES'):
                if line in sections:raise ValueError('duplicate PB section')
                current=line;sections[current]=[]
            elif line.strip():
                if current is None:raise ValueError('PB section title required')
                sections[current].append(line)
        if set(sections)!= {'META','PROJECTS','VOTES'}:raise ValueError('three PB sections required')
        def rows(name):
            lines=sections[name]
            if not lines:raise ValueError('section header required')
            reader=csv.DictReader(io.StringIO('\n'.join(lines)),delimiter=';')
            if not reader.fieldnames or len(set(reader.fieldnames))!=len(reader.fieldnames):raise ValueError('distinct section columns required')
            result=list(reader)
            if any(None in r or any(v is None for v in r.values()) for r in result):raise ValueError('PB column count differs')
            return result
        meta=rows('META')
        if any(set(r)!= {'key','value'} for r in meta) or len({r['key'] for r in meta})!=len(meta):raise ValueError('distinct metadata keys required')
        self.metadata={r['key']:r['value'] for r in meta};projects=rows('PROJECTS');votes=rows('VOTES')
        if int(self.metadata['num_projects'])!=len(projects) or int(self.metadata['num_votes'])!=len(votes):raise ValueError('PB declared populations differ')
        if not 1<=len(projects)<=64 or self.metadata['vote_type'] not in ('approval','cumulative'):raise ValueError('1..64 projects and approval/cumulative votes supported')
        if len({p['project_id'] for p in projects})!=len(projects) or any(not p['project_id'] for p in projects):raise ValueError('distinct project IDs required')
        self.projects=projects;ids={p['project_id'] for p in projects};published='score' if self.metadata['vote_type']=='cumulative' else 'votes'
        budget=Q(self.metadata['budget']);costs=[Q(p['cost']) for p in projects]
        if budget<0 or any(c<0 for c in costs):raise ValueError('nonnegative money required')
        categories=self.metadata.get('categories','').split(',') if 'budget_per_category' in self.metadata else []
        category_caps=[Q(x) for x in self.metadata.get('budget_per_category','').split(',')] if categories else []
        if len(categories)!=len(category_caps) or len(set(categories))!=len(categories) or any(c<0 for c in category_caps):raise ValueError('one nonnegative cap per category required')
        if len(categories)>15:raise ValueError('at most 15 category caps supported')
        if categories and any(p.get('category') not in categories for p in projects):raise ValueError('category caps require one known category per project')
        if 'budget_per_neighbourhood' in self.metadata:raise ValueError('neighbourhood cap model is not supported')
        self.money_scale=lcm(*(q.denominator for q in [budget,*costs,*category_caps]))
        self.budget=int(budget*self.money_scale)
        resources=[{'name':'budget','max':self.budget}]+[{'name':f'category:{name}','max':int(cap*self.money_scale)} for name,cap in zip(categories,category_caps)]
        variables=[]
        for p,c in zip(projects,costs):
            score=Q(p[published])
            if score<0:raise ValueError('nonnegative published support required')
            amount=int(c*self.money_scale)
            variables.append({'name':p['project_id'],'costs':[amount]+[amount if p.get('category')==name else 0 for name in categories],'profit':str(score),'upper':1})
        self.specification={'kind':'allocation','resources':resources,'variables':variables}
        observed=Counter();self.ballots=[];voter_ids=set()
        for v in votes:
            voter=v['voter_id']
            if voter in voter_ids:raise ValueError('distinct voter IDs required')
            voter_ids.add(voter)
            selected=v['vote'].split(',') if v['vote'] else []
            if len(set(selected))!=len(selected) or set(selected)-ids:raise ValueError('distinct known ballot project IDs required')
            points=v.get('points','').split(',') if v.get('points') else []
            if self.metadata['vote_type']=='cumulative':
                if len(points)!=len(selected):raise ValueError('one point value per cumulative choice required')
                weights=[Q(p) for p in points]
                if any(p<0 for p in weights):raise ValueError('nonnegative ballot points required')
            else:weights=[Q(1)]*len(selected)
            for name,weight in zip(selected,weights):observed[name]+=weight
            self.ballots.append(frozenset(name for name,weight in zip(selected,weights) if weight>0))
        self.support_audit=[{'project':p['project_id'],'published':str(Q(p[published])),'ballot_total':str(observed[p['project_id']])} for p in projects if Q(p[published])!=observed[p['project_id']]]
        self.source=source or {};self.sha256=hashlib.sha256(text.encode('utf8')).hexdigest();self.score_field=published
    def summary(self):
        return {'metadata':deepcopy(self.metadata),'project_count':len(self.projects),'ballot_count':len(self.ballots),'budget':str(Q(self.budget,self.money_scale)), 'money_scale':self.money_scale,'score_field':self.score_field,'support_discrepancies':deepcopy(self.support_audit),'source':deepcopy(self.source),'source_sha256':self.sha256,'scope':'analytical maximum total published support; does not reproduce the municipal voting rule'}
    def describe(self,point):
        if not isinstance(point,(list,tuple)) or len(point)!=len(self.projects) or any(type(x) is not int or x not in (0,1) for x in point):raise ValueError('complete original binary plan required')
        selected={p['project_id'] for p,x in zip(self.projects,point) if x}
        used=[sum(x*v['costs'][k] for x,v in zip(point,self.specification['variables'])) for k in range(len(self.specification['resources']))]
        return {'point':list(point),'projects':[{'id':p['project_id'],'name':p.get('name',p['project_id']),'cost':p['cost'],'support':p[self.score_field]} for p,x in zip(self.projects,point) if x], 'spend':str(Q(used[0],self.money_scale)), 'support':str(sum(Q(v['profit'])*x for v,x in zip(self.specification['variables'],point))), 'represented_ballots':sum(bool(b&selected) for b in self.ballots),'resource_usage':used}

class BudgetSession:
    def __init__(self,election,constructor=CompletionPlanner,cache_size=16):
        self.election=election;self.constructor=constructor;self.cache_size=integer(cache_size,1,64,'scenario cache size');self.cache=OrderedDict();self.builds=0;self.hits=0
    def state(self,budget=None,locks=None):
        e=self.election;budget=e.budget if budget is None else integer(budget,0,2**64-1,'scaled budget')
        locks={} if locks is None else locks
        ids={p['project_id'] for p in e.projects}
        if not isinstance(locks,dict) or set(locks)-ids or any(type(x) is not int or x not in (0,1) for x in locks.values()):raise ValueError('locks map known project IDs to zero or one')
        key=(budget,tuple(sorted(locks.items())))
        if key in self.cache:self.hits+=1;self.cache.move_to_end(key);return self.cache[key]
        spec=deepcopy(e.specification);spec['resources'][0]['max']=budget
        used=[sum(v['costs'][k]*locks.get(v['name'],0) for v in spec['variables']) for k in range(len(spec['resources']))]
        free=[i for i,p in enumerate(e.projects) if p['project_id'] not in locks]
        feasible=all(u<=r['max'] for u,r in zip(used,spec['resources']))
        fixed_score=sum(Q(v['profit'])*locks.get(v['name'],0) for v in spec['variables'])
        planner=None
        if feasible and free:
            spec['variables']=[spec['variables'][i] for i in free]
            for r,u in zip(spec['resources'],used):r['max']-=u
            planner=self.constructor(spec)
        state={'planner':planner,'budget':budget,'locks':dict(locks),'free':free,'feasible':feasible,'fixed_score':fixed_score}
        self.builds+=1;self.cache[key]=state
        if len(self.cache)>self.cache_size:self.cache.popitem(last=False)
        return state
    def evaluate(self,request):
        if not isinstance(request,dict) or set(request)-{'budget','locks','operation','rank','point','seed','optimal'}:raise ValueError('known planning request fields required')
        op=request.get('operation','view')
        if op not in ('view','select','rank','sample'):raise ValueError('known budgeting operation required')
        allowed={'view':set(),'select':{'rank','optimal'},'rank':{'point','optimal'},'sample':{'seed','optimal'}}[op]|{'operation','budget','locks'}
        if set(request)-allowed:raise ValueError('operation arguments differ')
        optimal=request.get('optimal',False)
        if type(optimal) is not bool:raise ValueError('optimal must be Boolean')
        s=self.state(request.get('budget'),request.get('locks'));p=s['planner'];e=self.election
        count=p.count() if p else int(s['feasible'])
        best=p.optimize() if p else {'maximum':'0' if count else None,'maximizer_count':count,'point':[] if count else None}
        def original(free):
            point=[s['locks'].get(project['project_id'],0) for project in e.projects]
            for i,x in zip(s['free'],free):point[i]=x
            return point
        maximum=None if best['maximum'] is None else str(Q(best['maximum'])+s['fixed_score'])
        output={'count':count,'maximum':maximum,'maximizer_count':best['maximizer_count'],'budget':s['budget'],'locks':dict(s['locks']),'original_order':[project['project_id'] for project in e.projects]}
        if op=='rank':
            point=request.get('point')
            e.describe(point)
            if any(point[i]!=s['locks'][project['project_id']] for i,project in enumerate(e.projects) if project['project_id'] in s['locks']):raise ValueError('plan violates a lock')
            if not count:raise ValueError('infeasible scenario')
            output['rank']=p.rank([point[i] for i in s['free']],optimal=optimal) if p else 0
        else:
            if op=='select':
                rank=request.get('rank');integer(rank,0,(best['maximizer_count'] if optimal else count)-1,'rank')
                free=p.select(rank,optimal=optimal) if p else []
            elif op=='sample':
                seed=request.get('seed')
                if seed is not None and type(seed) is not int:raise ValueError('integer sample seed required')
                if not count:raise ValueError('cannot sample empty scenario')
                free=p.sample(rng=Random(seed) if seed is not None else None,optimal=optimal) if p else []
            else:free=best['point']
            output['plan']=e.describe(original(free)) if free is not None else None
        output['scope']='uniform feasible original portfolios or maximum total published support; distinct represented ballots reported separately'
        return output
