"""Guided, bounded original-coordinate portfolio queries over the real planner."""
import hashlib
import json
import os
import sys
import time
from copy import deepcopy
from fractions import Fraction
from pathlib import Path
from .planning import CompletionPlanner
from .resources import runtime_root

_SESSION = None

def exact_json(value):
    if isinstance(value, int) and not isinstance(value, bool): return str(value)
    if isinstance(value, Fraction): return str(value)
    if isinstance(value, dict): return {k: exact_json(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)): return [exact_json(v) for v in value]
    return value

def model(root=None):
    root = Path(root or runtime_root())
    path = root/'examples/planning/petersen_50_population.json'
    raw = path.read_bytes()
    catalog=root/'desktop/explorer/dist/catalog.json'
    snapshot=json.loads(catalog.read_text()).get('commit') if catalog.is_file() else None
    return {'specification': json.loads(raw)['specification'], 'installed_engine_snapshot':snapshot,
            'source_path': path.relative_to(root).as_posix(),
            'source_sha256': hashlib.sha256(raw).hexdigest(),
            'scope': 'Original Petersen projects; profit is an objective score, not a promised financial return.'}

def execute(body, folder, root=None):
    global _SESSION
    if not isinstance(body, dict) or set(body)-{'kind','action','resources','prefix','rank','seed','timeout'}:
        raise ValueError('Known portfolio fields required')
    action = body.get('action','build')
    if action not in ('build','conditional','select','sample'): raise ValueError('Unknown portfolio action')
    if action=='select':
        rank=body.get('rank')
        if not isinstance(rank,str) or not rank.isascii() or not rank.isdecimal() or len(rank)>30: raise ValueError('Enter a nonnegative integer rank')
    if action=='sample':
        seed=body.get('seed')
        if type(seed) is not int or not 0<=seed<=2**31-1: raise ValueError('Use an integer seed from 0 to 2147483647')
    source = model(root); spec = deepcopy(source['specification'])
    resources = body.get('resources', spec['resources'])
    if not isinstance(resources,list) or len(resources)!=5: raise ValueError('Five original resources required')
    for original, resource in zip(spec['resources'], resources):
        if not isinstance(resource,dict) or set(resource)-{'name','min','max'} or resource.get('name')!=original['name']:
            raise ValueError('Preserve original resource names')
        if any(type(resource.get(k,0)) is not int or not 0<=resource.get(k,0)<=1000000 for k in ('min','max')) or resource.get('min',0)>resource.get('max',0):
            raise ValueError('Use integer limits from zero to one million, with minimum at most maximum')
    spec['resources']=deepcopy(resources)
    prefix=body.get('prefix',[])
    if not isinstance(prefix,list) or len(prefix)>50 or any(type(x) is not int or x not in (0,1) for x in prefix):
        raise ValueError('Original binary project prefix required')
    if action=='build' and prefix: raise ValueError('Build uses the complete original population')
    identity=hashlib.sha256(json.dumps(spec,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    folder=Path(folder);folder.mkdir(parents=True,exist_ok=True)
    begun=time.monotonic()
    def progress(stats):
        data=dict(stats,elapsed_seconds=time.monotonic()-begun,phase='Exact population calculation',percentage=None)
        temporary=folder/'progress.tmp';temporary.write_text(json.dumps(data));temporary.replace(folder/'progress.json')
    reused=_SESSION is not None and _SESSION[0]==identity
    if not reused:
        _SESSION=None
        progress({'message':'Constructing bounded residual polynomials. Large cases may take several minutes.'})
        planner=CompletionPlanner(spec,_progress=progress)
        _SESSION=(identity,planner)
    planner=_SESSION[1]
    planner._progress=progress
    summary=planner.summary()
    answer={'schema':'pp-portfolio-explorer/1','action':action,'input_sha256':identity,
            'source':source,'specification':spec,'summary':summary,'session_reused':reused,
            'elapsed_seconds':time.monotonic()-begun}
    point=None
    if action=='conditional':
        answer['conditional']=planner.completions(prefix)
        if len(prefix)<50:
            answer['branches']=[planner.completions(prefix+[x]) for x in (0,1)]
        # Conditional optimal witness comes directly from the native original mask.
        result=planner.index.query(prefix)
        point=planner._decode(result['mask']) if result['count'] else None
    elif action=='select':
        rank=body.get('rank')
        if not isinstance(rank,str) or not rank.isascii() or not rank.isdecimal() or len(rank)>30: raise ValueError('Enter a nonnegative integer rank')
        point=planner.select(int(rank));answer['rank']=rank
    elif action=='sample':
        from random import Random
        seed=body.get('seed')
        if type(seed) is not int or not 0<=seed<=2**31-1: raise ValueError('Use an integer seed from 0 to 2147483647')
        point=planner.sample(Random(seed));answer['seed']=seed
    else: point=summary['optimization']['point']
    if point is not None:
        answer['selection']={'point':point,'projects':[v['name'] for v,x in zip(spec['variables'],point) if x],
                            'profit':str(sum(Fraction(v['profit'])*x for v,x in zip(spec['variables'],point))),
                            'resource_use':[sum(v['costs'][k]*x for v,x in zip(spec['variables'],point)) for k in range(5)]}
    answer['elapsed_seconds']=time.monotonic()-begun
    evidence=dict(answer,engine_evidence=planner.evidence())
    (folder/'portfolio-evidence.json').write_text(json.dumps(exact_json(evidence),indent=2)+'\n')
    (folder/'portfolio-request.json').write_text(json.dumps(body,indent=2)+'\n')
    return exact_json(answer)

def main():
    # A single persistent subprocess retains the planner, never a partial answer.
    for line in sys.stdin:
        try:
            request=json.loads(line)
            result=execute(request['body'],request['folder'])
            response={'result':result}
        except Exception as error: response={'error':str(error)}
        print(json.dumps(response),flush=True)

if __name__=='__main__': main()
