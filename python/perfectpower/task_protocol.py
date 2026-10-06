"""Auditable held-out partitions and exact-answer evaluation for curve tasks."""
from hashlib import sha256
from copy import deepcopy


def heldout_tasks(population, size, *, seed=0, train_percent=70, validation_percent=15, family='curve'):
    if any(type(x) is not int or not 0 <= x <= 100 for x in (train_percent, validation_percent)) or train_percent+validation_percent > 100:
        raise ValueError('nonnegative train/validation percentages with sum at most 100 required')
    records = population.sample(size, seed=seed)
    tasks = []
    for r in records:
        # +/- branches with the same chart parameter belong to one group.
        group = str(r['parameter']) if r['parameter'] is not None else str(tuple(abs(v) for v in r['values'].values()))
        group_id = sha256((family+'\n'+group).encode()).hexdigest()
        bucket = int(sha256((str(seed)+'\n'+group_id).encode()).hexdigest(), 16) % 100
        split = 'train' if bucket < train_percent else 'validation' if bucket < train_percent+validation_percent else 'test'
        task_id = sha256((population.population_id+'\n'+str(r['rank'])).encode()).hexdigest()
        tasks.append(dict(task_id=task_id, group_id=group_id, split=split, family=family,
                          prompt=dict(operation='recover_rank', population=population.specification, values=r['values']),
                          answer=dict(rank=r['rank']), record=r))
    return dict(schema='pp-heldout-tasks/1', seed=seed, population_id=population.population_id, tasks=tasks,
                protocol='grouped parameter hash split; related signs stay together; no unseen-family claim')


def public_tasks(packet, split):
    if split not in ('train', 'validation', 'test'):
        raise ValueError('unknown split')
    return [deepcopy({k: t[k] for k in ('task_id', 'group_id', 'split', 'family', 'prompt')})
            for t in packet['tasks'] if t['split'] == split]


def evaluate_tasks(packet, predictions, split='test'):
    if not isinstance(predictions, dict):
        raise ValueError('task-id to exact answer mapping required')
    expected = {t['task_id']: t for t in packet['tasks'] if t['split'] == split}
    if split not in ('train', 'validation', 'test') or set(predictions)-set(expected):
        raise ValueError('predictions must belong to the selected split')
    def correct(k, task):
        value = predictions.get(k)
        return isinstance(value, dict) and set(value) == {'rank'} and type(value['rank']) is int and value == task['answer']
    details = [dict(task_id=k, answered=k in predictions, correct=correct(k, t))
               for k, t in expected.items()]
    correct = sum(t['correct'] for t in details)
    return dict(split=split, total=len(details), answered=len(predictions), correct=correct,
                accuracy=None if not details else str(__import__('fractions').Fraction(correct, len(details))), details=details)


def heldout_families(families,*,size_per_family=64,seed=0):
    """Split whole declared mathematical families, rejecting cross-split aliases."""
    from .populations import ExactPopulation
    if not isinstance(families,list) or not 1<=len(families)<=64:raise ValueError('one through 64 family definitions required')
    if type(size_per_family) is not int or not 0<=size_per_family<=100000:raise ValueError('bounded nonnegative family sample size required')
    splits={};populations={};tasks=[];sources=[];identities=set()
    for i,family in enumerate(families):
        if set(family)!={'family','split','specification'} or family['split'] not in ('train','validation','test'):
            raise ValueError('family name, split and population specification required')
        name=family['family'];split=family['split']
        if not isinstance(name,str) or not name:raise ValueError('nonempty source-family label required')
        if name in splits and splits[name]!=split:raise ValueError('source family appears in multiple splits')
        splits[name]=split;p=ExactPopulation(family['specification'])
        if p.population_id in populations and populations[p.population_id]!=split:raise ValueError('population alias crosses held-out splits')
        populations[p.population_id]=split
        packet=heldout_tasks(p,min(size_per_family,p.cardinality),seed=seed+i,family=name)
        for task in packet['tasks']:
            if task['task_id'] in identities:raise ValueError('duplicate source task identity')
            identities.add(task['task_id']);task['split']=split;tasks.append(task)
        sources.append(dict(family=name,split=split,population_id=p.population_id,cardinality=p.cardinality))
    return dict(schema='pp-heldout-families/1',seed=seed,sources=sources,tasks=tasks,
        protocol='entire declared source families held out; no population alias may cross partitions')


def solve_public_tasks(tasks):
    """Measured exact-solver baseline reading only public prompt fields."""
    from .populations import ExactPopulation
    from .catalogue import encoded
    from time import perf_counter_ns
    cache={};predictions={};ledger=[]
    for task in tasks:
        prompt=task['prompt']
        if prompt['operation']!='recover_rank':raise ValueError('unsupported public task operation')
        key=encoded(prompt['population']);start=perf_counter_ns()
        if key not in cache:cache[key]=ExactPopulation(prompt['population'])
        population=cache[key];rank=population.locate(**prompt['values'])
        elapsed=perf_counter_ns()-start
        predictions[task['task_id']]=dict(rank=rank)
        ledger.append(dict(task_id=task['task_id'],elapsed_ns=elapsed))
    return dict(predictions=predictions,ledger=ledger,compiled_definitions=len(cache),
        provenance='exact-solver baseline executes public prompts; no private answers read; not an LLM benchmark')
