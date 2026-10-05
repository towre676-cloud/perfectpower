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
