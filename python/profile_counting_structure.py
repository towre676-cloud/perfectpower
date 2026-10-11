#!/usr/bin/env python3
"""Bounded structural measurements without looking at solver timings.

Scope is a min-degree upper bound, not exact treewidth. Unit propagation is
separate from the counter's stronger equivalence and gate preprocessing.
Unprofiled inputs remain explicit in the output, never disappear from scope.
"""
import argparse
import collections
import hashlib
import heapq
import json
from pathlib import Path


def normalize(clauses):
    return sorted({tuple(sorted(set(c))) for c in clauses
                   if not any(-x in c for x in c)})


def propagate(clauses):
    occurrences = collections.defaultdict(list)
    sizes = [len(c) for c in clauses]
    satisfied = set()
    assignment = {}
    pending = collections.deque(c[0] for c in clauses if len(c) == 1)
    if any(not c for c in clauses):
        return [], {}, True
    for i, c in enumerate(clauses):
        for x in c:
            occurrences[x].append(i)
    while pending:
        x = pending.popleft()
        v, value = abs(x), x > 0
        if v in assignment:
            if assignment[v] != value:
                return [], assignment, True
            continue
        assignment[v] = value
        satisfied.update(occurrences[x])
        for i in occurrences[-x]:
            if i in satisfied:
                continue
            sizes[i] -= 1
            if sizes[i] == 0:
                return [], assignment, True
            if sizes[i] == 1:
                left = [z for z in clauses[i] if abs(z) not in assignment]
                if len(left) == 1:
                    pending.append(left[0])
    return normalize([tuple(x for x in c if abs(x) not in assignment)
                      for i, c in enumerate(clauses) if i not in satisfied]), assignment, False


def plan_component(graph, vertices):
    if len(vertices) > 8192:
        return {'status': 'VARIABLE_LIMIT', 'variables': len(vertices)}
    g = {v: set(graph[v]) for v in vertices}
    heap = [(len(ns), v) for v, ns in g.items()]
    heapq.heapify(heap)
    scope, states, eliminated = 0, 0, 0
    while g:
        while heap:
            degree, v = heapq.heappop(heap)
            if v in g and len(g[v]) == degree:
                break
        width = degree + 1
        scope = max(scope, width)
        if width > 18:
            return {'status': 'SCOPE_LIMIT', 'max_scope': scope, 'estimated_states': states,
                    'eliminated': eliminated, 'variables': len(vertices)}
        states += 1 << width
        if states > 8_000_000:
            return {'status': 'STATE_LIMIT', 'max_scope': scope, 'estimated_states': states,
                    'eliminated': eliminated, 'variables': len(vertices)}
        neighbors = g.pop(v)
        for u in neighbors:
            g[u].discard(v)
            g[u].update(neighbors - {u})
            heapq.heappush(heap, (len(g[u]), u))
        eliminated += 1
    return {'status': 'ACCEPT', 'max_scope': scope, 'estimated_states': states,
            'eliminated': eliminated, 'variables': len(vertices)}


def profile(text):
    clauses, current, header = [], [], None
    literal_count = 0
    for line in text.splitlines():
        tokens = line.split()
        if not tokens or tokens[0] == 'c':
            continue
        if tokens[0] == 'p':
            if header is not None or len(tokens) != 4 or tokens[1] != 'cnf':
                raise ValueError('DIMACS header')
            header = tuple(map(int, tokens[2:]))
            continue
        if tokens == ['%']:
            break
        for x in map(int, tokens):
            if x:
                if header is None or abs(x) > header[0]:
                    raise ValueError('literal outside declared universe')
                current.append(x)
                literal_count += 1
                if len(current) > 1024:
                    return {'status': 'CLAUSE_PROFILE_LIMIT', 'declared_variables': header[0],
                            'declared_clauses': header[1]}
                if literal_count > 300_000:
                    return {'status': 'LITERAL_PROFILE_LIMIT', 'declared_variables': header[0],
                            'declared_clauses': header[1]}
            else:
                clauses.append(tuple(current))
                current = []
    if header is None or current or len(clauses) != header[1]:
        raise ValueError('DIMACS dimensions')
    used = {abs(x) for c in clauses for x in c}
    f = normalize(clauses)
    residual, fixed, contradiction = propagate(f)
    active = {abs(x) for c in residual for x in c}
    result = {'status': 'PROFILED', 'declared_variables': header[0],
              'declared_clauses': header[1], 'used_variables': len(used),
              'initial_free_variables': header[0] - len(used),
              'clause_width_histogram': dict(sorted(collections.Counter(map(len, f)).items())),
              'unit_fixed_variables': len(fixed), 'unit_contradiction': contradiction,
              'residual_variables': len(active), 'residual_clauses': len(residual),
              'residual_free_variables': header[0] - len(active) - len(fixed)}
    graph = {v: set() for v in active}
    edges = 0
    for c in residual:
        vs = {abs(x) for x in c}
        for v in vs:
            before = len(graph[v])
            graph[v].update(vs - {v})
            edges += len(graph[v]) - before
        if edges > 400_000:
            result.update(graph_status='EDGE_LIMIT', directed_edges=edges)
            return result
    todo = set(graph)
    components = []
    while todo:
        start = min(todo)
        reached = {start}
        pending = [start]
        todo.remove(start)
        while pending:
            for u in graph[pending.pop()]:
                if u in todo:
                    todo.remove(u)
                    reached.add(u)
                    pending.append(u)
        components.append(plan_component(graph, reached))
    result.update(graph_status='PROFILED', directed_edges=edges,
                  components=components,
                  all_components_accepted=all(c['status'] == 'ACCEPT' for c in components),
                  largest_component=max((c['variables'] for c in components), default=0))
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--manifest', type=Path, required=True)
    p.add_argument('--corpus', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    if a.output.exists():
        raise ValueError('fresh output required')
    manifest = json.loads(a.manifest.read_text())
    report = {'schema': 'pp-cnf-structural-profile/1',
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'manifest_sha256': hashlib.sha256(a.manifest.read_bytes()).hexdigest(),
              'scope': 'Bounded unit propagation and component min-degree planning; no timing labels used',
              'results': [], 'completed': False}
    def save():
        tmp = a.output.with_suffix('.tmp')
        tmp.write_text(json.dumps(report, indent=2) + '\n')
        tmp.replace(a.output)
    save()
    for row in manifest['instances']:
        raw = (a.corpus / row['name']).read_bytes()
        if hashlib.sha256(raw).hexdigest() != row['sha256']:
            raise ValueError('input hash changed')
        metrics = {'status': 'BYTE_PROFILE_LIMIT'} if len(raw) > 8 * 1024**2 else profile(raw.decode())
        report['results'].append(dict(name=row['name'], sha256=row['sha256'], **metrics))
        save()
        print(row['name'], metrics['status'], metrics.get('all_components_accepted'), flush=True)
    report['completed'] = True
    save()


if __name__ == '__main__':
    main()
