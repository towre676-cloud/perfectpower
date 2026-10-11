"""Finite graph structure with replayable elimination forests (Diestel §12.3)."""
from collections import deque
from itertools import combinations
from .divisor_square import WorkLimit


def graph(n, edges):
    if type(n) is not int or n < 0:
        raise ValueError('nonnegative integer vertex count required')
    adj = [set() for _ in range(n)]
    for edge in edges:
        if len(edge) != 2:
            raise ValueError('edge needs two vertices')
        a, b = edge
        if any(type(x) is not int or not 0 <= x < n for x in edge) or a == b:
            raise ValueError('simple graph edge outside carrier or loop')
        adj[a].add(b); adj[b].add(a)
    return adj


def components(adj, removed=()):
    remaining = set(range(len(adj))) - set(removed); out = []
    while remaining:
        start = min(remaining); remaining.remove(start); todo = [start]; block = []
        while todo:
            v = todo.pop(); block.append(v)
            fresh = adj[v] & remaining
            remaining.difference_update(fresh); todo.extend(sorted(fresh, reverse=True))
        out.append(sorted(block))
    return out


def elimination_forest(n, edges, order=None, *, work_limit=1_000_000):
    """Min-fill heuristic; width is an upper bound, never an optimality claim."""
    if type(work_limit) is not int or work_limit < 1: raise ValueError('positive decomposition work budget required')
    work = 0
    edges = list(edges); adj = graph(n, edges); alive = set(range(n)); bags = []; chosen = []
    if order is not None:
        order = list(order)
        if any(type(v) is not int for v in order) or sorted(order) != list(range(n)):
            raise ValueError('elimination order must be a permutation')
    while alive:
        def score(v):
            nonlocal work
            ns = adj[v] & alive
            work += 1 + len(ns)*(len(ns)-1)//2
            if work > work_limit: raise WorkLimit('decomposition search budget exceeded')
            return sum(b not in adj[a] for a,b in combinations(sorted(ns),2)), len(ns), v
        v = order[len(chosen)] if order is not None else min(alive, key=score)
        ns = adj[v] & alive; bags.append([v] + sorted(ns)); chosen.append(v)
        for a,b in combinations(ns,2):
            adj[a].add(b); adj[b].add(a)
        alive.remove(v)
    position = {v:i for i,v in enumerate(chosen)}
    parents = [min((position[v] for v in bag[1:]), default=None) for bag in bags]
    packet = {'schema':'pp-elimination-forest/1', 'order':chosen, 'bags':bags,
              'parents':parents, 'width':max((len(b)-1 for b in bags), default=-1),
              'optimal_width_proved':False}
    check_decomposition(n, edges, packet)
    return packet


def check_decomposition(n, edges, packet):
    """Coverage, forest and running intersection; no heuristic is rerun."""
    adj = graph(n, edges); bags = packet['bags']; parents = packet['parents']
    if len(bags) != len(parents) or len(bags) != n:
        raise ValueError('one bag per vertex required')
    if sorted(packet['order']) != list(range(n)) or any(type(v) is not int for v in packet['order']):
        raise ValueError('invalid order')
    tree = [set() for _ in bags]
    for i,(bag,p) in enumerate(zip(bags, parents)):
        if not bag or len(set(bag)) != len(bag) or any(type(v) is not int or not 0 <= v < n for v in bag):
            raise ValueError('invalid bag')
        if packet['order'][i] not in bag:
            raise ValueError('eliminated vertex missing')
        if p is not None:
            if type(p) is not int or not i < p < len(bags):
                raise ValueError('parent must be later; cycles forbidden')
            tree[i].add(p); tree[p].add(i)
    for v in range(n):
        containing = {i for i,b in enumerate(bags) if v in b}
        if not containing: raise ValueError('vertex uncovered')
        seen = {min(containing)}; todo = list(seen)
        while todo:
            fresh = (tree[todo.pop()] & containing) - seen
            seen.update(fresh); todo.extend(fresh)
        if seen != containing: raise ValueError('running intersection failed')
        if any(not any(v in b and w in b for b in bags) for w in adj[v]):
            raise ValueError('edge uncovered')
    if packet['width'] != max((len(b)-1 for b in bags), default=-1):
        raise ValueError('width mismatch')
    return True


def machine_structure(spec, initial=0):
    """Directed reachability plus undirected structure; preserves action labels."""
    from .future_states import normalize, future_quotient
    spec = normalize(spec); n = len(spec['observations'])
    if type(initial) is not int or not 0 <= initial < n: raise ValueError('invalid initial state')
    transitions = [[s,a,t] for a,row in sorted(spec['actions'].items()) for s,t in enumerate(row) if t is not None]
    outgoing = [[] for _ in range(n)]
    for s,a,t in transitions: outgoing[s].append((a,t))
    words = {initial:[]}; todo = deque([initial])
    while todo:
        s = todo.popleft()
        for a,t in outgoing[s]:
            if t not in words: words[t] = words[s]+[a]; todo.append(t)
    edges = sorted({tuple(sorted((s,t))) for s,a,t in transitions if s != t})
    return {'schema':'pp-machine-graph/1', 'transitions':transitions,
            'reachable':sorted(words), 'unreachable':sorted(set(range(n))-words.keys()),
            'shortest_access_words':{str(s):w for s,w in sorted(words.items())},
            'decomposition':elimination_forest(n,edges), 'future_quotient':future_quotient(spec)}
