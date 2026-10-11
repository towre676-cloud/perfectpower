"""Constructive matching/Hall and integral flow/cut certificates."""
from collections import deque
from .graph_structure import graph


def _bipartite(left, right, edges):
    if any(type(x) is not int or x < 0 for x in (left,right)):
        raise ValueError('nonnegative integer carrier sizes required')
    adj = [set() for _ in range(left)]
    for a,b in edges:
        if type(a) is not int or type(b) is not int or not 0 <= a < left or not 0 <= b < right:
            raise ValueError('bipartite edge outside carrier')
        adj[a].add(b)
    return adj


def matching(left, right, edges):
    edges = list(edges); adj = _bipartite(left,right,edges); lm = {}; rm = {}
    for root in range(left):
        todo = deque([root]); previous = {}; seen = {root}; end = None
        while todo and end is None:
            a = todo.popleft()
            for b in sorted(adj[a]):
                if b in previous: continue
                previous[b] = a
                if b not in rm: end = b; break
                c = rm[b]
                if c not in seen: seen.add(c); todo.append(c)
        if end is not None:
            b = end
            while True:
                a = previous[b]; old = lm.get(a); lm[a] = b; rm[b] = a
                if old is None: break
                b = old
    # Alternating reachability from ALL unmatched left vertices.
    zl = set(range(left))-lm.keys(); zr = set(); todo = deque(sorted(zl))
    while todo:
        a = todo.popleft()
        for b in adj[a]:
            if lm.get(a) == b or b in zr: continue
            zr.add(b)
            if b in rm and rm[b] not in zl: zl.add(rm[b]); todo.append(rm[b])
    packet = {'schema':'pp-matching-hall/1','matching':[[a,b] for a,b in sorted(lm.items())],
              'cover_left':sorted(set(range(left))-zl),'cover_right':sorted(zr),
              'hall_left':sorted(zl),'hall_neighbors':sorted({b for a in zl for b in adj[a]}),
              'saturates_left':len(lm)==left}
    check_matching(left,right,edges,packet); return packet


def check_matching(left,right,edges,packet):
    adj = _bipartite(left,right,edges); pairs = packet['matching']
    if any(len(p)!=2 or type(p[0]) is not int or type(p[1]) is not int or not 0 <= p[0] < left or p[1] not in adj[p[0]] for p in pairs):
        raise ValueError('invalid matching edge')
    if len({a for a,b in pairs})!=len(pairs) or len({b for a,b in pairs})!=len(pairs): raise ValueError('matching endpoints reused')
    def carrier(row,n):
        if any(type(v) is not int or not 0 <= v < n for v in row) or len(set(row))!=len(row): raise ValueError('invalid vertex set')
        return set(row)
    cl = carrier(packet['cover_left'],left); cr = carrier(packet['cover_right'],right)
    if len(cl)+len(cr)!=len(pairs) or any(a not in cl and b not in cr for a in range(left) for b in adj[a]):
        raise ValueError('cover does not certify maximum matching')
    hl = carrier(packet['hall_left'],left); hn = carrier(packet['hall_neighbors'],right)
    if hn != {b for a in hl for b in adj[a]}: raise ValueError('Hall neighbor set mismatch')
    if type(packet['saturates_left']) is not bool or packet['saturates_left'] != (len(pairs)==left): raise ValueError('saturation mismatch')
    if len(pairs)<left and len(hn)>=len(hl): raise ValueError('missing deficient Hall witness')
    return True


def distinct_assignment(domains):
    """All-different propagation: exact maximum assignment and Hall obstruction."""
    values = sorted({x for d in domains for x in d})
    if any(type(x) is not int for x in values): raise ValueError('integer values required')
    ids = {x:i for i,x in enumerate(values)}
    packet = matching(len(domains),len(values),[(a,ids[x]) for a,d in enumerate(domains) for x in d])
    return {'values':values,'packet':packet,
            'assignment':{a:values[b] for a,b in packet['matching']},
            'deficient_variables':packet['hall_left'] if not packet['saturates_left'] else [],
            'available_values':[values[b] for b in packet['hall_neighbors']] if not packet['saturates_left'] else []}


def _capacities(n, arcs, source, sink):
    if type(n) is not int or n < 2 or any(type(v) is not int or not 0 <= v < n for v in (source,sink)) or source==sink:
        raise ValueError('distinct terminals inside carrier required')
    c = [[0]*n for _ in range(n)]
    for a,b,w in arcs:
        if any(type(v) is not int for v in (a,b,w)) or not 0 <= a < n or not 0 <= b < n or a==b or w<0:
            raise ValueError('nonnegative integral capacities and valid nonloop arcs required')
        c[a][b] += w
    return c


def max_flow(n, arcs, source, sink):
    """Edmonds–Karp with antisymmetric net flow; parallel arcs are aggregated."""
    arcs = list(arcs); c = _capacities(n,arcs,source,sink); f = [[0]*n for _ in range(n)]
    while True:
        prev = {source:None}; todo = deque([source])
        while todo and sink not in prev:
            a = todo.popleft()
            for b in range(n):
                if b not in prev and c[a][b]-f[a][b]>0: prev[b]=a; todo.append(b)
        if sink not in prev: break
        path = []; b = sink
        while b != source: a=prev[b]; path.append((a,b)); b=a
        delta = min(c[a][b]-f[a][b] for a,b in path)
        for a,b in path: f[a][b]+=delta; f[b][a]-=delta
    flows = [[max(0,x) for x in row] for row in f]
    packet = {'schema':'pp-integral-flow-cut/1','flow':flows,'source_side':sorted(prev),
              'value':sum(f[source]), 'cut_capacity':sum(c[a][b] for a in prev for b in range(n) if b not in prev)}
    check_flow(n,arcs,source,sink,packet); return packet


def check_flow(n,arcs,source,sink,packet):
    c = _capacities(n,arcs,source,sink); f = packet['flow']; side = packet['source_side']
    if len(f)!=n or any(len(row)!=n for row in f): raise ValueError('flow matrix shape mismatch')
    if any(type(f[a][b]) is not int or not 0<=f[a][b]<=c[a][b] for a in range(n) for b in range(n)):
        raise ValueError('capacity violated')
    if any(type(a) is not int or not 0<=a<n for a in side) or len(set(side))!=len(side) or source not in side or sink in side:
        raise ValueError('invalid terminal cut')
    value = packet['value']
    if type(value) is not int or value<0: raise ValueError('nonnegative integral value required')
    for a in range(n):
        balance = sum(f[a])-sum(f[b][a] for b in range(n))
        if balance != (value if a==source else -value if a==sink else 0): raise ValueError('flow conservation failed')
    capacity = sum(c[a][b] for a in side for b in range(n) if b not in side)
    if type(packet['cut_capacity']) is not int or capacity != packet['cut_capacity'] or capacity != value:
        raise ValueError('primal and dual values do not agree')
    return True
