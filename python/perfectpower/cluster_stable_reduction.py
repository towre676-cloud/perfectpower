"""Cluster pictures, semistable models and tame conductors of hyperelliptic curves.

C: y^2=c*prod(x-r) over K=Q_p (p odd) or K=Q((t)), any genus.  Branch roots
live in one of three exact domains:

* Q_p with roots in Q or in Q(sqrt D), D squarefree, sqrt D not in Q_p;
* Q((t)) with roots in Q[t^(1/2), t^(-1/2)] (Puiseux polynomials).

The cluster tree, relative depths, nu_s, the geometric semistable double-cover
graph, its stable contraction and the potential toric/abelian ranks are
computed in every case.  When inertia fixes every root (K(R)/K unramified, or
integral t-exponents) the inertia action on the semistable special fibre is
derived from the parities of nu_s, giving the toric/abelian/unipotent ranks of
the Neron model and the conductor exponent, whose wild part vanishes.
"""
from fractions import Fraction as Q
from math import isqrt

INF = None


def is_prime(p):
    return type(p) is int and p >= 2 and all(p % d for d in range(2, isqrt(p) + 1))


def vp(x, p):
    x = Q(x)
    if not x:
        return INF
    n, d, k = abs(x.numerator), x.denominator, 0
    while n % p == 0:
        n //= p
        k += 1
    while d % p == 0:
        d //= p
        k -= 1
    return Q(k)


def _min(*vals):
    vals = [v for v in vals if v is not INF]
    return min(vals) if vals else INF


def legendre(a, p):
    a %= p
    return 0 if not a else (1 if pow(a, (p - 1) // 2, p) == 1 else -1)


class PadicDomain:
    """Q_p with roots a+b*sqrt(D); inertia generator acts by sqrt D -> -sqrt D iff p | D."""

    def __init__(self, p, D=1):
        if not is_prime(p) or p == 2:
            raise ValueError('odd prime required')
        if D != 1:
            if type(D) is not int or D == 0 or any(D % (q * q) == 0 for q in range(2, isqrt(abs(D)) + 1)):
                raise ValueError('squarefree integer D required')
            if D % p and legendre(D, p) == 1:
                raise ValueError('sqrt D lies in Q_p: supply the roots as rationals instead')
        self.p, self.D = p, D
        self.ramified = D != 1 and D % p == 0
        self.name = 'Q_%d' % p + ('' if D == 1 else '(sqrt %d)' % D)

    def parse(self, r):
        if isinstance(r, (list, tuple)):
            a, b = Q(r[0]), Q(r[1])
        else:
            a, b = Q(r), Q(0)
        if b and self.D == 1:
            raise ValueError('irrational root needs D')
        return (a, b)

    def sub(self, x, y):
        return (x[0] - y[0], x[1] - y[1])

    def v(self, x):
        a, b = x
        if self.D == 1:
            return vp(a, self.p)
        vb = vp(b, self.p)
        if self.ramified:
            return _min(vp(a, self.p), None if vb is INF else vb + Q(1, 2))
        return _min(vp(a, self.p), vb)

    def sigma(self, x):
        return (x[0], -x[1]) if self.ramified else x

    def frobenius(self, x):
        return (x[0], -x[1]) if (self.D != 1 and not self.ramified) else x

    def packet(self, x):
        return str(x[0]) if not x[1] else [str(x[0]), str(x[1])]

    def lead_v(self, c):
        return vp(c, self.p)


class PuiseuxDomain:
    """Q((t)) with roots sum a_q t^q, q in (1/2)Z; inertia: t^(1/2) -> -t^(1/2)."""

    name = 'Q((t))'

    def parse(self, r):
        if isinstance(r, dict):
            items = r.items()
        elif isinstance(r, (list, tuple)):
            items = [(e, a) for e, a in r]
        else:
            items = [(0, r)]
        out = {}
        for e, a in items:
            e, a = Q(e), Q(a)
            if (2 * e).denominator != 1:
                raise ValueError('exponents in (1/2)Z required')
            if a:
                out[e] = out.get(e, Q(0)) + a
        return tuple(sorted((e, a) for e, a in out.items() if a))

    def sub(self, x, y):
        d = dict(x)
        for e, a in y:
            d[e] = d.get(e, Q(0)) - a
        return tuple(sorted((e, a) for e, a in d.items() if a))

    def v(self, x):
        return min(e for e, a in x) if x else INF

    def sigma(self, x):
        return tuple((e, -a if e.denominator == 2 else a) for e, a in x)

    def packet(self, x):
        return [[str(e), str(a)] for e, a in x]

    def lead_v(self, c):
        c = self.parse(c)
        if any(e.denominator != 1 for e, a in c):
            raise ValueError('leading coefficient must lie in Q((t))')
        return self.v(c)


# ------------------------------------------------------------- linear algebra
def rank(rows):
    rows = [list(map(Q, r)) for r in rows if any(r)]
    rk, col = 0, 0
    ncol = len(rows[0]) if rows else 0
    while rk < len(rows) and col < ncol:
        piv = next((i for i in range(rk, len(rows)) if rows[i][col]), None)
        if piv is None:
            col += 1
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        for i in range(len(rows)):
            if i != rk and rows[i][col]:
                f = rows[i][col] / rows[rk][col]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[rk])]
        rk += 1
        col += 1
    return rk


# ------------------------------------------------------------- cluster picture
def cluster_picture(domain, roots, leading=1):
    roots = [domain.parse(r) for r in roots]
    n = len(roots)
    if not 3 <= n <= 24:
        raise ValueError('3 through 24 branch roots required')
    keys = {r: i for i, r in enumerate(roots)}
    if len(keys) != n:
        raise ValueError('distinct roots required')
    perm = []
    for r in roots:
        s = domain.sigma(r)
        if s not in keys:
            raise ValueError('root set not stable under inertia (polynomial not over K)')
        perm.append(keys[s])
    if hasattr(domain, 'frobenius'):
        for r in roots:
            if domain.frobenius(r) not in keys:
                raise ValueError('root set not Galois stable')
    vc = domain.lead_v(leading)
    if vc is INF:
        raise ValueError('nonzero leading coefficient required')
    dist = [[None if i == j else domain.v(domain.sub(roots[i], roots[j])) for j in range(n)] for i in range(n)]
    clusters = []

    def build(indices, parent):
        depth = min(dist[i][j] for a, i in enumerate(indices) for j in indices[a + 1:])
        idx = len(clusters)
        rec = dict(id=idx, roots=indices, size=len(indices), depth=depth, parent=parent, children=[], singletons=[])
        clusters.append(rec)
        rest = list(indices)
        while rest:
            i = rest[0]
            grp = [j for j in rest if j == i or dist[i][j] > depth]
            rest = [j for j in rest if j not in grp]
            if len(grp) == 1:
                rec['singletons'].append(grp[0])
            else:
                rec['children'].append(build(grp, idx))
        return idx

    build(list(range(n)), None)
    g = (n - 1) // 2
    by_set = {frozenset(c['roots']): c['id'] for c in clusters}
    sigma_clusters = [by_set.get(frozenset(perm[i] for i in c['roots'])) for c in clusters]
    if None in sigma_clusters:
        raise AssertionError('inertia does not permute clusters')
    for c in clusters:
        c['relative_depth'] = None if c['parent'] is None else c['depth'] - clusters[c['parent']]['depth']
        c['even'] = c['size'] % 2 == 0
        kids = [clusters[k] for k in c['children']]
        c['odd_children'] = len(c['singletons']) + sum(k['size'] % 2 for k in kids)
        c['uebereven'] = c['even'] and not c['singletons'] and all(k['size'] % 2 == 0 for k in kids)
        c['twin'] = c['size'] == 2
        c['cotwin'] = any(k['size'] == 2 * g for k in kids) and not c['uebereven']
        c['principal'] = c['size'] >= 3 and not c['cotwin'] and not (
            c['parent'] is None and c['even'] and len(kids) == 2 and not c['singletons']) and not (
            c['parent'] is None and c['even'] and any(k['size'] == 2 * g + 1 for k in kids))
        # nu_s = v(c)+|s| d_s+sum_{r notin s} d_{r ^ s}
        nu = vc + c['size'] * c['depth']
        inside = set(c['roots'])
        for r in range(n):
            if r not in inside:
                nu += min(dist[r][i] for i in inside)
        c['nu'] = nu
    return dict(n=n, genus=g, roots=roots, perm=perm, dist=dist, clusters=clusters, sigma_clusters=sigma_clusters,
                leading_valuation=vc, inertia_fixes_roots=all(perm[i] == i for i in range(n)))


def semistable_graph(pic):
    """Geometric semistable double-cover graph with explicit sheets and lifts."""
    cl = pic['clusters']
    vertices, lifts, edges = [], {}, []
    for c in cl:
        odd = c['odd_children'] + c['size'] % 2  # parent flag (infinity for R)
        if odd % 2:
            raise AssertionError('odd number of branch flags')
        lifts[c['id']] = []
        for sheet in range(1 if odd else 2):
            lifts[c['id']].append(len(vertices))
            vertices.append(dict(id=len(vertices), cluster=c['id'], sheet=sheet,
                                 genus=(odd - 2) // 2 if odd else 0, branch_flags=odd))
    for c in cl[1:]:
        par = cl[c['parent']]
        odd = c['size'] % 2
        length = c['relative_depth'] / 2 if odd else c['relative_depth']
        for j in range(1 if odd else 2):
            a = lifts[par['id']][j % len(lifts[par['id']])]
            b = lifts[c['id']][j % len(lifts[c['id']])]
            edges.append(dict(id=len(edges), child=c['id'], lift=j, parent_vertex=a, child_vertex=b,
                              length=length, ramified=bool(odd)))
    nv, ne = len(vertices), len(edges)
    comp = list(range(nv))

    def find(i):
        while comp[i] != i:
            i = comp[i]
        return i
    for e in edges:
        comp[find(e['parent_vertex'])] = find(e['child_vertex'])
    if len({find(i) for i in range(nv)}) != 1:
        raise AssertionError('semistable graph disconnected')
    b1 = ne - nv + 1
    genus = sum(v['genus'] for v in vertices) + b1
    if genus != pic['genus']:
        raise AssertionError('genus replay failed: %d != %d' % (genus, pic['genus']))
    return dict(vertices=vertices, edges=edges, cycle_rank=b1, lifts=lifts)


def stable_contraction(graph):
    """Contract genus-0 leaves and genus-0 bivalent vertices (lengths add)."""
    V = {v['id']: dict(genus=v['genus'], clusters=[v['cluster']]) for v in graph['vertices']}
    E = {e['id']: [e['parent_vertex'], e['child_vertex'], e['length']] for e in graph['edges']}
    changed = True
    while changed:
        changed = False
        for vid in sorted(V):
            if V[vid]['genus']:
                continue
            inc = [k for k, e in E.items() if vid in e[:2]]
            deg = sum((e[0] == vid) + (e[1] == vid) for e in (E[k] for k in inc))
            if deg == 1 and len(V) > 1:
                (k,) = inc
                o = E[k][0] if E[k][1] == vid else E[k][1]
                V[o]['clusters'] += V[vid]['clusters']
                del E[k], V[vid]
                changed = True
                break
            if deg == 2 and len(inc) == 2 and len(V) > 1:
                k1, k2 = inc
                a = E[k1][0] if E[k1][1] == vid else E[k1][1]
                b = E[k2][0] if E[k2][1] == vid else E[k2][1]
                E[k1] = [a, b, E[k1][2] + E[k2][2]]
                del E[k2]
                tgt = a
                V[tgt]['clusters'] += V[vid]['clusters']
                del V[vid]
                changed = True
                break
    order = sorted(V)
    ix = {v: i for i, v in enumerate(order)}
    verts = [dict(id=ix[v], genus=V[v]['genus'], clusters=sorted(V[v]['clusters'])) for v in order]
    edges = sorted([sorted([ix[a], ix[b]]) + [L] for a, b, L in E.values()], key=lambda e: (e[0], e[1], e[2]))
    b1 = len(edges) - len(verts) + 1
    return dict(vertices=verts, edges=[dict(ends=e[:2], length=str(e[2])) for e in edges], cycle_rank=b1,
                genus=sum(v['genus'] for v in verts) + b1)


def _integral(q, what):
    if q.denominator != 1:
        raise AssertionError('non-integral phase for ' + what)
    return int(q) % 2


def inertia_action(pic):
    """Tame inertia generator on the semistable special fibre and on H^1.

    Phases: sigma multiplies a residue of valuation q by exp(pi i q) on square
    roots.  Fixed clusters use alpha=exp(-2 pi i d_s) on X; a moved pair {s, sigma s}
    is labelled by transport and sigma^2 (which fixes every root) acts on it.
    """
    cl, sc = pic['clusters'], pic['sigma_clusters']
    for c in cl:
        if (2 * c['depth']).denominator != 1:
            raise AssertionError('depth outside (1/2)Z')
    mu = {c['id']: c['nu'] - c['size'] * c['depth'] for c in cl}
    role = {}
    for c in cl:  # parents precede children in the build order
        P = c['parent']
        if sc[c['id']] == c['id']:
            if P is not None and role[P] != 'fixed':
                raise AssertionError('fixed cluster below a moved cluster')
            role[c['id']] = 'fixed'
        elif role[P] == 'fixed':
            role[c['id']] = 'rep' if c['id'] < sc[c['id']] else 'image'
        else:
            role[c['id']] = role[P]
        if role[c['id']] != 'fixed' and sc[sc[c['id']]] != c['id']:
            raise AssertionError('inertia orbit longer than two')
    sheets, flags = {}, {}
    for c in cl:
        odd = c['odd_children'] + c['size'] % 2
        sheets[c['id']], flags[c['id']] = (1 if odd else 2), odd
    E = {c['id']: sum(cl[k]['size'] // 2 for k in c['children']) for c in cl}

    def vswap(sid, power):
        if sheets[sid] == 1:
            return 0
        return _integral(-power * mu[sid], 'two-sheet vertex')

    def eswap(cid, power):
        if cl[cid]['size'] % 2:
            return 0
        return _integral(-power * mu[cid], 'even edge')

    verts, vid = [], {}
    for c in cl:
        for j in range(sheets[c['id']]):
            vid[(c['id'], j)] = len(verts)
            verts.append(dict(id=len(verts), cluster=c['id'], sheet=j, genus=(flags[c['id']] - 2) // 2 if flags[c['id']] else 0))
    edges, eid = [], {}
    for c in cl[1:]:
        P = c['parent']
        twist = vswap(P, 1) if (role[c['id']] == 'image' and role[P] == 'fixed') else 0
        for j in range(1 if c['size'] % 2 else 2):
            eid[(c['id'], j)] = len(edges)
            edges.append(dict(id=len(edges), child=c['id'], lift=j,
                              parent_vertex=vid[(P, (j ^ twist) % sheets[P])], child_vertex=vid[(c['id'], j % sheets[c['id']])],
                              length=c['relative_depth'] / 2 if c['size'] % 2 else c['relative_depth'], ramified=bool(c['size'] % 2)))

    def vmap(v):
        s_, j = verts[v]['cluster'], verts[v]['sheet']
        if role[s_] == 'fixed':
            return vid[(s_, j ^ vswap(s_, 1))]
        if role[s_] == 'rep':
            return vid[(sc[s_], j)]
        return vid[(sc[s_], j ^ vswap(sc[s_], 2))]

    def emap(e):
        c_, j = edges[e]['child'], edges[e]['lift']
        if role[c_] == 'fixed':
            return eid[(c_, j ^ eswap(c_, 1))]
        if role[c_] == 'rep':
            return eid[(sc[c_], j)]
        return eid[(sc[c_], j ^ eswap(sc[c_], 2))]
    for e in edges:
        f = edges[emap(e['id'])]
        if (f['parent_vertex'], f['child_vertex']) != (vmap(e['parent_vertex']), vmap(e['child_vertex'])):
            raise AssertionError('inertia is not a graph automorphism')
    # abelian part: invariants of sigma on sum of H^1 of positive-genus components
    abelian2 = 0
    for v in verts:
        g, s_ = v['genus'], v['cluster']
        if not g or role[s_] == 'image':
            continue
        c = cl[s_]
        if role[s_] == 'rep':
            abelian2 += 2 * g if _integral(2 * (2 * c['depth'] * E[s_] - c['nu']), 'sigma^2 on component') == 0 else 0
            continue
        if c['depth'].denominator == 1:
            if any(sc[k] != k for k in c['children']):
                raise AssertionError('alpha=1 but children permuted')
            abelian2 += 2 * g if _integral(2 * c['depth'] * E[s_] - c['nu'], 'component sign') == 0 else 0
            continue
        n_odd = c['odd_children']
        if n_odd % 2:
            continue  # case B: sigma^2 is the hyperelliptic involution, no invariants
        eps = _integral(2 * c['depth'] * E[s_] - c['nu'], 'component sign (alpha=-1)')
        fixed = 2 * (eps == 0) + 2 * ((eps + n_odd // 2) % 2 == 0)
        inv = 2 * g + 2 - fixed
        if inv % 2:
            raise AssertionError('Lefschetz average not integral')
        abelian2 += inv // 2
    ne = len(edges)
    rows = [[(1 if e['child_vertex'] == v['id'] else 0) - (1 if e['parent_vertex'] == v['id'] else 0) for e in edges] for v in verts]
    for e in edges:
        r = [0] * ne
        r[e['id']] += 1
        r[emap(e['id'])] -= 1
        rows.append(r)
    toric = ne - rank(rows)
    b1 = ne - len(verts) + 1
    pot_ab = sum(v['genus'] for v in verts)
    g = pic['genus']
    if 2 * g - abelian2 - toric < 0 or (2 * g - abelian2 - toric) % 1:
        raise AssertionError('negative conductor')
    n_tame = 2 * g - abelian2 - toric
    return dict(inertia_invariants_dimension=abelian2 + toric, abelian_part_invariants=abelian2, toric_rank=toric,
                conductor_exponent=n_tame, tame_part=n_tame, wild_part=0,
                semistable_over_K=(abelian2 + toric == 2 * pot_ab + b1), jacobian_good_reduction_over_K=(n_tame == 0),
                roles={str(k): v for k, v in sorted(role.items())},
                vertex_permutation=[vmap(v['id']) for v in verts], edge_permutation=[emap(e['id']) for e in edges])


def ddmm_semistability(pic):
    """DDMM criterion: e(K(R)/K)<=2 (automatic here), proper clusters inertia
    invariant, principal clusters with d_s in Z and nu_s in 2Z."""
    if any(pic['sigma_clusters'][c['id']] != c['id'] for c in pic['clusters']):
        return False
    return all(c['depth'].denominator == 1 and c['nu'] % 2 == 0 for c in pic['clusters'] if c['principal'])


def analyse(domain, roots, leading=1):
    pic = cluster_picture(domain, roots, leading)
    graph = semistable_graph(pic)
    stable = stable_contraction(graph)
    if stable['genus'] != pic['genus']:
        raise AssertionError('stable contraction changed the genus')
    inertia = inertia_action(pic)
    ddmm = ddmm_semistability(pic)
    if inertia['semistable_over_K'] != ddmm:
        raise AssertionError('graph-action semistability disagrees with the DDMM criterion')
    pot_ab = sum(v['genus'] for v in stable['vertices'])
    out = dict(schema='pp-cluster-stable-reduction/1', field=domain.name,
               roots=[domain.packet(r) for r in pic['roots']], leading_valuation=str(pic['leading_valuation']),
               genus=pic['genus'],
               clusters=[dict(id=c['id'], roots=c['roots'], size=c['size'], depth=str(c['depth']),
                              relative_depth=None if c['relative_depth'] is None else str(c['relative_depth']),
                              parent=c['parent'], children=c['children'], even=c['even'], uebereven=c['uebereven'],
                              twin=c['twin'], cotwin=c['cotwin'], principal=c['principal'], nu=str(c['nu']),
                              inertia_image=pic['sigma_clusters'][c['id']])
                         for c in pic['clusters']],
               inertia_root_permutation=pic['perm'], inertia_fixes_roots=pic['inertia_fixes_roots'],
               semistable_graph=dict(vertices=[dict((k, v[k]) for k in ('id', 'cluster', 'sheet', 'genus', 'branch_flags')) for v in graph['vertices']],
                                     edges=[dict(child=e['child'], lift=e['lift'], ends=[e['parent_vertex'], e['child_vertex']],
                                                 length=str(e['length']), ramified=e['ramified']) for e in graph['edges']],
                                     cycle_rank=graph['cycle_rank']),
               stable_graph=stable, potential_toric_rank=stable['cycle_rank'], potential_abelian_rank=pot_ab,
               potentially_good=stable['cycle_rank'] == 0 and len(stable['vertices']) == 1,
               ddmm_semistable_over_K=ddmm, reduction_over_K=inertia,
               genus_identity_checked=True)
    return out


def puiseux_roots_from_rates(spec):
    """Helper: [(centre, coefficient, exponent), ...] -> roots centre+coefficient*t^exponent."""
    out = []
    for a, b, e in spec:
        out.append({Q(0): Q(a), Q(e): Q(b)} if Q(b) and Q(e) else {Q(0): Q(a) + Q(b)})
    return out
