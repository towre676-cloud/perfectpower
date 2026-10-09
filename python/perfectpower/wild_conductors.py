"""Wild conductor exponents from the Galois representation (open item N41).

The conductor exponent of an abelian variety A/Q_p is

    a(A) = (dim V - dim V^I) + Sw(V),        V = V_l(A), l != p,

and both terms are independent of l.  This module computes them from Galois
data of torsion fields, never from a minimal regular model or from PARI's
elllocalred / genus2red (those are oracles in the develop script and tests).

Number fields stand in for p-adic fields: a global polynomial T irreducible
over Q gives the etale algebra Q_p[x]/(T) as the product of the completions of
Q[x]/(T) at the primes above p, so local ramification data (e, f, different)
are read from nfinit([T, [p]]), which is maximal at p.  When the splitting
field M of the relevant polynomial is small enough for galoisinit, the full
lower ramification filtration G_0 > G_1 > ... at a prime of M above p is taken
from idealramgroups and the Galois action on roots from nfgaloisapply.

1. Swan conductors of permutation representations from local discriminants:
   Sw(Q_l[roots of T]) = sum_P f_P (v_P(D) - e_P + 1).
2. Elliptic curves, Swan conductor:
   * p=2, l=3: for every 2-subgroup H of GL_2(F_3),
       2 - dim E[3]^H = (8 - #orbits of H on E[3]-0)/2 - (4 - #orbits on P(E[3]))/2,
     so Sw(E) = (Sw(points) - Sw(lines))/2, the points being the roots of the
     degree-8 resultant in t=y'+lam*x and the lines the roots of psi_3;
   * p=3, l=2: E[2]+1 = F_2[roots of the 2-division cubic] as Brauer
     characters of 3-groups, so Sw(E) = Sw(cubic);
   * independently, Sw = sum_{i>=1} |G_i|/|G_0| (2 - dim E[l]^{G_i}) from the
     ramification groups of Q(E[l]) and the fixed points of G_i.
3. Elliptic curves, tame part without Tate's algorithm: v(j)<0 gives a quadratic
   twist (by -c6) of a Tate curve, multiplicative exactly when Q_p(sqrt(-c6)) is
   unramified (tame part 1, else 2); v(j)>=0 gives potentially good reduction,
   good exactly when inertia fixes E[3] (p=2) or E[4] (p=3) pointwise
   (Serre-Tate), i.e. when every field of a torsion point is unramified.
4. Genus two (any genus) at odd p, wild allowed: the cluster picture over the
   splitting field M (depths from v_P of root differences), the inertia image
   G_0 acting on roots, and its tame character theta(s)=s(pi)/pi mod P.  The
   invariants dim V^I come from a Lefschetz average over a covering group of
   the inertia image acting on the semistable fibre.  A wild element acts on
   the component of a cluster it fixes as a translation x->x+b when it moves
   the children; the fixed points then lie over infinity and are counted with
   their ell-adic Lefschetz multiplicities (3 at the ramified point, 2 at each
   unramified point fixed, 1 when composed with the hyperelliptic involution).
   The Swan conductor is that of J[2], i.e. of the roots, both from the
   filtration and from local discriminants.
5. Genus two at p=2 for split Jacobians: y^2=g(x^2) (and any Mobius image of
   it) has Jac ~ E1 x E2, and the Galois-route conductors of E1, E2 add.
"""
from fractions import Fraction as Q
from math import gcd, log
import itertools

SCHEMA = 'pp-wild-conductors/1'

_GP = r'''
wc_rootperm(nf, s, R) = my(n=#R, B=vector(n,i,nfalgtobasis(nf,R[i])), out=vector(n)); for(i=1,n, my(im=nfalgtobasis(nf, nfgaloisapply(nf, s, R[i]))); for(j=1,n, if(im==B[j], out[i]=j-1; break))); out;
wc_unif(nf, pr) = { my(a = pr[2]); if(nfeltval(nf, a, pr) == 1, return(a)); for(i=1, #nf.zk, for(c=-2,2, my(b = a + c*nf.zk[i]); if(nfeltval(nf, b, pr)==1, return(b)))); for(i=1, #nf.zk, my(b = nfeltmul(nf, pr[1], nf.zk[i])); if(nfeltval(nf, b, pr)==1, return(b))); error("no uniformizer"); }
wc_tame(nf, pr, s, pi, g, modpr) = my(r = nfeltdiv(nf, nfgaloisapply(nf, s, pi), pi)); fflog(nfmodpr(nf, r, modpr), g);
wc_monic(g) = my(c = pollead(g), n = poldegree(g), v = variable(g)); g = g / content(g); c = pollead(g); c^(n-1) * subst(g, v, v/c);
wc_patch2(L, F) = my(v = L, d = v[1], B = d[2][2], F2 = subst(F, variable(F), 'x)); my(found = 0); for(i=1, #B, if(B[i][1]==2, B[i][2] = 1/F2; found = 1)); if(!found, B = concat([[2, 1/F2]], B)); d[2][2] = B; v[1] = d; v;
wc_ldata(T, p) = my(nf = nfinit([wc_monic(T), [p]])); [[pr.e, pr.f, idealval(nf, nf.diff, pr)] | pr <- idealprimedec(nf, p)];
'''

_PARI = None


def pari():
    global _PARI
    if _PARI is None:
        import cypari2
        P = cypari2.Pari()
        try:
            P.allocatemem(512 * 10 ** 6)
        except Exception:  # pragma: no cover
            pass
        for line in _GP.strip().split('\n'):
            P(line)
        _PARI = P
    return _PARI


def _pol(P, c, var='x'):
    return P('Pol([%s], %s)' % (','.join(str(x) for x in reversed(list(c))), var))


def _vp(n, p):
    n = Q(n)
    if not n:
        return 10 ** 9
    k, a, b = 0, abs(n.numerator), n.denominator
    while a % p == 0:
        a //= p
        k += 1
    while b % p == 0:
        b //= p
        k -= 1
    return k


# ------------------------------------------------------------- permutation conductors
def permutation_conductor(T, p, P=None):
    """Artin conductor of Q_l[roots of T] at p, split as tame + Swan, from local discriminants.

    T: PARI polynomial (squarefree, rational).  Linear factors contribute 0.
    """
    P = P or pari()
    fa = P.factor(T)
    rows, art, tame, swan = [], 0, 0, 0
    for i in range(int(P.matsize(fa)[0])):
        g = fa[i, 0]
        if int(fa[i, 1]) != 1:
            raise ValueError('squarefree polynomial required')
        if int(P.poldegree(g)) == 1:
            continue
        for e, f, vd in P('wc_ldata')(g, p):
            e, f, vd = int(e), int(f), int(vd)
            art += f * vd
            tame += f * (e - 1)
            swan += f * (vd - e + 1)
            rows.append((int(P.poldegree(g)), e, f, vd))
    return dict(artin=art, tame=tame, swan=swan, primes=sorted(rows))


# ------------------------------------------------------------- elliptic torsion polynomials
def _b_invariants(a):
    a1, a2, a3, a4, a6 = [Q(x) for x in a]
    b2 = a1 * a1 + 4 * a2
    b4 = 2 * a4 + a1 * a3
    b6 = a3 * a3 + 4 * a6
    b8 = a1 * a1 * a6 + 4 * a2 * a6 - a1 * a3 * a4 + a2 * a3 * a3 - a4 * a4
    c4 = b2 * b2 - 24 * b4
    c6 = -b2 ** 3 + 36 * b2 * b4 - 216 * b6
    disc = -b2 * b2 * b8 - 8 * b4 ** 3 - 27 * b6 * b6 + 9 * b2 * b4 * b6
    return b2, b4, b6, b8, c4, c6, disc


def torsion_polynomials(a, ell, P=None):
    """x-polynomial and point polynomial (in t=y'+lam*x, y'=2y+a1x+a3) of E[ell]-0, ell in {2,3,4}.

    ell=2: the 2-division cubic (its roots are the three points).
    ell=3: psi_3 (4 lines) and the degree-8 point polynomial.
    ell=4: the degree-6 factor of psi_4/psi_2 (points of exact order 4 up to sign)
           and the degree-12 point polynomial.
    lam is the least of 0,1,-1,2,-2,... making the point polynomial squarefree.
    """
    P = P or pari()
    b2, b4, b6, b8 = _b_invariants(a)[:4]
    cubic = P('4*x^3+(%s)*x^2+2*(%s)*x+(%s)' % (b2, b4, b6))
    if ell == 2:
        return dict(lines=cubic, points=cubic, lam=None)
    if ell == 3:
        xpol = P('3*x^4+(%s)*x^3+3*(%s)*x^2+3*(%s)*x+(%s)' % (b2, b4, b6, b8))
    elif ell == 4:
        xpol = P('2*x^6+(b2)*x^5+5*(b4)*x^4+10*(b6)*x^3+10*(b8)*x^2+((b2)*(b8)-(b4)*(b6))*x+((b4)*(b8)-(b6)^2)'
                 .replace('b2', '(%s)' % b2).replace('b4', '(%s)' % b4).replace('b6', '(%s)' % b6).replace('b8', '(%s)' % b8))
    else:
        raise ValueError('ell in {2,3,4}')
    for lam in [0, 1, -1, 2, -2, 3, -3, 5, -5, 7]:
        R = P.polresultant(xpol, P('(t-(%d)*x)^2' % lam) - cubic, 'x')
        R = P.subst(R, 't', P('x'))
        if P.poldisc(R) != 0:
            return dict(lines=xpol, points=R, lam=lam)
    raise AssertionError('no separating linear form found')


# ------------------------------------------------------------- elliptic: Swan, tame part, conductor
def elliptic_swan_permutation(a, p, P=None):
    """Swan conductor of E at p in {2,3} from permutation conductors of torsion polynomials."""
    P = P or pari()
    if p == 2:
        tp = torsion_polynomials(a, 3, P)
        pts, lines = permutation_conductor(tp['points'], 2, P), permutation_conductor(tp['lines'], 2, P)
        twice = pts['swan'] - lines['swan']
        if twice % 2:
            raise AssertionError('odd Swan difference: the GL_2(F_3) character identity failed')
        return dict(swan=twice // 2, route='Sw(E)=(Sw(E[3]-0)-Sw(P(E[3])))/2', points=pts, lines=lines, lam=tp['lam'])
    if p == 3:
        tp = torsion_polynomials(a, 2, P)
        pts = permutation_conductor(tp['points'], 3, P)
        return dict(swan=pts['swan'], route='Sw(E)=Sw(E[2]-0)', points=pts)
    return dict(swan=0, route='p>3: inertia image has order prime to p')


def _close(gens, mul, ident):
    elems = {ident}
    frontier = [ident]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = mul(x, g)
                if y not in elems:
                    elems.add(y)
                    nxt.append(y)
        frontier = nxt
    return elems


def _compose(a, b):
    """(a o b)(i) = a(b(i)) on tuples."""
    return tuple(a[i] for i in b)


def splitting_galois_data(T, p, max_degree=96, P=None):
    """Galois data of the splitting field M of T at a prime above p.

    Returns the roots' action of the inertia filtration [G_0, G_1, ...] (as sets of
    root permutations together with the tame exponent), e_P, f_P, the tame index,
    and the valuation table v_P(r_i-r_j)/e_P.  None if [M:Q] > max_degree.
    """
    P = P or pari()
    Ty = P.subst(P('wc_monic')(T), 'x', P('y'))
    M = P.nfsplitting(Ty)
    deg = int(P.poldegree(M))
    if deg > max_degree:
        return None
    M = P.subst(P.polredbest(P.subst(M, P.variable(M), P('x'))), 'x', P('y'))
    nf = P.nfinit(M)
    gal = P.galoisinit(M)
    roots = P.nfroots(M, T)
    n = int(P.poldegree(T))
    if len(roots) != n:
        raise AssertionError('splitting field does not split T: %s %s %d' % (T, M, len(roots)))
    pr = P.idealprimedec(nf, p)[0]
    e_P, f_P = int(pr[2]), int(pr[3])
    rg = P.idealramgroups(nf, gal, pr)
    et = e_P
    while et % p == 0:
        et //= p
    q = p ** f_P
    pi = P('wc_unif')(nf, pr)
    modpr = P.nfmodprinit(nf, pr)
    g = P.ffprimroot(P.nfmodpr(nf, P('y'), modpr))
    cache = {}

    def gen_data(perm):
        key = str(perm)
        if key not in cache:
            s = P.galoispermtopol(gal, perm)
            rp = tuple(int(x) for x in P('wc_rootperm')(nf, s, roots))
            if sorted(rp) != list(range(n)):
                raise AssertionError('automorphism does not permute the roots')
            lg = int(P('wc_tame')(nf, pr, s, pi, g, modpr))
            if lg % ((q - 1) // et):
                raise AssertionError('tame character outside mu_e')
            cache[key] = (rp, (lg // ((q - 1) // et)) % et)
        return cache[key]
    groups = []
    for grp in list(rg)[1:]:
        gens = [gen_data(gg) for gg in grp[0]]
        ident = (tuple(range(n)), 0)
        elems = _close(gens, lambda x, y: (_compose(x[0], y[0]), (x[1] + y[1]) % et), ident)
        order = 1
        for o in grp[1]:
            order *= int(o)
        if len(elems) != order:
            raise AssertionError('root action of a ramification group is not faithful')
        groups.append(sorted(elems))
    if not groups:  # PARI omits trailing trivial groups: unramified prime
        groups = [[(tuple(range(n)), 0)]]
    dist = [[None] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            v = Q(int(P.nfeltval(nf, P('(a,b)->a-b')(roots[i], roots[j]), pr)), e_P)
            dist[i][j] = dist[j][i] = v
    return dict(degree=deg, e=e_P, f=f_P, tame_index=et, groups=groups, dist=dist, n=n,
                filtration_orders=[len(G) for G in groups])


def swan_from_filtration(groups, fixed_dim, total_dim):
    """Sw = sum_{i>=1} |G_i|/|G_0| (dim - dim W^{G_i})."""
    if not groups:
        return 0
    g0 = len(groups[0])
    s = Q(0)
    for G in groups[1:]:
        s += Q(len(G), g0) * (total_dim - fixed_dim(G))
    if s.denominator != 1:
        raise AssertionError('non-integral Swan conductor (Hasse-Arf)')
    return int(s)


def elliptic_swan_filtration(a, p, P=None, max_degree=96):
    """Swan conductor of E from the ramification groups of Q(E[l]) (l=3 at p=2, l=2 at p=3)."""
    P = P or pari()
    ell = 3 if p == 2 else 2
    tp = torsion_polynomials(a, ell, P)
    gd = splitting_galois_data(tp['points'], p, max_degree, P)
    if gd is None:
        return None
    npts = gd['n']

    def fixed_dim(G):
        fix = sum(all(el[0][i] == i for el in G) for i in range(npts))
        d = round(log(fix + 1) / log(ell))
        if ell ** d != fix + 1:
            raise AssertionError('fixed points of a ramification group do not form a subgroup')
        return d
    sw = swan_from_filtration(gd['groups'], fixed_dim, 2)
    return dict(swan=sw, field_degree=gd['degree'], e=gd['e'], f=gd['f'], filtration_orders=gd['filtration_orders'])


def elliptic_tame_part(a, p, P=None):
    """2 - dim V^I without Tate's algorithm (j-invariant, twist, Serre-Tate)."""
    P = P or pari()
    b2, b4, b6, b8, c4, c6, disc = _b_invariants(a)
    if not disc:
        raise ValueError('singular curve')
    vj = 3 * _vp(c4, p) - _vp(disc, p) if c4 else 10 ** 9
    if vj < 0:
        d = -c6
        k = _vp(d, p)
        u = d / Q(p) ** k
        if p == 2:
            unram = k % 2 == 0 and (u.numerator * u.denominator) % 4 == 1
        else:
            unram = k % 2 == 0
        return dict(tame=1 if unram else 2, kind='potentially multiplicative', twist=str(d), twist_unramified=unram, v_j=vj)
    ell = 3 if p == 2 else 4
    if p not in (2, 3):
        ell = 3
    tp = torsion_polynomials(a, ell, P)
    pc = permutation_conductor(tp['points'], p, P)
    good = pc['artin'] == 0
    return dict(tame=0 if good else 2, kind='potentially good', torsion_level=ell, torsion_points_artin=pc['artin'],
                v_j=None if vj >= 10 ** 8 else vj)


def elliptic_conductor_galois(a, p, P=None, filtration=False):
    """Conductor exponent of E at p from the Galois representation (tame part + Swan)."""
    P = P or pari()
    tame = elliptic_tame_part(a, p, P)
    sw = elliptic_swan_permutation(a, p, P)
    out = dict(schema=SCHEMA, p=p, ainvs=[str(x) for x in a], tame=tame['tame'], swan=sw['swan'],
               conductor_exponent=tame['tame'] + sw['swan'], tame_data=tame, swan_route=sw['route'])
    if tame['tame'] == 0 and sw['swan']:
        raise AssertionError('good reduction with nonzero Swan conductor')
    if filtration and p in (2, 3):
        fl = elliptic_swan_filtration(a, p, P)
        out['swan_filtration'] = fl
        if fl is not None and fl['swan'] != sw['swan']:
            raise AssertionError('Swan conductor: filtration and permutation routes disagree')
    return out


_KODAIRA_COMPONENTS = {'I0': 1, 'II': 1, 'III': 2, 'IV': 3, 'I0*': 5, 'IV*': 7, 'III*': 8, 'II*': 9}


def kodaira_components(kod):
    """Number of geometric components m of the special fibre of the minimal regular model."""
    if kod in _KODAIRA_COMPONENTS:
        return _KODAIRA_COMPONENTS[kod]
    if kod.endswith('*'):
        return 5 + int(kod[1:-1])
    return int(kod[1:])


def ogg_exponent(kod, vdisc_min):
    """Ogg's formula f = v(Delta_min) - m + 1."""
    return vdisc_min - kodaira_components(kod) + 1


def pari_kodaira_symbol(code):
    """Inverse of dyadic_reduction.kodaira_pari_code."""
    code = int(code)
    if code == 1:
        return 'I0'
    if code > 4:
        return 'I%d' % (code - 4)
    if code < -4:
        return 'I%d*' % (-code - 4)
    return {2: 'II', 3: 'III', 4: 'IV', -1: 'I0*', -2: 'II*', -3: 'III*', -4: 'IV*'}[code]


# ------------------------------------------------------------- genus >= 2 at odd p: Lefschetz over the inertia image
class _DistDomain:
    def __init__(self, p, dist):
        self.p, self.dist = p, dist

    def parse(self, r):
        return int(r)

    def sub(self, i, j):
        return (i, j)

    def v(self, x):
        return self.dist[x[0]][x[1]]

    def sigma(self, i):
        return i

    def lead_v(self, c):
        return Q(_vp(c, self.p))


def _frac1(x):
    x = Q(x)
    return x - (x.numerator // x.denominator)


def _cluster_perm(pic, root_perm):
    by = {frozenset(c['roots']): c['id'] for c in pic['clusters']}
    out = []
    for c in pic['clusters']:
        img = frozenset(root_perm[i] for i in c['roots'])
        if img not in by:
            raise AssertionError('Galois action does not permute clusters')
        out.append(by[img])
    return out


def inertia_invariants(pic, elements):
    """dim V^I (abelian and toric parts) by a Lefschetz average over a finite group.

    elements: list of (root permutation, k) forming a group, where the element
    multiplies p^a (prime-to-p roots, modulo the maximal ideal) by exp(2 pi i k a).
    """
    cl = pic['clusters']
    N = len(elements)
    cperm = [_cluster_perm(pic, el[0]) for el in elements]
    info = {}
    for c in cl:
        flags = c['odd_children'] + c['size'] % 2
        E = sum(cl[k]['size'] // 2 for k in c['children'])
        odd_kids = [('r', i) for i in c['singletons']] + [('c', k) for k in c['children'] if cl[k]['size'] % 2]
        all_kids = [('r', i) for i in c['singletons']] + [('c', k) for k in c['children']]
        info[c['id']] = dict(two=(flags == 0), g=(flags - 2) // 2 if flags else 0, E=E, mu=c['nu'] - c['size'] * c['depth'],
                             n=c['odd_children'], odd_kids=odd_kids, all_kids=all_kids, d=c['depth'], nu=c['nu'])

    def sheet_sign(mu, k):
        x = Q(k) * mu
        if x.denominator != 1:
            raise AssertionError('sheet phase is not a sign')
        return 1 if int(x) % 2 == 0 else -1

    def kid_fixed(o, idx):
        return elements[idx][0][o[1]] == o[1] if o[0] == 'r' else cperm[idx][o[1]] == o[1]

    graph_traces = []
    for idx, (rp, k) in enumerate(elements):
        fixV = fixE = 0
        for c in cl:
            if cperm[idx][c['id']] != c['id']:
                continue
            I = info[c['id']]
            fixV += (2 if sheet_sign(I['mu'], k) == 1 else 0) if I['two'] else 1
            if c['parent'] is not None:
                fixE += (2 if sheet_sign(I['mu'], k) == 1 else 0) if c['size'] % 2 == 0 else 1
        graph_traces.append(1 - fixV + fixE)
    if sum(graph_traces) % N:
        raise AssertionError('graph Lefschetz average not integral')
    toric_inv = sum(graph_traces) // N

    ab_inv, seen, rows, wild_seen = 0, set(), [], 0
    naive_sum = Q(0)  # ablation: every fixed point counted once
    for c in cl:
        I = info[c['id']]
        if I['two'] or I['g'] < 1 or c['id'] in seen:
            continue
        orbit = sorted({cp[c['id']] for cp in cperm})
        seen.update(orbit)
        stab = [i for i in range(N) if cperm[i][c['id']] == c['id']]
        traces, naive = [], []
        for idx in stab:
            k = elements[idx][1]
            a_ph = _frac1(Q(k) * I['d'])
            g_ph = _frac1(Q(k) * (I['nu'] - 2 * I['d'] * I['E']) / 2)
            n_odd = I['n']
            if a_ph == 0:
                if g_ph not in (0, Q(1, 2)):
                    raise AssertionError('alpha=1 forces the identity or the hyperelliptic involution')
                moved = [o for o in I['all_kids'] if not kid_fixed(o, idx)]
                if not moved:
                    traces.append(2 * I['g'] if g_ph == 0 else 2 - (n_odd + (1 if n_odd % 2 else 0)))
                    naive.append(traces[-1])
                    continue
                if len(moved) != len(I['all_kids']):
                    raise AssertionError('a translation of the component fixes a child')
                wild_seen += 1
                if g_ph == 0:
                    mult = 3 if n_odd % 2 else 4
                else:
                    mult = 1 if n_odd % 2 else 0
                traces.append(2 - mult)
                naive.append(2 - (1 if n_odd % 2 else (2 if g_ph == 0 else 0)))
                continue
            fixed_kids = [o for o in I['odd_kids'] if kid_fixed(o, idx)]
            if len(fixed_kids) > 1:
                raise AssertionError('two odd children fixed by a nontrivial rotation')
            if fixed_kids:
                fix0 = 1
            else:
                if _frac1(2 * g_ph) != 0:
                    raise AssertionError('gamma^2 != 1 over the fixed point')
                fix0 = 2 if g_ph == 0 else 0
            if n_odd % 2:
                fixinf = 1
            else:
                ph = _frac1(g_ph - Q(n_odd, 2) * a_ph)
                if _frac1(2 * ph) != 0:
                    raise AssertionError('phase at infinity not a sign')
                fixinf = 2 if ph == 0 else 0
            traces.append(2 - fix0 - fixinf)
            naive.append(traces[-1])
        naive_sum += Q(sum(naive), len(stab))
        s = sum(traces)
        if s % len(stab):
            raise AssertionError('component Lefschetz average not integral')
        ab_inv += s // len(stab)
        rows.append(dict(cluster=c['id'], orbit=orbit, genus=I['g'], stabiliser_order=len(stab), invariants=s // len(stab)))
    return dict(abelian_invariants=ab_inv, toric_invariants=toric_inv, components=rows, wild_translations=wild_seen,
                naive_abelian_invariants=str(naive_sum),
                group_order=N)


def curve_conductor_galois(coeffs, p, P=None, max_degree=96):
    """Conductor exponent of Jac(y^2=f) at an odd prime p from the Galois route (wild allowed).

    coeffs: integer coefficients of f (low->high), squarefree, degree >= 3.
    Returns None when the splitting field is larger than max_degree.
    """
    from .cluster_stable_reduction import cluster_picture
    if p == 2:
        raise ValueError('odd p required (the double cover is wild at 2)')
    P = P or pari()
    T = _pol(P, coeffs)
    if P.poldisc(T) == 0:
        raise ValueError('squarefree f required')
    gd = splitting_galois_data(T, p, max_degree, P)
    if gd is None:
        return None
    n = gd['n']
    pic = cluster_picture(_DistDomain(p, gd['dist']), list(range(n)), coeffs[-1])
    G0 = gd['groups'][0]
    et, eP = gd['tame_index'], gd['e']
    elements = []
    for rp, j in G0:
        for jj in (j, j + et):
            elements.append((rp, Q(jj * eP, et)))
    inv = inertia_invariants(pic, elements)
    g = pic['genus']
    tame = 2 * g - inv['abelian_invariants'] - inv['toric_invariants']
    if tame < 0:
        raise AssertionError('negative tame conductor')

    # the permutation module: dim W^{G_i} = number of G_i-orbits on the roots
    swan = swan_from_filtration(gd['groups'], lambda G: len({frozenset(_orbit(G, i)) for i in range(n)}), n)
    disc_route = permutation_conductor(T, p, P)
    if disc_route['swan'] != swan:
        raise AssertionError('Swan conductor: filtration and discriminant routes disagree')
    return dict(schema=SCHEMA, p=p, coefficients=[int(c) for c in coeffs], genus=g, splitting_degree=gd['degree'],
                e=eP, f=gd['f'], tame_index=et, filtration_orders=gd['filtration_orders'],
                depths=sorted({str(c['depth']) for c in pic['clusters']}),
                cluster_sizes=[c['size'] for c in pic['clusters']],
                abelian_invariants=inv['abelian_invariants'], toric_invariants=inv['toric_invariants'],
                wild_translations=inv['wild_translations'], tame_part=tame, swan=swan,
                naive_multiplicity_conductor=str(2 * g - naive_sum_q(inv) - inv['toric_invariants'] + swan),
                conductor_exponent=tame + swan, wild=gd['tame_index'] != gd['e'])


def naive_sum_q(inv):
    return Q(inv['naive_abelian_invariants'])


def _orbit(G, i):
    return {el[0][i] for el in G}


# ------------------------------------------------------------- genus two at 2: split Jacobians
def bielliptic_factors(g):
    """E1: Y^2=g(X), E2: Y^2=X^3 g(1/X) for y^2=g(x^2), as a-invariants."""
    from .dyadic_reduction import weierstrass_from_hyperelliptic
    g = [Q(x) for x in g]
    if len(g) != 4 or not g[0] or not g[3]:
        raise ValueError('cubic g with g(0) != 0 required')
    return weierstrass_from_hyperelliptic(g), weierstrass_from_hyperelliptic(list(reversed(g)))


def _integral_ainvs(a):
    from .dyadic_reduction import _integral_model
    return _integral_model(a)


def bielliptic_conductor_galois(g, p, P=None):
    """Conductor exponent at p of Jac(y^2=g(x^2)) ~ E1 x E2, each from the Galois route."""
    P = P or pari()
    E1, E2 = bielliptic_factors(g)
    r1 = elliptic_conductor_galois(_integral_ainvs(E1), p, P)
    r2 = elliptic_conductor_galois(_integral_ainvs(E2), p, P)
    return dict(schema=SCHEMA, p=p, g=[str(x) for x in g], E1=r1, E2=r2,
                tame_part=r1['tame'] + r2['tame'], swan=r1['swan'] + r2['swan'],
                conductor_exponent=r1['conductor_exponent'] + r2['conductor_exponent'])


def mobius_sextic(f, m):
    """Coefficients of (c x+d)^6 f((a x+b)/(c x+d)) for f of degree <= 6 (low->high), m=(a,b,c,d)."""
    from math import comb
    a, b, c, d = m
    f = list(f) + [0] * (7 - len(f))
    out = [0] * 7
    for i, fi in enumerate(f):
        if not fi:
            continue
        # (a x+b)^i (c x+d)^(6-i)
        A = [comb(i, r) * a ** r * b ** (i - r) for r in range(i + 1)]
        B = [comb(6 - i, r) * c ** r * d ** (6 - i - r) for r in range(7 - i)]
        for r, x in enumerate(A):
            for s, y in enumerate(B):
                out[r + s] += fi * x * y
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


# ------------------------------------------------------------- analytic oracle (functional equation)
def analytic_exponent_check(coeffs, odd_conductor, k, P=None, euler2=None):
    """Bit accuracy of the functional equation of L(Jac(y^2=f), s) with conductor odd*2^k.

    Uses PARI lfungenus2 for the Dirichlet series and the odd bad Euler factors
    and lfuncheckfeq; a value <= -30 is a functional equation to that accuracy,
    while a wrong conductor gives roughly -12 or worse.  lfungenus2 takes the
    Euler factor at 2 to be 1 when genus2red cannot treat 2; euler2 (coefficients
    of F_2(T), low->high) replaces it.  This is an oracle, not a proof.
    """
    P = P or pari()
    L = P('lfungenus2(%s)' % _pol(P, coeffs))
    if euler2 is not None and list(euler2) != [1]:
        L = P('wc_patch2')(L, P('Pol([%s], x)' % ','.join(str(x) for x in reversed(list(euler2)))))
    L2 = P('(L,N)->my(v=L);v[5]=N;v')(L, odd_conductor * 2 ** k)
    return int(P.lfuncheckfeq(L2))


def elliptic_euler_factor_2(a, P=None):
    """Local factor of an elliptic curve at 2 (oracle side, from PARI ellap)."""
    P = P or pari()
    E = P.ellinit([int(x) for x in a])
    ap = int(P.ellap(E, 2))
    good = int(P.valuation(P.ellglobalred(E)[0], 2)) == 0
    return [1, -ap, 2] if good else ([1, -ap] if ap else [1])


def poly_mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out
