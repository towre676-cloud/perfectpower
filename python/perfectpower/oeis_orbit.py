"""Finding the symmetry behind a cluster of OEIS entries, and proving it.

**Discovery** (`discover`): generate coordinates of one arithmetic orbit, here
`(1 + sqrt 2)^k = A_k + B_k sqrt 2`, under a library of observation maps (`A`, `B`, `2B`, `(A-1)/2`,
`B^2`, `AB`, ...) on all powers, the even powers (norm +1) and the odd powers (norm -1), and look
them up in a global term index.  Every hit is a *candidate* coordinate map.

**Verification** (`atlas`): each candidate is re-checked against the full original `.seq` entry,
term by term with exact integers at the entry's own offset.  An entry is promoted to
`DEFINITION_PROVED_EQUIVALENT` only if it is in `PROVED`: its definition, read from the `.seq`
text, is formalized in `PerfectPower/SqrtTwoOrbit.lean` with the same offset, the Lean theorems
exist, and every term agrees.  Everything else stays `TERMS_AGREE_UNPROVED` (or `REJECTED`).

**Mordell check** (`mordell_check`): A081119/A081120 count the integral solutions of
`y^2 = x^3 + n` and `y^2 = x^3 - n`.  Every curve whose complete list is certified in Lean is
compared with those counts; for the curves the compiler cannot enumerate, the published count and
the points a scan finds are recorded as ranked leads (a published count is not a proof).
"""
from __future__ import annotations

import json
import re
from math import isqrt
from pathlib import Path

from .oeis_source import Entry, parse_seq

from .resources import runtime_root
ROOT = runtime_root()


def orbit(n: int = 90) -> tuple[list[int], list[int]]:
    """A_k, B_k for (1 + sqrt 2)^k, k < n."""
    A, B = [1], [0]
    for _ in range(n - 1):
        A.append(A[-1] + 2 * B[-1])
        B.append(A[-2] + B[-1])
    return A, B


FILTERS = {'all': (1, 0), 'even': (2, 0), 'odd': (2, 1)}   # k = P*i + r


def _half(x):
    return x // 2 if x % 2 == 0 else None


def _odd_half(x, s):
    return (x + s) // 2 if (x + s) % 2 == 0 else None


MAPS = {
    'A': lambda a, b: a, 'B': lambda a, b: b, '2B': lambda a, b: 2 * b, 'B/2': lambda a, b: _half(b),
    '(A-1)/2': lambda a, b: _odd_half(a, -1), '(A+1)/2': lambda a, b: _odd_half(a, 1),
    'A^2': lambda a, b: a * a, 'B^2': lambda a, b: b * b,
    '(B/2)^2': lambda a, b: None if b % 2 else (b // 2) ** 2,
    'AB': lambda a, b: a * b, '2AB': lambda a, b: 2 * a * b, 'A+B': lambda a, b: a + b,
    'A+2B': lambda a, b: a + 2 * b, 'A-B': lambda a, b: a - b, 'B-A': lambda a, b: b - a,
    '(A^2-1)/2': lambda a, b: _odd_half(a * a, -1), 'B(B+1)/2': lambda a, b: b * (b + 1) // 2,
    'A^2+B^2': lambda a, b: a * a + b * b,
    '(A-1)(A+1)/4': lambda a, b: ((a - 1) // 2) * ((a + 1) // 2) if a % 2 else None,
    '(A+B)/2': lambda a, b: _half(a + b),
}


def coordinate(fname: str, mname: str, i: int, A=None, B=None):
    """The value of map `mname` at the `i`-th power in filter `fname`."""
    P, r = FILTERS[fname]
    k = P * i + r
    if A is None or k >= len(A):
        A, B = orbit(k + 2)
    return MAPS[mname](A[k], B[k])


def unit_orbit(t: int, sigma: int, a0: tuple[int, int], b0: tuple[int, int], n: int = 90):
    """The two coordinate sequences of a quadratic unit: x(k+2) = t x(k+1) + sigma x(k)."""
    A, B = list(a0), list(b0)
    while len(A) < n:
        A.append(t * A[-1] + sigma * A[-2])
        B.append(t * B[-1] + sigma * B[-2])
    return A[:n], B[:n]


# the orbits searched: (1 + sqrt 2)^k = A + B sqrt 2, phi^k = (L + F sqrt 5)/2, (2 + sqrt 3)^k
ORBITS = {
    'sqrt2': lambda n=90: orbit(n),
    'phi': lambda n=90: unit_orbit(1, 1, (2, 1), (0, 1), n),
    'sqrt3': lambda n=90: unit_orbit(4, -1, (1, 2), (0, 1), n),
}


def discover(index: dict, width: int = 5, min_terms: int = 8, A=None, B=None) -> list[dict]:
    """Candidate coordinate maps for every index entry: (entry, filter, map, shift)."""
    if A is None:
        A, B = orbit(90)
    windows: dict[tuple, list] = {}
    for aid, (off, name, ts) in index.items():
        for p in range(min(3, max(0, len(ts) - width))):
            windows.setdefault(tuple(ts[p:p + width]), []).append((aid, p))
    found: dict[str, dict] = {}
    for fname, (P, r) in FILTERS.items():
        ks = range(r, len(A), P)
        for mname, m in MAPS.items():
            vals = [m(A[k], B[k]) for k in ks]
            for st in range(4):
                s = vals[st:]
                if any(v is None for v in s[:12]) or len(set(s[:width])) < width - 1:
                    continue
                for aid, p in windows.get(tuple(s[:width]), []):
                    off, name, ts = index[aid]
                    L = len(ts) - p
                    if L < min_terms or any(ts[p + i] != s[i] for i in range(min(L, len(s)))):
                        continue
                    # the entry's a(offset + p + i) is the coordinate at power index st + i
                    cand = {'oeis': aid, 'filter': fname, 'map': mname,
                            'power_index_of_first_term': st - p, 'index_terms_agreeing': L,
                            'name_prefix': name[:60]}
                    prev = found.get(aid)
                    if prev is None or (prev['filter'], len(prev['map'])) > (fname, len(mname)):
                        found[aid] = cand
    return sorted(found.values(), key=lambda c: c['oeis'])


# --------------------------------------------------------------------------------------------
# the entries whose definitions are formalized and proved (PerfectPower/SqrtTwoOrbit.lean)
# --------------------------------------------------------------------------------------------

L = 'PerfectPower.SqrtTwoOrbit.'

def _A(k):
    return orbit(k + 1)[0][k]


def _B(k):
    return orbit(k + 1)[1][k]


PROVED = {
    'A000129': {'offset': 0, 'kind': 'recurrence', 'value': lambda n: _B(n),
                'coordinate': 'B_n', 'lean': [L + 'A000129', L + 'A000129_eq']},
    'A001541': {'offset': 0, 'kind': 'recurrence', 'value': lambda n: _A(2 * n),
                'coordinate': 'A_{2n}', 'lean': [L + 'A001541', L + 'A001541_eq']},
    'A001542': {'offset': 0, 'kind': 'recurrence', 'value': lambda n: _B(2 * n),
                'coordinate': 'B_{2n}', 'lean': [L + 'A001542', L + 'A001542_eq']},
    'A001109': {'offset': 0, 'kind': 'recurrence', 'value': lambda n: _B(2 * n) // 2,
                'coordinate': 'B_{2n}/2', 'lean': [L + 'A001109', L + 'A001109_eq']},
    'A001108': {'offset': 0, 'kind': 'recurrence', 'value': lambda n: (_A(2 * n) - 1) // 2,
                'coordinate': '(A_{2n}-1)/2', 'lean': [L + 'A001108', L + 'A001108_eq']},
    'A001652': {'offset': 0, 'kind': 'recurrence', 'value': lambda n: (_A(2 * n + 1) - 1) // 2,
                'coordinate': '(A_{2n+1}-1)/2', 'lean': [L + 'A001652', L + 'A001652_eq']},
    'A002315': {'offset': 0, 'kind': 'recurrence (initial values from the terms)',
                'value': lambda n: _A(2 * n + 1), 'coordinate': 'A_{2n+1}',
                'lean': [L + 'A002315', L + 'A002315_eq', L + 'A002315_A001653']},
    'A005319': {'offset': 0, 'kind': 'recurrence (initial values from the terms)',
                'value': lambda n: 2 * _B(2 * n), 'coordinate': '2 B_{2n}',
                'lean': [L + 'A005319', L + 'A005319_eq']},
    'A001110': {'offset': 0, 'kind': 'set: square triangular numbers, increasing',
                'value': lambda n: (_B(2 * n) // 2) ** 2, 'coordinate': '(B_{2n}/2)^2',
                'lean': [L + 'A001110', L + 'A001110_enumerates']},
    'A001653': {'offset': 1, 'kind': 'set: k with 2k^2 - 1 a square, increasing',
                'value': lambda n: _B(2 * n - 1), 'coordinate': 'B_{2n-1}',
                'lean': [L + 'A001653', L + 'A001653_enumerates']},
    'A055997': {'offset': 1, 'kind': 'set: k >= 1 with k(k-1)/2 a square, increasing',
                'value': lambda n: (_A(2 * n - 2) + 1) // 2, 'coordinate': '(A_{2n-2}+1)/2',
                'lean': [L + 'A055997', L + 'A055997_enumerates']},
    'A084703': {'offset': 0, 'kind': 'set: squares k with 2k + 1 a square, increasing',
                'value': lambda n: _B(2 * n) ** 2, 'coordinate': 'B_{2n}^2',
                'lean': [L + 'A084703', L + 'A084703_enumerates']},
    'A075870': {'offset': 1, 'kind': 'set: k with 2k^2 - 4 a square, increasing',
                'value': lambda n: 2 * _B(2 * n - 1), 'coordinate': '2 B_{2n-1}',
                'lean': [L + 'A075870', L + 'A075870_enumerates']},
}

# hand-written proofs for definitions that need more than a recurrence (PerfectPower/SqrtTwoBatch.lean)
LB = 'PerfectPower.SqrtTwoBatch.'
PROVED.update({
    'A046090': {'offset': 0, 'kind': 'Pythagorean triples (X, X+1, Z) by increasing Z, X+1 (from (0,1,1))',
                'value': lambda n: (_A(2 * n + 1) + 1) // 2, 'coordinate': '(A_{2n+1}+1)/2',
                'lean': [LB + 'A046090', LB + 'triples_listed', LB + 'triple_iff', LB + 'A046090_eq']},
    'A115598': {'offset': 1, 'kind': 'Pythagorean triples by increasing Z (from (3,4,5)), Z-(X+1)',
                'value': lambda n: _B(2 * n + 1) - (_A(2 * n + 1) + 1) // 2,
                'coordinate': 'B_{2n+1} - (A_{2n+1}+1)/2',
                'lean': [LB + 'A115598', LB + 'pos_triples_listed', LB + 'A115598_eq']},
    'A115599': {'offset': 1, 'kind': 'Pythagorean triples by increasing Z (from (3,4,5)), Z-X',
                'value': lambda n: _B(2 * n + 1) - (_A(2 * n + 1) - 1) // 2,
                'coordinate': 'B_{2n+1} - (A_{2n+1}-1)/2',
                'lean': [LB + 'A115599', LB + 'pos_triples_listed', LB + 'A115599_eq']},
    'A098602': {'offset': 0, 'kind': 'product of entries A001652 * A046090',
                'value': lambda n: (_A(2 * n + 1) ** 2 - 1) // 4, 'coordinate': '(A_{2n+1}^2-1)/4',
                'lean': [LB + 'A098602', LB + 'A098602_eq']},
    'A090390': {'offset': 0, 'kind': 'matrix orbit: (1,0,0) M^n, leading entry',
                'value': lambda n: _A(n) ** 2, 'coordinate': 'A_n^2',
                'lean': [LB + 'A090390', LB + 'vM_eq', LB + 'A090390_eq']},
    'A078522': {'offset': 1, 'kind': 'set: k with (k+1)(2k+1) a square (coprime splitting), increasing',
                'value': lambda n: _B(2 * n - 1) ** 2 - 1, 'coordinate': 'B_{2n-1}^2 - 1',
                'lean': [LB + 'A078522', LB + 'A078522_enumerates']},
    'A055792': {'offset': 0, 'kind': 'set: a and floor(a/2) squares; 0 is the exceptional element',
                'value': lambda n: 0 if n == 0 else _A(2 * n - 2) ** 2, 'coordinate': '0, then A_{2n-2}^2',
                'lean': [LB + 'A055792', LB + 'A055792_enumerates', LB + 'sq_eq_two_sq']},
    'A046176': {'offset': 1, 'kind': 'set: k with k^2 hexagonal (residue filter mod 4), increasing',
                'value': lambda n: _B(4 * n - 2) // 2, 'coordinate': 'B_{4n-2}/2',
                'lean': [LB + 'A046176', LB + 'A046176_enumerates', LB + 'A_mod4']},
    'A008843': {'offset': 0, 'kind': 'set: x^2 with x^2 - 2y^2 = -1, increasing',
                'value': lambda n: _A(2 * n + 1) ** 2, 'coordinate': 'A_{2n+1}^2',
                'lean': [LB + 'A008843', LB + 'A008843_enumerates', LB + 'A008843_A002315']},
    'A008844': {'offset': 0, 'kind': 'set: y^2 with x^2 - 2y^2 = -1, increasing',
                'value': lambda n: _B(2 * n + 1) ** 2, 'coordinate': 'B_{2n+1}^2',
                'lean': [LB + 'A008844', LB + 'A008844_enumerates', LB + 'A008844_A001653']},
})

LC = 'PerfectPower.SqrtTwoBridges.'
PROVED['A001333'] = {'offset': 0, 'kind': 'continued-fraction numerators of sqrt(2), from p_(-1) = 1 (Mathlib GenContFract.of)',
                     'value': lambda n: _A(n), 'coordinate': 'A_n',
                     'lean': [LC + 'A001333', LC + 'A001333_eq', LC + 'cf_sqrt2_s', LC + 'contsAux_sqrt2',
                              LC + 'convs_sqrt2']}

# definitions proved from their own text (PerfectPower/SqrtTwoDefs.lean)
LD = 'PerfectPower.SqrtTwoDefs.'
PROVED.update({
    'A024537': {'offset': 0, 'kind': 'floor recursion a(n) = floor(a(n-1)/(sqrt(2) - 1)), a(0) = 1',
                'value': lambda n: (_A(n + 1) + 1) // 2, 'coordinate': '(A_{n+1}+1)/2',
                'lean': [LD + 'A024537', LD + 'A024537_eq', LD + 'floor_step']},
    'A171842': {'offset': 0, 'kind': 'binomial transform of 1,0,1,0,2,0,4,... (finite sum, binomial theorem)',
                'value': lambda n: (_A(n) + 1) // 2, 'coordinate': '(A_n+1)/2',
                'lean': [LD + 'A171842', LD + 'c171842', LD + 'A171842_eq']},
    'A163271': {'offset': 1, 'kind': 'reduced numerators of r(n) = (r(n-1)+2)/(r(n-1)+1), r(1) = 0',
                'value': lambda n: 2 * _B(n - 1), 'coordinate': '2 B_{n-1}',
                'lean': [LD + 'A163271', LD + 'r163', LD + 'A163271_eq', LD + 'coprime_A_2B']},
    'A069306': {'offset': 2, 'kind': '2 x n binary arrays with an edge-adjacent path of 1s from the '
                                  'upper-left corner to the right column (frontier transfer)',
                'value': lambda n: _B(n + 1), 'coordinate': 'B_{n+1}',
                'lean': [LD + 'A069306', LD + 'Good', LD + 'reach_iff', LD + 'A069306_eq']},
})


def _lean_names() -> set[str]:
    names = set()
    for p in (ROOT / 'PerfectPower').rglob('*.lean'):
        ns = re.search(r'^namespace (\S+)', p.read_text(), re.M)
        pre = ns.group(1) + '.' if ns else ''
        for m in re.finditer(r'^(?:theorem|lemma|def|noncomputable def)\s+(\S+)', p.read_text(), re.M):
            names.add(pre + m.group(1))
    return names


def check_proved(e: Entry, lean_names: set[str] | None = None) -> dict:
    """The promotion test for one entry: offset, every term, and the Lean names."""
    spec = PROVED[e.id]
    lean_names = lean_names if lean_names is not None else _lean_names()
    bad = None
    for n, t in e.indexed():
        if spec['value'](n) != t:
            bad = {'n': n, 'entry': t, 'coordinate': spec['value'](n)}
            break
    missing = [x for x in spec['lean'] if x not in lean_names]
    ok = bad is None and e.offset == spec['offset'] and not missing
    return {'offset_entry': e.offset, 'offset_lean': spec['offset'], 'terms_checked': len(e.terms),
            'first_disagreement': bad, 'missing_lean': missing, 'ok': ok}


def load_auto() -> dict:
    """Entries proved by the generated Lean (`receipts/oeis_auto.json`), by id."""
    p = ROOT / 'receipts' / 'oeis_auto.json'
    if not p.exists():
        return {}
    return {r['oeis']: r for r in json.loads(p.read_text())['entries'] if r['status'] == 'PROVED'}


def atlas(source, candidates: list[dict], A=None, B=None, auto: dict | None = None) -> list[dict]:
    """Every candidate, re-verified against its full `.seq` entry.

    `auto` (from `load_auto`) adds the generated proofs: an entry whose definition the compiler
    proved equal to an orbit coordinate is promoted; when that equality starts after a finite
    initial segment and the discovered coordinate disagrees there, the outcome is
    `EXCEPTIONAL_SET_PROVED` (equal outside a finite set, which is recorded)."""
    lean_names = _lean_names()
    if A is None:
        A, B = orbit(400)
    auto = auto or {}
    out = []
    for c in candidates:
        text = source.text(c['oeis'])
        if text is None:
            out.append({**c, 'outcome': 'NOT_CHECKED', 'reason': 'entry not in the local snapshot'})
            continue
        e = parse_seq(text)
        rec = {'oeis': e.id, 'offset': e.offset, 'filter': c['filter'], 'map': c['map'],
               'coordinate': f"{c['map']} on {c['filter']} powers, a({e.offset} + i) at power "
                             f"index {c['power_index_of_first_term']} + i"}
        # re-check every term of the full entry against the discovered coordinate
        base = c['power_index_of_first_term']
        bad = None
        for i, t in enumerate(e.terms):
            j = base + i
            if j < 0:
                continue
            v = coordinate(c['filter'], c['map'], j, A, B)
            if v != t:
                bad = {'term_index': e.offset + i, 'entry': t, 'coordinate': v}
                break
        rec['terms_checked'] = len(e.terms)
        if bad is not None:
            rec['outcome'] = 'REJECTED'
            rec['first_counterexample'] = bad
            # does the entry agree after its first few terms (an initial-value convention)?
            last_bad = max((i for i, t in enumerate(e.terms) if base + i >= 0 and
                            coordinate(c['filter'], c['map'], base + i, A, B) != t), default=-1)
            if last_bad < len(e.terms) - 8:
                rec['agrees_from_term'] = e.offset + last_bad + 1
            g = auto.get(e.id)
            if g is not None and g.get('shift') and rec.get('agrees_from_term') is not None:
                rec['outcome'] = 'EXCEPTIONAL_SET_PROVED'
                rec['proof'] = _auto_proof(g)
        elif e.id in PROVED:
            chk = check_proved(e, lean_names)
            rec['proof'] = {'kind': PROVED[e.id]['kind'], 'coordinate': PROVED[e.id]['coordinate'],
                            'lean': PROVED[e.id]['lean'], **chk}
            rec['outcome'] = 'DEFINITION_PROVED_EQUIVALENT' if chk['ok'] else 'TERMS_AGREE_UNPROVED'
        elif e.id in auto:
            rec['proof'] = _auto_proof(auto[e.id])
            rec['outcome'] = 'DEFINITION_PROVED_EQUIVALENT'
        else:
            rec['outcome'] = 'TERMS_AGREE_UNPROVED'
        out.append(rec)
    return out


def _auto_proof(g: dict) -> dict:
    return {'kind': 'generated: ' + g['translation']['kind'], 'relation': g.get('relation'),
            'family': g.get('family'), 'fit': g.get('fit'),
            'lean': ['PerfectPower.OEISAuto.' + t for t in g['theorems']]}


# --------------------------------------------------------------------------------------------
# Mordell curves: certified lists against the published counts
# --------------------------------------------------------------------------------------------

def _certified_points(k: int):
    """The complete point list of y^2 = x^3 + k when it is certified in Lean, else None."""
    from .compiler import mordell_complete
    from .descent import certificate
    solved = mordell_complete(k)
    if solved is not None:
        T, lean = solved
        pts = sorted({(t, s * m) for t, ms in T.items() for m in ms for s in (1, -1)})
        return pts, lean
    if k < 0:
        c = certificate(-k)
        if c is not None:
            return sorted(set(c['points'])), ['PerfectPower.Descent.complete_of_cert']
        b = _branch_certified().get(-k)
        if b is not None:
            return b
    return None


def _branch_certified() -> dict:
    """Curves y^2 = x^3 - D with a Lean branch certificate (`receipts/mordell_branch.json`)."""
    p = ROOT / 'receipts' / 'mordell_branch.json'
    if not p.exists():
        return {}
    out = {}
    for r in json.loads(p.read_text())['curves_detail']:
        if r['status'] == 'COMPLETE':
            out[r['D']] = (sorted(tuple(pt) for pt in r['points']), [r['lean']])
    q = ROOT / 'receipts' / 'thue_graph.json'
    if q.exists():
        for r in json.loads(q.read_text())['curves']:
            if r['status'] == 'COMPLETE':
                out[r['D']] = (sorted(tuple(pt) for pt in r['points']), [r['lean']])
    return out


def _scan_points(k: int, X: int = 10 ** 5) -> list[tuple[int, int]]:
    out = []
    lo = -int(round(abs(k) ** (1 / 3))) - 2 if k > 0 else 0
    for x in range(lo, X):
        v = x ** 3 + k
        if v >= 0:
            r = isqrt(v)
            if r * r == v:
                out.extend({(x, r), (x, -r)})
    return sorted(set(out))


def mordell_check(source) -> dict:
    """Certified lists vs A081119 / A081120; leads for the uncertified curves."""
    from .oeis import unresolved_mordell
    plus = parse_seq(source.text('A081119'))
    minus = parse_seq(source.text('A081120'))
    counts = {n: t for n, t in plus.indexed()}
    counts.update({-n: t for n, t in minus.indexed()})
    checks, disagreements = [], []
    for k in sorted(counts):
        got = _certified_points(k)
        if got is None:
            continue
        pts, lean = got
        rec = {'k': k, 'certified_points': len(pts), 'published': counts[k], 'lean': lean}
        checks.append(rec)
        if len(pts) != counts[k]:
            disagreements.append(rec)
    leads = []
    branch = _branch_certified()
    for cv in unresolved_mordell(-100, 100):
        k = cv['k']
        if k not in counts or -k in branch:
            continue
        pts = _scan_points(k)
        leads.append({'k': k, 'published_count': counts[k], 'scan_points': len(pts),
                      'points': pts, 'scan_matches_published': len(pts) == counts[k]})
    # nonempty first, then the ones where the scan already finds the published number of points
    leads.sort(key=lambda r: (r['published_count'] == 0, not r['scan_matches_published'], abs(r['k'])))
    return {'sources': {'A081119': 'y^2 = x^3 + n', 'A081120': 'y^2 = x^3 - n'},
            'certified_checked': len(checks), 'disagreements': disagreements, 'checks': checks,
            'leads': leads,
            'note': 'A081119 cites Gebel-Petho-Zimmer (1998) and Bennett-Ghadermarzi (2015) for the '
                    'computations; a published count is a lead, not a proof. The entry also records '
                    'the route used when the rank is 0: the integral points are the torsion points.'}


PROVED_OUTCOMES = ('DEFINITION_PROVED_EQUIVALENT', 'TRANSPORTED_FROM_DUPLICATE')

# entries whose text says "Essentially a duplicate" with a shift fixed only by their terms:
# (shift, Lean names of `a(n) = target(n + shift)`)
SHIFTED_DUPLICATES = {'A048624': (2, ['PerfectPower.SqrtTwoBridges.A048624',
                                      'PerfectPower.SqrtTwoBridges.A048624_eq']),
                      # "Duplicate of A024537", but both records have offset 0 and the terms are
                      # A024537 from index 1: the label holds only with this shift
                      'A018905': (1, ['PerfectPower.SqrtTwoDefs.A018905',
                                      'PerfectPower.SqrtTwoDefs.A018905_eq'])}


def transport(source, rows: list[dict]) -> None:
    """Proof transport along the reference graph: an entry named "Duplicate of X" (or
    "Essentially a duplicate of X") whose target X is proved, and whose every term agrees with X at
    the same index, is `TRANSPORTED_FROM_DUPLICATE`."""
    by_id = {r['oeis']: r for r in rows}
    for r in rows:
        if r['outcome'] != 'TERMS_AGREE_UNPROVED':
            continue
        e = parse_seq(source.text(r['oeis']))
        m = re.match(r'\s*(?:Essentially a )?[Dd]uplicate of (A\d{6})', e.name)
        if not m or m.group(1) not in by_id or by_id[m.group(1)]['outcome'] not in PROVED_OUTCOMES:
            continue
        t = dict(parse_seq(source.text(m.group(1))).indexed())
        mine = e.indexed()
        if all(n in t and t[n] == v for n, v in mine):
            r['outcome'] = 'TRANSPORTED_FROM_DUPLICATE'
            r['proof'] = {'kind': 'duplicate entry', 'target': m.group(1),
                          'terms_compared': len(mine), 'lean': by_id[m.group(1)]['proof']['lean']}
            continue
        # "Essentially a duplicate": a shift, when the terms determine exactly one (0 < s <= 4)
        shifts = [s for s in range(1, 5) if all(n + s in t and t[n + s] == v for n, v in mine)]
        lean = SHIFTED_DUPLICATES.get(e.id)
        if len(shifts) == 1 and lean and lean[0] == shifts[0]:
            r['outcome'] = 'TRANSPORTED_WITH_SHIFT'
            r['proof'] = {'kind': 'duplicate entry with a shift read from the terms',
                          'target': m.group(1), 'shift_from_terms': shifts[0],
                          'terms_compared': len(mine), 'lean': lean[1]}


def run(source, candidates: list[dict]) -> dict:
    auto = load_auto()
    others = {}
    for name in ('phi', 'sqrt3'):
        p = ROOT / 'data' / 'oeis' / f'discovery_{name}.json'
        if p.exists():
            A, B = ORBITS[name](400)
            others[name] = atlas(source, json.loads(p.read_text()), A, B, auto)
            transport(source, others[name])
    main = atlas(source, candidates, auto=auto)
    transport(source, main)
    return {'snapshot': source.version(), 'orbit': '(1 + sqrt 2)^k = A_k + B_k sqrt 2',
            'atlas': main, 'other_orbits': others,
            'mordell': mordell_check(source)}
