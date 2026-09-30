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

ROOT = Path(__file__).resolve().parents[2]


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


def discover(index: dict, width: int = 5, min_terms: int = 8) -> list[dict]:
    """Candidate coordinate maps for every index entry: (entry, filter, map, shift)."""
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


def atlas(source, candidates: list[dict]) -> list[dict]:
    """Every candidate, re-verified against its full `.seq` entry."""
    lean_names = _lean_names()
    A, B = orbit(400)
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
        elif e.id in PROVED:
            chk = check_proved(e, lean_names)
            rec['proof'] = {'kind': PROVED[e.id]['kind'], 'coordinate': PROVED[e.id]['coordinate'],
                            'lean': PROVED[e.id]['lean'], **chk}
            rec['outcome'] = 'DEFINITION_PROVED_EQUIVALENT' if chk['ok'] else 'TERMS_AGREE_UNPROVED'
        else:
            rec['outcome'] = 'TERMS_AGREE_UNPROVED'
        out.append(rec)
    return out


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
    return None


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
    for cv in unresolved_mordell(-100, 100):
        k = cv['k']
        if k not in counts:
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


def run(source, candidates: list[dict]) -> dict:
    return {'snapshot': source.version(), 'orbit': '(1 + sqrt 2)^k = A_k + B_k sqrt 2',
            'atlas': atlas(source, candidates), 'mordell': mordell_check(source)}
