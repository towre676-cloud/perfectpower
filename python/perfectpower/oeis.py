"""OEIS as a discovery and comparison layer: problems, not just terms.

The OEIS is a source of candidate *correspondences*.  Terms that agree are never a proof.  This
module does three things, and keeps them separate:

1. `problems()` exports PerfectPower's side: for each problem, its definition, the orbit it
   comes from, and several **coordinates** of that orbit (hit indices, witnesses, values).  Each
   coordinate comes with terms, an exact recurrence (checked on the terms), its growth rate,
   its certified counting constant, and the Lean theorems that establish it.  Committed as
   `receipts/oeis_problems.json`.
2. `atlas(stripped, names, reviewed)` compares those coordinates against a **local** OEIS
   snapshot (`stripped.gz`, `names.gz`, which the OEIS publishes daily).  The snapshot is never
   committed: its use is governed by the OEIS end-user license.  Each candidate gets one of
   four outcomes:
   * `DEFINITION_PROVED_EQUIVALENT`: the terms agree, a Lean theorem characterizes our set, and
     a reviewer has recorded (in `reviewed`) that the Lean definition is the entry's definition;
   * `TERMS_AGREE_UNPROVED`: every compared term agrees; no equivalence is claimed;
   * `RELATED_BY_TRANSFORMATION`: agreement after a stated transformation (`2x`, `x^2`, …);
   * `REJECTED`: a long agreeing prefix, then the first counterexample (recorded).
   The atlas stores A-numbers, alignment, the transformation, the counterexample and the
   retrieval date; it copies no names or terms from the snapshot.
3. `premise_candidates(names)` ranks entries whose names mention an unresolved Mordell equation
   `y^2 = x^3 + k` (a compiler `NOT_ENUMERATED` case), putting names that suggest a complete
   list ("all", "complete", "only", "integral points") first.  These are reading leads, nothing
   more.
"""
from __future__ import annotations

import gzip
import re
from fractions import Fraction
from math import isqrt, log, sqrt
from pathlib import Path

OUTCOMES = ('DEFINITION_PROVED_EQUIVALENT', 'TERMS_AGREE_UNPROVED', 'RELATED_BY_TRANSFORMATION',
            'REJECTED')

MIN_AGREE = 6          # compared terms needed before an agreement is reported
MIN_REJECT_PREFIX = 5  # agreeing terms before a disagreement is worth reporting


# ---------------------------------------------------------------------------
# PerfectPower's side
# ---------------------------------------------------------------------------

def _orbit(D: int, u: int, v: int, p0: tuple[int, int], n: int) -> list[tuple[int, int]]:
    out, (X, Y) = [], p0
    for _ in range(n):
        out.append((X, Y))
        X, Y = X * u + D * Y * v, X * v + Y * u
    return out


def _check_recurrence(terms: list[int], coeffs: list[int]) -> bool:
    """a(j + k) = sum_i coeffs[i] a(j + k - 1 - i) for all available j."""
    k = len(coeffs)
    return all(terms[j + k] == sum(c * terms[j + k - 1 - i] for i, c in enumerate(coeffs))
               for j in range(len(terms) - k))


def square_triangular_cluster(n_terms: int = 30) -> dict:
    """The orbit (3 + sqrt 8)^j and six coordinates of it (PerfectPower/SquareTriangular.lean)."""
    pts = _orbit(8, 3, 1, (1, 0), n_terms + 1)[1:]          # j = 1, 2, ...
    X = [p[0] for p in pts]
    Y = [p[1] for p in pts]
    lin, sq = [6, -1], [35, -35, 1]
    L = 'PerfectPower.SquareTriangular.'
    coords = [
        ('PellIdx', 'n >= 1 with 2n^2 + 1 a square', '2 Y_j', [2 * y for y in Y], lin, 1, 1, 1,
         [L + 'pellIdx_iff', L + 'pellIdx_count']),
        ('PellRoot', 'm with m^2 = 2n^2 + 1 for some n >= 1', 'X_j', X, lin, 1, 1, 1,
         [L + 'pellRoot_iff', L + 'pellRoot_count']),
        ('SqTriRoot', 't >= 1 with t^2 triangular', 'Y_j', Y, lin, 1, 1, 1,
         [L + 'sqTriRoot_iff', L + 'sqTriRoot_count']),
        ('TriIdx', 'u >= 1 with u(u+1)/2 a square', '(X_j - 1)/2', [(x - 1) // 2 for x in X], [7, -7, 1],
         1, 1, 1, [L + 'triIdx_iff', L + 'triIdx_count']),
        ('SqTri', 'v >= 1 both square and triangular', 'Y_j^2', [y * y for y in Y], sq, 2, 1, 1,
         [L + 'sqTri_iff', L + 'sqTri_count']),
        ('OddSqTri', 'odd square triangular numbers', 'Y_j^2, j odd', [Y[i] ** 2 for i in range(0, n_terms, 2)],
         None, 2, 1, 2, [L + 'oddSqTri_iff', L + 'oddSqTri_count']),
    ]
    out = []
    for key, definition, coord, terms, rec, r, g, P, lean in coords:
        if rec is not None:
            assert _check_recurrence(terms, rec), key
        const = Fraction(g, P * r)
        out.append({'key': key, 'definition': definition, 'coordinate': coord, 'terms': terms,
                    'recurrence': rec, 'growth': f'eps^({r}j)' if r > 1 else 'eps^j',
                    'count_constant': f'{const} / log(3 + 2*sqrt(2))',
                    'count_constant_value': float(const) / log(3 + 2 * sqrt(2)),
                    'least': terms[0], 'lean': lean})
    return {'problem': 'square_triangular', 'orbit': 'X_j + Y_j sqrt(8) = (3 + sqrt(8))^j',
            'norm_form': 'X^2 - 8 Y^2 = 1', 'field': 'Q(sqrt(2))',
            'field_symmetry': 'conjugation m + n sqrt(2) -> m - n sqrt(2) fixes the norm m^2 - 2n^2',
            'unit': '3 + 2 sqrt(2) (= 3 + sqrt(8)) advances the orbit',
            'substitution': 'm = 2u + 1, n = 2t (the Pell equation forces n even)',
            'lean_orbit': [L + 'sol_iff', L + 'sol_nat', L + 'even_of_pell'],
            'lean_count': 'PerfectPower.Observation.observed_count',
            'coordinates': out}


def _plan_problems(n_terms: int = 20) -> list[dict]:
    """The catalogued infinite plans: hit indices and first witnesses as coordinates."""
    import sys
    root = Path(__file__).resolve().parents[1]
    sys.path.insert(0, str(root))
    from make_lean_plans import catalogue  # noqa: E402
    from .compiler import STRUCTURED_INFINITE, compile_constraint, count_cert
    out = []
    for name, con in catalogue():
        plan = compile_constraint(con)
        if plan.status != STRUCTURED_INFINITE:
            continue
        hits = []
        for n, ws in plan.iter_hits(10 ** 80):
            hits.append((n, ws))
            if len(hits) >= n_terms:
                break
        cc = None
        try:
            cc = count_cert(con)
        except Exception:  # noqa: BLE001 - a missing certificate only drops the constant
            cc = None
        const = None if cc is None else str(cc['sum_g_over_P'])
        coords = [{'key': 'hits', 'coordinate': 'hit indices n', 'terms': [n for n, _ in hits],
                   'count_constant': None if const is None else f'{const} / log(eps)'},
                  {'key': 'witness', 'coordinate': 'least witness', 'terms': [min(ws) for _, ws in hits]}]
        out.append({'problem': name, 'constraint': con.describe(), 'method': plan.method,
                    'least': hits[0][0] if hits else None,
                    'lean': [f'PerfectPower.Generated.Plans.{name}'], 'coordinates': coords})
    return out


def problems(n_terms: int = 30) -> list[dict]:
    return [square_triangular_cluster(n_terms)] + _plan_problems()


# ---------------------------------------------------------------------------
# a local OEIS snapshot
# ---------------------------------------------------------------------------

def _open(path: Path):
    path = Path(path)
    return gzip.open(path, 'rt', encoding='utf-8', errors='replace') if path.suffix == '.gz' \
        else open(path, encoding='utf-8', errors='replace')


def load_stripped(path) -> dict[str, list[int]]:
    """`A000045 ,0,1,1,2,3,...` lines to {A-number: terms}."""
    out = {}
    with _open(path) as f:
        for line in f:
            if not line.startswith('A'):
                continue
            aid, _, rest = line.partition(' ')
            terms = [t for t in rest.strip().strip(',').split(',') if t]
            try:
                out[aid] = [int(t) for t in terms]
            except ValueError:
                continue
    return out


def load_names(path) -> dict[str, str]:
    out = {}
    with _open(path) as f:
        for line in f:
            if line.startswith('A'):
                aid, _, name = line.partition(' ')
                out[aid] = name.strip()
    return out


def build_index(stripped: dict[str, list[int]], width: int = 4, starts: int = 6) -> dict:
    """Windows of `width` consecutive terms at the first `starts` positions of each entry."""
    idx: dict[tuple, list] = {}
    for aid, terms in stripped.items():
        for p in range(min(starts, max(0, len(terms) - width + 1))):
            idx.setdefault(tuple(terms[p:p + width]), []).append((aid, p))
    return idx


TRANSFORMS = {
    'identity': lambda x: x,
    '2x': lambda x: 2 * x,
    'x/2': lambda x: x // 2 if x % 2 == 0 else None,
    'x^2': lambda x: x * x,
    'sqrt(x)': lambda x: isqrt(x) if x >= 0 and isqrt(x) ** 2 == x else None,
    '2x+1': lambda x: 2 * x + 1,
    '(x-1)/2': lambda x: (x - 1) // 2 if x % 2 else None,
    'x(x+1)/2': lambda x: x * (x + 1) // 2,
}


def compare(ours: list[int], theirs: list[int], pos: int) -> dict:
    """Align `ours[0]` with `theirs[pos]` and compare the overlap."""
    n = min(len(ours), len(theirs) - pos)
    for i in range(n):
        if ours[i] != theirs[pos + i]:
            return {'agree': i, 'compared': n, 'first_counterexample':
                    {'our_index': i, 'ours': ours[i], 'theirs': theirs[pos + i]}}
    return {'agree': n, 'compared': n, 'first_counterexample': None}


def classify(ours: list[int], aid: str, theirs: list[int], pos: int, transform: str,
             lean: list[str] | None, reviewed: dict) -> dict | None:
    c = compare(ours, theirs, pos)
    rec = {'oeis': aid, 'alignment': {'our_first_term_at_their_position': pos},
           'transformation': transform, 'agreeing_terms': c['agree'], 'compared_terms': c['compared']}
    if c['first_counterexample'] is None:
        if c['agree'] < MIN_AGREE:
            return None
        if transform != 'identity':
            rec['outcome'] = 'RELATED_BY_TRANSFORMATION'
        elif lean and aid in reviewed:
            rec['outcome'] = 'DEFINITION_PROVED_EQUIVALENT'
            rec['lean'] = lean
            rec['review'] = reviewed[aid]
        else:
            rec['outcome'] = 'TERMS_AGREE_UNPROVED'
            if lean:
                rec['lean_candidate'] = lean
        return rec
    if c['agree'] >= MIN_REJECT_PREFIX:
        rec['outcome'] = 'REJECTED'
        rec['first_counterexample'] = c['first_counterexample']
        return rec
    return None


def atlas(stripped: dict[str, list[int]], reviewed: dict | None = None, probs: list | None = None,
          retrieved: str | None = None, max_per_coordinate: int = 20) -> list[dict]:
    """Every candidate correspondence between PerfectPower coordinates and the snapshot."""
    reviewed = reviewed or {}
    probs = probs if probs is not None else problems()
    idx = build_index(stripped)
    out = []
    for prob in probs:
        for co in prob['coordinates']:
            terms = [t for t in co['terms'] if t is not None]
            found = []
            for tname, f in TRANSFORMS.items():
                tt = [f(x) for x in terms]
                if any(x is None for x in tt[:8]):
                    continue
                tt = [x for x in tt if x is not None]
                if len(tt) < 4 or len(set(tt[:4])) < 3:
                    continue
                for aid, p in idx.get(tuple(tt[:4]), []):
                    rec = classify(tt, aid, stripped[aid], p, tname, co.get('lean') or prob.get('lean'),
                                   reviewed)
                    if rec is not None:
                        found.append(rec)
            # identity first, then longer agreements
            found.sort(key=lambda r: (OUTCOMES.index(r['outcome']), -r['agreeing_terms'], r['oeis']))
            seen = set()
            for rec in found:
                if rec['oeis'] in seen:
                    continue
                seen.add(rec['oeis'])
                out.append({'problem': prob['problem'], 'coordinate': co['key'],
                            'retrieved': retrieved, **rec})
                if len(seen) >= max_per_coordinate:
                    break
    return out


# ---------------------------------------------------------------------------
# reading leads for unresolved Mordell curves
# ---------------------------------------------------------------------------

_COMPLETE_WORDS = ('all ', 'complete', 'only', 'integral points', 'integer solutions', 'finite')


def unresolved_mordell(kmin: int = -100, kmax: int = 100, scan: int = 10 ** 4) -> list[dict]:
    """k with y^2 = x^3 + k NOT_ENUMERATED by the compiler, and the points a scan finds."""
    from .compiler import NOT_ENUMERATED, PowerConstraint, compile_constraint
    out = []
    for k in range(kmin, kmax + 1):
        if k == 0:
            continue
        plan = compile_constraint(PowerConstraint((k, 0, 0, 1), 2))
        if plan.status != NOT_ENUMERATED:
            continue
        pts = sorted({x for x in range(-int(abs(k) ** (1 / 3)) - 1, scan)
                      if x ** 3 + k >= 0 and isqrt(x ** 3 + k) ** 2 == x ** 3 + k})
        out.append({'k': k, 'x_found_by_scan': pts,
                    'missing_premise': (plan.data.get('missing_premise') or {}).get('premise')})
    return out


def premise_candidates(names: dict[str, str], curves: list[dict] | None = None) -> list[dict]:
    """Entries whose names mention x^3 + k (or y^2 = x^3 + k), ranked by completeness words."""
    curves = curves if curves is not None else unresolved_mordell()
    out = []
    for cv in curves:
        k = cv['k']
        sign = '+' if k > 0 else '-'
        pat = re.compile(r'(?:[xn]\^3|[xn]³)\s*' + re.escape(sign) + r'\s*' + str(abs(k)) + r'(?!\d)')
        for aid, name in names.items():
            if pat.search(name):
                low = name.lower()
                score = sum(w in low for w in _COMPLETE_WORDS)
                out.append({'k': k, 'oeis': aid, 'completeness_score': score,
                            'x_found_by_scan': cv['x_found_by_scan']})
    out.sort(key=lambda r: (-r['completeness_score'], r['k'], r['oeis']))
    return out
