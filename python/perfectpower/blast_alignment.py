"""Finite alignment populations over N[M,U,G,L], exact scores and rank/select.

Global paths consume both sequences, affine gaps cost open + length*extend,
no immediately opposing gaps. Literal character equality; ambiguous letters
are not expanded. The polynomial engine is budgeted, never silently pruned.
"""
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from hashlib import sha256
from .divisor_square import WorkLimit
from .psg_polynomial import rational

FEATURES = ('matches', 'mismatches', 'gap_openings', 'gap_residues')
ZERO = (0, 0, 0, 0)


def sequence(value, *, limit=100000):
    if type(value) is not str or len(value) > limit or any(not ('A' <= c <= 'Z') for c in value.upper()):
        raise ValueError('bounded ungapped ASCII sequence required')
    return value.upper()


def add(a, b):
    return tuple(x+y for x, y in zip(a, b))


def subtract(a, b):
    return tuple(x-y for x, y in zip(a, b))


def weights(match=2, mismatch=3, gap_open=5, gap_extend=1):
    r, p, o, e = map(rational, (match, mismatch, gap_open, gap_extend))
    if r <= 0 or min(p, o, e) < 0:
        raise ValueError('positive reward and nonnegative penalties required')
    return (r, -p, -o, -e)


def score(feature, scoring):
    if len(feature) != 4 or len(scoring) != 4:
        raise ValueError('four feature counts and four signed scoring weights required')
    return sum((a*rational(b) for a, b in zip(feature, scoring)), Q(0))


class AlignmentFamily:
    """Complete finite global population; counts are operation-path counts."""
    def __init__(self, query, subject, *, term_limit=250000, work_limit=2000000):
        self.query, self.subject = sequence(query, limit=96), sequence(subject, limit=96)
        if len(self.query)+len(self.subject) > 128:
            raise WorkLimit('alignment population combined length exceeds 128')
        if any(type(x) is not int or x < 1 for x in (term_limit, work_limit)):
            raise ValueError('positive term and work budgets required')
        self.term_limit, self.work_limit = term_limit, work_limit
        self.work = self.retained_terms = 0
        self._suffix = lru_cache(None)(self._build_suffix)
        self.terms = dict(self._suffix(0, 0, 'M'))

    def transitions(self, i, j, previous):
        out = []
        if i < len(self.query) and j < len(self.subject):
            equal = self.query[i] == self.subject[j]
            out.append(('M', i+1, j+1, (int(equal), int(not equal), 0, 0)))
        if i < len(self.query) and previous != 'I':
            out.append(('D', i+1, j, (0, 0, int(previous != 'D'), 1)))
        if j < len(self.subject) and previous != 'D':
            out.append(('I', i, j+1, (0, 0, int(previous != 'I'), 1)))
        return out

    def _build_suffix(self, i, j, previous):
        if i == len(self.query) and j == len(self.subject):
            return ((ZERO, 1),)
        out = Counter()
        for operation, u, v, increment in self.transitions(i, j, previous):
            for feature, count in self._suffix(u, v, operation):
                self.work += 1
                if self.work > self.work_limit:
                    raise WorkLimit('alignment polynomial transition budget exhausted')
                out[add(feature, increment)] += count
        self.retained_terms += len(out)
        if self.retained_terms > self.term_limit:
            raise WorkLimit('alignment polynomial retained-term budget exhausted')
        return tuple(sorted(out.items()))

    @property
    def count(self):
        return sum(self.terms.values())

    def select(self, feature, index=0):
        feature = tuple(feature)
        if type(index) is not int or not 0 <= index < self.terms.get(feature, 0):
            raise ValueError('rank outside requested feature fibre')
        i = j = 0
        previous, operations, remaining = 'M', [], feature
        while i < len(self.query) or j < len(self.subject):
            for operation, u, v, increment in self.transitions(i, j, previous):
                child = subtract(remaining, increment)
                count = dict(self._suffix(u, v, operation)).get(child, 0)
                if index >= count:
                    index -= count
                else:
                    operations.append(operation)
                    i, j, previous, remaining = u, v, operation, child
                    break
            else:
                raise AssertionError('alignment unranking failed')
        return self.render(''.join(operations))

    def rank(self, operations):
        rendered = self.render(operations)
        remaining = tuple(rendered['features'])
        i = j = rank = 0
        previous = 'M'
        for selected in operations:
            for operation, u, v, increment in self.transitions(i, j, previous):
                child = subtract(remaining, increment)
                if operation == selected:
                    i, j, previous, remaining = u, v, operation, child
                    break
                rank += dict(self._suffix(u, v, operation)).get(child, 0)
            else:
                raise ValueError('illegal alignment operation')
        return rank

    def render(self, operations):
        i = j = 0
        previous, feature, a, b = 'M', ZERO, [], []
        for selected in operations:
            possible = {t[0]: t for t in self.transitions(i, j, previous)}
            if selected not in possible:
                raise ValueError('illegal alignment path')
            _, u, v, increment = possible[selected]
            a.append(self.query[i] if u > i else '-')
            b.append(self.subject[j] if v > j else '-')
            i, j, previous, feature = u, v, selected, add(feature, increment)
        if (i, j) != (len(self.query), len(self.subject)):
            raise ValueError('path does not consume both complete sequences')
        return {'operations': operations, 'query': ''.join(a), 'subject': ''.join(b), 'features': list(feature)}

    def optimal(self, scoring):
        values = {f: score(f, scoring) for f in self.terms}
        best = max(values.values())
        winners = sorted(f for f, v in values.items() if v == best)
        return {'score': str(best), 'features': [list(f) for f in winners],
                'alignment_count': sum(self.terms[f] for f in winners),
                'representative': self.select(winners[0]), 'complete': True, 'scope': 'declared global alignment paths'}

    def polynomial(self):
        from .psg_polynomial import Polynomial
        return Polynomial(FEATURES, self.terms)

    def packet(self):
        return {'schema': 'pp-blast-alignment-family/1', 'query': self.query, 'subject': self.subject,
                'query_sha256': sha256(self.query.encode()).hexdigest(),
                'subject_sha256': sha256(self.subject.encode()).hexdigest(),
                'features': list(FEATURES), 'terms': [[list(f), c] for f, c in sorted(self.terms.items())],
                'alignment_count': self.count, 'work': self.work, 'retained_terms': self.retained_terms,
                'model': 'global; literal equality; no opposing adjacent gaps; open + length*extend',
                'complete': True, 'kernel_checked': False}


def exact_alignment(query, subject, scoring=None, *, local=True, substitution=None, cell_limit=1000000):
    """Exact affine scalar DP, one traceback; optional explicit pair score table.

    Local scores use positive gap penalties. All cells are searched; only a
    representative optimum is returned, not all local alignment multiplicities.
    """
    q, s = sequence(query), sequence(subject)
    w = tuple(map(rational, weights() if scoring is None else scoring))
    if len(w) != 4 or w[0] <= 0 or any(x > 0 for x in w[1:]):
        raise ValueError('positive reward and nonpositive signed penalties required')
    if local and (w[2] >= 0 or w[3] >= 0):
        raise ValueError('local alignment requires strictly positive gap penalties')
    if type(cell_limit) is not int or cell_limit < 1:
        raise ValueError('positive cell budget required')
    if (len(q)+1)*(len(s)+1)*3 > cell_limit:
        raise WorkLimit('scalar alignment cell budget exhausted')
    pair = None if substitution is None else {k: rational(v) for k, v in substitution.items()}
    if pair is not None and any(a+b not in pair for a in set(q) for b in set(s)):
        raise ValueError('substitution matrix must cover every encountered residue pair')
    values, pointers = {(0, 0, 'M'): Q(0)}, {}
    best, endpoint = Q(0), (0, 0, 'M')
    for i in range(len(q)+1):
        for j in range(len(s)+1):
            for state in ('M', 'D', 'I'):
                key = (i, j, state)
                candidates = []
                if state == 'M' and i and j:
                    reward = pair[q[i-1]+s[j-1]] if pair is not None else w[int(q[i-1] != s[j-1])]
                    candidates = [(values[k]+reward, k) for p in ('M', 'D', 'I')
                                  for k in [(i-1, j-1, p)] if k in values]
                elif state == 'D' and i:
                    candidates = [(values[k]+w[3]+(w[2] if p != 'D' else 0), k)
                                  for p in ('M', 'D') for k in [(i-1, j, p)] if k in values]
                elif state == 'I' and j:
                    candidates = [(values[k]+w[3]+(w[2] if p != 'I' else 0), k)
                                  for p in ('M', 'I') for k in [(i, j-1, p)] if k in values]
                if local and state == 'M':
                    candidates.insert(0, (Q(0), None))
                if candidates:
                    value, parent = max(candidates, key=lambda t: t[0])
                    values[key], pointers[key] = value, parent
                    if local and value > best:
                        best, endpoint = value, key
    if not local:
        endpoints = [(values[k], k) for state in ('M', 'D', 'I')
                     for k in [(len(q), len(s), state)] if k in values]
        best, endpoint = max(endpoints, key=lambda t: t[0])
    i, j, state = endpoint
    end = (i, j)
    a, b, operations = [], [], []
    while pointers.get((i, j, state)) is not None:
        parent = pointers[i, j, state]
        a.append(q[i-1] if state != 'I' else '-')
        b.append(s[j-1] if state != 'D' else '-')
        operations.append(state)
        i, j, state = parent
    return {'schema': 'pp-blast-exact-alignment/1', 'score': str(best),
            'query': ''.join(reversed(a)), 'subject': ''.join(reversed(b)),
            'operations': ''.join(reversed(operations)), 'query_interval': [i, end[0]],
            'subject_interval': [j, end[1]], 'coordinate_convention': 'zero-based half-open',
            'scoring': list(map(str, w)), 'substitution': None if pair is None else {k: str(v) for k, v in sorted(pair.items())},
            'query_sha256': sha256(q.encode()).hexdigest(), 'subject_sha256': sha256(s.encode()).hexdigest(),
            'character_policy': 'literal equality; ambiguity symbols are not expanded',
            'mode': 'local' if local else 'global',
            'complete_score_search': True, 'all_optima_enumerated': False,
            'scope': 'supplied sequence pair, explicit affine model', 'kernel_checked': False}
