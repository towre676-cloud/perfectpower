"""Exact calendar constraints and declared Dresden numerical models.

No image reading, ephemeris, historical uniqueness or Lean refinement is implied.
All dates are integer days relative to an explicitly chosen epoch.
"""
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from math import gcd
from .semilinear_domains import count_domain


def _integer(n):
    if type(n) is not int:
        raise ValueError('integer required')
    return n


def long_count_days(digits):
    """Canonical most-significant-first Long Count; any number of places."""
    if not isinstance(digits, (list, tuple)) or not digits:
        raise ValueError('nonempty digit sequence required')
    total, weight = 0, 1
    for i, digit in enumerate(reversed(digits)):
        _integer(digit)
        radix = 18 if i == 1 else 20
        if digit < 0 or (i < len(digits)-1 and digit >= radix):
            raise ValueError('noncanonical Long Count digit')
        total += digit * weight
        weight *= radix
    return total


def days_long_count(days, places=5):
    _integer(days); _integer(places)
    if days < 0 or not 1 <= places <= 64:
        raise ValueError('nonnegative days and 1..64 places required')
    out = []
    for i in range(places-1):
        radix = 18 if i == 1 else 20
        days, digit = divmod(days, radix)
        out.append(digit)
    return [days] + out[::-1]


@dataclass(frozen=True)
class Progression:
    """All integer days congruent to residue modulo a positive modulus."""
    residue: int
    modulus: int

    def __post_init__(self):
        _integer(self.residue); _integer(self.modulus)
        if self.modulus <= 0:
            raise ValueError('positive modulus required')
        object.__setattr__(self, 'residue', self.residue % self.modulus)

    def contains(self, day):
        return (_integer(day)-self.residue) % self.modulus == 0

    def domain(self):
        return {'cells': [{'interval': [None, None], 'modulus': self.modulus,
                           'residues': [self.residue]}]}

    def count(self, lo, hi):
        return count_domain(self.domain(), _integer(lo), _integer(hi))

    def select(self, rank, lo, hi):
        _integer(rank)
        if rank < 0 or rank >= self.count(lo, hi):
            raise IndexError('rank outside bounded population')
        return lo + (self.residue-lo) % self.modulus + rank*self.modulus

    def intersect(self, other):
        g = gcd(self.modulus, other.modulus)
        delta = other.residue-self.residue
        if delta % g:
            return None
        reduced = other.modulus//g
        k = (delta//g * pow(self.modulus//g, -1, reduced)) % reduced if reduced > 1 else 0
        return Progression(self.residue+self.modulus*k, self.modulus*reduced)


def calendar_round(number, sign, haab_day, *, origin=(4, 19, 348)):
    """number 1..13; sign 0..19 (Imix..Ajaw); haab_day 0..364.

    Default epoch convention: 4 Ajaw 8 Kumk'u. No Gregorian correlation.
    """
    for v in (number, sign, haab_day, *origin):
        _integer(v)
    if not (1 <= number <= 13 and 0 <= sign < 20 and 0 <= haab_day < 365):
        raise ValueError('invalid calendar phase')
    if len(origin) != 3 or not (1 <= origin[0] <= 13 and 0 <= origin[1] < 20 and 0 <= origin[2] < 365):
        raise ValueError('invalid epoch phase')
    p = Progression(number-origin[0], 13).intersect(Progression(sign-origin[1], 20))
    return p.intersect(Progression(haab_day-origin[2], 365))


def calendar_phase(day, *, origin=(4, 19, 348)):
    calendar_round(*origin, origin=origin)  # validate convention
    _integer(day)
    return ((origin[0]-1+day) % 13+1, (origin[1]+day) % 20, (origin[2]+day) % 365)


def solve_alternatives(readings, lo, hi, *, combination_limit=100000):
    """Each independent inscription has alternative congruence readings.

    Return every compatible reading assignment, retaining provenance even when
    several assignments describe the same day population. Never count their
    overlapping populations as a distinct-day union.
    """
    _integer(lo); _integer(hi); _integer(combination_limit)
    if lo > hi or combination_limit < 1:
        raise ValueError('ordered bounds and positive budget required')
    size = 1
    for group in readings:
        if not group:
            raise ValueError('empty reading group')
        size *= len(group)
    if size > combination_limit:
        raise ValueError('reading assignment budget exceeded; no partial result')
    for group in readings:
        for reading in group:
            if set(reading) != {'id', 'residue', 'modulus', 'source', 'location'} or not all(
                    isinstance(reading[k], str) and reading[k] for k in ('id', 'source', 'location')):
                raise ValueError('source-linked reading required')
            Progression(reading['residue'], reading['modulus'])
        if len({r['id'] for r in group}) != len(group):
            raise ValueError('duplicate alternative id')
    survivors = []
    for assignment in product(*readings):
        p = Progression(0, 1)
        for r in assignment:
            p = p.intersect(Progression(r['residue'], r['modulus']))
            if p is None:
                break
        if p is not None and p.count(lo, hi):
            survivors.append({'readings': list(assignment), 'residue': p.residue,
                              'modulus': p.modulus, 'count': p.count(lo, hi),
                              'first': p.select(0, lo, hi), 'last': p.select(p.count(lo, hi)-1, lo, hi)})
    return {'schema': 'pp-dresden-readings/1', 'bounds': [lo, hi],
            'assignments_examined': size, 'complete_within_declared_readings': True,
            'survivors': survivors}


@dataclass(frozen=True)
class VenusRule:
    name: str
    rounds: int
    days: int
    source: str
    status: str  # literature interpretation or synthetic experiment

    def __post_init__(self):
        _integer(self.rounds); _integer(self.days)
        if self.rounds < 1 or self.days < 1 or not self.name or not self.source or self.status not in (
                'literature_interpretation', 'synthetic'):
            raise ValueError('positive, named, source-linked correction rule required')

    @property
    def mean_period(self):
        return Fraction(self.days, self.rounds)

    def execute(self, rounds, *, anchor=0, reference='583.9214'):
        """Restart at each complete block; 584-day steps inside a block.

        This declared recurrence is an arithmetic experiment, not a claim that
        the source prescribes indefinitely repeating the rule.
        """
        _integer(rounds); _integer(anchor)
        if rounds < 0:
            raise ValueError('nonnegative round required')
        ref = Fraction(reference)
        if ref <= 0:
            raise ValueError('positive rational mean reference required')
        blocks, remainder = divmod(rounds, self.rounds)
        day = anchor+blocks*self.days+584*remainder
        return {'day': day, 'blocks': blocks, 'remainder': remainder,
                'error_against_mean': str(Fraction(day-anchor)-rounds*ref),
                'reference_kind': 'constant mean; not an ephemeris'}

    def error_envelope(self, rounds, *, reference='583.9214'):
        """Exact min/max error over every integer round 0..rounds, O(1)."""
        _integer(rounds)
        if rounds < 0:
            raise ValueError('nonnegative horizon required')
        b, r = divmod(rounds, self.rounds)
        candidates = {0, rounds, b*self.rounds}
        if b:
            candidates.update({self.rounds-1, (b-1)*self.rounds, b*self.rounds-1})
        errors = [(Fraction(self.execute(n, reference=reference)['error_against_mean']), n)
                  for n in sorted(candidates)]
        return {'minimum': str(min(e for e,n in errors)), 'maximum': str(max(e for e,n in errors)),
                'candidate_rounds': sorted(candidates), 'horizon': rounds}


def venus_rules():
    src = 'https://escholarship.org/uc/item/6cr1s6jd'
    return [VenusRule('canonical_584', 1, 584, 'declared canonical arithmetic model', 'synthetic'),
            VenusRule('aldana_CVI1', 122, 71240, src+'#printed-page-66', 'literature_interpretation'),
            VenusRule('aldana_CVI2', 183, 106860, src+'#printed-page-66', 'literature_interpretation')]


def reconstruct_intervals(options, target, *, state_limit=100000):
    """Complete bounded interval-sum reconstruction by dynamic programming.

    Count assignments, retain viable values at every position, and a witness.
    Synthetic or transcribed status is supplied by the caller's source record.
    """
    _integer(target); _integer(state_limit)
    if state_limit < 1:
        raise ValueError('positive state budget required')
    choices = []
    for values in options:
        vals = sorted(set(_integer(x) for x in values))
        if not vals or vals[0] < 0:
            raise ValueError('nonempty nonnegative interval choices required')
        choices.append(vals)
    prefixes = [{0: 1}]; work = 0
    for vals in choices:
        nxt = {}
        for total, count in prefixes[-1].items():
            for v in vals:
                work += 1
                if work > state_limit:
                    raise ValueError('reconstruction budget exceeded; no partial result')
                if total+v <= target:
                    nxt[total+v] = nxt.get(total+v, 0)+count
        prefixes.append(nxt)
    viable = [set() for _ in choices]; remaining = {target}; witness = []
    for i in range(len(choices)-1, -1, -1):
        prev = set()
        for total in remaining:
            for v in choices[i]:
                work += 1
                if work > state_limit:
                    raise ValueError('reconstruction budget exceeded; no partial result')
                if total-v in prefixes[i]:
                    viable[i].add(v); prev.add(total-v)
        remaining = prev
    count = prefixes[-1].get(target, 0)
    if count:
        rem = target
        for i in range(len(choices)-1, -1, -1):
            v = next(v for v in choices[i] if rem-v in prefixes[i])
            witness.append(v); rem -= v
        witness.reverse()
    return {'count': count, 'unique': count == 1, 'viable_values': [sorted(v) for v in viable],
            'witness': witness if count else None, 'complete_within_declared_options': True}



def polynomial_calendar(p, predicate, lo, hi, *, node_limit=100000):
    """Intersect a calendar progression with original-day polynomial predicates.

    Substitute day=a+m*k before root isolation. This avoids constructing a
    residue truth table of length m, even when m is enormous.
    """
    from . import polyalg as P
    from .polynomial_domains import integer_domain
    _integer(lo); _integer(hi)
    if lo > hi:
        raise ValueError('ordered finite day bounds required')
    nodes = 0
    def transport(node, depth=0):
        nonlocal nodes
        nodes += 1
        if depth > 64 or nodes > 2048:
            raise ValueError('predicate transport budget exceeded')
        if type(node) is bool:
            return node
        if not isinstance(node, dict):
            raise ValueError('structured polynomial predicate required')
        if set(node) == {'poly', 'relation'}:
            if not isinstance(node['poly'],(list,tuple)) or not node['poly'] or len(node['poly']) > 65:
                raise ValueError('1..65 polynomial coefficients required')
            for c in node['poly']: _integer(c)
            return {'poly': [int(c) for c in P.compose_linear(P.poly(node['poly']),p.residue,p.modulus)],
                    'relation': node['relation']}
        if set(node) != {'op','args'} or not isinstance(node['args'], (list,tuple)):
            raise ValueError('Boolean sign predicate required')
        return {'op':node['op'], 'args':[transport(c,depth+1) for c in node['args']]}
    transformed = transport(predicate)
    domain = integer_domain(transformed,node_limit=node_limit)
    lower = -((p.residue-lo)//p.modulus)
    upper = (hi-p.residue)//p.modulus
    intervals=[]
    for a,b in domain['intervals']:
        a=lower if a is None else max(a,lower)
        b=upper if b is None else min(b,upper)
        if a<=b: intervals.append([a,b])
    return {'schema':'pp-dresden-polynomial-calendar/1',
            'source_predicate':predicate, 'bounds':[lo,hi],
            'chart':{'residue':p.residue,'modulus':p.modulus},
            'parameter_domain':domain, 'bounded_parameter_intervals':intervals,
            'count':sum(b-a+1 for a,b in intervals),
            'complete_within_declared_model':True}


def polynomial_calendar_select(packet, rank):
    _integer(rank)
    if rank < 0 or rank >= packet['count']:
        raise IndexError('rank outside polynomial calendar population')
    for a,b in packet['bounded_parameter_intervals']:
        size=b-a+1
        if rank<size:
            return packet['chart']['residue']+packet['chart']['modulus']*(a+rank)
        rank-=size
    raise AssertionError('invalid population packet')

def execute_request(request):
    """JSON-ready entry point, independently usable from the repo CLI."""
    operation = request['operation']
    if operation in ('source_tables','lunar_census','lunar_window','lunar_compare','restart_policy','overlap'):
        import json
        from pathlib import Path
        from . import dresden_eclipse as E
        root=Path(__file__).resolve().parents[2]/'research/dresden'
        if operation=='restart_policy':
            return E.optimal_restart_order(request.get('long_count',4),request.get('short_count',1))
        if operation=='overlap':
            return E.overlap_schedule(request['station_months'],request['restart_steps'])
        if operation=='source_tables':
            return {'eclipse':E.station_audit(json.loads((root/'eclipse_stations.json').read_text())),
                    'venus':E.venus_table_audit(json.loads((root/'venus_numbers.json').read_text()))}
        source=json.loads((root/'lunar_source.json').read_text())
        if operation in ('lunar_window','lunar_compare'):
            from . import dresden_analysis as A
            if operation=='lunar_window':
                rows=A.interval_distribution(source['days'],request['months'],request.get('start',0),request.get('end'))
                return {'source':source['source'],'convention':source['integer_day_convention'],
                        'distribution':rows,'summary':A.distribution_summary(rows)}
            a,b=request['months'];mean=Fraction(request.get('centering_mean','29.530589'))
            if mean<=0:raise ValueError('positive centering mean required')
            rows=[A.interval_distribution(source['days'],n) for n in (a,b)]
            offsets=[(n*mean).__floor__() for n in (a,b)]
            return {'source':source['source'],'months':[a,b],'centering_mean':str(mean),
                    'offsets':offsets,'total_variation':A.total_variation(*rows,*offsets)}
        census=E.lunar_interval_census(source['days'])
        return {'census':census,'published_comparison':E.compare_lunar_report(census,source['reported_rows'])}
    if operation == 'long_count':
        n = long_count_days(request['digits'])
        return {'days': n, 'canonical': days_long_count(n, request.get('places', 5))}
    if operation == 'calendar_round':
        p = calendar_round(request['number'], request['sign'], request['haab_day'],
                           origin=tuple(request.get('origin', (4,19,348))))
        if p is None:
            return {'compatible': False}
        lo,hi = request['bounds']
        count = p.count(lo,hi)
        return {'compatible': True, 'residue': p.residue, 'modulus': p.modulus,
                'count': count, 'first': p.select(0,lo,hi) if count else None,
                'last': p.select(count-1,lo,hi) if count else None}
    if operation == 'polynomial_calendar':
        return polynomial_calendar(Progression(request['residue'],request['modulus']),
                                   request['predicate'], *request['bounds'],
                                   node_limit=request.get('node_limit',100000))
    if operation == 'readings':
        return solve_alternatives(request['readings'], *request['bounds'],
                                  combination_limit=request.get('combination_limit',100000))
    if operation == 'reconstruct':
        return reconstruct_intervals(request['options'],request['target'],
                                     state_limit=request.get('state_limit',100000))
    if operation == 'venus':
        rules = {r.name:r for r in venus_rules()}
        r = rules[request['rule']]
        rounds = request['rounds']; ref=request.get('reference','583.9214')
        return {'rule': r.name, 'status': r.status, 'source': r.source,
                'mean_period': str(r.mean_period),
                'execution': r.execute(rounds, anchor=request.get('anchor',0), reference=ref),
                'envelope': r.error_envelope(rounds,reference=ref)}
    raise ValueError('unsupported Dresden operation')


def main():
    import argparse
    import json
    import sys
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('request',nargs='?',help='JSON request file; otherwise stdin')
    args=parser.parse_args()
    if args.request:
        with open(args.request,encoding='utf8') as f: request=json.load(f)
    else: request=json.load(sys.stdin)
    print(json.dumps(execute_request(request),indent=2,sort_keys=True))


if __name__=='__main__': main()
