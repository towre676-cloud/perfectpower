"""Complete bounded coherent HSP-chain populations and sensitivity explanations."""
from functools import lru_cache
from fractions import Fraction as Q
from .blast_alignment import score
from .divisor_square import WorkLimit


def chain_population(hits, scoring, *, max_query_gap=None, max_subject_gap=None, min_coverage=0, frame_modulus=None, work_limit=200000):
    """Enumerate every nonempty compatible chain in each query/subject/strand group.

    Both coordinates increase in their own oriented axes. No overlap allowed.
    Gap limits concern unaligned spacing, not BTOP alignment gap penalties.
    Coverage is union query length; optional frame spacing is a user constraint.
    """
    hits = list(hits)
    if len(hits) > 128:
        raise WorkLimit('chain population limited to 128 HSPs')
    if type(min_coverage) is not int or min_coverage < 0 or type(work_limit) is not int or work_limit < 1:
        raise ValueError('nonnegative coverage and positive work budget required')
    for value in (max_query_gap, max_subject_gap):
        if value is not None and (type(value) is not int or value < 0):
            raise ValueError('nonnegative optional spacing limits required')
    if frame_modulus is not None and (type(frame_modulus) is not int or frame_modulus < 1):
        raise ValueError('positive optional frame modulus required')
    order = sorted(range(len(hits)), key=lambda i: (*hits[i].interval('q', oriented=True), i))
    children = {i: [] for i in order}
    rejected = []
    for pos, i in enumerate(order):
        a = hits[i]
        for j in order[pos+1:]:
            b = hits[j]
            if any(a.fields[k] != b.fields[k] for k in ('qseqid', 'sseqid')) or a.strand != b.strand or (a.fields['qend'] >= a.fields['qstart']) != (b.fields['qend'] >= b.fields['qstart']):
                continue
            qgap = b.interval('q', oriented=True)[0]-a.interval('q', oriented=True)[1]
            sgap = b.interval('s', oriented=True)[0]-a.interval('s', oriented=True)[1]
            reason = ('query_overlap_or_order' if qgap < 0 else 'subject_overlap_or_order' if sgap < 0 else
                      'query_spacing' if max_query_gap is not None and qgap > max_query_gap else
                      'subject_spacing' if max_subject_gap is not None and sgap > max_subject_gap else
                      'frame_spacing' if frame_modulus is not None and (sgap-qgap) % frame_modulus else None)
            if reason:
                rejected.append({'from': i, 'to': j, 'reason': reason})
            else:
                children[i].append(j)
    work = 0
    rows = []
    def visit(path, coverage, features):
        nonlocal work
        work += 1
        if work > work_limit:
            raise WorkLimit('chain path budget exceeded; no complete population returned')
        if coverage >= min_coverage:
            rows.append({'hits': list(path), 'query_coverage_bases': coverage, 'features': list(features), 'score': str(score(features, scoring))})
        for j in children[path[-1]]:
            f = hits[j].features
            visit(path+(j,), coverage+abs(hits[j].fields['qend']-hits[j].fields['qstart'])+1,
                  tuple(a+b for a, b in zip(features, f)))
    for i in order:
        visit((i,), abs(hits[i].fields['qend']-hits[i].fields['qstart'])+1, hits[i].features)
    rows.sort(key=lambda r: (-Q(r['score']), -r['query_coverage_bases'], r['hits']))
    return {'schema': 'pp-blast-chain-population/1', 'chains': rows, 'count': len(rows),
            'compatible_edges': [[i, j] for i in order for j in children[i]], 'rejected_edges': rejected,
            'complete': True, 'scope': 'all nonempty nonoverlapping compatible chains of supplied HSPs',
            'biological_event_established': False}


def distinguishing_features(hypotheses, *, costs=None, work_limit=100000):
    """Exact minimum worst-case adaptive measurement tree over a finite menu.

    Hypotheses are fixed feature vectors, measurements reveal one coordinate
    without noise. This plans inspection of alignment summaries, not wet-lab assays.
    """
    if not hypotheses or len(hypotheses) > 16 or any(len(f) != 4 for f in hypotheses.values()):
        raise ValueError('one through sixteen named four-feature hypotheses required')
    costs = tuple(Q(str(x)) for x in (costs or (1, 1, 1, 1)))
    if len(costs) != 4 or any(x <= 0 for x in costs):
        raise ValueError('four positive costs required')
    names = tuple(sorted(hypotheses)); work = 0
    @lru_cache(None)
    def solve(indices):
        nonlocal work
        work += 1
        if work > work_limit:
            raise WorkLimit('inspection policy budget exceeded')
        if len(indices) <= 1:
            return Q(0), {'identified': names[indices[0]]}
        options = []
        for coordinate in range(4):
            groups = {}
            for i in indices:
                groups.setdefault(hypotheses[names[i]][coordinate], []).append(i)
            if len(groups) < 2:
                continue
            branches = [(value, solve(tuple(group))) for value, group in sorted(groups.items())]
            price = costs[coordinate]+max(result[0] for _, result in branches)
            options.append((price, coordinate, branches))
        if not options:
            return Q(0), {'indistinguishable': [names[i] for i in indices]}
        price, coordinate, branches = min(options, key=lambda x: (x[0], x[1]))
        return price, {'coordinate': coordinate, 'cost': str(costs[coordinate]),
                       'branches': [{'value': value, 'next': result[1]} for value, result in branches]}
    price, tree = solve(tuple(range(len(names))))
    return {'worst_case_cost': str(price), 'tree': tree, 'complete': True,
            'scope': 'noiseless feature inspections; identical feature vectors remain grouped'}
