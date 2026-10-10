"""Exact sequence correlations, feature queries and similarity filtrations."""
from fractions import Fraction as Q
from decimal import Decimal
from collections import defaultdict
from .blast_alignment import sequence, score
from .psg_polynomial import rational
from .blast_io import COMPLEMENT
from .divisor_square import WorkLimit


def identity_correlation(query, subject, *, reverse_complement=False, work_limit=2000000):
    """Indicator-polynomial convolution gives literal identities at every offset.

    offset means subject[0] lies at query[offset]. This is an ungapped identity
    profile, not a significance estimate or a BLAST heuristic replacement.
    """
    from . import polyalg as P
    q, s = sequence(query), sequence(subject)
    if not q or not s:
        raise ValueError('nonempty sequences required')
    if reverse_complement:
        if any(c not in 'ACGTRYSWKMBDHVNU' for c in s):
            raise ValueError('nucleotide alphabet required for reverse complement')
        s = s.translate(COMPLEMENT)[::-1]
    alphabet = sorted(set(q) | set(s))
    if len(q)*len(s)*len(alphabet) > work_limit:
        raise WorkLimit('correlation convolution budget exceeded')
    coefficients = [Q(0)]*(len(q)+len(s)-1)
    for letter in alphabet:
        a = P.poly([int(c == letter) for c in q])
        b = P.poly([int(c == letter) for c in reversed(s)])
        for i, value in enumerate(P.mul(a, b)):
            coefficients[i] += value
    rows = []
    for i, matches in enumerate(coefficients):
        offset = i-(len(s)-1)
        overlap = max(0, min(len(q), offset+len(s))-max(0, offset))
        rows.append({'offset': offset, 'matches': int(matches), 'overlap': overlap,
                     'identity': str(Q(matches, overlap)) if overlap else '0'})
    return {'schema': 'pp-blast-polynomial-correlation/1', 'rows': rows,
            'reverse_complement': reverse_complement, 'complete': True,
            'scope': 'literal ungapped identity for every relative offset via exact indicator-polynomial products'}


def query_family(family, *, inequalities=(), residues=(), min_matches=0, max_gap_openings=None, limit=10000):
    """Push forward exact populations to constrained feature fibres."""
    inequalities = [(tuple(map(rational, a)), rational(b)) for a, b in inequalities]
    if any(len(a) != 4 for a, b in inequalities):
        raise ValueError('four coefficients per inequality required')
    if type(min_matches) is not int or min_matches < 0 or (max_gap_openings is not None and (type(max_gap_openings) is not int or max_gap_openings < 0)):
        raise ValueError('nonnegative integer feature bounds required')
    for coordinate, modulus, allowed in residues:
        if type(coordinate) is not int or not 0 <= coordinate < 4 or type(modulus) is not int or modulus < 1 or any(type(a) is not int or not 0 <= a < modulus for a in allowed):
            raise ValueError('valid coordinate/modulus/allowed residues required')
    selected = []
    for f, count in sorted(family.terms.items()):
        if f[0] < min_matches or (max_gap_openings is not None and f[2] > max_gap_openings):
            continue
        if any(score(a, f) > b for a, b in inequalities) or any(f[i] % modulus not in allowed for i, modulus, allowed in residues):
            continue
        if len(selected) >= limit:
            raise WorkLimit('selected feature fibre budget exceeded')
        selected.append({'feature': list(f), 'count': count, 'representative': family.select(f)})
    return {'fibres': selected, 'feature_count': len(selected), 'alignment_count': sum(row['count'] for row in selected),
            'complete': True, 'scope': 'complete feature filtering of supplied finite global alignment family'}


def similarity_edges(hits, *, maximum_evalue='0.001', minimum_identity='1/2', minimum_coverage='1/2'):
    """Conservative reciprocal per-HSP edges; max identity supplies edge weight.

    Requires a qualifying HSP in each search direction. Does not merge disjoint
    HSP coverage, infer orthology, or resolve conflicting strand evidence.
    """
    threshold, identity, coverage = Decimal(maximum_evalue), rational(minimum_identity), rational(minimum_coverage)
    if not threshold.is_finite() or threshold < 0 or not 0 <= identity <= 1 or not 0 <= coverage <= 1:
        raise ValueError('valid E-value, identity and coverage thresholds required')
    vertices = sorted({h.fields[k] for h in hits for k in ('qseqid', 'sseqid')})
    if len(vertices) > 32:
        raise WorkLimit('similarity network exceeds 32 vertices')
    grouped = defaultdict(list)
    for hit in hits:
        f = hit.fields
        if f['qseqid'] == f['sseqid'] or 'qlen' not in f or 'slen' not in f:
            continue
        exact_identity = Q(hit.features[0], f['length'])
        qcoverage = Q(abs(f['qend']-f['qstart'])+1, f['qlen'])
        scoverage = Q(abs(f['send']-f['sstart'])+1, f['slen'])
        if Decimal(f['evalue']) <= threshold and exact_identity >= identity and min(qcoverage, scoverage) >= coverage:
            grouped[f['qseqid'], f['sseqid']].append((exact_identity, hit.strand))
    edges, unresolved = [], []
    for i, a in enumerate(vertices):
        for j in range(i+1, len(vertices)):
            b = vertices[j]
            forward, backward = grouped[a, b], grouped[b, a]
            if not forward or not backward:
                continue
            signs = {sign for _, sign in forward+backward}
            if len(signs) != 1:
                unresolved.append([a, b]); continue
            weight = min(max(w for w, _ in forward), max(w for w, _ in backward))
            if weight:
                edges.append((i, j, weight, signs.pop()))
    return {'vertices': vertices, 'edges': edges, 'unresolved_strands': unresolved,
            'scope': 'reciprocal qualifying individual HSPs in supplied hit set; not complete homology or orthology'}


def graph_filtration(vertices, edges):
    """Exact threshold topology; equal-weight edges enter together."""
    if type(vertices) is not int or not 1 <= vertices <= 64 or len(edges) > 256:
        raise WorkLimit('filtration requires <=64 vertices and <=256 edges')
    clean, seen = [], set()
    for a, b, weight, orientation in edges:
        if type(a) is not int or type(b) is not int or not 0 <= a < b < vertices or (a, b) in seen:
            raise ValueError('distinct valid unordered edges required')
        weight = rational(weight)
        if weight <= 0:
            raise ValueError('positive similarity weight required')
        seen.add((a, b)); clean.append((a, b, weight))
    rows = []
    for threshold in sorted({w for a, b, w in clean}, reverse=True):
        parent = list(range(vertices))
        def root(a):
            while parent[a] != a:
                a = parent[a]
            return a
        selected = [(a, b) for a, b, w in clean if w >= threshold]
        for a, b in selected:
            parent[root(a)] = root(b)
        groups = defaultdict(list)
        for i in range(vertices):
            groups[root(i)].append(i)
        rows.append({'threshold': str(threshold), 'components': sorted(groups.values()),
                     'component_count': len(groups), 'edge_count': len(selected),
                     'graph_cycle_rank': len(selected)-vertices+len(groups)})
    return {'levels': rows, 'complete': True, 'scope': 'graph filtration of supplied weighted edges; graph cycles are not clique-complex holes'}
