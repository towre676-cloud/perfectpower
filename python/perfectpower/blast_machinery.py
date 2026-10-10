"""Biological adapters to existing PSG, SOE, Gamma and exact Hodge machinery."""
from fractions import Fraction as Q
from math import comb
from itertools import combinations
from .blast_alignment import AlignmentFamily, FEATURES
from .psg_polynomial import rational, Polynomial
from .divisor_square import WorkLimit


def partition_statistics(family, activities=(1, 1, 1, 1)):
    """Exact finite rational activity ensemble, not an evolutionary posterior."""
    values = tuple(map(rational, activities))
    if len(values) != 4 or any(x <= 0 for x in values):
        raise ValueError('four positive exact activities required')
    polynomial = family.polynomial()
    normalizer = polynomial.evaluate(values)
    means = []
    covariance = []
    for i, variable in enumerate(FEATURES):
        means.append(values[i]*polynomial.derivative(variable).evaluate(values)/normalizer)
    for i, x in enumerate(FEATURES):
        row = []
        for j, y in enumerate(FEATURES):
            factorial_moment = values[i]*values[j]*polynomial.derivative(x).derivative(y).evaluate(values)/normalizer
            row.append(factorial_moment+(means[i] if i == j else 0)-means[i]*means[j])
        covariance.append(row)
    return {'normalizer': str(normalizer), 'means': list(map(str, means)),
            'covariance': [list(map(str, row)) for row in covariance],
            'scope': 'finite supplied alignment population with rational monomial activities; no biological calibration'}


def sensitivity_jet(family, activities, direction, order=4):
    """PSG finite jet of partition function along an affine activity path."""
    if type(order) is not int or not 0 <= order <= 32:
        raise ValueError('jet order in 0..32 required')
    activities, direction = tuple(map(rational, activities)), tuple(map(rational, direction))
    if len(activities) != 4 or len(direction) != 4:
        raise ValueError('four-dimensional activity path required')
    from .psg_jets import convolution
    out = [Q(0)]*(order+1)
    for feature, count in family.terms.items():
        jet = [Q(count)]+[Q(0)]*order
        for exponent, base, slope in zip(feature, activities, direction):
            factor = [Q(0)]*(order+1)
            for k in range(min(exponent, order)+1):
                factor[k] = comb(exponent, k)*base**(exponent-k)*slope**k
            jet = convolution(jet, factor, order)
        out = [a+b for a, b in zip(out, jet)]
    return {'coefficients': list(map(str, out)), 'order': order,
            'scope': 'exact Taylor coefficients of finite alignment partition polynomial; no unknown higher coefficients asserted'}


def fixed_alignment_null(length, matches, *, match_probability='1/4'):
    """Exact binomial tail for a fixed ungapped comparison under an IID null.

    Does not account for alignment selection, gaps, database size or composition
    dependence and must never be labelled a BLAST E-value.
    """
    if type(length) is not int or not 0 <= length <= 512 or type(matches) is not int or not 0 <= matches <= length:
        raise ValueError('length <=512 and match count within length required')
    p = rational(match_probability)
    if not 0 <= p <= 1:
        raise ValueError('probability in [0,1] required')
    tail = sum((comb(length, k)*p**k*(1-p)**(length-k) for k in range(matches, length+1)), Q(0))
    from .gamma_arithmetic import normalize
    gamma = normalize({'kind': 'binomial', 'width': matches}) if matches <= 64 else None
    return {'tail_probability': str(tail), 'length': length, 'matches': matches,
            'match_probability': str(p), 'fixed_width_binomial_bridge': gamma,
            'scope': 'fixed ungapped position pairs with IID Bernoulli identity null', 'is_blast_evalue': False}


def alignment_machine(query, subject):
    """Finite partial DFA with feature increments encoded in action labels."""
    family = AlignmentFamily(query, subject)
    states = [(0, 0, 'M')]; indices = {states[0]: 0}; transitions = []
    cursor = 0
    while cursor < len(states):
        i, j, previous = states[cursor]; row = {}
        for operation, u, v, increment in family.transitions(i, j, previous):
            child = (u, v, operation)
            if child not in indices:
                if len(states) >= 128:
                    raise WorkLimit('SOE alignment carrier exceeds 128 states')
                indices[child] = len(states); states.append(child)
            label = ('match' if increment[0] else 'mismatch') if operation == 'M' else operation+('_open' if increment[2] else '_extend')
            row[label] = indices[child]
        transitions.append(row); cursor += 1
    actions = {label: [row.get(label) for row in transitions]
               for label in ('match', 'mismatch', 'D_open', 'D_extend', 'I_open', 'I_extend')}
    observations = [int(i == len(query) and j == len(subject)) for i, j, previous in states]
    return {'observations': observations, 'actions': actions}, states


def motif_machine(motifs, alphabet='ACGT'):
    """Prefix DFA for exact literal motifs, with complete suffix-match readouts."""
    from .blast_alignment import sequence
    motifs = tuple(sorted(set(sequence(m, limit=32) for m in motifs)))
    if not motifs or any(not m or any(c not in alphabet for c in m) for m in motifs) or len(set(alphabet)) != len(alphabet) or not alphabet or len(alphabet) > 16:
        raise ValueError('nonempty motifs over a distinct alphabet of size <=16 required')
    prefixes = sorted({''} | {m[:i] for m in motifs for i in range(1, len(m)+1)}, key=lambda p: (len(p), p))
    if len(prefixes) > 128:
        raise WorkLimit('motif carrier exceeds 128 states')
    def target(prefix, letter):
        word = prefix+letter
        return prefixes.index(max((p for p in prefixes if word.endswith(p)), key=len))
    model = {'observations': [[m for m in motifs if p.endswith(m)] for p in prefixes],
             'actions': {a: [target(p, a) for p in prefixes] for a in alphabet}}
    return model, prefixes


def soe_packet(model, *, compile_lean=False):
    from .future_states import future_quotient, check_quotient
    packet = future_quotient(model)
    check_quotient(packet, model)
    out = {'model': model, 'quotient': packet, 'state_count': len(model['observations']),
           'class_count': len(packet['blocks']), 'kernel_checked': False,
           'scope': 'all finite words of supplied feature-labelled or motif partial machine'}
    if compile_lean:
        from .checked_soe import compile_soe
        out['lean_compilation'] = compile_soe(model, packet)
    return out


def motif_count_machine(motifs, alphabet='ACGT'):
    """Reuse exact linear observability for counts of accepted alphabet words."""
    from .observable_machine import minimal_machine
    model, labels = motif_machine(motifs, alphabet)
    n = len(labels)
    if n > 64:
        raise WorkLimit('linear motif machine exceeds 64 states')
    # Sum deterministic symbol transitions; multiplying by A counts all words.
    operator = [[0]*n for _ in range(n)]
    for row in model['actions'].values():
        for source, target in enumerate(row):
            operator[target][source] += 1
    seed = [int(i == 0) for i in range(n)]
    readout = [int(bool(o)) for o in model['observations']]
    packet = minimal_machine([operator], seed, [readout])
    return {'machine': packet, 'prefixes': labels,
            'scope': 'counts of alphabet words ending in at least one supplied motif; not occurrence counts or sequence probabilities'}


def feature_diagnostic(hypotheses, costs=(1, 1, 1, 1)):
    """Reuse repository global optimal noiseless diagnostic-policy machinery."""
    from .diagnostic_programs import DiagnosticPolicy
    from .exact_linear import identity
    specification = {'operators': [identity(4)], 'hypotheses': hypotheses,
                     'readouts': {name: [int(i == j) for i in range(4)] for j, name in enumerate(FEATURES)},
                     'operator_costs': [1], 'readout_costs': dict(zip(FEATURES, costs))}
    return DiagnosticPolicy(specification).packet


def similarity_geometry(vertices, edges, *, fill_triangles=True):
    """Exact graph/clique-complex Hodge decomposition with supplied edge weights.

    Vertices/edges are supplied relationships. Triangles fill graph cliques;
    this is not a phylogeny or a Riemann surface of the underlying sequences.
    """
    from . import exact_linear as E
    from .weighted_hodge import weighted_hodge
    from .connection_polytope import ConnectionGraph
    if type(vertices) is not int or not 1 <= vertices <= 32 or not 1 <= len(edges) <= 64:
        raise WorkLimit('graph requires <=32 vertices and 1..64 edges')
    clean, seen = [], set()
    for a, b, weight, orientation in edges:
        if type(a) is not int or type(b) is not int or not 0 <= a < b < vertices or (a, b) in seen:
            raise ValueError('distinct ordered nonloop endpoints required')
        weight = rational(weight)
        if weight <= 0 or type(orientation) is not int or orientation not in (-1, 1):
            raise ValueError('positive weights and strand signs required')
        seen.add((a, b)); clean.append((a, b, weight, orientation))
    index = {(a, b): i for i, (a, b, _, _) in enumerate(clean)}
    triangles = [t for t in combinations(range(vertices), 3) if all((a, b) in index for a, b in combinations(t, 2))] if fill_triangles else []
    if len(triangles) > 64:
        raise WorkLimit('clique triangle budget exceeds 64')
    boundary1 = [[int(v == b)-int(v == a) for a, b, _, _ in clean] for v in range(vertices)]
    boundary2 = [[0]*max(1, len(triangles)) for _ in clean]
    for column, (a, b, c) in enumerate(triangles):
        for edge, sign in (((a, b), 1), ((b, c), 1), ((a, c), -1)):
            boundary2[index[edge]][column] = sign
    mass1 = [[weight if i == j else Q(0) for j in range(len(clean))] for i, (_, _, weight, _) in enumerate(clean)]
    hodge = weighted_hodge(boundary1, boundary2, E.identity(vertices), mass1, E.identity(max(1, len(triangles))))
    gain = ConnectionGraph(vertices, tuple((a, b, int(orientation < 0)) for a, b, _, orientation in clean), 2)
    lap = [[Q(0)]*vertices for _ in range(vertices)]
    for a, b, weight, _ in clean:
        lap[a][a] += weight; lap[b][b] += weight; lap[a][b] -= weight; lap[b][a] -= weight
    powers, moments = E.identity(vertices), []
    for k in range(1, 5):
        powers = E.multiply(powers, lap)
        moments.append(str(sum(powers[i][i] for i in range(vertices))))
    return {'schema': 'pp-blast-similarity-geometry/1', 'vertices': vertices,
            'edges': [[a, b, str(w), o] for a, b, w, o in clean], 'triangles': triangles,
            'boundary1': boundary1, 'boundary2': boundary2, 'hodge': hodge,
            'laplacian': [[str(v) for v in row] for row in lap], 'spectral_moments': moments,
            'strand_transport': gain.support(), 'kernel_checked': False,
            'scope': 'supplied weighted similarity complex and Z/2 strand transport; no evolutionary direction or intrinsic surface asserted'}


def semiring_alignment(query, subject, scoring=None, activities=(1, 1, 1, 1)):
    """Use existing typed transports for count, mass and minimum negative score.

    Terminal states absorb with unit weight; a horizon of n+m includes every
    complete path exactly once, independently of its number of columns.
    """
    from .semantic_fibres import Transport
    from .blast_alignment import weights, score
    family = AlignmentFamily(query, subject)
    model, states = alignment_machine(family.query, family.subject)
    labels = tuple(str(i) for i in range(len(states)))
    positions = {state: i for i, state in enumerate(states)}
    scoring = weights() if scoring is None else tuple(map(rational, scoring))
    activities = tuple(map(rational, activities))
    if len(activities) != 4 or any(x <= 0 for x in activities):
        raise ValueError('four positive rational activities required')
    totals = {}
    for mode in ('count', 'mass', 'minplus'):
        entries = []
        for k, (i, j, previous) in enumerate(states):
            if model['observations'][k]:
                entries.append((str(k), str(k), 0 if mode == 'minplus' else 1))
            for operation, u, v, increment in family.transitions(i, j, previous):
                child = positions[u, v, operation]
                value = Q(1)
                if mode == 'mass':
                    for activity, exponent in zip(activities, increment):
                        value *= activity**exponent
                elif mode == 'minplus':
                    value = -score(increment, scoring)
                entries.append((str(k), str(child), value))
        arrow = Transport(labels, labels, entries, mode=mode)
        current = {label: (None if mode == 'minplus' else 0) for label in labels}
        current['0'] = 0 if mode == 'minplus' else 1
        for _ in range(len(family.query)+len(family.subject)):
            current = arrow.apply(current)
        terminal = [current[str(i)] for i, o in enumerate(model['observations']) if o]
        totals[mode] = str(min(Q(x) for x in terminal if x is not None)) if mode == 'minplus' else str(sum((Q(x) for x in terminal), Q(0)))
    return {'count': int(Q(totals['count'])), 'partition_mass': totals['mass'],
            'minimum_negative_score': totals['minplus'], 'horizon': len(family.query)+len(family.subject),
            'scope': 'complete absorbing finite global alignment DAG under existing count, mass and min-plus transports'}
