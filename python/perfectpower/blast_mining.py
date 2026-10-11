"""Source-bound BLAST mining using exact graph populations and formal series.

Counts refer to supplied HSPs and literal motifs. Neither search completeness
nor orthology nor an evolutionary likelihood is implied by these adapters.
"""
from collections import defaultdict
from decimal import Decimal
from fractions import Fraction as Q
from hashlib import sha256
from itertools import combinations
import json

from .blast_alignment import score, weights
from .blast_io import replay
from .blast_machinery import motif_machine
from .divisor_square import WorkLimit
from .graph_counting import GraphPopulation


def _group(hit):
    f = hit.fields
    return (f['qseqid'], f['sseqid'], hit.strand, f['qend'] >= f['qstart'])


def _limits(*values):
    if any(x is not None and (type(x) is not int or x < 0) for x in values):
        raise ValueError('nonnegative integer spacing/coverage limits required')


class ChainIndex:
    """Complete nonempty HSP paths, compressed by ending vertex and coverage.

    Exact length polynomial, optimal score/tie multiplicity, and random access.
    Spacing is a constraint, not a charged inter-HSP affine alignment gap.
    """
    def __init__(self, hits, scoring=None, *, min_coverage=0,
                 max_query_gap=None, max_subject_gap=None, frame_modulus=None,
                 cell_limit=1_000_000):
        self.hits = tuple(hits)
        if len(self.hits) > 512:
            raise WorkLimit('HSP DAG carrier exceeds 512')
        _limits(min_coverage, max_query_gap, max_subject_gap)
        if frame_modulus is not None and (type(frame_modulus) is not int or frame_modulus < 1):
            raise ValueError('positive frame modulus required')
        if type(cell_limit) is not int or cell_limit < 1:
            raise ValueError('positive DAG cell budget required')
        if len({_group(h) for h in self.hits}) > 1:
            raise ValueError('one query/subject/orientation group required')
        self.scoring = tuple(weights() if scoring is None else map(Q, scoring))
        if len(self.scoring) != 4:
            raise ValueError('four rational score weights required')
        self.minimum = min_coverage
        self.constraints = {'min_coverage': min_coverage, 'max_query_gap': max_query_gap,
                            'max_subject_gap': max_subject_gap, 'frame_modulus': frame_modulus}
        self.order = sorted(range(len(self.hits)), key=lambda i: (*self.hits[i].interval('q', oriented=True), i))
        self.children = {i: [] for i in self.order}
        self.coverage = [abs(h.fields['qend']-h.fields['qstart'])+1 for h in self.hits]
        self.values = [score(h.features, self.scoring) for h in self.hits]
        for pos, i in enumerate(self.order):
            for j in self.order[pos+1:]:
                qgap = self.hits[j].interval('q', oriented=True)[0]-self.hits[i].interval('q', oriented=True)[1]
                sgap = self.hits[j].interval('s', oriented=True)[0]-self.hits[i].interval('s', oriented=True)[1]
                if qgap < 0 or sgap < 0:
                    continue
                if max_query_gap is not None and qgap > max_query_gap:
                    continue
                if max_subject_gap is not None and sgap > max_subject_gap:
                    continue
                if frame_modulus is not None and (sgap-qgap) % frame_modulus:
                    continue
                self.children[i].append(j)
        # Bottom-up suffix polynomials indexed by (HSP count, query bases).
        self.suffix = {}; cells = 0
        for i in reversed(self.order):
            terms = {(1, self.coverage[i]): 1}
            for j in self.children[i]:
                for (length, coverage), count in self.suffix[j].items():
                    cells += 1
                    if cells > cell_limit:
                        raise WorkLimit('DAG polynomial work budget; no complete index returned')
                    key = length+1, coverage+self.coverage[i]
                    terms[key] = terms.get(key, 0)+count
            cells += len(terms)
            if cells > cell_limit:
                raise WorkLimit('DAG polynomial storage budget; no complete index returned')
            self.suffix[i] = terms
        self.work = cells
        self.count = sum(c for terms in self.suffix.values() for (_, v), c in terms.items() if v >= self.minimum)
        # Independent max-plus DP by exact coverage, retaining all tie counts.
        best = {}; candidates = []
        for i in reversed(self.order):
            row = {self.coverage[i]: (self.values[i], 1, (i,))}
            for j in self.children[i]:
                for cov, (value, count, path) in best[j].items():
                    cov += self.coverage[i]; value += self.values[i]; path = (i,)+path
                    old = row.get(cov)
                    if old is None or value > old[0]:
                        row[cov] = value, count, path
                    elif value == old[0]:
                        row[cov] = value, count+old[1], min(path, old[2])
            best[i] = row
            candidates.extend(v for c, v in row.items() if c >= self.minimum)
        self.optimum = None
        if candidates:
            value = max(x[0] for x in candidates)
            ties = [x for x in candidates if x[0] == value]
            self.optimum = {'score': str(value), 'count': sum(x[1] for x in ties),
                            'hits': list(min(x[2] for x in ties))}

    def _block(self, i, prefix_coverage):
        return sum(c for (_, v), c in self.suffix[i].items() if prefix_coverage+v >= self.minimum)

    def select(self, rank):
        if type(rank) is not int or not 0 <= rank < self.count:
            raise ValueError('rank outside complete chain population')
        path = []; coverage = 0; menu = self.order
        while True:
            for i in menu:
                block = self._block(i, coverage)
                if rank < block:
                    path.append(i); coverage += self.coverage[i]; break
                rank -= block
            else:
                raise AssertionError('chain count/select inconsistency')
            if coverage >= self.minimum:
                if rank == 0:
                    return path
                rank -= 1
            menu = self.children[i]

    def rank(self, path):
        path = tuple(path)
        if not path or any(type(i) is not int for i in path):
            raise ValueError('nonempty admissible HSP index path required')
        result = coverage = 0; menu = self.order
        for pos, i in enumerate(path):
            if i not in menu:
                raise ValueError('path violates HSP DAG')
            result += sum(self._block(j, coverage) for j in menu[:menu.index(i)])
            coverage += self.coverage[i]
            if pos < len(path)-1 and coverage >= self.minimum:
                result += 1
            menu = self.children[i]
        if coverage < self.minimum:
            raise ValueError('path fails minimum query coverage')
        return result

    def packet(self):
        spectrum = defaultdict(int)
        for terms in self.suffix.values():
            for (n, c), multiplicity in terms.items():
                if c >= self.minimum:
                    spectrum[n] += multiplicity
        return {'schema': 'pp-blast-chain-index/1', 'source_hits': [h.packet() for h in self.hits],
                'scoring': list(map(str, self.scoring)), 'minimum_query_bases': self.minimum,
                'constraints': self.constraints,
                'order': self.order, 'edges': [[i, j] for i in self.order for j in self.children[i]],
                'count': self.count, 'length_polynomial': [[n, c] for n, c in sorted(spectrum.items())],
                'optimal': self.optimum, 'work_cells': self.work, 'complete': True,
                'kernel_checked': False, 'scope': 'nonempty paths of supplied HSP DAG; scores sum within-HSP features'}


def selection_model(hits, *, nonempty=True):
    """Indicator factors and equivalent CNF for coherent HSP subsets.

    Opposite orientations, coordinate overlaps and crossed order conflict.
    No maximum spacing constraint: pairwise compatibility then equals a chain.
    """
    hits = tuple(hits)
    if len(hits) > 512:
        raise WorkLimit('HSP selection carrier exceeds 512')
    if type(nonempty) is not bool:
        raise ValueError('boolean nonempty option required')
    if len({(h.fields['qseqid'], h.fields['sseqid']) for h in hits}) > 1:
        raise ValueError('one query/subject pair required')
    factors = []; conflicts = []
    for i, j in combinations(range(len(hits)), 2):
        a, b = hits[i], hits[j]
        coherent = False
        if _group(a) == _group(b):
            aq, bq = a.interval('q', oriented=True), b.interval('q', oriented=True)
            ass, bs = a.interval('s', oriented=True), b.interval('s', oriented=True)
            coherent = (aq[1] <= bq[0] and ass[1] <= bs[0]) or (bq[1] <= aq[0] and bs[1] <= ass[0])
        if not coherent:
            conflicts.append([i, j]); factors.append({'scope': [i, j], 'values': [1, 1, 1, 0]})
    # Nonempty is handled by subtracting the unique empty assignment in the
    # separator wrapper; avoid a dense 2^n global factor.
    clauses = [(-i-1, -j-1) for i, j in conflicts]
    if nonempty:
        clauses.append(tuple(range(1, len(hits)+1)))
    return {'specification': {'domains': [[0, 1] for _ in hits], 'factors': factors},
            'clauses': clauses, 'conflicts': conflicts, 'nonempty': nonempty}


class HSPSelectionPopulation:
    """Complete selections with shared separator or optional native CNF backend."""
    def __init__(self, hits, *, backend='separator', nonempty=True, cell_limit=1_000_000, timeout=120):
        self.hits = tuple(hits); self.model = selection_model(self.hits, nonempty=nonempty)
        self.backend = backend; self.nonempty = nonempty
        if backend == 'separator':
            self.engine = GraphPopulation(self.model['specification'], cell_limit=cell_limit)
            self.count = self.engine.count()-int(nonempty)
        elif backend == 'native':
            from .model_counting import CNF, CNFCounter
            self.engine = CNFCounter(CNF(len(self.hits), tuple(self.model['clauses'])), timeout=timeout)
            try:
                self.count = self.engine.count()
            except Exception:
                self.engine.close(); raise
        else:
            raise ValueError('separator or native backend required')

    def close(self):
        if self.backend == 'native':
            self.engine.close()

    def __enter__(self): return self
    def __exit__(self, *args): self.close()

    def select(self, rank):
        if type(rank) is not int or not 0 <= rank < self.count:
            raise ValueError('rank outside HSP selection population')
        return self.engine.select(rank+int(self.backend == 'separator' and self.nonempty))

    def rank(self, assignment):
        if self.nonempty and not any(assignment):
            raise ValueError('empty HSP selection excluded')
        return self.engine.rank(assignment)-int(self.backend == 'separator' and self.nonempty)

    def marginal(self, variable):
        if type(variable) is not int or not 0 <= variable < len(self.hits):
            raise ValueError('HSP variable outside carrier')
        if self.backend == 'separator':
            result = self.engine.marginal(variable)
            result[0] -= int(self.nonempty)
            return result
        return {x: self.engine.count([variable+1 if x else -variable-1]) for x in (0, 1)}

    def packet(self):
        return {'schema': 'pp-blast-selection-population/1', 'source_hits': [h.packet() for h in self.hits],
                'model': self.model, 'backend': self.backend, 'count': self.count,
                'evidence': self.engine.certificate() if self.backend == 'separator' else self.engine.last,
                'complete': True, 'kernel_checked': False,
                'scope': 'coherent subsets of supplied HSPs; nonempty option explicit; no inter-HSP spacing bound'}


    def count_where(self, fixed):
        """Exact conditional count in original HSP coordinates."""
        if any(type(i) is not int or not 0 <= i < len(self.hits) or type(b) is not int or b not in (0, 1) for i,b in fixed.items()):
            raise ValueError('original HSP indices and binary conditions required')
        if self.backend == 'native':
            return self.engine.count([i+1 if b else -i-1 for i,b in sorted(fixed.items())])
        return self.engine.restrict(fixed).count()-int(self.nonempty and not any(fixed.values()))

    def sample(self, *, seed=None):
        """Uniform over original assignments by integer rank."""
        from random import Random, SystemRandom
        if seed is not None and type(seed) is not int:
            raise ValueError('integer sampling seed required')
        if self.count == 0:
            raise ValueError('cannot sample empty HSP population')
        return self.select((SystemRandom() if seed is None else Random(seed)).randrange(self.count))


def motif_series(motifs, *, alphabet='ACGT', probabilities=None):
    """Exact overlapping motif hit probability and expected occurrence OGFs.

    Markov prefix transitions under supplied IID letter probabilities; a seen
    bit preserves occurrence-anywhere, and a reward block accumulates overlaps.
    Polynomial resolvent identities bind the series to the full source operator.
    """
    from .witness_resolvent import witness_resolvent
    model, labels = motif_machine(motifs, alphabet)
    n = len(labels)
    if n > 16:
        raise WorkLimit('motif series limited to 16 prefix states')
    if probabilities is None:
        p = {a: Q(1, len(alphabet)) for a in alphabet}
    else:
        if set(probabilities) != set(alphabet) or any(isinstance(v, float) for v in probabilities.values()):
            raise ValueError('one exact rational probability per alphabet letter required')
        p = {a: Q(v) for a, v in probabilities.items()}
    if any(v < 0 for v in p.values()) or sum(p.values()) != 1:
        raise ValueError('nonnegative letter probabilities summing exactly to one required')
    seen = [[Q(0)]*(2*n) for _ in range(2*n)]
    reward = [[Q(0)]*(2*n) for _ in range(2*n)]
    for a, targets in model['actions'].items():
        for i, j in enumerate(targets):
            multiplicity = len(model['observations'][j])
            for flag in (0, 1):
                seen[j+n*int(bool(flag or multiplicity))][i+n*flag] += p[a]
                reward[j+n*flag][i+n*flag] += p[a]
            reward[j+n][i] += p[a]*multiplicity
    seed = [int(i == 0) for i in range(2*n)]
    output = [[int(i >= n) for i in range(2*n)]]
    hit = witness_resolvent(seen, seed, output)
    expectation = witness_resolvent(reward, seed, output)
    return {'schema': 'pp-blast-motif-series/1', 'motifs': sorted(set(motifs)), 'prefixes': labels,
            'alphabet': alphabet, 'probabilities': {a: str(v) for a, v in p.items()},
            'hit_probability': hit, 'expected_occurrences': expectation,
            'kernel_checked': False, 'is_blast_evalue': False,
            'scope': 'IID letters; exact overlapping literal motifs anywhere in words of length n; no fitted biological model'}


def motif_values(packet, length, *, modulus=None):
    from .witness_resolvent import verify_resolvent
    from .generating_functions import RationalSeries
    if packet.get('schema') != 'pp-blast-motif-series/1':
        raise ValueError('motif series packet required')
    # Rebuild from source; a valid but unrelated resolvent is not acceptable.
    rebuilt = motif_series(packet['motifs'], alphabet=packet['alphabet'], probabilities=packet['probabilities'])
    from .blast_report import json_ready
    if json_ready(rebuilt) != json_ready(packet):
        raise ValueError('motif source/series packet changed')
    result = {}
    for name in ('hit_probability', 'expected_occurrences'):
        receipt = packet[name]
        if not verify_resolvent(receipt):
            raise ValueError('motif resolvent failed polynomial identity replay')
        output = receipt['outputs'][0]
        series = RationalSeries({k: output[k] for k in ('numerator', 'denominator')})
        result[name] = str(series.coefficient(length, modulus=modulus))
    return {'length': length, 'modulus': modulus, **result}


def similarity_topology(vertices, edges, *, face_limit=512):
    """Threshold snapshots of the triangle-filled similarity complex over Q.

    This is the clique 2-skeleton. H0/H1 agree with the full clique complex;
    reported H2 is only for this skeleton, since tetrahedra are not included.
    """
    from .graph_topology import cellular_homology
    if type(vertices) is not int or not 0 <= vertices <= 32 or len(edges) > 64:
        raise WorkLimit('cellular similarity scope: <=32 vertices and <=64 edges')
    if type(face_limit) is not int or face_limit < 0:
        raise ValueError('nonnegative triangle budget required')
    clean = []; pairs = set()
    for a, b, w, orientation in edges:
        if any(type(x) is not int for x in (a, b)) or not 0 <= a < b < vertices or (a, b) in pairs:
            raise ValueError('unique valid unordered similarity edges required')
        if isinstance(w, float) or Q(w) <= 0 or orientation not in (-1, 1):
            raise ValueError('positive rational weight and strand sign required')
        pairs.add((a, b)); clean.append((a, b, Q(w)))
    rows = []
    for threshold in sorted({w for _, _, w in clean}, reverse=True):
        selected = [(a, b) for a, b, w in clean if w >= threshold]
        ix = {e: i for i, e in enumerate(selected)}; faces = []; triangles = []
        for a, b, c in combinations(range(vertices), 3):
            if {(a, b), (b, c), (a, c)} <= ix.keys():
                if len(faces) >= face_limit:
                    raise WorkLimit('triangle budget; no full filtration returned')
                row = [0]*len(selected)
                row[ix[a, b]] = row[ix[b, c]] = 1; row[ix[a, c]] = -1
                faces.append(row); triangles.append([a, b, c])
        homology = cellular_homology(vertices, selected, faces)
        rows.append({'threshold': str(threshold), 'triangles': triangles, 'homology': homology})
    return {'schema': 'pp-blast-similarity-topology/1', 'snapshots': rows,
            'scope': 'triangle-filled threshold snapshots; no persistence pairing; H2 is skeleton-only; no biological cycles inferred'}


def assignment_diagnosis(hits, *, query_ids=None, subject_ids=None):
    """Maximum distinct-subject assignment, with matching/cover/Hall replay."""
    from .graph_optimization import matching
    hits = tuple(hits)
    queries = sorted({h.fields['qseqid'] for h in hits} if query_ids is None else set(query_ids))
    subjects = sorted({h.fields['sseqid'] for h in hits} if subject_ids is None else set(subject_ids))
    if len(queries)+len(subjects) > 4096 or len(hits) > 100000:
        raise WorkLimit('assignment carrier budget exceeded')
    qi = {v: i for i, v in enumerate(queries)}; si = {v: i for i, v in enumerate(subjects)}
    edges = sorted({(qi[h.fields['qseqid']], si[h.fields['sseqid']]) for h in hits})
    certificate = matching(len(queries), len(subjects), edges)
    return {'queries': queries, 'subjects': subjects, 'edges': edges, 'certificate': certificate,
            'assignment': [[queries[a], subjects[b]] for a, b in certificate['matching']],
            'scope': 'maximum cardinality distinct-subject assignment on supplied qualifying HSPs; not orthology or score optimum'}


def capacity_assignment(hits, capacities, *, query_ids=None):
    """Maximum assignment with user-supplied subject reuse capacities."""
    from .graph_optimization import max_flow
    hits = tuple(hits)
    queries = sorted({h.fields['qseqid'] for h in hits} if query_ids is None else set(query_ids))
    subjects = sorted(capacities)
    if len(queries)+len(subjects) > 128:
        raise WorkLimit('capacity flow carrier exceeds 128 sequence vertices')
    if any(type(v) is not int or v < 0 for v in capacities.values()):
        raise ValueError('nonnegative integer subject capacities required')
    qi = {v:i+1 for i,v in enumerate(queries)}
    si = {v:i+1+len(queries) for i,v in enumerate(subjects)}
    sink = len(queries)+len(subjects)+1
    arcs = [(0, qi[q], 1) for q in queries]+[(si[s],sink,capacities[s]) for s in subjects]
    pairs = sorted({(h.fields['qseqid'],h.fields['sseqid']) for h in hits})
    arcs += [(qi[q],si[s],1) for q,s in pairs]
    certificate = max_flow(sink+1, arcs, 0, sink)
    return {'queries': queries, 'subjects': subjects, 'capacities': dict(capacities), 'arcs': arcs,
            'certificate': certificate,
            'assignment': [[q,s] for q,s in pairs if certificate['flow'][qi[q]][si[s]]],
            'scope': 'maximum cardinality assignment under user capacities; not biological copy-number inference'}


def mine(hits, queries, subjects, *, nucleotide=True, maximum_evalue='0.001',
         minimum_identity='1/2', minimum_coverage='0', scoring=None,
         selection_backend='separator', motifs=(), cell_limit=1_000_000,
         source_hashes=None):
    """Replay all sources, filter candidates, compile per-pair populations.

    Missing sources and source-length disagreements are errors. WorkLimit is
    exposed per optional population, never replaced by a partial count.
    """
    from .blast_explore import similarity_edges
    hits = tuple(hits)
    threshold = Decimal(maximum_evalue); identity = Q(minimum_identity); coverage = Q(minimum_coverage)
    if not threshold.is_finite() or threshold < 0 or not 0 <= identity <= 1 or not 0 <= coverage <= 1:
        raise ValueError('valid exact mining thresholds required')
    if selection_backend not in ('separator', 'native'):
        raise ValueError('separator or native selection backend required')
    if motifs and not nucleotide:
        raise ValueError('batch motif adapter uses the DNA alphabet; use motif command for custom alphabets')
    retained = []; tracebacks = []; rejected = []
    for i, h in enumerate(hits):
        f = h.fields
        q, s = queries[f['qseqid']], subjects[f['sseqid']]
        if f.get('qlen') != len(q) or f.get('slen') != len(s):
            raise ValueError('declared HSP source lengths disagree or are missing')
        tracebacks.append(replay(h, q, s, nucleotide=nucleotide))
        reason = ('evalue' if Decimal(f['evalue']) > threshold else
                  'identity' if Q(h.features[0], f['length']) < identity else
                  'coverage' if min(Q(abs(f['qend']-f['qstart'])+1, len(q)), Q(abs(f['send']-f['sstart'])+1, len(s))) < coverage else
                  'self_hit' if f['qseqid'] == f['sseqid'] else None)
        if reason:
            rejected.append({'hit': i, 'reason': reason})
        else:
            retained.append(i)
    grouped = defaultdict(list); paired = defaultdict(list)
    for i in retained:
        grouped[_group(hits[i])].append(i)
        paired[hits[i].fields['qseqid'], hits[i].fields['sseqid']].append(i)
    chains = []; selections = []
    for group, indices in sorted(grouped.items()):
        try:
            index = ChainIndex([hits[i] for i in indices], scoring, cell_limit=cell_limit)
            chains.append({'group': list(group), 'hit_indices': indices, 'index': index.packet()})
        except WorkLimit as error:
            chains.append({'group': list(group), 'hit_indices': indices, 'status': 'WORK_LIMIT', 'reason': str(error)})
    for pair, indices in sorted(paired.items()):
        try:
            with HSPSelectionPopulation([hits[i] for i in indices], backend=selection_backend, cell_limit=cell_limit) as population:
                selections.append({'pair': list(pair), 'hit_indices': indices, 'population': population.packet(),
                                   'inclusion_counts': [population.marginal(i)[1] for i in range(len(indices))]})
        except WorkLimit as error:
            selections.append({'pair': list(pair), 'hit_indices': indices, 'status': 'WORK_LIMIT', 'reason': str(error)})
    accepted = [hits[i] for i in retained]
    # Network adapters are optional bounded analyses; the source receipt is
    # still returned when their own carrier budget is exceeded.
    network = None; topology = None
    try:
        network = similarity_edges(accepted, maximum_evalue=str(threshold), minimum_identity=str(identity), minimum_coverage=str(coverage))
        topology = similarity_topology(len(network['vertices']), network['edges'])
    except WorkLimit as error:
        topology = {'status': 'WORK_LIMIT', 'reason': str(error)}
    source = {'hits': [h.packet() for h in hits],
              'queries': {k: sha256(v.encode()).hexdigest() for k, v in sorted(queries.items())},
              'subjects': {k: sha256(v.encode()).hexdigest() for k, v in sorted(subjects.items())}}
    source_digest = sha256(json.dumps(source, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    try:
        assignment = assignment_diagnosis(accepted, query_ids=queries, subject_ids=subjects)
    except WorkLimit as error:
        assignment = {'status': 'WORK_LIMIT', 'reason': str(error)}
    motif_packets = []
    if motifs:
        motif_packet = motif_series(motifs)
        for k, v in sorted(queries.items()):
            try:
                null = motif_values(motif_packet, len(v))
            except WorkLimit as error:
                null = {'status': 'WORK_LIMIT', 'reason': str(error)}
            motif_packets.append({'record': k, 'literal_occurrences': {m: [i for i in range(len(v)-len(m)+1) if v.startswith(m, i)] for m in motifs},
                                  'iid_null': null})
        motif_packets.append({'source_model': motif_packet})
    return {'schema': 'pp-blast-mining/2', 'source_sha256': source_digest, 'source': source,
            'file_sha256': source_hashes or {}, 'tracebacks': tracebacks,
            'parameters': {'nucleotide': nucleotide, 'maximum_evalue': str(threshold), 'minimum_identity': str(identity),
                           'minimum_coverage': str(coverage), 'selection_backend': selection_backend,
                           'scoring': list(map(str, weights() if scoring is None else scoring)),
                           'cell_limit': cell_limit, 'motifs': list(motifs)},
            'retained_hit_indices': retained, 'rejected': rejected, 'chains': chains, 'selections': selections,
            'distinct_assignment': assignment, 'similarity': network,
            'topology': topology, 'motifs': motif_packets, 'complete_database_search': False,
            'kernel_checked': False, 'scope': 'exact analyses of supplied, source-replayed HSP candidates; each optional budget failure explicit'}


def verify_mining(packet, hits, queries, subjects, *, source_hashes=None):
    """Reexecute all source-derived results; native runtime statistics ignored.

    Raw file hashes are checked when supplied. This is executable source replay,
    not a Lean proof that the Python and C++ implementations are correct.
    """
    from copy import deepcopy
    from .blast_report import json_ready
    if packet.get('schema') != 'pp-blast-mining/2':
        raise ValueError('mining receipt required')
    parameters = dict(packet['parameters'])
    expected = mine(hits, queries, subjects, source_hashes=source_hashes, **parameters)
    actual = deepcopy(packet)
    for result in (expected, actual):
        for row in result['selections']:
            pop = row.get('population')
            if pop and pop['backend'] == 'native':
                pop.pop('evidence', None)
    if json_ready(expected) != json_ready(actual):
        raise ValueError('mining receipt differs from source replay')
    return True
