"""Reusable application objects over the existing exact engines."""
from copy import deepcopy
from fractions import Fraction as Q
from .divisor_square import WorkLimit


class SequenceLibrary:
    """Compile named readouts together; exact laws concern supplied definitions."""
    def __init__(self, specification):
        from .integral_machine import integral_machine
        from .witness_resolvent import witness_resolvent
        self.specification = deepcopy(specification)
        s = self.specification
        if set(s) != {'operator', 'seed', 'readouts'} or not isinstance(s['readouts'], dict):
            raise ValueError('operator, seed and named readouts required')
        self.names = tuple(s['readouts'])
        if not self.names or any(not isinstance(n, str) or not n.isidentifier() for n in self.names):
            raise ValueError('named readouts required')
        rows = list(s['readouts'].values())
        self.machine = integral_machine([s['operator']], s['seed'], rows)
        self.laws = witness_resolvent(s['operator'], s['seed'], rows)

    def summary(self):
        return dict(names=self.names, state_dimension=self.machine['state_dimension'],
                    shared_dimension=self.machine['minimal_dimension'], laws=self.laws['outputs'])

    def terms(self, index, modulus=None):
        from .integral_machine import modular_power_output
        from .witness_resolvent import resolvent_value
        values = (modular_power_output(self.machine, index, modulus) if modulus is not None else
                  [resolvent_value(self.laws, index, i) for i in range(len(self.names))])
        return dict(zip(self.names, values))

    def compare(self, other, left, right):
        from .witness_resolvent import compare_resolvents
        return compare_resolvents(self.laws, other.laws,
                                  left_output=self.names.index(left), right_output=other.names.index(right))

    def subsequence(self, offset=0, step=1):
        from .witness_resolvent import subsequence_resolvent
        s = self.specification
        return subsequence_resolvent(s['operator'], s['seed'], list(s['readouts'].values()),
                                    offset=offset, step=step)

    def experiment(self, left, right, operator_cost=1, readout_costs=None):
        """Globally cheapest finite separating word for positive operator cost."""
        from .optimal_experiments import cheapest_experiment
        result = cheapest_experiment(self.machine, left, right, [operator_cost], readout_costs)
        if 'readout' in result:
            result['name'] = self.names[result['readout']]
        return result

    def diagnostic(self,hypotheses,operator_cost=1,readout_costs=None):
        from .diagnostic_programs import DiagnosticPolicy
        spec=dict(operators=[self.specification['operator']],readouts=self.specification['readouts'],hypotheses=hypotheses,operator_costs=[operator_cost])
        if readout_costs is not None:
            if not isinstance(readout_costs,dict):
                readout_costs=list(readout_costs)
                if len(readout_costs)!=len(self.names):raise ValueError('matching readout costs required')
                readout_costs=dict(zip(self.names,readout_costs))
            spec['readout_costs']=readout_costs
        return DiagnosticPolicy(spec).evidence()

    def witness_experiment(self, left, right, operator_cost=1, readout_costs=None):
        """Legacy finite-witness comparison, retained for reproduction."""
        from .integral_machine import distinguish_states
        from .observable_machine import _word, _apply
        answer = distinguish_states(self.machine, left, right)
        if answer['status'] == 'ALL_FUTURE_EQUAL':
            return answer
        cost = Q(operator_cost)
        costs = [Q(1)] * len(self.names) if readout_costs is None else list(map(Q, readout_costs))
        if cost < 0 or len(costs) != len(self.names) or any(x < 0 for x in costs):
            raise ValueError('nonnegative matching exact costs required')
        s = self.specification
        choices = []
        for output, word in self.machine['rational_certificate']['readout_words']:
            a = _apply([s['readouts'][self.names[output]]], _word([s['operator']], left, word))[0]
            b = _apply([s['readouts'][self.names[output]]], _word([s['operator']], right, word))[0]
            if a != b:
                choices.append((cost * len(word) + costs[output], output, tuple(word), a, b))
        price, output, word, a, b = min(choices)
        return dict(status='DISTINGUISHED_BY_WORD', name=self.names[output], word=word,
                    left_value=a, right_value=b, cost=price,
                    scope='minimum supplied cost among compiled witness words; not among all words')


class InverseDesign:
    """Reuse a discrete calibration decomposition across observations/targets."""
    def __init__(self, specification):
        from .closest_integer import IntegerLiftOptimizer
        if set(specification) - {'matrix', 'metric'} or 'matrix' not in specification:
            raise ValueError('matrix and optional metric required')
        self.optimizer = IntegerLiftOptimizer(specification['matrix'],
            None if specification.get('metric') is None else [[Q(x) for x in row] for row in specification['metric']])

    def solve(self, observation, target):
        return self.optimizer.nearest(observation, [Q(x) for x in target])

    def policy(self, observation, lower, upper, target_origin, target_basis, target_box, inequalities=(), node_limit=500000):
        from .decision_regions import CalibrationPolicy
        return CalibrationPolicy(dict(matrix=self.optimizer.certificate['matrix'],metric=self.optimizer.mass,
            observation=observation,lower=lower,upper=upper,target_origin=target_origin,target_basis=target_basis,target_box=target_box,
            inequalities=inequalities,node_limit=node_limit)).evidence()

    def solve_box(self, observation, target, lower, upper, inequalities=(), node_limit=100000):
        from .bounded_inverse import closest_in_box
        return closest_in_box(self.optimizer.certificate['matrix'], observation, target,
                              lower, upper, self.optimizer.mass, inequalities, node_limit=node_limit)


class GraphEnsemble:
    """Exact conditional sampling with rational or algebraic probabilities."""
    def __init__(self, specification):
        from .connection_polytope import ConnectionGraph
        from .connection_measure import ConnectionMeasure
        if set(specification) - {'vertices', 'edges', 'power', 'weights'}:
            raise ValueError('unknown graph field')
        graph = ConnectionGraph(specification['vertices'], tuple(specification['edges']), specification['power'])
        self.measure = ConnectionMeasure(graph, specification.get('weights'))
        if self.measure.kernel is None:
            raise ValueError('rank-deficient graph has no normalized basis ensemble')

    @staticmethod
    def _rational(value):
        if any(value.coefficients[1:]):
            raise ValueError('nonrational event probability')
        return Q(value.coefficients[0])

    def event(self, included=(), excluded=()):
        return self._probability(self.measure.event(included, excluded))

    def _probability(self, value):
        if not any(value.coefficients[1:]):return self._rational(value)
        return dict(order=self.measure.graph.power, coefficients=list(map(str,value.coefficients)))

    def sample(self, size, seed=0, included=(), excluded=(), rng=None):
        from random import Random
        if type(size) is not int or not 0 <= size <= 1000:
            raise ValueError('sample size 0 through 1000 required')
        inc, exc = tuple(included), tuple(excluded)
        if size * max(1, len(self.measure.graph.edges))**4 > self.measure.work_limit:
            raise WorkLimit('aggregate sequential event work exceeds sampling budget')
        probability = self.measure.event(inc, exc)
        if probability == self.measure.field.element(0):
            raise ValueError('conditioning event has zero probability')
        random = Random(seed) if rng is None else rng
        records = []
        for _ in range(size):
            yes, no, denominator, decisions = list(inc), list(exc), probability, []
            for edge in range(len(self.measure.graph.edges)):
                if edge in yes or edge in no:
                    continue
                numerator = self.measure.event(yes + [edge], no)
                p = numerator * denominator.inverse()
                from .cyclotomic_real import exact_bernoulli
                take, decision = exact_bernoulli(p, self.measure.graph.power, random)
                decisions.append(dict(edge=edge, probability=self._probability(p), included=take, comparison=decision))
                if take:
                    yes.append(edge); denominator = numerator
                else:
                    no.append(edge); denominator -= numerator
            yes.sort()
            if len(yes) != self.measure.graph.vertices or self.measure.graph.support(yes)['rank'] != len(yes):
                raise AssertionError('sample is not a complete graph basis')
            value = self._probability(denominator * probability.inverse())
            records.append(dict(edges=yes, conditional_probability=str(value) if isinstance(value,Q) else value, decisions=decisions))
        value = self._probability(probability)
        return dict(schema='pp-graph-sample/2', seed=seed, included=inc, excluded=exc,
                    conditioning_probability=str(value) if isinstance(value,Q) else value, samples=records,
                    distribution='determinant-weighted bases, independent draws with replacement',
                    basis_enumerations=0, execution_verified=False)

    def reweight(self, weights):
        from .connection_updates import reweight
        return reweight(self.measure, weights)

    def with_weights(self, weights):
        """Return a derived ensemble and proof, preserving the source object."""
        from .connection_measure import ConnectionMeasure
        packet = self.reweight(weights)
        # Updates return both a transport proof and a new checked measure.
        updated = ConnectionMeasure.from_receipt(packet['updated'])
        if updated.kernel is None:
            raise ValueError('weight update destroys the normalized basis ensemble')
        derived = self.__class__.__new__(self.__class__)
        derived.measure = updated
        return derived, packet


class GeometryWorkbench:
    """Certified local chart panels, with contained path queries."""
    def __init__(self, specification):
        from .metric_boxes import compare, MetricBoxSpace
        if set(specification) != {'coefficients', 'panels'} or not 1 <= len(specification['panels']) <= 16:
            raise ValueError('coefficients and one through 16 named panels required')
        self.packets, self.spaces, self.transitions = {}, {}, {}
        for name, panel in specification['panels'].items():
            packet = compare(specification['coefficients'], **panel)
            self.spaces[name] = MetricBoxSpace(packet)
            self.packets[name] = packet

    def point(self, panel, point, bits=48):
        return self.spaces[panel].point(point, bits=bits)

    def segment(self, panel, start, end):
        return self.spaces[panel].segment(start, end)

    def grid(self, panel, resolution=9):
        if type(resolution) is not int or not 2 <= resolution <= 32:
            raise ValueError('grid resolution 2 through 32 required')
        a, b, c, d = map(Q, self.packets[panel]['box'])
        return [self.point(panel, [a+(b-a)*i/(resolution-1), c+(d-c)*j/(resolution-1)])
                for j in range(resolution) for i in range(resolution)]

    def write_html(self, path, resolution=9):
        from .geometry_workbench import write_html
        return write_html(self, path, resolution)

    def transition(self, source, target):
        from .chart_transitions import certify_transition
        a,b=self.packets[source],self.packets[target]
        if b['chart_data']['chart']!='finite':raise ValueError('target panel must be a finite chart')
        key=(source,target)
        if key not in self.transitions:
            data=a['chart_data']
            self.transitions[key]=certify_transition(data['coefficients'],data['chart'],a['box'],b['box'],data['branch'])
        return deepcopy(self.transitions[key])

    def transport(self, source, target, point):
        from .chart_transitions import transport_point
        result=transport_point(self.transition(source,target),point)
        a=self.point(source,result['source_point']);b=self.point(target,result['target_point']);factor=Q(result['density_multiplier'])
        interval=[max(Q(a['density_interval'][0]),factor*Q(b['density_interval'][0])),
                  min(Q(a['density_interval'][1]),factor*Q(b['density_interval'][1]))]
        if interval[0]>interval[1]:raise AssertionError('compatible density enclosures disagree')
        return dict(result,source_density=a['density_interval'],target_density=b['density_interval'],
                    common_source_density=list(map(str,interval)),compatible=True)


class CombinatorialDesign:
    """Chosen Gamma analysis and complete square-triangular size workflows."""
    def __init__(self, specification):
        from .gamma_arithmetic import normalize
        if set(specification) - {'expression', 'degree'} or 'expression' not in specification:
            raise ValueError('Gamma expression and optional power degree required')
        self.specification = deepcopy(specification)
        normalize(specification['expression'])

    def gamma(self, interval=None, n=None, complete=False):
        from .gamma_arithmetic import analyze_gamma
        return analyze_gamma(self.specification['expression'], self.specification.get('degree', 2),
                             interval=interval, n=n, complete=complete)

    def sizes(self, bound, filters=()):
        from .square_triangular_queries import query
        if type(bound) is not int or not 0 <= bound < 10**1000:
            raise ValueError('nonnegative size bound below 10^1000 required')
        return query(bound, filters)

    def select_size(self, rank, filters=()):
        from .square_triangular_queries import select, residue_schedule
        if type(rank) is not int or not 0 <= rank <= 1000:
            raise ValueError('size rank 0 through 1000 required')
        schedule = residue_schedule(filters)
        positives = sorted(j if j else schedule['period'] for j in schedule['cycle_hits'])
        if not positives:
            raise ValueError('no admissible positive size')
        index = (rank//len(positives))*schedule['period']+positives[rank%len(positives)]
        if index > 1365:
            raise WorkLimit('selected Pell size exceeds application bit budget')
        return select(rank, filters)
