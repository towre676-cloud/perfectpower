"""Finite, exact phase descent and actual linear morphisms.

The category here is finite Q-vector spaces graded by Q/Z, with rational
matrices preserving the grade. It is a split spectral model, not an assertion
that arbitrary complex representations have rational eigenbases. Its finite
Grothendieck algebra is Q[Q/Z]. No higher categorical structure is presumed.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from math import gcd, lcm
from .period_transport import PhaseObject, _cyclotomic, _divide_monic


def _int(n, name, low=1):
    if type(n) is not int or n < low:
        raise ValueError(name + ' must be an integer >= ' + str(low))
    return n


def _q(x):
    if type(x) not in (int, str, Q):
        raise ValueError('exact rational input required')
    return Q(x)


def _phase(x):
    return _q(x) % 1


def _pairs(data):
    return data.items() if isinstance(data, dict) else data


def _canonical(data):
    out = {}
    for x, c in _pairs(data):
        x = _phase(x)
        out[x] = out.get(x, Q(0)) + _q(c)
    return tuple(sorted((x, c) for x, c in out.items() if c))


@dataclass(frozen=True)
class PhaseClass:
    """Finite-support rational group algebra of rational angles modulo one."""
    terms: tuple = ()

    def __post_init__(self):
        object.__setattr__(self, 'terms', _canonical(self.terms))

    @classmethod
    def from_stage(cls, obj):
        if not isinstance(obj, PhaseObject):
            raise ValueError('PhaseObject required')
        return cls(obj.phases())

    @property
    def conductor(self):
        n = 1
        for x, _ in self.terms:
            n = lcm(n, x.denominator)
        return n

    def at_stage(self, n=None):
        n = self.conductor if n is None else _int(n, 'stage')
        if n % self.conductor:
            raise ValueError('stage does not contain every phase')
        return PhaseObject(n, tuple((int(n*x), c) for x, c in self.terms))

    def __add__(self, other):
        return PhaseClass(self.terms + other.terms)

    def scale(self, coefficient):
        a = _q(coefficient)
        return PhaseClass(tuple((x, a*c) for x, c in self.terms))

    def __mul__(self, other):
        return PhaseClass(tuple((x+y, a*b) for x, a in self.terms for y, b in other.terms))

    def dual(self):
        return PhaseClass(tuple((-x, c) for x, c in self.terms))

    def packet(self):
        return {'conductor': self.conductor, 'terms': [[str(x), str(c)] for x, c in self.terms]}


def colimit_witness(*objects):
    """Exhibit equality at one finite stage iff canonical phase classes agree.

    A global colimit element always has finite support, hence a finite common
    denominator. This routine checks the finite witness, not infinitely many
    stages or an unspecified higher-category colimit.
    """
    if not objects or any(not isinstance(o, PhaseObject) for o in objects):
        raise ValueError('at least one finite stage object is required')
    n = lcm(*(o.conductor for o in objects))
    classes = tuple(PhaseClass.from_stage(o) for o in objects)
    lifted = tuple(o.lift(n) for o in objects)
    canonical_equal = all(c == classes[0] for c in classes)
    stage_equal = all(o == lifted[0] for o in lifted)
    if canonical_equal != stage_equal:
        raise ArithmeticError('finite colimit equality failed')
    return {'common_stage': n, 'equal': canonical_equal,
            'canonical_classes': [c.packet() for c in classes],
            'common_stage_packets': [o.packet() for o in lifted],
            'scope': 'directed colimit of finite rational group algebras along phase-preserving inflation'}


@dataclass(frozen=True)
class StageFunctional:
    """A Q-linear functional on all N phase basis vectors at one stage."""
    conductor: int
    values: tuple

    def __post_init__(self):
        _int(self.conductor, 'stage')
        values = tuple(_q(v) for v in self.values)
        if len(values) != self.conductor:
            raise ValueError('one functional value per phase basis vector is required')
        object.__setattr__(self, 'values', values)

    def evaluate(self, value):
        obj = value if isinstance(value, PhaseObject) else value.at_stage(self.conductor)
        if obj.conductor != self.conductor:
            obj = PhaseClass.from_stage(obj).at_stage(self.conductor)
        return sum((c*self.values[k] for k, c in obj.terms), Q(0))

    def compatible(self, other):
        d = gcd(self.conductor, other.conductor)
        return all(self.values[k*(self.conductor//d)] == other.values[k*(other.conductor//d)]
                   for k in range(d))


class FiniteLinearCocone:
    """Unique functional on the span of the supplied stages' phase bases.

    Finite compatible data do not specify new phase values at an unseen
    conductor. Evaluation outside the covered span raises ValueError.
    """
    def __init__(self, stages):
        self.stages = tuple(stages)
        if not self.stages or any(not isinstance(s, StageFunctional) for s in self.stages):
            raise ValueError('nonempty StageFunctional collection required')
        self.values = {}
        for stage in self.stages:
            for k, value in enumerate(stage.values):
                phase = Q(k, stage.conductor)
                if phase in self.values and self.values[phase] != value:
                    raise ValueError('functional values disagree on a common phase')
                self.values[phase] = value

    def evaluate(self, value):
        value = PhaseClass.from_stage(value) if isinstance(value, PhaseObject) else value
        if not isinstance(value, PhaseClass):
            raise ValueError('PhaseClass or PhaseObject required')
        if any(x not in self.values for x, _ in value.terms):
            raise ValueError('phase lies outside the finite cocone covered span')
        return sum((c*self.values[x] for x, c in value.terms), Q(0))

    def receipt(self):
        return {'stages': [s.conductor for s in self.stages],
                'covered_basis_count': len(self.values),
                'common_conductor': lcm(*(s.conductor for s in self.stages)),
                'scope': 'unique linear descent on the covered span; no arbitrary extension to uncovered phases'}


@dataclass(frozen=True)
class PhaseSpace:
    """Actual rational vector spaces with rational phase grading and fixed bases."""
    multiplicities: tuple = ()

    def __post_init__(self):
        data = _canonical(self.multiplicities)
        if any(c.denominator != 1 or c < 0 for _, c in data):
            raise ValueError('vector-space multiplicities must be nonnegative integers')
        object.__setattr__(self, 'multiplicities', tuple((x, int(c)) for x, c in data))

    @property
    def dimension(self):
        return sum(d for _, d in self.multiplicities)

    @property
    def conductor(self):
        return self.phase_class().conductor

    def phase_class(self):
        return PhaseClass(self.multiplicities)

    def dims(self):
        return dict(self.multiplicities)

    def direct_sum(self, other):
        return PhaseSpace(self.multiplicities + other.multiplicities)

    def tensor(self, other):
        return PhaseSpace(tuple((x+y, a*b) for x, a in self.multiplicities for y, b in other.multiplicities))

    def dual(self):
        return PhaseSpace(tuple((-x, d) for x, d in self.multiplicities))

    def basis(self):
        return tuple((x, i) for x, d in self.multiplicities for i in range(d))


def _matrix(rows, nr, nc):
    rows = tuple(tuple(_q(v) for v in row) for row in rows)
    if len(rows) != nr or any(len(row) != nc for row in rows):
        raise ValueError('linear block has the wrong dimensions')
    return rows


def _zeros(nr, nc):
    return tuple(tuple(Q(0) for _ in range(nc)) for _ in range(nr))


def _mm(a, b, nc):
    return tuple(tuple(sum((x*y for x, y in zip(row, col)), Q(0))
                       for col in zip(*b)) for row in a) if b else _zeros(len(a), nc)


@dataclass(frozen=True)
class PhaseLinearMap:
    """Actual grade-preserving rational matrix blocks; zero blocks are omitted."""
    source: PhaseSpace
    target: PhaseSpace
    blocks: tuple = ()

    def __post_init__(self):
        sd, td = self.source.dims(), self.target.dims()
        blocks = {}
        for x, matrix in _pairs(self.blocks):
            x = _phase(x)
            if x in blocks:
                raise ValueError('duplicate matrix block')
            if x not in sd or x not in td:
                raise ValueError('a matrix block must preserve an existing phase')
            matrix = _matrix(matrix, td[x], sd[x])
            if any(v for row in matrix for v in row):
                blocks[x] = matrix
        object.__setattr__(self, 'blocks', tuple(sorted(blocks.items())))

    @classmethod
    def identity(cls, space):
        return cls(space, space, tuple((x, tuple(tuple(Q(i == j) for j in range(d))
                                                    for i in range(d))) for x, d in space.multiplicities))

    def then(self, other):
        """Return other after self."""
        if self.target != other.source:
            raise ValueError('linear composition requires equal intermediate spaces')
        a, b = dict(self.blocks), dict(other.blocks)
        return PhaseLinearMap(self.source, other.target, tuple((x, _mm(b[x], a[x], self.source.dims()[x]))
                                  for x in a.keys() & b.keys()))

    def apply(self, vector):
        values = dict(_pairs(vector))
        sd, td = self.source.dims(), self.target.dims()
        if set(values) - set(sd):
            raise ValueError('vector has an unknown phase')
        values = {x: tuple(_q(v) for v in values.get(x, (0,)*d)) for x, d in sd.items()}
        if any(len(values[x]) != d for x, d in sd.items()):
            raise ValueError('vector has the wrong phase dimension')
        blocks = dict(self.blocks)
        return {x: tuple(sum((a*b for a, b in zip(row, values[x])), Q(0)) for row in blocks[x])
                if x in blocks else (Q(0),)*d for x, d in td.items()}

    def dual(self):
        return PhaseLinearMap(self.target.dual(), self.source.dual(),
                              tuple((-x, tuple(zip(*m))) for x, m in self.blocks))

    def forget(self):
        """Dense rational matrix of the faithful underlying-vector-space functor."""
        sd, td = self.source.basis(), self.target.basis()
        blocks = dict(self.blocks)
        return tuple(tuple(blocks[x][i][j] if x == y and x in blocks else Q(0)
                           for y, j in sd) for x, i in td)

    def direct_sum(self, other):
        source, target = self.source.direct_sum(other.source), self.target.direct_sum(other.target)
        sa, ta, sb, tb = self.source.dims(), self.target.dims(), other.source.dims(), other.target.dims()
        aa, bb = dict(self.blocks), dict(other.blocks)
        out = []
        for x in source.dims().keys() & target.dims().keys():
            rows = [[Q(0)]*source.dims()[x] for _ in range(target.dims()[x])]
            for matrix, ro, co in ((aa.get(x, ()), 0, 0), (bb.get(x, ()), ta.get(x, 0), sa.get(x, 0))):
                for i, row in enumerate(matrix):
                    for j, v in enumerate(row):
                        rows[ro+i][co+j] = v
            out.append((x, rows))
        return PhaseLinearMap(source, target, tuple(out))

    def tensor(self, other):
        source, target = self.source.tensor(other.source), self.target.tensor(other.target)
        sb = _tensor_basis(self.source, other.source)
        tb = _tensor_basis(self.target, other.target)
        aa, bb = dict(self.blocks), dict(other.blocks)
        out = []
        for x in source.dims().keys() & target.dims().keys():
            rows = []
            for p, i, q, j in tb[x]:
                rows.append(tuple(aa[p][i][k]*bb[q][j][ell]
                                  if p == r and q == t and p in aa and q in bb else Q(0)
                                  for r, k, t, ell in sb[x]))
            out.append((x, rows))
        return PhaseLinearMap(source, target, tuple(out))


def _tensor_basis(a, b):
    out = {}
    for p, da in a.multiplicities:
        for q, db in b.multiplicities:
            out.setdefault((p+q) % 1, []).extend((p, i, q, j) for i in range(da) for j in range(db))
    return out


def direct_sum_inclusions(a, b):
    target = a.direct_sum(b)
    ad, bd = a.dims(), b.dims()
    left, right = [], []
    for x, d in a.multiplicities:
        left.append((x, tuple(tuple(Q(i == j) for j in range(d)) for i in range(target.dims()[x]))))
    for x, d in b.multiplicities:
        right.append((x, tuple(tuple(Q(i-ad.get(x, 0) == j) for j in range(d))
                                     for i in range(target.dims()[x]))))
    return PhaseLinearMap(a, target, tuple(left)), PhaseLinearMap(b, target, tuple(right))


def _stage_check(space, n):
    _int(n, 'conductor')
    if n % space.conductor:
        raise ValueError('space phases are not defined at this cyclic stage')


def inflate_space(space, n, N):
    _stage_check(space, n)
    _int(N, 'larger conductor')
    if N % n:
        raise ValueError('inflation requires n dividing N')
    return space  # Rational angle/eigenvalue stays fixed through C_N -> C_n.


def induce_space(space, n, N):
    _stage_check(space, n)
    _int(N, 'larger conductor')
    if N % n:
        raise ValueError('induction requires n dividing N')
    d = N//n
    return PhaseSpace(tuple((Q(int(x*n)+n*j, N), m) for x, m in space.multiplicities for j in range(d)))


def _restriction_basis(space, N, n):
    _stage_check(space, N)
    _int(n, 'subgroup conductor')
    if N % n:
        raise ValueError('restriction requires n dividing N')
    out = {}
    for x, d in space.multiplicities:
        y = (x*(N//n)) % 1
        out.setdefault(y, []).extend((x, i) for i in range(d))
    return out


def restrict_space(space, N, n):
    return PhaseSpace(tuple((x, len(basis)) for x, basis in _restriction_basis(space, N, n).items()))


def induce_map(f, n, N):
    source, target = induce_space(f.source, n, N), induce_space(f.target, n, N)
    d = N//n
    return PhaseLinearMap(source, target, tuple((Q(int(x*n)+n*j, N), matrix)
                            for x, matrix in f.blocks for j in range(d)))


def restrict_map(f, N, n):
    source, target = restrict_space(f.source, N, n), restrict_space(f.target, N, n)
    sb, tb = _restriction_basis(f.source, N, n), _restriction_basis(f.target, N, n)
    blocks = dict(f.blocks)
    out = []
    for x in source.dims().keys() & target.dims().keys():
        out.append((x, tuple(tuple(blocks[p][i][j] if p == q and p in blocks else Q(0)
                                  for q, j in sb[x]) for p, i in tb[x])))
    return PhaseLinearMap(source, target, tuple(out))


def frobenius_to_restriction(f, V, W, n, N):
    """Hom_N(Ind V,W) -> Hom_n(V,Res W), by stacking actual matrix rows."""
    if f.source != induce_space(V, n, N) or f.target != W:
        raise ValueError('map has the wrong induction-adjunction source or target')
    target, rb = restrict_space(W, N, n), _restriction_basis(W, N, n)
    blocks = dict(f.blocks)
    return PhaseLinearMap(V, target, tuple((x, tuple(blocks[p][i] if p in blocks else (Q(0),)*d
                                   for p, i in rb.get(x, ())))
                         for x, d in V.multiplicities if x in target.dims()))


def frobenius_from_restriction(g, V, W, n, N):
    """Inverse Hom_n(V,Res W) -> Hom_N(Ind V,W), by splitting rows."""
    if g.source != V or g.target != restrict_space(W, N, n):
        raise ValueError('map has the wrong restriction-adjunction source or target')
    source, rb = induce_space(V, n, N), _restriction_basis(W, N, n)
    blocks = dict(g.blocks)
    out = {}
    for x, rows in rb.items():
        if x not in blocks:
            continue
        for j, (p, i) in enumerate(rows):
            if p not in source.dims():
                continue
            out.setdefault(p, [[Q(0)]*source.dims()[p] for _ in range(W.dims()[p])])[i] = list(blocks[x][j])
    return PhaseLinearMap(source, W, tuple(out.items()))


@dataclass(frozen=True)
class CyclotomicValue:
    """Exact Q[z]/Phi_N polynomial value, used for full complex DFT traces."""
    conductor: int
    coefficients: tuple

    def __post_init__(self):
        n = _int(self.conductor, 'DFT conductor')
        if n > 64:
            raise ValueError('exact DFT conductor budget is 64')
        coeffs = tuple(_q(v) for v in self.coefficients) or (Q(0),)
        remainder = _divide_monic(coeffs, _cyclotomic(n))[1]
        object.__setattr__(self, 'coefficients', remainder)

    @classmethod
    def root(cls, n, exponent=0):
        _int(n, 'DFT conductor')
        if n > 64:
            raise ValueError('exact DFT conductor budget is 64')
        k = exponent % n
        return cls(n, (Q(0),)*k + (Q(1),))

    def __add__(self, other):
        if self.conductor != other.conductor:
            raise ValueError('DFT values require the same ambient conductor')
        size = max(len(self.coefficients), len(other.coefficients))
        a, b = self.coefficients+(Q(0),)*(size-len(self.coefficients)), other.coefficients+(Q(0),)*(size-len(other.coefficients))
        return CyclotomicValue(self.conductor, tuple(x+y for x, y in zip(a, b)))

    def scale(self, c):
        c = _q(c)
        return CyclotomicValue(self.conductor, tuple(c*x for x in self.coefficients))

    def times_root(self, exponent):
        n = self.conductor
        out = [Q(0)]*n
        for j, c in enumerate(self.coefficients):
            out[(j+exponent) % n] += c
        return CyclotomicValue(n, tuple(out))

    def rational(self):
        if any(self.coefficients[1:]):
            raise ValueError('cyclotomic value is not rational')
        return self.coefficients[0]


@dataclass(frozen=True)
class DFTProfile:
    conductor: int
    traces: tuple

    def __post_init__(self):
        n = _int(self.conductor, 'DFT conductor')
        if n > 64 or len(self.traces) != n or any(not isinstance(t, CyclotomicValue) or t.conductor != n for t in self.traces):
            raise ValueError('DFT needs exactly N cyclotomic traces, with N <= 64')

    def inverse(self):
        n = self.conductor
        values = []
        for k in range(n):
            value = CyclotomicValue(n, (0,))
            for r, trace in enumerate(self.traces):
                value = value + trace.times_root(-k*r)
            values.append(value.scale(Q(1, n)).rational())
        return PhaseClass(tuple((Q(k, n), c) for k, c in enumerate(values)))


def dft_profile(value, conductor=None):
    if isinstance(value, PhaseSpace):
        value = value.phase_class()
    if isinstance(value, PhaseObject):
        value = PhaseClass.from_stage(value)
    if not isinstance(value, PhaseClass):
        raise ValueError('finite phase class required')
    n = value.conductor if conductor is None else _int(conductor, 'DFT conductor')
    if n > 64 or n % value.conductor:
        raise ValueError('DFT stage must contain every phase and be at most 64')
    traces = []
    for r in range(n):
        trace = CyclotomicValue(n, (0,))
        for x, c in value.terms:
            trace = trace + CyclotomicValue.root(n, int(x*n)*r).scale(c)
        traces.append(trace)
    return DFTProfile(n, tuple(traces))


@dataclass(frozen=True)
class CyclicPeriodTrace:
    phase_class: PhaseClass
    weight: object

    def coefficient(self, index, *, max_conductor=4096):
        _int(index, 'Dirichlet index')
        return self.phase_class.at_stage().cyclotomic_trace(index, max_conductor=max_conductor)

    def packet(self):
        return {'schema': 'pp-cyclic-period-trace/1', 'phases': self.phase_class.packet(),
                'weight': str(self.weight), 'domain': 'Re(weight)>1',
                'definition': 'sum_q multiplicity(q)*Li_weight(exp(2*pi*i*q))',
                'mellin': '1/Gamma(weight) integral_0^1 (-log x)^(weight-1) sum_q multiplicity(q)*exp(2*pi*i*q)/(1-x*exp(2*pi*i*q)) dx',
                'scope': 'the full complex family is injective by Dirichlet-series uniqueness and DFT; a single weight or real part need not be injective'}


def cyclic_period_trace(value, weight='s'):
    if isinstance(value, PhaseSpace):
        value = value.phase_class()
    if isinstance(value, PhaseObject):
        value = PhaseClass.from_stage(value)
    if not isinstance(value, PhaseClass):
        raise ValueError('finite phase class required')
    if type(weight) in (int, Q) and weight <= 1:
        raise ValueError('absolute-convergence trace requires weight > 1')
    return CyclicPeriodTrace(value, weight)


def _divisors(n):
    lo, hi = [], []
    for d in range(1, __import__('math').isqrt(n)+1):
        if n % d == 0:
            lo.append(d)
            if d*d != n:
                hi.append(n//d)
    return lo + hi[::-1]


def _phi(n):
    out, k, p = n, n, 2
    while p*p <= k:
        if k % p == 0:
            out -= out//p
            while k % p == 0:
                k //= p
        p += 1
    return out-out//k if k > 1 else out


def induced_primitive_factorization(n, degree):
    """Root-order proof certificate for Phi_n(x^degree), not dense expansion."""
    _int(n, 'base conductor')
    _int(degree, 'induction degree')
    N = n*degree
    orders = tuple(m for m in _divisors(N) if m//gcd(m, degree) == n)
    factors = [{'conductor': m, 'degree': _phi(m)} for m in orders]
    total = sum(f['degree'] for f in factors)
    if total != degree*_phi(n):
        raise ArithmeticError('cyclotomic factorization degree check failed')
    return {'base_conductor': n, 'degree': degree, 'total_degree': total,
            'factors': factors, 'root_order_criterion': 'm/gcd(m,degree)=base_conductor',
            'identity': 'Phi_n(x^degree)=product_m Phi_m(x)',
            'proof': 'a primitive m-th root raised to degree has order m/gcd(m,degree); all roots are simple in characteristic zero'}


def descent_receipt():
    """Small deterministic integration receipt; larger validation lives in tests."""
    line = PhaseSpace(((Q(1, 1680), 1),))
    induced = induce_space(line, 1680, 443520)
    primitive = sum(d for x, d in induced.multiplicities if x.denominator == 443520)
    cls = PhaseClass(((Q(1, 6), 2), (Q(1, 3), -3), (0, 1)))
    dft = dft_profile(cls, 12)
    return {'schema': 'pp-phase-descent/1',
            'category': 'finite Q-vector spaces graded by Q/Z, with actual rational matrix morphisms',
            'colimit': 'Q[Q/Z] is the directed colimit of Q[C_N] under phase-preserving inflation',
            'induction_dimensions': {'base_line': 1, 'inflated_line': inflate_space(line, 1680, 443520).dimension,
                                     'induced_line': induced.dimension, 'primitive_branches': primitive,
                                     'nonprimitive_branches': induced.dimension-primitive, 'base_primitive_field': _phi(1680)},
            'factorization': induced_primitive_factorization(1680, 264),
            'dft_example': {'conductor': 12, 'class': cls.packet(), 'recovered_exactly': dft.inverse() == cls},
            'full_complex_mellin_family_injective': True,
            'scope': 'finite linear category, conductor colimit, and cyclic induction adjunction; no claimed higher colimit or unspecified E8 adjoint lift'}
