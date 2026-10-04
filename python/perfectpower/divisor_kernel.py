"""Exact divisor coordinates and matrix-free GCD/occupancy kernels.

Public vectors are indexed 1..N, stored in ordinary zero-based lists. Exact
mode accepts only int/Fraction; numerical mode is explicit and finite-only.
The factorization is classical, not a new Diophantine completeness theorem.
"""
from fractions import Fraction as Q
from math import isfinite, isqrt, prod


class KernelLimit(ValueError):
    """The declared size or arithmetic-operation budget was exceeded."""


def _budget(n, passes=1, work_limit=30_000_000, size_limit=1_000_000):
    if type(n) is not int or n < 1:
        raise ValueError('nonempty vector required')
    if type(work_limit) is not int or work_limit < 1 or type(size_limit) is not int or size_limit < 1:
        raise ValueError('positive integer budgets required')
    if n > size_limit:
        raise KernelLimit('size limit exceeded')
    visits = sum(n // d for d in range(1, n + 1))
    if passes * visits > work_limit:
        raise KernelLimit('divisor-visit budget exceeded')
    return visits


def _values(values, exact=True):
    out = list(values)
    if exact:
        if any(type(v) not in (int, Q) for v in out):
            raise ValueError('exact integers or Fractions required')
    else:
        if any(type(v) not in (int, float, Q) for v in out):
            raise ValueError('real numerical entries required')
        out = list(map(float, out))
        if not all(map(isfinite, out)):
            raise ValueError('finite numerical entries required')
    return out


def divisor_transform(values, *, inverse=False, multiples=False,
                      work_limit=30_000_000, size_limit=1_000_000):
    """D or D^T, or their integer inverses; D[i,d]=[d divides i]."""
    x = _values(values); n = len(x)
    _budget(n, work_limit=work_limit, size_limit=size_limit)
    if inverse:
        y = x[:]
        if multiples:
            for d in range(n, 0, -1):
                for j in range(2*d, n+1, d):
                    y[d-1] -= y[j-1]
        else:
            for d in range(1, n+1):
                for j in range(2*d, n+1, d):
                    y[j-1] -= y[d-1]
    else:
        y = [0] * n
        for d in range(1, n+1):
            for j in range(d, n+1, d):
                if multiples: y[d-1] += x[j-1]
                else: y[j-1] += x[d-1]
    return y


class DivisorKernel:
    """K[i,j]=w(gcd(i,j)), optionally divided by max(i,j).

    Construct from g=mu*w. ``from_weights`` performs the correct downward
    divisor inversion, not the incorrect upward-multiple formula in old notes.
    """
    def __init__(self, coefficients, *, normalized=False, exact=True,
                 work_limit=30_000_000, size_limit=1_000_000):
        if type(normalized) is not bool or type(exact) is not bool:
            raise ValueError('Boolean normalized and exact flags required')
        self.g = tuple(_values(coefficients, exact)); self.n = len(self.g)
        self.visits = _budget(self.n, 3, work_limit, size_limit)
        self.normalized, self.exact = normalized, exact
        self.work_limit, self.size_limit = work_limit, size_limit

    @classmethod
    def from_weights(cls, weights, **options):
        exact = options.get('exact', True)
        w = _values(weights, exact)
        _budget(len(w), 3, options.get('work_limit', 30_000_000), options.get('size_limit', 1_000_000))
        g = w[:]
        for d in range(1, len(w)+1):
            for j in range(2*d, len(w)+1, d):
                g[j-1] -= g[d-1]
        return cls(g, **options)

    def weights(self):
        # The arithmetic is also usable in numerical mode, without silently
        # passing floats to the public exact transform.
        w = [0] * self.n
        for d, g in enumerate(self.g, 1):
            for j in range(d, self.n+1, d): w[j-1] += g
        return w

    def _vector(self, values):
        x = _values(values, self.exact)
        if len(x) != self.n: raise ValueError('vector dimension mismatch')
        return x

    def _divide(self, a, b):
        return Q(a, b) if self.exact else a/b

    def apply(self, values):
        x = self._vector(values); y = [0] * self.n
        for d, g in enumerate(self.g, 1):
            if not g: continue
            length = self.n // d
            if not self.normalized:
                total = g * sum(x[d-1::d])
                for j in range(d, self.n+1, d): y[j-1] += total
            else:
                # H[k,l]=1/max(k,l). Prefix x and suffix x/l avoid
                # cancellation from subtracting nearly equal total sums.
                suffix = [0] * (length+1)
                for k in range(length, 0, -1):
                    suffix[k-1] = suffix[k] + self._divide(x[d*k-1], k)
                prefix = 0; scale = self._divide(g, d)
                for k in range(1, length+1):
                    prefix += x[d*k-1]
                    y[d*k-1] += scale * (self._divide(prefix, k) + suffix[k])
        if not self.exact and not all(map(isfinite, y)):
            raise ArithmeticError('numerical overflow')
        return y

    def energy(self, values):
        """Evaluate x^T K x by the divisor/threshold sum-of-squares identity."""
        x = self._vector(values); answer = 0
        for d, g in enumerate(self.g, 1):
            if not g: continue
            if not self.normalized:
                answer += g * sum(x[d-1::d])**2
            else:
                length = self.n // d; prefix = 0; block = 0
                for k in range(1, length+1):
                    prefix += x[d*k-1]
                    block += self._divide(prefix**2, k*(k+1) if k < length else k)
                answer += self._divide(g, d) * block
        if not self.exact and not isfinite(answer): raise ArithmeticError('numerical overflow')
        return answer

    def certificate(self):
        """Exact inertia for raw kernels; sufficient normalized positivity.

        A negative g is inconclusive for the normalized kernel, whose block
        Gram factors overlap. Floating signs never receive an exact claim.
        """
        base = {'n': self.n, 'normalized': self.normalized,
                'arithmetic': 'exact' if self.exact else 'floating',
                'divisor_visits': self.visits, 'dense_matrix_allocated': False,
                'execution_verified': False}
        if not self.exact: return {**base, 'status': 'NUMERICAL_ONLY'}
        signs = {name: sum(test(g) for g in self.g) for name, test in
                 [('positive', lambda g:g>0), ('negative', lambda g:g<0), ('zero', lambda g:g==0)]}
        if not self.normalized:
            return {**base, 'status': 'EXACT_DIVISOR_CONGRUENCE', 'inertia': signs,
                    'rank': self.n-signs['zero'], 'positive_semidefinite': not signs['negative'],
                    'determinant': prod(self.g) if self.n <= 64 else None,
                    'determinant_formula': 'product(g[1..N])'}
        if signs['negative']: return {**base, 'status': 'SIGNED_GRAM_INCONCLUSIVE'}
        covered = [False]*self.n
        for d, g in enumerate(self.g, 1):
            if g:
                for j in range(d, self.n+1, d): covered[j-1] = True
        return {**base, 'status': 'EXACT_NONNEGATIVE_THRESHOLD_GRAM',
                'positive_semidefinite': True, 'positive_definite': all(covered),
                'rank': sum(covered), 'coordinate_kernel': [i+1 for i,v in enumerate(covered) if not v]}

    def solve(self, rhs, *, domain='rational'):
        """Complete raw-kernel affine fibre over Q or Z, in divisor coordinates.

        Free coordinates are 1-based positions of zero g; x=D^{-T}u. This
        compressed parameterization avoids an N-by-nullity basis allocation.
        """
        if self.normalized or not self.exact:
            raise ValueError('exact unnormalized kernel required for solving')
        if domain not in ('rational','integer'): raise ValueError('domain must be rational or integer')
        b = self._vector(rhs)
        if domain == 'integer' and any(Q(v).denominator != 1 for v in (*self.g, *b)):
            raise ValueError('integer weights and rhs required for integer solving')
        opts = {'work_limit':self.work_limit, 'size_limit':self.size_limit}
        z = divisor_transform(b, inverse=True, **opts); u = [0]*self.n; free = []
        for i, (g, value) in enumerate(zip(self.g, z), 1):
            if not g:
                if value:
                    return {'status':'DIVISOR_IMAGE_OBSTRUCTION', 'coordinate':i,
                            'transformed_rhs':value, 'domain':domain}
                free.append(i)
            else:
                v = Q(value)/g
                if domain == 'integer' and v.denominator != 1:
                    return {'status':'DIVISOR_CONGRUENCE_OBSTRUCTION', 'coordinate':i,
                            'transformed_rhs':int(value), 'modulus':abs(int(g)),
                            'residue':int(value)%abs(int(g)), 'domain':domain}
                u[i-1] = int(v) if v.denominator == 1 else v
        return {'status':'COMPLETE_DIVISOR_AFFINE_FIBRE', 'domain':domain,
                'particular':divisor_transform(u, inverse=True, multiples=True, **opts),
                'divisor_coordinates':u, 'free_divisor_coordinates':free,
                'parameterization':'x = inverse_multiple_zeta(u); each free u[j] is arbitrary in the stated domain'}

    def lift(self, solution, parameters=()):
        if solution.get('status') != 'COMPLETE_DIVISOR_AFFINE_FIBRE':
            raise ValueError('solution fibre required')
        parameters = _values(parameters)
        if len(parameters) != len(solution['free_divisor_coordinates']):
            raise ValueError('one parameter per free divisor coordinate required')
        if solution['domain']=='integer' and any(Q(v).denominator!=1 for v in parameters):
            raise ValueError('integer parameters required')
        u = self._vector(solution['divisor_coordinates'])
        for j, t in zip(solution['free_divisor_coordinates'], parameters): u[j-1] = t
        return divisor_transform(u, inverse=True, multiples=True,
                                 work_limit=self.work_limit, size_limit=self.size_limit)


def power_kernel(n, degree=1, **options):
    """w(n)=n^degree; integer degrees 0..8 yield exact Jordan coefficients."""
    if type(degree) is not int or not 0 <= degree <= 8:
        raise ValueError('degree must be an integer in 0..8')
    _budget(n, 3, options.get('work_limit',30_000_000),options.get('size_limit',1_000_000))
    return DivisorKernel.from_weights([i**degree for i in range(1,n+1)], **options)


def sigma_kernel(n, **options):
    """w=sigma, so g(n)=n, without constructing a dense GCD matrix."""
    _budget(n, 3, options.get('work_limit',30_000_000),options.get('size_limit',1_000_000))
    return DivisorKernel(range(1,n+1), **options)


def threshold_solve(rhs, *, size_limit=1_000_000):
    """Exact O(N) inverse of H[i,j]=1/max(i,j).

    H^{-1} has diagonal 2*i^2 except its final entry N^2, and adjacent
    entries -i*(i+1). In particular integral observations have integral lifts.
    """
    b=_values(rhs); n=len(b)
    if type(size_limit) is not int or size_limit<1 or not n:
        raise ValueError('nonempty vector and positive integer size limit required')
    if n>size_limit:raise KernelLimit('size limit exceeded')
    differences=[i*(i+1)*(b[i-1]-b[i]) for i in range(1,n)] + [n*b[-1]]
    return [differences[i]-(differences[i-1] if i else 0) for i in range(n)]


def sparse_divisor_counts(indices, *, index_limit=1_000_000, work_limit=30_000_000):
    """Divisor-frequency coordinates of a finite indicator, without N storage.

    Trial factorization is exact and separately budgeted; repeated indices are
    intentionally counted as repeated occurrences. No primality heuristic.
    """
    if type(index_limit) is not int or index_limit < 1 or type(work_limit) is not int or work_limit < 1:
        raise ValueError('positive integer budgets required')
    counts = {}; visits = 0
    for n in indices:
        if type(n) is not int or not 1 <= n <= index_limit:
            raise ValueError('positive integer index within the limit required')
        m=n; factors=[]; p=2
        while p <= isqrt(m):
            visits+=1
            if visits > work_limit: raise KernelLimit('factor/divisor budget exceeded')
            e=0
            while m%p==0: m//=p; e+=1
            if e: factors.append((p,e))
            p=3 if p==2 else p+2
        if m>1: factors.append((m,1))
        divisors=[1]
        for p,e in factors:
            old=divisors[:]; power=1
            for _ in range(e):
                power*=p; visits+=len(old)
                if visits > work_limit: raise KernelLimit('factor/divisor budget exceeded')
                divisors.extend(d*power for d in old)
        for d in divisors:
            visits+=1
            if visits > work_limit: raise KernelLimit('factor/divisor budget exceeded')
            counts[d]=counts.get(d,0)+1
    return counts


def sparse_pairing(left, right, *, degree=1):
    """Sum d^degree c_left[d] c_right[d], the sigma_degree(gcd) Gram form."""
    if type(degree) is not int or not 0 <= degree <= 8:
        raise ValueError('degree must be an integer in 0..8')
    for counts in (left,right):
        if any(type(d) is not int or d<1 or type(c) is not int or c<0 for d,c in counts.items()):
            raise ValueError('positive divisor keys and nonnegative integer counts required')
    if len(left)>len(right): left,right=right,left
    return sum(d**degree*c*right.get(d,0) for d,c in left.items())
