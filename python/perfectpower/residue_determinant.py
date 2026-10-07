"""Exact bounded auxiliary relations and modular determinant certificates.

No floating point, global height premise, or integral saturation assertion.
Discovery is separate from replay; emitted Lean checks concrete integer data.
"""
from fractions import Fraction
from math import factorial, gcd
import hashlib
import json


MAX_ROWS = 64
MAX_COLUMNS = 8
MAX_BITS = 4096


def integer(x, bits=MAX_BITS):
    if type(x) is not int or x.bit_length() > bits:
        raise ValueError('bounded literal integer required')
    return x


def matrix(a, *, square=False):
    if not isinstance(a, list) or not 1 <= len(a) <= MAX_ROWS:
        raise ValueError('one through 64 rows required')
    if not isinstance(a[0], list) or not 1 <= len(a[0]) <= MAX_COLUMNS:
        raise ValueError('one through eight columns required')
    n = len(a[0])
    if any(not isinstance(row, list) or len(row) != n for row in a):
        raise ValueError('rectangular integer matrix required')
    if square and len(a) != n:
        raise ValueError('square matrix required')
    return [[integer(x) for x in row] for row in a]


def transpose(a):
    return list(map(list, zip(*a)))


def multiply(a, b):
    return [[integer(sum(x*y for x, y in zip(row, col)))
             for col in transpose(b)] for row in a]


def determinant(a):
    """Fraction-free Bareiss, with det(empty)=1 for adjugate minors."""
    if not a:
        return 1
    b = [row[:] for row in a]
    n = len(b)
    sign, previous = 1, 1
    for k in range(n-1):
        pivot = next((i for i in range(k, n) if b[i][k]), None)
        if pivot is None:
            return 0
        if pivot != k:
            b[pivot], b[k] = b[k], b[pivot]
            sign = -sign
        p = b[k][k]
        for i in range(k+1, n):
            for j in range(k+1, n):
                value = b[i][j]*p-b[i][k]*b[k][j]
                q, r = divmod(value, previous)
                if r:
                    raise ValueError('nonexact Bareiss division')
                b[i][j] = integer(q)
            b[i][k] = 0
        previous = p
    return integer(sign*b[-1][-1])


def independent_rows(a):
    echelon, indices = [], []
    for i, row in enumerate(a):
        v = list(map(Fraction, row))
        for pivot, e in echelon:
            q = v[pivot]
            v = [x-q*y for x, y in zip(v, e)]
        pivot = next((j for j, x in enumerate(v) if x), None)
        if pivot is not None:
            q = v[pivot]
            echelon.append((pivot, [x/q for x in v]))
            indices.append(i)
    return indices


def adjugate(a):
    n = len(a)
    return [[integer((-1)**(i+j)*determinant([
        [a[r][c] for c in range(n) if c != i]
        for r in range(n) if r != j])) for j in range(n)] for i in range(n)]


def primitive(v):
    g = 0
    for x in v:
        g = gcd(g, x)
    if not g:
        return None
    sign = 1 if next(x for x in v if x) > 0 else -1
    return [sign*x//g for x in v]


def _kernel_data(a, indices):
    n = len(a[0])
    b = [a[i] for i in indices]
    if not b:
        return [], 1, [[int(i == j) for j in range(n)] for i in range(n)]
    gram = multiply(b, transpose(b))
    d = determinant(gram)
    if d <= 0:
        raise ValueError('independent rational rows required')
    c = multiply(multiply(transpose(b), adjugate(gram)), b)
    return b, d, [[integer(d*int(i == j)-c[i][j]) for j in range(n)] for i in range(n)]


def kernel_packet(a):
    a = matrix(a)
    indices = independent_rows(a)
    b, d, k = _kernel_data(a, indices)
    relations = []
    for col in transpose(k):
        v = primitive(col)
        if v is not None and v not in relations:
            relations.append(v)
    return {'schema': 'pp-integral-kernel/1', 'matrix': a,
            'independent_row_indices': indices, 'basis_rows': b,
            'gram_determinant': d, 'kernel_matrix': k, 'relations': relations,
            'rank': len(indices), 'nullity': len(a[0])-len(indices),
            'rational_kernel_spanning': True, 'integral_saturation_certified': False,
            'execution_verified': False}


def verify_kernel(packet):
    try:
        if packet['schema'] != 'pp-integral-kernel/1':
            return False
        a = matrix(packet['matrix'])
        indices = packet['independent_row_indices']
        if not isinstance(indices, list) or any(type(i) is not int for i in indices) or indices != independent_rows(a):
            return False
        b, d, k = _kernel_data(a, indices)
        if packet['basis_rows'] != b or integer(packet['gram_determinant']) != d or matrix(packet['kernel_matrix'], square=True) != k:
            return False
        if b and matrix(packet['basis_rows']) != b:
            return False
        if any(any(row) for row in multiply(a, k)):
            return False
        expected = []
        for col in transpose(k):
            v = primitive(col)
            if v is not None and v not in expected:
                expected.append(v)
        if packet['relations'] != expected:
            return False
        for c in packet['relations']:
            if not isinstance(c, list) or len(c) != len(a[0]) or any(type(x) is not int for x in c):
                return False
            if not any(c) or any(sum(x*y for x, y in zip(row, c)) for row in a):
                return False
        return (integer(packet['rank']) == len(indices) and integer(packet['nullity']) == len(a[0])-len(indices)
                and packet['rational_kernel_spanning'] is True
                and packet['integral_saturation_certified'] is False
                and packet['execution_verified'] is False)
    except (KeyError, TypeError, ValueError, IndexError, OverflowError):
        return False


def monomial_matrix(points, exponents, center=None):
    if not isinstance(points, list) or not 1 <= len(points) <= MAX_ROWS:
        raise ValueError('bounded nonempty point list required')
    dimension = len(points[0])
    if not 1 <= dimension <= 4:
        raise ValueError('one through four variables required')
    if any(not isinstance(p, list) or len(p) != dimension for p in points):
        raise ValueError('point dimension mismatch')
    if not isinstance(exponents, list) or not 1 <= len(exponents) <= MAX_COLUMNS:
        raise ValueError('one through eight monomials required')
    if any(not isinstance(e, list) or len(e) != dimension or
           any(type(v) is not int or v < 0 for v in e) or sum(e) > 12 for e in exponents):
        raise ValueError('bounded nonnegative exponent tuples required')
    if len({tuple(e) for e in exponents}) != len(exponents):
        raise ValueError('distinct monomials required')
    center = [0]*dimension if center is None else center
    if not isinstance(center, list) or len(center) != dimension:
        raise ValueError('center dimension mismatch')
    center = [integer(x, 256) for x in center]
    points = [[integer(x, 256) for x in p] for p in points]
    def term(p, e):
        v = 1
        for x, z, power in zip(p, center, e):
            v = integer(v*(x-z)**power)
        return v
    return [[term(p, e) for e in exponents] for p in points], center


def auxiliary_packet(points, exponents, *, center=None):
    a, center = monomial_matrix(points, exponents, center)
    return {'schema': 'pp-bounded-auxiliary/1', 'points': points, 'exponents': exponents,
            'center': center, 'kernel': kernel_packet(a),
            'scope': 'supplied integer points only', 'global_completeness': False}


def verify_auxiliary(packet):
    try:
        a, _ = monomial_matrix(packet['points'], packet['exponents'], packet['center'])
        return (packet['schema'] == 'pp-bounded-auxiliary/1'
                and packet['kernel']['matrix'] == a and verify_kernel(packet['kernel'])
                and packet['scope'] == 'supplied integer points only'
                and packet['global_completeness'] is False)
    except (KeyError, TypeError, ValueError, IndexError):
        return False


def modular_transform(a, modulus):
    """Integral E with E*A in modular echelon form and gcd(det(E),M)=1.

    No primality assumption: a composite modulus can fail to supply a unit
    pivot, which is rejected rather than silently treated as a field.
    """
    n = len(a)
    u = [row[:] for row in a]
    e = [[int(i == j) for j in range(n)] for i in range(n)]
    rank = 0
    for col in range(n):
        pivot = next((i for i in range(rank, n) if gcd(u[i][col], modulus) == 1), None)
        if pivot is None:
            if any(u[i][col] % modulus for i in range(rank, n)):
                raise ValueError('nonunit modular pivot: choose another modulus')
            continue
        u[rank], u[pivot] = u[pivot], u[rank]
        e[rank], e[pivot] = e[pivot], e[rank]
        scale = pow(u[rank][col], -1, modulus)
        u[rank] = [integer(scale*x) for x in u[rank]]
        e[rank] = [integer(scale*x) for x in e[rank]]
        for i in range(rank+1, n):
            q = u[i][col] % modulus
            u[i] = [integer(x-q*y) for x, y in zip(u[i], u[rank])]
            e[i] = [integer(x-q*y) for x, y in zip(e[i], e[rank])]
        rank += 1
    weights = [int(all(x % modulus == 0 for x in row)) for row in u]
    return e, u, weights


def determinant_packet(a, modulus):
    a = matrix(a, square=True)
    modulus = integer(modulus, 128)
    if modulus <= 1:
        raise ValueError('modulus greater than one required')
    e, u, weights = modular_transform(a, modulus)
    divisor = integer(modulus**sum(weights))
    bounds = [max(map(abs, row)) for row in a]
    bound = factorial(len(a))
    for b in bounds:
        bound = integer(bound*b)
    return {'schema': 'pp-residue-determinant/1', 'matrix': a, 'modulus': modulus,
            'transform': e, 'transformed': u, 'row_weights': weights,
            'divisor': divisor, 'row_bounds': bounds, 'determinant_bound': bound,
            'status': 'zero-certified' if bound < divisor else 'bound-insufficient',
            'execution_verified': False}


def verify_determinant(packet):
    try:
        if packet['schema'] != 'pp-residue-determinant/1':
            return False
        a = matrix(packet['matrix'], square=True)
        e = matrix(packet['transform'], square=True)
        u = matrix(packet['transformed'], square=True)
        if len(e) != len(a) or len(u) != len(a) or multiply(e, a) != u:
            return False
        m = integer(packet['modulus'], 128)
        if m <= 1:
            return False
        weights = packet['row_weights']
        if not isinstance(weights, list) or len(weights) != len(a) or any(type(w) is not int or w not in (0, 1) for w in weights):
            return False
        if any(x % m**w for row, w in zip(u, weights) for x in row):
            return False
        d = integer(m**sum(weights))
        if integer(packet['divisor']) != d or gcd(d, determinant(e)) != 1:
            return False
        bounds = packet['row_bounds']
        if not isinstance(bounds, list) or len(bounds) != len(a):
            return False
        if any(integer(b) < 0 or any(abs(x) > b for x in row) for b, row in zip(bounds, a)):
            return False
        bound = factorial(len(a))
        for b in bounds:
            bound = integer(bound*b)
        status = 'zero-certified' if bound < d else 'bound-insufficient'
        return (integer(packet['determinant_bound']) == bound and packet['status'] == status
                and packet['execution_verified'] is False)
    except (KeyError, TypeError, ValueError, IndexError, OverflowError):
        return False


def _lean_matrix(a):
    return '!![' + '; '.join(', '.join(f'({x})' for x in row) for row in a) + ']'


def _lean_vector(v):
    return '![' + ', '.join(f'({x})' for x in v) + ']'


def native_kernel(packet):
    if not verify_kernel(packet):
        raise ValueError('invalid kernel packet')
    a, k = packet['matrix'], packet['kernel_matrix']
    rows, cols = len(a), len(a[0])
    if rows > 8 or any(abs(x).bit_length() > 64 for row in a+k for x in row):
        raise ValueError('native reduction budget: at most eight rows and 64-bit entries')
    tag = hashlib.sha256(json.dumps(packet, sort_keys=True).encode()).hexdigest()[:16]
    ns = 'Kernel_' + tag
    lines = ['import PerfectPower.IntegralKernelWitness',
             'import PerfectPower.ResidueDeterminantCertificate',
             'import Mathlib.Tactic', 'set_option maxRecDepth 100000',
             'set_option maxHeartbeats 0', f'namespace {ns}', 'open Matrix',
             f'def A : Matrix (Fin {rows}) (Fin {cols}) ℤ := {_lean_matrix(a)}',
             f'def K : Matrix (Fin {cols}) (Fin {cols}) ℤ := {_lean_matrix(k)}',
             'theorem annihilates : A * K = 0 := by decide +kernel']
    rank = packet['rank']
    if rank > 4:
        raise ValueError('native Gram reduction budget: rank at most four')
    if rank:
        b = packet['basis_rows']
        lines += [f'def B : Matrix (Fin {rank}) (Fin {cols}) ℤ := {_lean_matrix(b)}',
                  f'def rowIndices : Fin {rank} → Fin {rows} := {_lean_vector(packet["independent_row_indices"])}',
                  'theorem B_is_selected : B = (fun i j => A (rowIndices i) j) := by decide +kernel',
                  'theorem K_is_kernel : K = PerfectPower.IntegralKernelWitness.integralKernelMatrix B := by decide +kernel',
                  'theorem gram_nonzero : (B * B.transpose).det ≠ 0 := by decide +kernel',
                  f'theorem rational_spanning (x : Fin {cols} → ℚ) (hx : (A.map (Int.castRingHom ℚ)) *ᵥ x = 0) :',
                  '    x ∈ Submodule.span ℚ (Set.range (fun j => fun i => (K i j : ℚ))) := by',
                  '  let Bq := B.map (Int.castRingHom ℚ)',
                  '  have hb : Bq *ᵥ x = 0 := by',
                  '    ext i',
                  '    simpa only [Bq, B_is_selected, Matrix.map_apply, Matrix.mulVec] using congrFun hx (rowIndices i)',
                  '  have hd : (Bq * Bq.transpose).det ≠ 0 := by',
                  '    have he := (Int.castRingHom ℚ).map_det (B * B.transpose)',
                  '    simp only [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map] at he',
                  '    change ((B * B.transpose).det : ℚ) = (Bq * Bq.transpose).det at he',
                  '    rw [← he]',
                  '    exact_mod_cast gram_nonzero',
                  '  have hs := PerfectPower.IntegralKernelWitness.mem_span_integralKernelMatrix_columns Bq hd x hb',
                  '  have hk : PerfectPower.IntegralKernelWitness.integralKernelMatrix Bq = K.map (Int.castRingHom ℚ) := by',
                  '    simpa only [K_is_kernel, Bq] using (PerfectPower.IntegralKernelWitness.integralKernelMatrix_map (Int.castRingHom ℚ) B).symm',
                  '  simpa only [hk, Matrix.map_apply] using hs',
                  '#print axioms rational_spanning']
    # Small concrete exact arithmetic is checked independently of the producer.
    for i, c in enumerate(packet['relations']):
        lines += [f'def c{i} : Fin {cols} → ℤ := {_lean_vector(c)}',
                  f'theorem relation{i} : c{i} ≠ 0 ∧ A *ᵥ c{i} = 0 := by decide +kernel',
                  f'#print axioms relation{i}']
    lines += ['#print axioms annihilates', f'end {ns}']
    return '\n'.join(lines) + '\n'


def native_auxiliary(packet):
    if not verify_auxiliary(packet):
        raise ValueError('invalid source-bound auxiliary packet')
    k = packet['kernel']
    code = native_kernel(k)
    tag = hashlib.sha256(json.dumps(k, sort_keys=True).encode()).hexdigest()[:16]
    rows, cols, dimension = len(packet['points']), len(packet['exponents']), len(packet['center'])
    extra = [f'def points : Matrix (Fin {rows}) (Fin {dimension}) ℤ := {_lean_matrix(packet["points"])}',
             f'def exponents : Matrix (Fin {cols}) (Fin {dimension}) ℕ := {_lean_matrix(packet["exponents"])}',
             f'def center : Fin {dimension} → ℤ := {_lean_vector(packet["center"])}',
             f'def evaluations : Matrix (Fin {rows}) (Fin {cols}) ℤ := fun i j =>',
             '  ∏ t, (points i t - center t) ^ exponents j t',
             'theorem evaluation_source : A = evaluations := by decide +kernel',
             '#print axioms evaluation_source']
    for i in range(len(k['relations'])):
        extra += [f'theorem source_relation{i} : evaluations *ᵥ c{i} = 0 := by',
                  f'  rw [← evaluation_source]; exact relation{i}.2',
                  f'#print axioms source_relation{i}']
    return code.replace('open Matrix', 'open Matrix\nopen scoped BigOperators').replace(
        f'end Kernel_{tag}', '\n'.join(extra) + f'\nend Kernel_{tag}')


def native_determinant(packet):
    if not verify_determinant(packet) or packet['status'] != 'zero-certified':
        raise ValueError('successful determinant certificate required')
    a, e, u = packet['matrix'], packet['transform'], packet['transformed']
    n = len(a)
    if n > 4:
        raise ValueError('native determinant reduction budget: dimension at most four')
    if any(abs(x).bit_length() > 64 for row in a+e+u for x in row):
        raise ValueError('native reduction budget: 64-bit entries')
    tag = hashlib.sha256(json.dumps(packet, sort_keys=True).encode()).hexdigest()[:16]
    ns = 'Determinant_' + tag
    # Bézout coefficients for gcd(D,det(E))=1 make the cancellation premise explicit.
    d, det_e = packet['divisor'], determinant(e)
    r0, r1, s0, s1, t0, t1 = d, det_e, 1, 0, 0, 1
    while r1:
        q = r0//r1
        r0, r1, s0, s1, t0, t1 = r1, r0-q*r1, s1, s0-q*s1, t1, t0-q*t1
    if r0 < 0:
        s0, t0 = -s0, -t0
    return f'''import PerfectPower.ResidueDeterminantCertificate
import Mathlib.Tactic
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {ns}
open Matrix
open scoped BigOperators
def A : Matrix (Fin {n}) (Fin {n}) ℤ := {_lean_matrix(a)}
def E : Matrix (Fin {n}) (Fin {n}) ℤ := {_lean_matrix(e)}
def U : Matrix (Fin {n}) (Fin {n}) ℤ := {_lean_matrix(u)}
def weights : Fin {n} → ℕ := {_lean_vector(packet['row_weights'])}
def bounds : Fin {n} → ℝ := {_lean_vector(packet['row_bounds'])}
theorem transform : E * A = U := by decide +kernel
theorem row_divides : ∀ i j, ({packet['modulus']} : ℤ)^weights i ∣ U i j := by decide +kernel
theorem divisor_sum : ({packet['modulus']} : ℤ)^(∑ i, weights i) = {d} := by decide +kernel
theorem coprime : IsCoprime ({d} : ℤ) E.det := by
  refine ⟨{s0}, {t0}, ?_⟩
  decide +kernel
theorem divides : ({d} : ℤ) ∣ A.det := by
  apply PerfectPower.ResidueDeterminantCertificate.determinant_dvd_of_transform A E {d} coprime
  rw [transform]
  have h := PerfectPower.ResidueDeterminantCertificate.pow_sum_dvd_det_of_row_dvd
    ({packet['modulus']} : ℤ) weights U row_divides
  rwa [divisor_sum] at h
theorem magnitude : ∀ i j, |(A i j : ℝ)| ≤ bounds i := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [A, bounds, Matrix.cons_val_zero, Matrix.cons_val_succ]
theorem strict_bound : (Nat.factorial (Fintype.card (Fin {n})) : ℝ) * ∏ i, bounds i < ({d} : ℝ) := by
  norm_num [bounds, Fin.prod_univ_succ, Nat.factorial]
theorem determinant_zero : A.det = 0 :=
  PerfectPower.ResidueDeterminantCertificate.determinant_zero_of_divisor_bound A {d} bounds divides magnitude strict_bound
#print axioms determinant_zero
end {ns}
'''
