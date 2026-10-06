"""Exact modular evaluation certificate for the rational balanced trace basis."""
import numpy as np
from valentiner_joint import operator_basis

PRIME = 1000003


class ModularComplex:
    """Formal Gaussian residues; conjugation flips i, and i^2=-1."""
    def __init__(self, a, b=0): self.a, self.b = int(a)%PRIME, int(b)%PRIME

    @staticmethod
    def cast(v):
        if isinstance(v, ModularComplex): return v
        if isinstance(v, complex):
            assert v.real == int(v.real) and v.imag == int(v.imag)
            return ModularComplex(int(v.real), int(v.imag))
        return ModularComplex(v)

    def __add__(self, v):
        v = self.cast(v); return ModularComplex(self.a+v.a, self.b+v.b)
    __radd__ = __add__

    def __mul__(self, v):
        v = self.cast(v); return ModularComplex(self.a*v.a-self.b*v.b, self.a*v.b+self.b*v.a)
    __rmul__ = __mul__

    def conjugate(self): return ModularComplex(self.a, -self.b)
    @property
    def real(self): return self.a


def modular_pivots(matrix):
    A = np.array(matrix, dtype=np.int64)%PRIME; rows = list(range(len(A))); rank = 0
    for j in range(A.shape[1]):
        candidates = np.flatnonzero(A[rank:, j])
        if len(candidates) == 0: continue
        k = rank+int(candidates[0]); A[[rank, k]] = A[[k, rank]]; rows[rank], rows[k] = rows[k], rows[rank]
        A[rank] = (A[rank]*pow(int(A[rank, j]), -1, PRIME))%PRIME
        A[rank+1:] = (A[rank+1:]-A[rank+1:, j, None]*A[rank])%PRIME
        rank += 1
        if rank == len(A): break
    return rank, rows[:rank]


def independence_certificate():
    rng = np.random.default_rng(208063); rows = []
    for _ in range(260):
        x = np.array([ModularComplex(v) for v in rng.integers(-3, 4, 54)], dtype=object)
        degrees, names, values = operator_basis(x, balanced_only=True, exact_values=True)
        rows.append([int(v)%PRIME for v in values])
    A = np.array(rows, dtype=np.int64); witnesses = []
    for degree in [2, 4, 6]:
        indices = [i for i, d in enumerate(degrees) if d == degree]
        rank, pivot_rows = modular_pivots(A[:, indices])
        assert rank == len(indices)
        assert modular_pivots(A[np.ix_(pivot_rows, indices)])[0] == len(indices)
        witnesses.append({'degree': degree, 'rank': rank, 'operators': [names[i] for i in indices], 'nonzero_square_minor_rows': pivot_rows})
    return {'prime': PRIME, 'seed': 208063, 'integer_coordinate_range': [-3, 3], 'evaluation_points': 260,
            'balanced_basis_witnesses': witnesses,
            'unbalanced_completion': 'Distinct source/link phase bidegrees separate the six source sextics and determinant sectors. I6 and det(L)^2 are independent already on L=e1 e1^T: I6=1, det(L)^2=0. Multiplication by nonzero det(L) preserves independence of the seven quadratic invariants for the quintics.',
            'meaning': 'Each full-rank finite-field evaluation minor proves independence of the corresponding integer-coefficient real polynomials over Q, hence over R. No floating-rank inference is used for the operator census.'}
