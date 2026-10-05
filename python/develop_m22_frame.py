"""Recover the Wilson operator algebra from the preserved exact word ledger.

No fitted CKM inputs enter reconstruction. Exact identities validate the entire
available ledger; unitary carrier extraction is explicitly numerical.
"""
from pathlib import Path
from fractions import Fraction
import hashlib
import json
import numpy as np
import sympy as sp
from sympy.polys.matrices import DomainMatrix
from scipy.linalg import eigh
from flint import fmpq_mat

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'galois_merge/vendor/forge/DATA/RELATION/TASK_SELECTED_WORD_PROGRAMS_V23/exact_prefix_1023.npz'
OUT = ROOT / 'receipts/m22_frame'


def independent_rows(a, p=1000003):
    echelon, selected = {}, []
    for i, row in enumerate(a):
        v = np.asarray([int(x) % p for x in row], dtype=np.int64)
        for k in sorted(echelon):
            if v[k]:
                v = (v - v[k] * echelon[k]) % p
        nz = np.flatnonzero(v)
        if len(nz):
            k = int(nz[0])
            echelon[k] = v * pow(int(v[k]), -1, p) % p
            selected.append(i)
        if len(selected) == a.shape[1]:
            break
    return selected


def prepend(i, bit):
    n = (i + 1).bit_length() - 1
    return (1 << (n + 1)) - 1 + bit * (1 << n) + i - ((1 << n) - 1)


def reverse(i):
    bits = bin(i + 1)[3:]
    return int('1' + bits[::-1], 2) - 1, bits.count('1')


def recover():
    # This is a hash-recorded, trusted repository archive, also read by its
    # original verifier. Its exact integer arrays use NumPy's object encoding.
    w = np.load(SOURCE, allow_pickle=True)['hecke']
    selected = independent_rows(w[:511])
    assert len(selected) == 152
    inverse = fmpq_mat(w[selected].tolist()).inv()

    def solve(indices, signs=None):
        c = w[indices].copy()
        if signs is not None:
            c *= np.asarray(signs, dtype=object)[:, None]
        result = inverse * fmpq_mat(c.tolist())
        assert all(x.denominator == 1 for x in result.entries())
        return np.asarray([[int(result[i,j]) for j in range(152)] for i in range(152)], dtype=np.int64)

    rx = solve([2*i+1 for i in selected])
    ry = solve([2*i+2 for i in selected])
    lx = solve([prepend(i, 0) for i in selected])
    ly = solve([prepend(i, 1) for i in selected])
    rev = [reverse(i) for i in selected]
    star = solve([i for i, _ in rev], [(-1)**n for _, n in rev])
    assert np.array_equal(w[:511] @ rx, w[1::2])
    assert np.array_equal(w[:511] @ ry, w[2::2])
    assert np.array_equal(w[:511] @ lx, w[[prepend(i, 0) for i in range(511)]])
    assert np.array_equal(w[:511] @ ly, w[[prepend(i, 1) for i in range(511)]])
    assert np.array_equal(star @ star, np.eye(152, dtype=np.int64))
    assert np.array_equal(lx @ rx, rx @ lx)
    assert np.array_equal(lx @ ry, ry @ lx)
    assert np.array_equal(ly @ rx, rx @ ly)
    assert np.array_equal(ly @ ry, ry @ ly)
    assert np.all(star.sum(axis=1) == 1) and np.all((star == 0) | (star == 1))
    # Positive trace metric in orbital coordinates, normalized at the identity.
    weights = {151: Fraction(1)}
    queue = [151]
    while queue:
        i = queue.pop()
        for r, sign in ((rx, 1), (ry, -1)):
            for j in np.flatnonzero(r[i]):
                assert r[j, i] != 0
                value = weights[i] * Fraction(sign * int(r[j, i]), int(r[i, j]))
                assert value > 0
                if int(j) in weights:
                    assert weights[int(j)] == value
                else:
                    weights[int(j)] = value
                    queue.append(int(j))
    assert len(weights) == 152
    g = np.asarray([int(weights[i]) for i in range(152)], dtype=np.int64)
    assert all(weights[i].denominator == 1 for i in range(152))
    assert g.sum() == 7392
    for r, sign in ((rx, 1), (ry, -1), (lx, 1), (ly, -1)):
        assert np.array_equal(r * g[None, :], sign * r.T * g[:, None])
    return selected, rx, ry, lx, ly, star, g


def numerical_carriers(rx, ry, lx, ly, g):
    sqrt = np.sqrt(g)
    def physical(r):
        return sqrt[:, None] * r.T / sqrt[None, :]
    x, y, leftx, lefty = map(physical, (rx, ry, lx, ly))
    selector = (leftx + .173 * 1j * lefty
                + .031 * (leftx@lefty-lefty@leftx)
                + .007 * 1j * (leftx@leftx@lefty+lefty@leftx@leftx))
    values, vectors = eigh(selector)
    groups = []
    for i, v in enumerate(values):
        if not groups or abs(v - values[groups[-1][0]]) > 1e-7:
            groups.append([])
        groups[-1].append(i)
    carriers, fingerprints = [], set()
    for group in groups:
        basis = vectors[:, group]
        xx, yy = basis.conj().T @ x @ basis, basis.conj().T @ y @ basis
        # Odd star words distinguish conjugate complex-type blocks; even trace
        # data alone may identify a conjugate pair and undercount simple blocks.
        word_traces = []
        front = [np.eye(len(group))]
        for _ in range(5):
            front = [v @ a for v in front for a in (xx, yy)]
            for v in front:
                tr = np.trace(v)
                word_traces.extend([tr.real, tr.imag])
        fingerprint = (len(group), *np.round(word_traces, 4))
        if fingerprint in fingerprints:
            continue
        fingerprints.add(fingerprint)
        entry = dict(dimension=len(group), fingerprint=list(map(float, fingerprint[1:9])),
                     invariance_residual=float(max(np.linalg.norm(x@basis-basis@xx), np.linalg.norm(y@basis-basis@yy))),
                     x_eigenvalues=eigh(xx)[0].tolist(), iy_eigenvalues=eigh(1j*yy)[0].tolist())
        if len(group) == 3:
            ex, ux = eigh(xx)
            ey, uy = eigh(1j*yy)
            mixing = ux.conj().T @ uy
            probabilities = abs(mixing)**2
            entry.update(x_has_simple_spectrum=bool(np.min(np.diff(ex)) > 1e-7),
                         iy_has_simple_spectrum=bool(np.min(np.diff(ey)) > 1e-7))
            if entry['x_has_simple_spectrum']:
                entry.update(probabilities=probabilities.tolist(),
                             conjugate_column_difference=float(np.max(abs(probabilities[:, 0]-probabilities[:, 2]))),
                             diagnosis='Two identical probability columns prevent a hierarchical CKM frame.')
            else:
                entry.update(diagnosis='Repeated X eigenvalue leaves a U(2) frame freedom.',
                             unique_x_line_probabilities=probabilities[2].tolist(),
                             unique_x_line_max_probability=float(probabilities[2].max()))
        carriers.append(entry)
    return carriers


def cover_phase_audit():
    # C12 x C5 is cyclic of order 60. Enumerate characters without choosing the
    # desired angle: residues are 5a+12b modulo 60.
    phases = sorted({(5*a+12*b) % 60 for a in range(12) for b in range(5)})
    assert phases == list(range(60))
    primitive = [n for n in phases if sp.gcd(n, 60) == 1]
    golden = [n for n in primitive if n % 5 in (1, 4)]
    assert golden == [1,11,19,29,31,41,49,59]
    # This identity is exact: 1-2 cos(72 deg) = (3-sqrt(5))/2.
    z = sp.Symbol('z')
    assert sp.minpoly(1-2*sp.cos(2*sp.pi/5), z) == z*z-3*z+1
    return dict(central_order=12, local_order=5, product_order=60,
                primitive_positive_angles=[6*n for n in primitive if n < 30],
                golden_positive_angles=[6*n for n in golden if n < 30],
                golden_polynomial='C^2-3C+1',
                sixty_six_character=dict(central_exponent=7, fifth_exponent=3, residue=11),
                sixty_six_selected=False,
                scope='An order-60 subgroup supplies possible phases. Central scalar multiplication leaves residual eigenprojectors unchanged; no CKM phase follows.')


def main():
    selected, rx, ry, lx, ly, star, g = recover()
    OUT.mkdir(parents=True, exist_ok=True)
    operators = dict(basis_word_indices=selected, right_x=rx.tolist(), right_y=ry.tolist(),
                     left_x=lx.tolist(), left_y=ly.tolist(), transpose=np.argmax(star, axis=1).tolist(),
                     subdegrees=g.tolist())
    (OUT/'recovered_operators.json').write_text(json.dumps(operators, separators=(',', ':'))+'\n')
    carriers = numerical_carriers(rx, ry, lx, ly, g)
    # Exact characteristic polynomials of the real integral regular operators.
    t = sp.Symbol('t')
    factors = {}
    for name, matrix in (('X', rx), ('Y', ry)):
        polynomial = DomainMatrix.from_Matrix(sp.Matrix(matrix.tolist())).charpoly()
        coefficients = [int(x) for x in polynomial]
        factors[name] = str(sp.factor(sp.Poly.from_list(coefficients, t).as_expr()))
    receipt = dict(source=str(SOURCE.relative_to(ROOT)), source_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
                   exact_ledger_checks=True, dimension=152, permutation_degree=int(g.sum()),
                   generators=dict(X='A49', Y='-A12-A48-A59+A95+A116+A125'),
                   expected_simple_block_sizes=[1,3,3,2,5,5,5,3,3,6],
                   recovered_simple_block_sizes=sorted(c['dimension'] for c in carriers),
                   characteristic_polynomial_factors=factors,
                   cover_phase_audit=cover_phase_audit(),
                   numerical_carriers=carriers,
                   scope='Q192 canonical incidence pair only; no CKM fit; carrier coordinates are numerical')
    print('recovered sizes', receipt['recovered_simple_block_sizes'], flush=True)
    assert sorted(receipt['expected_simple_block_sizes']) == receipt['recovered_simple_block_sizes']
    (OUT/'frame_audit.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
