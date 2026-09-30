"""The open Thue branches as a graph of certified transformations.

Each open branch of the branch compiler (`branch_descent.py`) is an equation

    F(a, b) = M,   F = (c0, c1, c2, c3) = q a^3 + 3 p a^2 b - 3 D q a b^2 - p D b^3,  M = k^3,

with a *readout* back to the curve: y = (p W1(a, b) + D q W2(a, b)) / k^3.  A node is the whole
equation (form, right-hand side, readout data); an edge is a matrix T in GL_2(Z) with
F o T = G, which maps the solutions of G = M bijectively onto those of F = M.

Canonical forms.  For a binary cubic with nonzero discriminant the Hessian
H(F) = (c1^2 - 3 c0 c2, c1 c2 - 9 c0 c3, c2^2 - 3 c1 c3) is a covariant: H(F o T) = H(F) o T
(det T = +-1).  All forms here have positive discriminant (three real roots), so H is positive
definite; reducing H to |B| <= A <= C and taking the least F o T over the finitely many matrices
that keep H reduced gives a canonical representative: F ~ G iff their canonical forms agree.
The discovered edges are certificates (a matrix and an identity checked by Lean), not a claim
that the search found every equivalence by itself: the canonical form is what makes the class
count exact.
"""
from __future__ import annotations

from itertools import product
from math import gcd

Form = tuple[int, int, int, int]


def compose(F: Form, T) -> Form:
    """F(t11 u + t12 v, t21 u + t22 v) as a form in (u, v)."""
    (t11, t12), (t21, t22) = T
    c0, c1, c2, c3 = F
    # expand sum c_i X^(3-i) Y^i with X = t11 u + t12 v, Y = t21 u + t22 v
    def mul(P, Q):
        out = [0] * (len(P) + len(Q) - 1)
        for i, x in enumerate(P):
            for j, y in enumerate(Q):
                out[i + j] += x * y
        return out
    X, Y = [t11, t12], [t21, t22]           # coefficients of u, v
    res = [0, 0, 0, 0]
    for i, c in enumerate(F):
        term = [1]
        for _ in range(3 - i):
            term = mul(term, X)
        for _ in range(i):
            term = mul(term, Y)
        for j in range(4):
            res[j] += c * term[j]
    return tuple(res)


def evalF(F: Form, a: int, b: int) -> int:
    c0, c1, c2, c3 = F
    return c0 * a ** 3 + c1 * a * a * b + c2 * a * b * b + c3 * b ** 3


def disc(F: Form) -> int:
    a, b, c, d = F
    return b * b * c * c - 4 * a * c ** 3 - 4 * b ** 3 * d - 27 * a * a * d * d + 18 * a * b * c * d


def hessian(F: Form) -> tuple[int, int, int]:
    c0, c1, c2, c3 = F
    return (c1 * c1 - 3 * c0 * c2, c1 * c2 - 9 * c0 * c3, c2 * c2 - 3 * c1 * c3)


def qcompose(H, T):
    A, B, C = H
    (t11, t12), (t21, t22) = T
    return (A * t11 * t11 + B * t11 * t21 + C * t21 * t21,
            2 * A * t11 * t12 + B * (t11 * t22 + t12 * t21) + 2 * C * t21 * t22,
            A * t12 * t12 + B * t12 * t22 + C * t22 * t22)


def matmul(S, T):
    return ((S[0][0] * T[0][0] + S[0][1] * T[1][0], S[0][0] * T[0][1] + S[0][1] * T[1][1]),
            (S[1][0] * T[0][0] + S[1][1] * T[1][0], S[1][0] * T[0][1] + S[1][1] * T[1][1]))


def det(T):
    return T[0][0] * T[1][1] - T[0][1] * T[1][0]


def reduce_hessian(H):
    """(reduced H, T) with H o T reduced, by Gauss reduction of a positive definite form."""
    T = ((1, 0), (0, 1))
    A, B, C = H
    assert A > 0 and B * B - 4 * A * C < 0, 'Hessian must be positive definite'
    while True:
        # translate: make |B| <= A
        if abs(B) > A:
            n = -((B + A) // (2 * A)) if B > 0 else (A - B) // (2 * A)
            n = round(-B / (2 * A))
            S = ((1, n), (0, 1))
            A, B, C = qcompose((A, B, C), S)
            T = matmul(T, S)
            continue
        if A > C:
            S = ((0, -1), (1, 0))
            A, B, C = qcompose((A, B, C), S)
            T = matmul(T, S)
            continue
        return (A, B, C), T


# matrices that can map a reduced positive definite form to a reduced one (automorphs, sign
# flips, swaps): entries bounded by 1 suffice for Gauss-reduced forms
SMALL = [((a, b), (c, d)) for a, b, c, d in product((-1, 0, 1), repeat=4) if a * d - b * c in (1, -1)]


def canonical(F: Form):
    """(canonical form, T) with F o T = canonical form, T in GL_2(Z)."""
    H0, T0 = reduce_hessian(hessian(F))
    best = None
    for S in SMALL:
        H = qcompose(H0, S)
        if not (abs(H[1]) <= H[0] <= H[2]):
            continue
        T = matmul(T0, S)
        G = compose(F, T)
        key = G
        if best is None or key < best[0]:
            best = (key, T)
    return best


def automorphisms(F: Form) -> list:
    """All T in GL_2(Z) with F o T = F (the stabilizer; finite for disc != 0)."""
    G, T0 = canonical(F)
    H0, _ = reduce_hessian(hessian(G))
    out = []
    Hc, Tc = reduce_hessian(hessian(G))
    for S in SMALL:
        H = qcompose(Hc, S)
        if not (abs(H[1]) <= H[0] <= H[2]):
            continue
        U = matmul(matmul(Tc, S), inverse(Tc))
        if compose(G, U) == G:
            out.append(U)
    # conjugate back to F: F o (T0 U T0^-1) = F
    return sorted({matmul(matmul(T0, U), inverse(T0)) for U in out})


def inverse(T):
    d = det(T)
    return ((T[1][1] * d, -T[0][1] * d), (-T[1][0] * d, T[0][0] * d))


def content(F: Form) -> int:
    g = 0
    for c in F:
        g = gcd(g, c)
    return g


def open_equations(ledger: dict) -> list[dict]:
    """Every open branch of every OPEN_BRANCH curve, as a node."""
    from .branch_descent import compile_curve
    nodes = []
    for rec in ledger['curves_detail']:
        if rec['status'] != 'OPEN_BRANCH':
            continue
        D = rec['D']
        c = compile_curve(D)
        for e in c['open']:
            k, p, q = e['k'], e['p'], e['q']
            F = (q, 3 * p, -3 * D * q, -p * D)
            nodes.append({'D': D, 'k': k, 'p': p, 'q': q, 'F': F, 'M': k ** 3})
    return nodes


def classes(nodes: list[dict]) -> dict:
    """Group nodes by (canonical form, M); each node records its edge T to the representative."""
    groups: dict = {}
    for n in nodes:
        G, T = canonical(n['F'])
        n['canonical'] = G
        n['T'] = T
        groups.setdefault((G, n['M']), []).append(n)
    return groups
