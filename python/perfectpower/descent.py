"""Descent certificates for y^2 = x^3 - D (D > 0), discovered here and checked by Lean.

The Lean side is `PerfectPower/Descent.lean`.  For y^2 + D = x^3 the conjugate factors
y + sqrt(-D), y - sqrt(-D) of x^3 lie in Z[sqrt(-D)].  The certificate shows, by finite checks,
that y + sqrt(-D) is a cube:

* a Thue box (r, t) with r^2 + D t^2 < (K + 1) r t, so every relevant norm is at most K;
* the table: for k <= K, |q| <= Q (K^3 < D (Q + 1)^2), every p^2 + D q^2 = k^3 has q = 0 and
  k = j^2 (an ideal class of order 3 would show up here as a representation with q != 0);
* for each such j, `div_ok`: j^3 | (a - b sqrt(-D))^3 implies j | a - b sqrt(-D), checked on
  residues mod j^3 (integral closedness at the primes of j).

Then y = p^3 - 3Dp, x = p^2 + D with 3p^2 - D = +-1, a complete and possibly nonempty list.
Every function here mirrors a Lean definition; nothing here is trusted by the Lean theorem.
"""
from __future__ import annotations

from math import gcd, isqrt


def W1(D: int, a: int, b: int) -> int:
    return a ** 3 - 3 * D * a * b * b


def W2(D: int, a: int, b: int) -> int:
    return D * b ** 3 - 3 * a * a * b


def div_ok(D: int, j: int) -> bool:
    """`Descent.divB`: j^3 | W1, W2 on residues mod j^3 forces j | a, b."""
    M = j ** 3
    for A in range(M):
        for B in range(M):
            if W1(D, A, B) % M == 0 and W2(D, A, B) % M == 0 and (A % j or B % j):
                return False
    return True


def thue_box(D: int, max_t: int = 60) -> tuple[int, int, int]:
    """(K, r, t) with r^2 + D t^2 < (K + 1) r t and K as small as found."""
    best = None
    for t in range(1, max_t + 1):
        r0 = isqrt(D * t * t)
        for r in range(max(1, r0 - 1), r0 + 3):
            K = (r * r + D * t * t) // (r * t)
            if best is None or K < best[0]:
                best = (K, r, t)
    return best


def table(D: int, K: int, Q: int) -> tuple[list, list[int]]:
    """`Descent.tableB`: (failures, the j that occur)."""
    bad, js = [], set()
    for k in range(1, K + 1):
        for q in range(-Q, Q + 1):
            t = k ** 3 - D * q * q
            if t < 0:
                continue
            s = isqrt(t)
            if s * s != t:
                continue
            j = isqrt(k)
            if q != 0 or j * j != k:
                bad.append({'k': k, 'p': s, 'q': q})
            else:
                js.add(j)
    for j in sorted(js):
        if not div_ok(D, j):
            bad.append({'div': j})
    return bad, sorted(js)


def point_list(D: int) -> list[tuple[int, int]]:
    """`Descent.pointList`, in the same order."""
    out = []
    for i in range(2 * D + 3):
        p = i - (D + 1)
        if 3 * p * p - D in (1, -1):
            out.append((p * p + D, p ** 3 - 3 * D * p))
    return out


def class_number(D: int) -> int:
    """h(-4D): reduced primitive forms a x^2 + b x y + c y^2 of discriminant -4D."""
    disc, h, a = -4 * D, 0, 1
    while 3 * a * a <= -disc:
        for b in range(-a + 1, a + 1):
            if (b * b - disc) % (4 * a):
                continue
            c = (b * b - disc) // (4 * a)
            if c < a or (b < 0 and a == c) or gcd(gcd(a, abs(b)), c) != 1:
                continue
            h += 1
        a += 1
    return h


def _squarefree(n: int) -> bool:
    d = 2
    while d * d <= n:
        if n % (d * d) == 0:
            return False
        d += 1
    return True


def certificate(D: int, max_j: int = 5, max_K: int = 200) -> dict | None:
    """The descent certificate for y^2 = x^3 - D, or None when the check fails (then nothing is
    claimed: the class number may be divisible by 3, a non-primitive representation may occur,
    or Z[sqrt(-D)] may not be integrally closed at a prime of j)."""
    if D <= 0:
        return None
    K, r, t = thue_box(D)
    if K > max_K:
        return None
    Q = 0
    while D * (Q + 1) ** 2 <= K ** 3:
        Q += 1
    if isqrt(K) > max_j:
        return None
    bad, js = table(D, K, Q)
    if bad:
        return None
    pts = point_list(D)
    h = class_number(D)
    return {'D': D, 'r': r, 't': t, 'K': K, 'Q': Q, 'j': js, 'points': pts,
            'class_number': h, 'field': f'Q(sqrt(-{D}))',
            'ring': f'Z[sqrt(-{D})]' + (' (the maximal order)' if _squarefree(D) and D % 4 in (1, 2)
                                         else ' (a non-maximal order; the residue checks still pass)'),
            'factorization': f'x^3 = (y + sqrt(-{D}))(y - sqrt(-{D}))',
            'units': '{+1, -1}',
            'why': (f'The class number of {"Z[sqrt(-%d)]" % D} is {h}, prime to 3, so the ideal whose cube is '
                    f'(y + sqrt(-{D})) is principal: the table shows no class of order 3 among norms '
                    f'k <= {K} (Thue box r/t = {r}/{t}). The units are +-1, both cubes, so '
                    f'y + sqrt(-{D}) = (p + q sqrt(-{D}))^3 and q (3p^2 - {D} q^2) = 1.'
                    if h % 3 else
                    f'The table passes although 3 | h = {h}; the conclusion rests on the checked table.'),
            'lean': 'PerfectPower.Descent.hits_of_cert'}


def lean_args(c: dict) -> str:
    """The certificate arguments of `Descent.hits_of_cert` / `complete_of_cert`."""
    return (f"{c['D']} (by norm_num) {c['r']} {c['t']} (by norm_num) (by norm_num) {c['K']} {c['Q']} "
            f"(by norm_num) (by norm_num) (by decide +kernel)")


def affine_hits(c: dict, r: int, s: int) -> list[tuple[int, int]]:
    """(n, m) with n >= 1 and m^2 = (r n + s)^3 - D, from the complete point list."""
    out = []
    for x, y in c['points']:
        if (x - s) % r == 0 and (x - s) // r >= 1:
            out.append(((x - s) // r, y))
    return sorted(out)


def _poly(a: int, b: int, c: int, e: int) -> str:
    out = ''
    for coef, mon in ((a, 'n^3'), (b, 'n^2'), (c, 'n'), (e, '')):
        if coef == 0:
            continue
        body = (f'{abs(coef)} {mon}' if abs(coef) != 1 or not mon else mon).strip()
        out += (' - ' if coef < 0 else ' + ') + body if out else ('-' if coef < 0 else '') + body
    return out or '0'


def lean_theorem(name: str, r: int, s: int, D: int, c: dict | None = None,
                 namespace: str | None = None) -> str:
    """A self-contained Lean theorem: the complete hit set of m^2 = (r n + s)^3 - D, stated on
    the expanded polynomial a n^3 + b n^2 + c n + e."""
    c = c or certificate(D)
    if c is None:
        raise ValueError(f'no descent certificate for D = {D}')
    if r == 0:
        raise ValueError('r must be nonzero')
    a, b, cc, e = r ** 3, 3 * r * r * s, 3 * r * s * s, s ** 3 - D
    hits = affine_hits(c, r, s)
    hl = '[' + ', '.join(f'({n}, ({m} : ℤ))' for n, m in hits) + ']'
    ns = sorted({n for n, _ in hits})
    rhs = ' ∨ '.join(f'n = {n}' for n in ns) if ns else 'False'
    body = (
        f"/-- `m^2 = {_poly(a, b, cc, e)}` (`= ({r} n + {s})^3 - {D}`), `n ≥ 1`, has exactly the\n"
        f"solutions `n ∈ {ns}`.  Descent certificate for `y^2 = x^3 - {D}` in `ℤ[√-{D}]`\n"
        f"(class number {c['class_number']}): Thue box `{c['r']}/{c['t']}`, norms `k ≤ {c['K']}`, `|q| ≤ {c['Q']}`,\n"
        f"cube-root checks for `j ∈ {c['j']}`; points {c['points']}. -/\n"
        f"theorem {name} (n : ℕ) (hn : 1 ≤ n) :\n"
        f"    IsHit 2 ({a} * (n : ℤ) ^ 3 + ({b}) * (n : ℤ) ^ 2 + {cc} * (n : ℤ) + ({e})) ↔ {rhs} := by\n"
        f"  have h := Descent.hits_of_cert {lean_args(c)}\n"
        f"    {r} ({s}) (by norm_num) {a} ({b}) {cc} ({e}) (by norm_num) (by norm_num) (by norm_num) (by norm_num)\n"
        f"    {hl} (by decide +kernel) n hn\n"
        f"  have e : Reflect.ev [{e}, {cc}, {b}, {a}] n = {a} * (n : ℤ) ^ 3 + ({b}) * (n : ℤ) ^ 2 + {cc} * (n : ℤ) + ({e}) := by\n"
        f"    simp only [Reflect.ev]; ring\n"
        f"  rw [e] at h; rw [h]; simp\n")
    return body


def standalone_file(name: str, r: int, s: int, D: int) -> str:
    """A complete `.lean` file for `lake env lean`."""
    return ("import PerfectPower.Descent\n\n"
            "/-! Emitted by `python -m perfectpower prove`; checked by the kernel, not trusted. -/\n\n"
            "open PerfectPower\n\n" + lean_theorem(name, r, s, D) + f"\n#print axioms {name}\n")
